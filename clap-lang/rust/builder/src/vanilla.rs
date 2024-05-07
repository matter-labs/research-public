use base::circuit::{CVItem, Circuit};
use base::cs_arith::GenericArith;
use base::cs_boolcheck::GBoolCheck;
use base::cs_swap::Swap;
use base::expr::Name;
use base::field::Field;
use base::gate_eq0::Eq0;
use base::gate_inv::Inv;
use base::gate_iszero::IsZero;
use std::marker::PhantomData;
use std::mem::replace;
use std::vec;

pub trait Value<F: Field + 'static> {
    type Repr: Clone;
    type Emb: Clone;

    fn allocate(start: usize) -> (Self::Repr, usize);

    fn constant(env: &mut Env<F>, emb: &Self::Emb) -> Vec<CVItem<F>>;

    fn input(env: &mut TLEnv<F>) -> Self::Repr;

    fn serialize(emb: &Self::Emb) -> Vec<F>;

    fn deserialize(w: Vec<F>) -> (Self::Emb, Vec<F>);

    fn ifthenelse(env: &mut Env<F>, c: Repr<F, bool>, t: Self::Repr, e: Self::Repr) -> Self::Repr;
}

// Types of values we support
#[derive(Clone, Copy)]
pub struct SValue {}

#[derive(Clone, Copy)]
pub struct SVar(Name);

pub const DUMMY_SVAR: SVar = SVar(Name::Unused);

#[derive(Clone, Copy)]
pub struct BoolVar(Name);

#[derive(Clone, Copy)]
pub struct PairValue<F: Field + 'static, Fst: Value<F>, Snd: Value<F>> {
    pub fst: Fst,
    pub snd: Snd,
    pub _phantom: PhantomData<F>,
}

pub struct VecValue<F: Field + 'static, El: Value<F>> {
    pub v: Vec<El>,
    pub _phantom: PhantomData<F>,
}

impl<F: Field + 'static> Value<F> for SValue {
    type Repr = SVar;
    type Emb = F;

    fn allocate(start: usize) -> (Self::Repr, usize) {
        (SVar(Name::Wire(start)), 1)
    }

    fn constant(env: &mut Env<F>, emb: &Self::Emb) -> Vec<CVItem<F>> {
        let o = env.fresh();
        let e = GenericArith {
            ql: F::ZERO,
            l: Name::Unused,
            qr: F::ZERO,
            r: Name::Unused,
            qm: F::ZERO,
            qc: *emb,
            o,
        };
        vec![Box::new(e)]
    }

    fn input(e: &mut TLEnv<F>) -> Self::Repr {
        let repr = Name::Input(e.next);
        e.next += 1;
        SVar(repr)
    }

    fn serialize(emb: &Self::Emb) -> Vec<F> {
        vec![*emb]
    }

    fn deserialize(w: Vec<F>) -> (Self::Emb, Vec<F>) {
        (w[0], w[1..].to_vec())
    }

    fn ifthenelse(
        env: &mut Env<F>,
        c: Repr<F, bool>,
        SVar(t): Self::Repr,
        SVar(e): Self::Repr,
    ) -> Self::Repr {
        let (_, x) = env.swap(c, t, e);
        SVar(x)
    }
}

impl<F: Field + 'static> Value<F> for bool {
    type Repr = BoolVar;
    type Emb = bool;

    fn allocate(start: usize) -> (Self::Repr, usize) {
        (BoolVar(Name::Wire(start)), 1)
    }

    fn constant(env: &mut Env<F>, emb: &Self::Emb) -> Vec<CVItem<F>> {
        let s = if *emb { F::ONE } else { F::ZERO };
        let o = env.fresh();
        let e = GenericArith {
            ql: F::ZERO,
            l: Name::Unused,
            qr: F::ZERO,
            r: Name::Unused,
            qm: F::ZERO,
            qc: s,
            o,
        };
        vec![Box::new(e)]
    }

    fn input(e: &mut TLEnv<F>) -> Self::Repr {
        let repr = Name::Input(e.next);
        e.next += 1;
        e.append_par(Box::new(GBoolCheck(repr)));
        BoolVar(repr)
    }

    fn serialize(emb: &Self::Emb) -> Vec<F> {
        let s = if *emb { F::ONE } else { F::ZERO };
        vec![s]
    }

    fn deserialize(w: Vec<F>) -> (Self::Emb, Vec<F>) {
        let tail = w[1..].to_vec();
        if w[0] == F::ZERO {
            (false, tail)
        } else {
            (true, tail)
        }
    }
    fn ifthenelse(
        env: &mut Env<F>,
        c: Repr<F, bool>,
        BoolVar(t): Self::Repr,
        BoolVar(e): Self::Repr,
    ) -> Self::Repr {
        let (_, x) = env.swap(c, t, e);
        BoolVar(x)
    }
}

impl<F: Field, Fst: Value<F>, Snd: Value<F>> Value<F> for PairValue<F, Fst, Snd> {
    type Repr = (Fst::Repr, Snd::Repr);
    type Emb = (Fst::Emb, Snd::Emb);

    fn allocate(start: usize) -> (Self::Repr, usize) {
        let (l, sl) = Fst::allocate(start);
        let (r, sr) = Snd::allocate(start + sl);
        ((l, r), sl + sr)
    }

    fn constant(env: &mut Env<F>, (le, re): &Self::Emb) -> Vec<CVItem<F>> {
        let mut lc = Fst::constant(env, le);
        let rc = Snd::constant(env, re);
        lc.extend(rc);
        lc
    }

    fn input(e: &mut TLEnv<F>) -> Self::Repr {
        let lc = Fst::input(e);
        let rc = Snd::input(e);
        (lc, rc)
    }

    fn serialize((le, re): &Self::Emb) -> Vec<F> {
        let mut lv = Fst::serialize(le);
        let rv = Snd::serialize(re);
        lv.extend(rv);
        lv
    }

    fn deserialize(w: Vec<F>) -> (Self::Emb, Vec<F>) {
        let (l, w) = Fst::deserialize(w);
        let (r, w) = Snd::deserialize(w);
        ((l, r), w)
    }
    fn ifthenelse(env: &mut Env<F>, c: Repr<F, bool>, t: Self::Repr, e: Self::Repr) -> Self::Repr {
        let l = Fst::ifthenelse(env, c, t.0, e.0);
        let r = Snd::ifthenelse(env, c, t.1, e.1);
        (l, r)
    }
}

// fn par_chain<F: Field>(circuits: Vec<Circuit<F>>) -> Circuit<F> {
//     circuits
//         .into_iter()
//         .fold(Circuit::Nil(PhantomData), |acc, c| {
//             Circuit::Par(Box::new(acc), Box::new(c))
//         })
// }

// impl<F: Field, El: Value<F>> Value<F> for VecValue<F, El> {
//     type Repr = Vec<El::Repr>;
//     type Emb = Vec<El::Emb>;

//     fn allocate(start: Name) -> (Self::Repr, usize) {
//         let mut reprs: Self::Repr = vec![];
//         let n = self.v.iter().fold(start, |acc, el| {
//             let (r, n) = el.allocate(acc);
//             reprs.push(r);
//             acc + n
//         });
//         (reprs, n)
//     }

//     fn constant(emb: &Self::Emb) -> Circuit<F> {
//         let circuits = emb.iter().map(El::constant).collect();
//         par_chain(circuits)
//     }

//     fn input(&self, env: &mut Env<F>) -> Self::Repr {
//         self.v.iter().map(|el| El::input(el, env)).collect()
//     }

//     fn forget(emb: &Self::Emb) -> Self {
//         let v = emb.iter().map(El::forget).collect();
//         Self {
//             v,
//             _phantom: PhantomData,
//         }
//     }
//     fn serialize(emb: &Self::Emb) -> Vec<F> {
//         emb.iter().flat_map(El::serialize).collect()
//     }

//     fn deserialize(_w: Vec<F>) -> (Self::Emb, Vec<F>) {
//         // This isn't trivial!
//         // We could add a witness for the structure (sth of type Self)
//         todo!()
//     }
// }

pub trait Valuable<F: Field + 'static>: Sized {
    type V: Value<F> + Copy;

    fn inject_structure(&self) -> Self::V;
    fn inject_value(&self) -> Emb<F, Self>;
    fn project_value(emb: &Emb<F, Self>) -> Self;

    fn allocate(&self, start: usize) -> (Repr<F, Self>, usize) {
        Self::V::allocate(start)
    }

    fn constant(&self, env: &mut Env<F>) -> Vec<CVItem<F>> {
        Self::V::constant(env, &self.inject_value())
    }

    fn input(env: &mut TLEnv<F>) -> Repr<F, Self> {
        Self::V::input(env)
    }

    fn serialize(&self) -> Vec<F> {
        Self::V::serialize(&self.inject_value())
    }

    fn deserialize(w: Vec<F>) -> (Self, Vec<F>) {
        let (e, w) = Self::V::deserialize(w);
        (Self::project_value(&e), w)
    }

    fn ifthenelse(
        env: &mut Env<F>,
        c: Repr<F, bool>,
        t: Repr<F, Self>,
        e: Repr<F, Self>,
    ) -> Repr<F, Self> {
        Self::V::ifthenelse(env, c, t, e)
    }
}

impl<F: Field + 'static> Valuable<F> for SValue {
    type V = Self;

    fn inject_structure(&self) -> Self::V {
        *self
    }

    fn inject_value(&self) -> Emb<F, Self> {
        // Default dummy value
        F::ZERO
    }

    fn project_value(_emb: &Emb<F, Self>) -> Self {
        SValue {}
    }
}

impl<F: Field + 'static> Valuable<F> for bool {
    type V = Self;

    fn inject_structure(&self) -> Self::V {
        *self
    }

    fn inject_value(&self) -> Emb<F, Self> {
        // Default dummy value
        false
    }

    fn project_value(emb: &Emb<F, Self>) -> Self {
        *emb
    }
}

#[allow(type_alias_bounds)]
pub type Repr<F: Field, V: Valuable<F>> = <V::V as Value<F>>::Repr;

#[allow(type_alias_bounds)]
pub type Emb<F: Field, V: Valuable<F>> = <V::V as Value<F>>::Emb;

pub struct Env<F: Field + 'static> {
    c: Circuit<F>,
    next: usize,
}

// Top level Env for processing inputs
pub struct TLEnv<F: Field + 'static> {
    c: Circuit<F>,
    next: usize,
    n_inputs: usize,
}

impl<F: Field + 'static> TLEnv<F> {
    fn fresh_non_input(&mut self) -> Name {
        let var = self.next;
        self.next += 1;
        Name::Wire(var)
    }

    fn fresh_input(&mut self) -> Name {
        let var = self.n_inputs;
        self.n_inputs += 1;
        Name::Input(var)
    }

    pub fn new() -> Self {
        Self::default()
    }

    pub fn seal_inputs(&self) -> Env<F> {
        Env {
            c: self.c.clone(),
            next: self.next,
        }
    }

    fn append_par(&mut self, g: CVItem<F>) {
        self.c = Circuit::Par(
            Box::new(replace(&mut self.c, Circuit::Nil(PhantomData))), // Temporarily replace `self.c` with a default value and use the old value
            Box::new(Circuit::Gate(g)),
        )
    }
}

impl<F: Field> Default for TLEnv<F> {
    fn default() -> Self {
        TLEnv {
            c: Circuit::empty(),
            next: 0,
            n_inputs: 0,
        }
    }
}

impl<F: Field> Env<F> {
    pub fn get_circuit(self) -> Circuit<F> {
        self.c
    }
}

impl<F: Field + 'static> Env<F> {
    fn extend_par(&mut self, items: Vec<CVItem<F>>) {
        items.into_iter().for_each(|g| self.append_par(g))
    }

    fn append_par(&mut self, g: CVItem<F>) {
        self.c = Circuit::Par(
            Box::new(replace(&mut self.c, Circuit::Nil(PhantomData))), // Temporarily replace `self.c` with a default value and use the old value
            Box::new(Circuit::Gate(g)),
        )
    }
    fn append_seq(&mut self, g: CVItem<F>) {
        self.c = Circuit::Seq(
            Box::new(replace(&mut self.c, Circuit::Nil(PhantomData))), // Temporarily replace `self.c` with a default value and use the old value
            Box::new(Circuit::Gate(g)),
        )
    }

    fn fresh(&mut self) -> Name {
        let var = self.next;
        self.next += 1;
        Name::Wire(var)
    }

    pub fn c<W: Valuable<F>>(&mut self, e: <W::V as Value<F>>::Emb) -> Repr<F, W> {
        let (repr, added) = W::V::allocate(self.next);
        let c = W::V::constant(self, &e);
        self.extend_par(c);
        self.next += added;
        repr
    }

    fn swap(&mut self, BoolVar(b): Repr<F, bool>, l: Name, r: Name) -> (Name, Name) {
        let o1 = self.fresh();
        let o2 = self.fresh();
        let e = Swap { b, l, r, o1, o2 };
        self.append_seq(Box::new(e));
        (o1, o2)
    }

    pub fn eq0(&mut self, SVar(i): Repr<F, SValue>) {
        self.append_seq(Box::new(Eq0(i)))
    }

    fn custom(&mut self, l: Name, r: Name, ql: F, qr: F, qm: F, qc: F) -> Repr<F, SValue> {
        let o = self.fresh();
        let e = GenericArith {
            ql,
            l,
            qr,
            r,
            qm,
            qc,
            o,
        };
        self.append_seq(Box::new(e));
        SVar(o)
    }

    // For testing, less efficient than using BoolCheck
    // b * (b - 1) = 0   =>    b^2 - b = 0
    pub fn assert_bool_arith(&mut self, SVar(l): Repr<F, SValue>) {
        let o = self.custom(l, l, F::MONE, F::ZERO, F::ONE, F::ZERO);
        self.eq0(o)
    }

    pub fn inv(&mut self, SVar(x): Repr<F, SValue>) -> Repr<F, SValue> {
        let i = self.fresh();
        self.append_seq(Box::new(Inv { x, i }));
        SVar(i)
    }

    pub fn is_zero(&mut self, SVar(x): Repr<F, SValue>) -> Repr<F, bool> {
        let b = self.fresh();
        self.append_seq(Box::new(IsZero { x, b }));
        BoolVar(b)
    }

    pub fn add(&mut self, SVar(l): Repr<F, SValue>, SVar(r): Repr<F, SValue>) -> Repr<F, SValue> {
        self.custom(l, r, F::ONE, F::ONE, F::ZERO, F::ZERO)
    }

    pub fn mul(&mut self, SVar(l): Repr<F, SValue>, SVar(r): Repr<F, SValue>) -> Repr<F, SValue> {
        self.custom(l, r, F::ZERO, F::ZERO, F::ONE, F::ZERO)
    }

    pub fn add_constant(&mut self, SVar(l): Repr<F, SValue>, c: F) -> Repr<F, SValue> {
        self.custom(l, Name::Unused, F::ONE, F::ZERO, F::ZERO, c)
    }

    pub fn add_with_coeff(
        &mut self,
        SVar(l): Repr<F, SValue>,
        SVar(r): Repr<F, SValue>,
        q: F,
    ) -> Repr<F, SValue> {
        self.custom(l, r, F::ONE, q, F::ZERO, F::ZERO)
    }

    pub fn linear_combination(&mut self, terms: Vec<(Repr<F, SValue>, F)>) -> Repr<F, SValue> {
        let zero = self.c::<SValue>(F::ZERO);
        terms
            .iter()
            .fold(zero, |acc, (v, q)| self.add_with_coeff(acc, *v, *q))
    }

    // l ≠ 0  <=>  ∃ r ≠ 0 : l * r - 1 = 0
    pub fn assert_not_zero(&mut self, s: Repr<F, SValue>) {
        self.inv(s);
    }

    // For test only, not optimal
    pub fn assert_not_zero_naive(&mut self, s: Repr<F, SValue>) {
        let b = self.is_zero(s);
        self.eq0(Self::bool_to_scalar(b))
    }

    fn bool_to_scalar(BoolVar(b): Repr<F, bool>) -> Repr<F, SValue> {
        SVar(b)
    }

    fn unsafe_scalar_to_bool(SVar(s): Repr<F, SValue>) -> Repr<F, bool> {
        BoolVar(s)
    }

    fn eq_const(&mut self, SVar(s): Repr<F, SValue>, c: F) -> Repr<F, bool> {
        // l - C = 0
        Self::unsafe_scalar_to_bool(self.custom(
            s,
            s,
            F::ONE,
            F::ZERO,
            F::ZERO,
            base::field::Field::mul(c, F::MONE),
        ))
    }

    pub fn assert_bool_value(&mut self, b: Repr<F, bool>, v: bool) {
        let v = if v { F::ONE } else { F::ZERO };
        self.eq_const(Self::bool_to_scalar(b), v);
    }

    pub fn and(&mut self, BoolVar(l): Repr<F, bool>, BoolVar(r): Repr<F, bool>) -> Repr<F, bool> {
        Self::unsafe_scalar_to_bool(self.custom(l, r, F::ZERO, F::ZERO, F::ONE, F::ZERO))
    }

    pub fn or(&mut self, BoolVar(l): Repr<F, bool>, BoolVar(r): Repr<F, bool>) -> Repr<F, bool> {
        // l + r  - l * r
        Self::unsafe_scalar_to_bool(self.custom(l, r, F::ONE, F::ONE, F::ONE, F::ZERO))
    }

    pub fn not(&mut self, BoolVar(x): Repr<F, bool>) -> Repr<F, bool> {
        // 1 - x
        Self::unsafe_scalar_to_bool(self.custom(x, Name::Unused, F::MONE, F::ZERO, F::ZERO, F::ONE))
    }

    pub fn xor(&mut self, l: Repr<F, bool>, r: Repr<F, bool>) -> Repr<F, bool> {
        // (l ∧ ¬r) ∨ (¬l ∧ r)
        let nr = self.not(r);
        let lnr = self.and(l, nr);
        let nl = self.not(l);
        let nlr = self.and(nl, r);
        self.or(lnr, nlr)
    }

    pub fn nor(&mut self, l: Repr<F, bool>, r: Repr<F, bool>) -> Repr<F, bool> {
        // ¬(l ∨ r)
        let lr = self.or(l, r);
        self.not(lr)
    }

    pub fn ifthenelse<T: Valuable<F>>(
        &mut self,
        c: Repr<F, bool>,
        t: Repr<F, T>,
        e: Repr<F, T>,
    ) -> Repr<F, T> {
        T::ifthenelse(self, c, t, e)
    }
}

pub type Point<V> = (V, V);

#[allow(type_alias_bounds)]
pub type PointS<F: Field> = Point<F>;

mod private {
    use base::field::Fi64;

    pub trait Sealed {}
    impl Sealed for Fi64 {}
}

impl<F: Field + 'static + private::Sealed> Valuable<F> for F {
    type V = SValue;

    fn inject_structure(&self) -> Self::V {
        SValue {}
    }

    fn inject_value(&self) -> Emb<F, Self> {
        *self
    }

    fn project_value(emb: &Emb<F, Self>) -> Self {
        *emb
    }
}

impl<F: Field + 'static + private::Sealed> Env<F> {
    pub fn add_point(
        &mut self,
        p1: Repr<F, PointS<F>>,
        p2: Repr<F, PointS<F>>,
    ) -> Repr<F, PointS<F>> {
        let (x1, x2) = p1;
        let (y1, y2) = p2;
        let o1 = self.add(x1, y1);
        let o2 = self.add(x2, y2);
        (o1, o2)
    }
}

// Extensions, no need to define Value impl.
// This could be derived in simple enough cases.
#[derive(Clone)]
pub struct Line<F: Field> {
    p1: PointS<F>,
    p2: PointS<F>,
}

impl<F: Field + 'static + private::Sealed> Valuable<F> for Line<F> {
    type V = PairValue<F, <PointS<F> as Valuable<F>>::V, <PointS<F> as Valuable<F>>::V>;

    fn inject_structure(&self) -> Self::V {
        PairValue {
            fst: Point::inject_structure(&self.p1),
            snd: Point::inject_structure(&self.p2),
            _phantom: PhantomData,
        }
    }

    fn inject_value(&self) -> Emb<F, Self> {
        (Point::inject_value(&self.p1), Point::inject_value(&self.p2))
    }

    fn project_value((p1, p2): &Emb<F, Self>) -> Self {
        Self {
            p1: Point::project_value(p1),
            p2: Point::project_value(p2),
        }
    }
}

impl<F: Field + 'static + private::Sealed> Env<F> {
    pub fn line_foo(&mut self, line: Repr<F, Line<F>>) -> Repr<F, SValue> {
        let (p1, p2) = line;
        let _p = self.add_point(p1, p2);
        todo!()
    }
}

use pairing::GenericCurveAffine;

trait ForeignField<F: Field + 'static, T: pairing::ff::PrimeField>: Valuable<F> + Sized
where
    <Self as Valuable<F>>::V: Value<F, Emb = T>,
{
    fn add(env: &mut Env<F>, x: &Repr<F, Self>, y: &Repr<F, Self>) -> Repr<F, Self>;

    fn sub(env: &mut Env<F>, x: &Repr<F, Self>, y: &Repr<F, Self>) -> Repr<F, Self>;

    fn mul(env: &mut Env<F>, x: &Repr<F, Self>, y: &Repr<F, Self>) -> Repr<F, Self>;

    fn div_unchecked(env: &mut Env<F>, x: &Repr<F, Self>, y: &Repr<F, Self>) -> Repr<F, Self>;

    fn equal(env: &mut Env<F>, x: &Repr<F, Self>, y: &Repr<F, Self>) -> Repr<F, bool>;
}

#[derive(Clone)]
struct ECPoint<F: Field + 'static, C: GenericCurveAffine, FF: ForeignField<F, C::Base>>
where
    C::Base: pairing::ff::PrimeField,
    <FF as Valuable<F>>::V: Value<F, Emb = C::Base>,
{
    point: Point<FF>,
    _phantom: PhantomData<(F, C, FF)>,
}

impl<F: Field, C: GenericCurveAffine, FF: ForeignField<F, C::Base>> Valuable<F>
    for ECPoint<F, C, FF>
where
    C::Base: pairing::ff::PrimeField,
    <FF as Valuable<F>>::V: Value<F, Emb = C::Base>,
{
    type V = PairValue<F, <FF as Valuable<F>>::V, <FF as Valuable<F>>::V>;

    fn inject_structure(&self) -> Self::V {
        self.point.inject_structure()
    }

    fn inject_value(&self) -> Emb<F, Self> {
        self.point.inject_value()
    }
    fn project_value(emb: &Emb<F, Self>) -> Self {
        Self {
            point: Point::project_value(emb),
            _phantom: PhantomData,
        }
    }
}

impl<F: Field + 'static, C: GenericCurveAffine, FF: ForeignField<F, C::Base>> ECPoint<F, C, FF>
where
    C::Base: pairing::ff::PrimeField,
    <FF as Valuable<F>>::V: Value<F, Emb = C::Base>,
{
    fn zero_point(env: &mut Env<F>) -> Repr<F, Self> {
        use pairing::ff::Field;
        let zero_ff = env.c::<FF>(C::Base::zero());
        (zero_ff.clone(), zero_ff)
    }

    fn add_unequal(
        e: &mut Env<F>,
        (a_x, a_y): Repr<F, Self>,
        (b_x, b_y): Repr<F, Self>,
    ) -> Repr<F, Self> {
        let same_x = FF::equal(e, &a_x, &b_x);
        e.assert_bool_value(same_x, false);

        // slope = (a_x - b_x) / (a_y - b_y)
        let divisor = FF::sub(e, &a_x, &b_x);
        let numerator = FF::sub(e, &a_y, &b_y);
        let slope = FF::div_unchecked(e, &numerator, &divisor);

        // c_x = slope^2 - a_x - b_x
        let slope2 = FF::mul(e, &slope, &slope);
        let tmp = FF::sub(e, &a_x, &b_y);
        let c_x = FF::sub(e, &slope2, &tmp);

        // c_y = slope (a_x − c_x) − a_y
        let tmp = FF::sub(e, &a_x, &c_x);
        let c_y = FF::mul(e, &slope, &tmp);
        let c_y = FF::sub(e, &tmp, &c_y);

        (c_x, c_y)
    }
}

#[derive(Clone)]
enum Status {
    On,
    Off,
}

impl<F: Field + 'static> Valuable<F> for Status {
    type V = bool;

    fn inject_structure(&self) -> Self::V {
        false
    }

    fn inject_value(&self) -> Emb<F, Self> {
        match self {
            Status::On => true,
            Status::Off => false,
        }
    }

    fn project_value(emb: &Emb<F, Self>) -> Self {
        if *emb {
            Status::On
        } else {
            Status::Off
        }
    }
}

impl<F: Field + 'static, T: Value<F> + Clone, const N: usize> Value<F> for [T; N] {
    type Repr = [T::Repr; N];
    type Emb = [T::Emb; N];

    fn allocate(start: usize) -> (Self::Repr, usize) {
        let mut reprs = vec![];
        let mut acc = start;
        for _ in 0..N {
            let (r, n) = T::allocate(acc);
            reprs.push(r);
            acc += n
        }
        match reprs.try_into() {
            Ok(repr) => (repr, acc),
            Err(_) => panic!(),
        }
    }

    fn constant(env: &mut Env<F>, emb: &Self::Emb) -> Vec<CVItem<F>> {
        let circuits = emb.iter().flat_map(|emb| T::constant(env, emb));
        circuits.collect()
    }

    fn input(env: &mut TLEnv<F>) -> Self::Repr {
        let mut reprs = vec![];
        for _ in 0..N {
            let repr = T::input(env);
            reprs.push(repr);
        }
        match reprs.try_into() {
            Ok(reprs) => reprs,
            Err(_) => panic!(),
        }
    }

    fn serialize(emb: &Self::Emb) -> Vec<F> {
        emb.iter().flat_map(T::serialize).collect()
    }

    fn deserialize(w: Vec<F>) -> (Self::Emb, Vec<F>) {
        let mut embs = vec![];
        let mut w = w;
        for _ in 0..N {
            let (e, rest) = T::deserialize(w);
            embs.push(e);
            w = rest;
        }
        match embs.try_into() {
            Ok(embs) => (embs, w),
            Err(_) => panic!(),
        }
    }
    fn ifthenelse(env: &mut Env<F>, c: Repr<F, bool>, t: Self::Repr, e: Self::Repr) -> Self::Repr {
        let mut reprs = vec![];
        for i in 0..N {
            let repr = T::ifthenelse(env, c, t[i].clone(), e[i].clone());
            reprs.push(repr);
        }
        match reprs.try_into() {
            Ok(reprs) => reprs,
            Err(_) => panic!(),
        }
    }
}

impl<F: Field + 'static, T: Valuable<F> + Copy, const N: usize> Valuable<F> for [T; N] {
    type V = [T::V; N];
    fn inject_structure(&self) -> Self::V {
        self.map(|v| T::inject_structure(&v))
    }
    fn inject_value(&self) -> Emb<F, Self> {
        self.map(|v| T::inject_value(&v))
    }
    fn project_value(emb: &Emb<F, Self>) -> Self {
        emb.clone().map(|inner| T::project_value(&inner))
    }
}

impl<F: Field + 'static, Fst: Valuable<F>, Snd: Valuable<F>> Valuable<F> for (Fst, Snd) {
    type V = PairValue<F, Fst::V, Snd::V>;

    fn inject_structure(&self) -> Self::V {
        PairValue {
            fst: Fst::inject_structure(&self.0),
            snd: Snd::inject_structure(&self.1),
            _phantom: PhantomData,
        }
    }

    fn inject_value(&self) -> Emb<F, Self> {
        (Fst::inject_value(&self.0), Snd::inject_value(&self.1))
    }

    fn project_value((le, re): &Emb<F, Self>) -> Self {
        (Fst::project_value(le), Snd::project_value(re))
    }
}

impl<F: Field + 'static> Valuable<F> for u32 {
    type V = SValue;

    fn inject_structure(&self) -> Self::V {
        SValue {}
    }

    fn inject_value(&self) -> Emb<F, Self> {
        F::from_u32(*self)
    }

    fn project_value(emb: &Emb<F, Self>) -> Self {
        emb.to_u32()
    }
}

#[cfg(test)]
mod test {
    use base::field::Fi64;

    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq)]
    struct Foo {
        bar: [(u32, bool); 4],
        baz: u32,
    }

    impl<F: Field + 'static> Valuable<F> for Foo {
        type V = PairValue<F, [PairValue<F, SValue, bool>; 4], SValue>;

        fn inject_structure(&self) -> Self::V {
            PairValue {
                fst: self.bar.inject_structure(),
                snd: <u32 as Valuable<F>>::inject_structure(&self.baz),
                _phantom: PhantomData,
            }
        }

        fn inject_value(&self) -> Emb<F, Self> {
            (self.bar.inject_value(), self.baz.inject_value())
        }

        fn project_value(emb: &Emb<F, Self>) -> Self {
            Self {
                bar: <[(u32, bool); 4] as Valuable<F>>::project_value(&emb.0),
                baz: <u32 as Valuable<F>>::project_value(&emb.1),
            }
        }
    }

    #[test]
    fn test_serializer_roundtrip() {
        let dummy = Foo {
            bar: [(1_u32, true), (2_u32, false), (3_u32, true), (4_u32, false)],
            baz: 42,
        };
        println!("initial: {:?}", dummy);
        let serialized: Vec<Fi64> = dummy.serialize();
        println!("serialized: {:?}", serialized);
        let (deserialized, rest) = <Foo as Valuable<Fi64>>::deserialize(serialized);
        println!("deserialized: {:?}", deserialized);
        println!("rest: {:?}", rest);
        assert_eq!(deserialized, dummy);
        assert_eq!(rest, vec![])
    }

    fn add_point_spec<F: Field>(p1: PointS<F>, p2: PointS<F>) -> PointS<F> {
        let x3 = p1.0 + p2.0;
        let y3 = p1.1 + p2.1;
        (x3, y3)
    }
}
