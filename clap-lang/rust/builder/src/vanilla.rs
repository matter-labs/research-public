use array_init::array_init;
use base::circuit::{CVItem, Circuit};
use base::cs_arith::{Assertion, GenericArith};
use base::cs_boolcheck::GBoolCheck;
use base::cs_linear_combination::{AssertionLC, GLinearCombination};
use base::cs_swap::Swap;
use base::expr::{Gate, Name};
use base::field::{Field, SmallField};
use base::flattened::Poseidon2Flattened;
use base::gate_eq0::Eq0;
use base::gate_inv::Inv;
use base::gate_iszero::IsZero;
use base::gate_limb_decomposition::LimbDecomposition;
use base::gate_split_32::Split32;
use base::gate_split_and_rotate::SplitAndRotate;
use base::lookups::{Ch4, Maj4, Merge4BitChunk, TriXor4};
use base::optimizer::Atomic;
use std::marker::PhantomData;
use std::mem::replace;
use std::sync::Arc;
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

#[derive(Clone, Copy, Debug)]
pub struct SVar(pub Name);

impl From<SVar> for Name {
    fn from(SVar(s): SVar) -> Self {
        s
    }
}

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
    type Repr: Clone;

    // fn inject_structure(&self) -> Self::V;
    fn inject_repr(repr: Self::Repr) -> <Self::V as Value<F>>::Repr;
    fn project_repr(repr: <Self::V as Value<F>>::Repr) -> Self::Repr;
    fn inject_value(&self) -> <Self::V as Value<F>>::Emb;
    fn project_value(emb: &<Self::V as Value<F>>::Emb) -> Self;

    fn allocate(&self, start: usize) -> (Self::Repr, usize) {
        let (repr, n) = Self::V::allocate(start);
        (Self::project_repr(repr), n)
    }

    fn constant(&self, env: &mut Env<F>) -> Vec<CVItem<F>> {
        Self::V::constant(env, &self.inject_value())
    }

    fn input(env: &mut TLEnv<F>) -> Self::Repr {
        Self::project_repr(Self::V::input(env))
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
        Self::project_repr(Self::V::ifthenelse(
            env,
            c,
            Self::inject_repr(t),
            Self::inject_repr(e),
        ))
    }
}

impl<F: Field + 'static> Valuable<F> for SValue {
    type V = Self;
    type Repr = <Self as Value<F>>::Repr;

    fn inject_repr(repr: Self::Repr) -> <Self::V as Value<F>>::Repr {
        repr
    }

    fn project_repr(repr: <Self::V as Value<F>>::Repr) -> Self::Repr {
        repr
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
    type Repr = <Self as Value<F>>::Repr;

    fn inject_repr(repr: Self::Repr) -> <Self::V as Value<F>>::Repr {
        repr
    }

    fn project_repr(repr: <Self::V as Value<F>>::Repr) -> Self::Repr {
        repr
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
pub type Repr<F: Field, V: Valuable<F>> = <V as Valuable<F>>::Repr;

#[allow(type_alias_bounds)]
pub type Emb<F: Field, V: Valuable<F>> = <V::V as Value<F>>::Emb;

#[derive(Clone)]
pub struct Env<F: Field + 'static> {
    pub c: Circuit<F>,
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
            Arc::new(replace(&mut self.c, Circuit::Nil(PhantomData))), // Temporarily replace `self.c` with a default value and use the old value
            Arc::new(Circuit::Gate(g)),
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
            Arc::new(replace(&mut self.c, Circuit::Nil(PhantomData))), // Temporarily replace `self.c` with a default value and use the old value
            Arc::new(Circuit::Gate(g)),
        )
    }

    fn append_seq(&mut self, g: CVItem<F>) {
        self.c = Circuit::Seq(
            Arc::new(replace(&mut self.c, Circuit::Nil(PhantomData))), // Temporarily replace `self.c` with a default value and use the old value
            Arc::new(Circuit::Gate(g)),
        )
    }

    fn append_seq_circ(&mut self, c: Circuit<F>) {
        self.c = Circuit::Seq(
            Arc::new(replace(&mut self.c, Circuit::Nil(PhantomData))), // Temporarily replace `self.c` with a default value and use the old value
            Arc::new(c),
        )
    }

    pub fn sync_env(&mut self, isolated: Env<F>) {
        self.append_seq_circ(isolated.c);
        self.next = isolated.next;
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
        W::project_repr(repr)
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

    pub fn assert_eq(&mut self, x: SVar, y: SVar) {
        self.assert_custom(
            x.into(),
            x.into(),
            F::ZERO,
            F::ONE,
            F::ZERO,
            F::ZERO,
            y.into(),
        )
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

    fn custom_arith_gate(
        &mut self,
        l: Name,
        r: Name,
        ql: F,
        qr: F,
        qm: F,
        qc: F,
    ) -> (Name, Box<dyn Gate<F>>) {
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
        (o, Box::new(e))
    }

    #[allow(clippy::too_many_arguments)]
    fn assert_custom_gate(
        &mut self,
        l: Name,
        r: Name,
        ql: F,
        qr: F,
        qm: F,
        qc: F,
        o: Name,
    ) -> Box<dyn Gate<F>> {
        let e = Assertion(GenericArith {
            ql,
            l,
            qr,
            r,
            qm,
            qc,
            o,
        });
        Box::new(e)
    }

    #[allow(clippy::too_many_arguments)]
    fn assert_custom(&mut self, l: Name, r: Name, ql: F, qr: F, qm: F, qc: F, o: Name) {
        let e = self.assert_custom_gate(l, r, ql, qr, qm, qc, o);
        self.append_seq(e)
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
    use boojum::field::goldilocks::GoldilocksField;

    pub trait Sealed {}
    impl Sealed for Fi64 {}
    impl Sealed for GoldilocksField {}
}

impl<F: Field + 'static + private::Sealed> Valuable<F> for F {
    type V = SValue;
    type Repr = SVar;

    fn inject_repr(repr: Self::Repr) -> <Self::V as Value<F>>::Repr {
        repr
    }

    fn project_repr(repr: <Self::V as Value<F>>::Repr) -> Self::Repr {
        repr
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
    type Repr = <Self::V as Value<F>>::Repr;

    // fn inject_structure(&self) -> Self::V {
    //     PairValue {
    //         fst: Point::inject_structure(&self.p1),
    //         snd: Point::inject_structure(&self.p2),
    //         _phantom: PhantomData,
    //     }
    // }

    fn inject_repr(repr: Self::Repr) -> <Self::V as Value<F>>::Repr {
        repr
    }

    fn project_repr(repr: <Self::V as Value<F>>::Repr) -> Self::Repr {
        repr
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
    type Repr = (Repr<F, FF>, Repr<F, FF>);

    // fn inject_structure(&self) -> Self::V {
    //     self.point.inject_structure()
    // }

    fn inject_repr((x, y): Self::Repr) -> <Self::V as Value<F>>::Repr {
        (FF::inject_repr(x), FF::inject_repr(y))
    }

    fn project_repr((x, y): <Self::V as Value<F>>::Repr) -> Self::Repr {
        (FF::project_repr(x), FF::project_repr(y))
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

#[derive(Clone, Copy)]
pub struct StatusVar(Name);

impl<F: Field + 'static> Valuable<F> for Status {
    type V = bool;
    type Repr = StatusVar;

    // fn inject_structure(&self) -> Self::V {
    //     false
    // }

    fn inject_repr(StatusVar(n): Self::Repr) -> <Self::V as Value<F>>::Repr {
        BoolVar(n)
    }

    fn project_repr(BoolVar(n): <Self::V as Value<F>>::Repr) -> Self::Repr {
        StatusVar(n)
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
    type Repr = [T::Repr; N];

    // fn inject_structure(&self) -> Self::V {
    //     self.map(|v| T::inject_structure(&v))
    // }

    fn input(env: &mut TLEnv<F>) -> Self::Repr {
        let mut r: Vec<T::Repr> = vec![];
        for _ in 0..N {
            let i = T::input(env);
            r.push(i)
        }
        match r.try_into() {
            Ok(v) => v,
            _ => unreachable!(),
        }
    }

    fn inject_repr(repr: Self::Repr) -> <Self::V as Value<F>>::Repr {
        repr.map(|r| T::inject_repr(r))
    }

    fn project_repr(repr: <Self::V as Value<F>>::Repr) -> Self::Repr {
        repr.map(|r| T::project_repr(r))
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
    type Repr = (Fst::Repr, Snd::Repr);

    fn inject_repr((f, s): Self::Repr) -> <Self::V as Value<F>>::Repr {
        (Fst::inject_repr(f), Snd::inject_repr(s))
    }

    fn project_repr((f, s): <Self::V as Value<F>>::Repr) -> Self::Repr {
        (Fst::project_repr(f), Snd::project_repr(s))
    }

    fn inject_value(&self) -> Emb<F, Self> {
        (Fst::inject_value(&self.0), Snd::inject_value(&self.1))
    }

    fn project_value((le, re): &Emb<F, Self>) -> Self {
        (Fst::project_value(le), Snd::project_value(re))
    }
}

pub trait ScalarLike<F: Field + 'static>: Valuable<F> {
    fn scalar(v: Repr<F, Self>) -> Repr<F, SValue>;
}

impl<F: Field + 'static> ScalarLike<F> for SValue {
    fn scalar(v: Repr<F, Self>) -> Repr<F, SValue> {
        v
    }
}
#[derive(Clone, Copy)]
pub struct U32Var(Name);

#[allow(clippy::missing_safety_doc)]
impl U32Var {
    pub unsafe fn from_variable_unchecked(v: SVar) -> Self {
        Self(v.0)
    }
}

impl Default for U32Var {
    fn default() -> Self {
        U32Var(Name::Unused)
    }
}

impl From<U32Var> for SVar {
    fn from(U32Var(v): U32Var) -> Self {
        SVar(v)
    }
}

impl<F: Field + 'static> Valuable<F> for u32 {
    type V = SValue;
    type Repr = U32Var;

    fn inject_repr(U32Var(n): Self::Repr) -> <Self::V as Value<F>>::Repr {
        SVar(n)
    }

    fn project_repr(SVar(n): <Self::V as Value<F>>::Repr) -> Self::Repr {
        U32Var(n)
    }

    fn inject_value(&self) -> Emb<F, Self> {
        F::from_u32(*self)
    }

    fn project_value(emb: &Emb<F, Self>) -> Self {
        emb.to_u32()
    }
}

impl<F: Field + 'static> ScalarLike<F> for u32 {
    fn scalar(v: Repr<F, Self>) -> Repr<F, SValue> {
        SVar(v.0)
    }
}

#[derive(Clone, Copy)]
pub struct U16Var(Name);

impl From<U16Var> for SVar {
    fn from(U16Var(v): U16Var) -> Self {
        SVar(v)
    }
}

impl Default for U16Var {
    fn default() -> Self {
        U16Var(Name::Unused)
    }
}

impl<F: Field + 'static> Valuable<F> for u16 {
    type V = SValue;
    type Repr = U16Var;

    fn inject_repr(U16Var(n): Self::Repr) -> <Self::V as Value<F>>::Repr {
        SVar(n)
    }

    fn project_repr(SVar(n): <Self::V as Value<F>>::Repr) -> Self::Repr {
        U16Var(n)
    }

    fn inject_value(&self) -> Emb<F, Self> {
        F::from_u32(*self as u32)
    }

    fn project_value(emb: &Emb<F, Self>) -> Self {
        emb.to_u32() as u16
    }
}

impl<F: Field + 'static> ScalarLike<F> for u16 {
    fn scalar(v: Repr<F, Self>) -> Repr<F, SValue> {
        SVar(v.0)
    }
}

#[derive(Clone, Copy)]
pub struct U36(u64);

#[derive(Clone, Copy)]
pub struct U36Var(Name);

impl<F: Field + 'static> Valuable<F> for U36 {
    type V = SValue;
    type Repr = U36Var;

    fn inject_repr(U36Var(n): Self::Repr) -> <Self::V as Value<F>>::Repr {
        SVar(n)
    }

    fn project_repr(SVar(n): <Self::V as Value<F>>::Repr) -> Self::Repr {
        U36Var(n)
    }

    fn inject_value(&self) -> Emb<F, Self> {
        F::from_u64(self.0)
    }

    fn project_value(emb: &Emb<F, Self>) -> Self {
        Self(emb.to_u64())
    }
}

#[derive(Clone, Copy)]
pub struct U4(u8);

#[derive(Clone, Copy)]
pub struct U4Var(Name);

impl From<U4Var> for SVar {
    fn from(U4Var(v): U4Var) -> Self {
        SVar(v)
    }
}

impl Default for U4Var {
    fn default() -> Self {
        U4Var(Name::Unused)
    }
}

impl<F: Field + 'static> Valuable<F> for U4 {
    type V = SValue;
    type Repr = U4Var;

    fn inject_repr(U4Var(n): Self::Repr) -> <Self::V as Value<F>>::Repr {
        SVar(n)
    }

    fn project_repr(SVar(n): <Self::V as Value<F>>::Repr) -> Self::Repr {
        U4Var(n)
    }

    fn inject_value(&self) -> Emb<F, Self> {
        F::from_u64(self.0 as u64)
    }

    fn project_value(emb: &Emb<F, Self>) -> Self {
        Self(emb.to_u64().try_into().unwrap())
    }
}

impl<F: Field + 'static> ScalarLike<F> for U4 {
    fn scalar(v: Repr<F, Self>) -> Repr<F, SValue> {
        SVar(v.0)
    }
}

#[derive(Clone, Copy)]
pub struct U8Var(Name);

impl Default for U8Var {
    fn default() -> Self {
        U8Var(Name::Unused)
    }
}

impl From<U8Var> for SVar {
    fn from(U8Var(v): U8Var) -> Self {
        SVar(v)
    }
}

#[allow(clippy::missing_safety_doc)]
impl U8Var {
    pub unsafe fn from_variable_unchecked(v: SVar) -> Self {
        Self(v.0)
    }
}

impl<F: SmallField + 'static> Valuable<F> for u8 {
    // TODO: automatic range checks for inputs?
    type V = SValue;
    type Repr = U8Var;

    fn input(e: &mut TLEnv<F>) -> Self::Repr {
        let repr = Name::Input(e.next);
        e.next += 1;
        let TLEnv { c, next, n_inputs } = e;
        let mut tmp = Env {
            c: c.clone(),
            next: *next,
        };
        range_check_u8(&mut tmp, SVar(repr));
        *e = TLEnv {
            c: tmp.c,
            next: tmp.next,
            n_inputs: *n_inputs,
        };
        U8Var(repr)
    }

    fn inject_repr(U8Var(n): Self::Repr) -> <Self::V as Value<F>>::Repr {
        SVar(n)
    }

    fn project_repr(SVar(n): <Self::V as Value<F>>::Repr) -> Self::Repr {
        U8Var(n)
    }

    fn inject_value(&self) -> Emb<F, Self> {
        F::from_u32(*self as u32)
    }

    fn project_value(emb: &Emb<F, Self>) -> Self {
        emb.to_u32().try_into().unwrap()
    }
}

impl<F: SmallField + 'static> ScalarLike<F> for u8 {
    fn scalar(v: Repr<F, Self>) -> Repr<F, SValue> {
        SVar(v.0)
    }
}

pub fn split_36_bits<F: SmallField>(
    cs: &mut Env<F>,
    input: Repr<F, SValue>,
) -> (Repr<F, u32>, Repr<F, U4>) {
    let (u32_part, chunks, range_check) = range_check_36_bits_using_sha256_tables_gate(cs, input);
    let low = u32_part;
    let high = chunks[8];
    let e = Split32 {
        i: input.0,
        oh: high.0,
        ol: low.0,
        range_check: Some(range_check),
    };
    cs.append_seq(Box::new(e));
    (U32Var(low.0), U4Var(high.0))
}

pub fn tri_xor_many<F: SmallField, S: ScalarLike<F>, const N: usize>(
    cs: &mut Env<F>,
    a: &[Repr<F, S>; N],
    b: &[Repr<F, S>; N],
    c: &[Repr<F, S>; N],
) -> [Repr<F, U4>; N] {
    let result = array_init(|_| SVar(cs.fresh()));
    for (((a, b), c), o) in a.iter().zip(b.iter()).zip(c.iter()).zip(result.iter()) {
        let e = TriXor4 {
            a: S::scalar(a.clone()).0,
            b: S::scalar(b.clone()).0,
            c: S::scalar(c.clone()).0,
            o: o.0,
        };
        cs.append_seq(Box::new(e));
    }
    result.map(|SVar(x)| U4Var(x))
}

pub fn ch_many<F: SmallField, S: ScalarLike<F>, const N: usize>(
    cs: &mut Env<F>,
    a: &[Repr<F, S>; N],
    b: &[Repr<F, S>; N],
    c: &[Repr<F, S>; N],
) -> [Repr<F, U4>; N] {
    let result = array_init(|_| SVar(cs.fresh()));
    for (((a, b), c), o) in a.iter().zip(b.iter()).zip(c.iter()).zip(result.iter()) {
        let e = Ch4 {
            a: S::scalar(a.clone()).0,
            b: S::scalar(b.clone()).0,
            c: S::scalar(c.clone()).0,
            o: o.0,
        };
        cs.append_seq(Box::new(e));
    }
    result.map(|SVar(x)| U4Var(x))
}

pub fn maj_many<F: SmallField, S: ScalarLike<F>, const N: usize>(
    cs: &mut Env<F>,
    a: &[Repr<F, S>; N],
    b: &[Repr<F, S>; N],
    c: &[Repr<F, S>; N],
) -> [Repr<F, U4>; N] {
    let result = array_init(|_| SVar(cs.fresh()));
    for (((a, b), c), o) in a.iter().zip(b.iter()).zip(c.iter()).zip(result.iter()) {
        let e = Maj4 {
            a: S::scalar(a.clone()).0,
            b: S::scalar(b.clone()).0,
            c: S::scalar(c.clone()).0,
            o: o.0,
        };
        cs.append_seq(Box::new(e));
    }
    result.map(|SVar(x)| U4Var(x))
}

fn tri_xor_gate<F: SmallField>(
    cs: &mut Env<F>,
    a: Repr<F, SValue>,
    b: Repr<F, SValue>,
    c: Repr<F, SValue>,
) -> Box<dyn Gate<F>> {
    let o = cs.fresh();
    let e = TriXor4 {
        a: a.0,
        b: b.0,
        c: c.0,
        o,
    };
    Box::new(e)
}

fn reduce_terms_gate<F: Field, S: ScalarLike<F>>(
    cs: &mut Env<F>,
    coeffs: [F; 4],
    vars: [Repr<F, S>; 4],
) -> (SVar, Box<dyn Gate<F>>) {
    let o = cs.fresh();
    let gate: GLinearCombination<F, Name, 4> = GLinearCombination {
        coeffs,
        vars: vars.map(|v| S::scalar(v).0),
        o,
    };
    (SVar(o), Box::new(gate))
}

pub fn reduce_terms<F: Field, S: ScalarLike<F>>(
    cs: &mut Env<F>,
    coeffs: [F; 4],
    vars: [Repr<F, S>; 4],
) -> SVar {
    let (o, g) = reduce_terms_gate::<F, S>(cs, coeffs, vars);
    cs.append_seq(g);
    o
}

pub fn reduce_terms_by_constant<F: Field, S: ScalarLike<F>>(
    cs: &mut Env<F>,
    reduction_constant: F,
    terms: [Repr<F, S>; 4],
) -> SVar {
    let mut reduction_constants = [F::ZERO; 4];
    reduction_constants[0] = F::ONE;
    let mut current = F::ONE;
    for dst in reduction_constants[1..].iter_mut() {
        current = current * reduction_constant;
        *dst = current;
    }
    reduce_terms::<F, S>(cs, reduction_constants, terms)
}

#[allow(clippy::type_complexity)]
fn chunks_into_u16_low_high_gates<F: SmallField>(
    cs: &mut Env<F>,
    chunks: [Repr<F, U4>; 8],
) -> (Repr<F, u16>, Repr<F, u16>, Vec<Box<dyn Gate<F>>>) {
    let chunks = chunks.map(|n| SVar(n.0));
    let to_u16_constants = [
        F::ONE,
        F::from_u64(1u64 << 4),
        F::from_u64(1u64 << 8),
        F::from_u64(1u64 << 12),
    ];

    let (SVar(low_u16), gate_1) = reduce_terms_gate::<F, SValue>(
        cs,
        to_u16_constants,
        [chunks[0], chunks[1], chunks[2], chunks[3]],
    );
    let (SVar(high_u16), gate_2) = reduce_terms_gate::<F, SValue>(
        cs,
        to_u16_constants,
        [chunks[4], chunks[5], chunks[6], chunks[7]],
    );
    (U16Var(low_u16), U16Var(high_u16), vec![gate_1, gate_2])
}

#[allow(clippy::type_complexity)]
pub fn chunks_into_u16_low_high<F: SmallField>(
    cs: &mut Env<F>,
    chunks: [Repr<F, U4>; 8],
) -> (Repr<F, u16>, Repr<F, u16>) {
    let (low, high, gs) = chunks_into_u16_low_high_gates(cs, chunks);
    gs.into_iter().for_each(|g| cs.append_seq(g));
    (low, high)
}

#[allow(clippy::type_complexity)]
fn range_check_36_bits_using_sha256_tables_gate<F: SmallField>(
    cs: &mut Env<F>,
    i: Repr<F, SValue>,
) -> (Repr<F, u32>, [Repr<F, U4>; 9], Box<dyn Gate<F>>) {
    let result: [SVar; 9] = array_init(|_| SVar(cs.fresh()));
    let result_as_u4 = result.map(|SVar(x)| U4Var(x));
    let (low_u16, high_u16, mut recomposition) =
        chunks_into_u16_low_high_gates(cs, result_as_u4[..8].try_into().unwrap());
    let (u32_part, g1) = cs.custom_arith_gate(
        low_u16.0,
        high_u16.0,
        F::ONE,
        F::from_u64(1u64 << 16),
        F::ZERO,
        F::ZERO,
    );
    // u32_part + 1<<32 * result[8] = input
    let g2 = cs.assert_custom_gate(
        u32_part,
        result[8].0,
        F::ONE,
        F::from_u64(1u64 << 16),
        F::ZERO,
        F::ZERO,
        i.0,
    );
    recomposition.push(g1);
    recomposition.push(g2);
    let e: LimbDecomposition<F, 9, 4> = LimbDecomposition {
        i: i.0,
        o: result.map(|v| v.0),
        recomposition,
        u4_rcs: result.map(|v| v.0).to_vec(),
        u32_part: Some(u32_part),
    };
    (
        U32Var(u32_part),
        result.map(|SVar(x)| U4Var(x)),
        Box::new(e),
    )
}

pub fn range_check_36_bits_using_sha256_tables<F: SmallField>(
    cs: &mut Env<F>,
    i: Repr<F, SValue>,
) -> (Repr<F, u32>, [Repr<F, U4>; 9]) {
    let (u32_part, chunks, gate) = range_check_36_bits_using_sha256_tables_gate(cs, i);
    cs.append_seq(gate);
    (u32_part, chunks)
}

pub fn range_check_32_bits_using_sha256_tables<F: SmallField>(
    cs: &mut Env<F>,
    i: Repr<F, SValue>,
) -> (Repr<F, u32>, [Repr<F, U4>; 8]) {
    let chunks = uint32_into_4bit_chunks(cs, U32Var(i.0));
    (U32Var(i.0), chunks)
}

pub fn uint32_into_4bit_chunks<F: SmallField>(
    cs: &mut Env<F>,
    i: Repr<F, u32>,
) -> [Repr<F, U4>; 8] {
    let result = array_init(|_| SVar(cs.fresh()));
    let result_as_u4 = result.map(|SVar(x)| U4Var(x));
    let (low_u16, high_u16, mut recomposition) = chunks_into_u16_low_high_gates(cs, result_as_u4);
    // low_16 + 1<<16 * high_u16 = i
    let g = cs.assert_custom_gate(
        low_u16.0,
        high_u16.0,
        F::ONE,
        F::from_u64(1u64 << 16),
        F::ZERO,
        F::ZERO,
        i.0,
    );
    recomposition.push(g);
    let e: LimbDecomposition<F, 8, 4> = LimbDecomposition {
        i: i.0,
        o: result.map(|v| v.0),
        recomposition,
        u4_rcs: result.map(|v| v.0).to_vec(),
        u32_part: Some(i.0),
    };
    cs.append_seq(Box::new(e));
    result.map(|SVar(x)| U4Var(x))
}

pub fn range_check_u8<F: SmallField>(cs: &mut Env<F>, i: Repr<F, SValue>) -> Repr<F, u8> {
    let result = array_init(|_| SVar(cs.fresh()));
    let g = cs.assert_custom_gate(
        result[0].0,
        result[1].0,
        F::ONE,
        F::from_u64(1u64 << 4),
        F::ZERO,
        F::ZERO,
        i.0,
    );
    let recomposition = vec![g];
    let e: LimbDecomposition<F, 2, 4> = LimbDecomposition {
        i: i.0,
        o: result.map(|v| v.0),
        recomposition,
        u4_rcs: result.map(|v| v.0).to_vec(),
        u32_part: None,
    };
    cs.append_seq(Box::new(e));
    U8Var(i.0)
}

fn merge_4bit_chunk_gate<F: SmallField, const SPLIT_AT: usize>(
    cs: &mut Env<F>,
    low: Repr<F, U4>,
    high: Repr<F, U4>,
    swap_output: bool,
) -> (Repr<F, U4>, Box<dyn Gate<F>>) {
    let reconstructed = cs.fresh();
    let swapped = cs.fresh();
    let e = Merge4BitChunk::<SPLIT_AT> {
        low: low.0,
        high: high.0,
        reconstructed,
        swapped,
    };
    let e = Box::new(e);
    if swap_output {
        (U4Var(swapped), e)
    } else {
        (U4Var(reconstructed), e)
    }
}

pub fn merge_4bit_chunk<F: SmallField, const SPLIT_AT: usize>(
    cs: &mut Env<F>,
    low: Repr<F, U4>,
    high: Repr<F, U4>,
    swap_output: bool,
) -> Repr<F, U4> {
    let (x, _e) = merge_4bit_chunk_gate::<F, SPLIT_AT>(cs, low, high, swap_output);
    x
}

#[allow(clippy::type_complexity)]
pub fn split_and_rotate<F: SmallField>(
    cs: &mut Env<F>,
    input: Repr<F, u32>,
    rotation: usize,
) -> ([Repr<F, U4>; 8], Repr<F, U4>, Repr<F, U4>) {
    let rotate_mod = rotation % 4;

    let decompose_low = cs.fresh();
    let aligned_variables: [SVar; 7] = array_init(|_| SVar(cs.fresh()));
    let decompose_high = cs.fresh();

    // Recomposition
    let mut coeffs = [F::ZERO; 4];
    let mut shift = 0;
    for (idx, dst) in coeffs.iter_mut().enumerate() {
        *dst = F::from_u64(1u64 << shift);

        if idx == 0 {
            shift += rotate_mod;
        } else {
            shift += 4;
        }
    }

    let (t, g1) = reduce_terms_gate::<F, SValue>(
        cs,
        coeffs,
        [
            SVar(decompose_low),
            aligned_variables[0],
            aligned_variables[1],
            aligned_variables[2],
        ],
    );

    for (_idx, dst) in coeffs.iter_mut().enumerate().skip(1) {
        *dst = F::from_u64(1u64 << shift);
        shift += 4;
    }
    coeffs[0] = F::ONE;

    let (t, g2) = reduce_terms_gate::<F, SValue>(
        cs,
        coeffs,
        [
            t,
            aligned_variables[3],
            aligned_variables[4],
            aligned_variables[5],
        ],
    );

    for (_idx, dst) in coeffs.iter_mut().enumerate().skip(1).take(2) {
        *dst = F::from_u64(1u64 << shift);
        shift += 4;
    }
    coeffs[0] = F::ONE;
    coeffs[3] = F::ZERO;

    let g3 = Box::new(AssertionLC(GLinearCombination {
        coeffs,
        // Use t in the last position as a dummy, it's multiplied
        // by 0 anyways
        vars: [t.0, aligned_variables[6].0, decompose_high, t.0],
        o: input.0,
    }));

    // now we merge once, and leave other chunks aligned
    let (merged, g4) = match rotate_mod {
        1 => {
            // 1 bit becomes high, so we swap inputs,
            // and swap result
            merge_4bit_chunk_gate::<_, 1>(cs, U4Var(decompose_low), U4Var(decompose_high), true)
        }
        2 => {
            // here we can use as is
            merge_4bit_chunk_gate::<_, 2>(cs, U4Var(decompose_high), U4Var(decompose_low), false)
        }
        3 => {
            // 3 bit becomes high, so we do as is
            merge_4bit_chunk_gate::<_, 1>(cs, U4Var(decompose_high), U4Var(decompose_low), false)
        }
        _ => unreachable!(),
    };

    // Add split_and_rotate gate

    let (_, _, range_check) = range_check_36_bits_using_sha256_tables_gate(cs, input.into());

    let recomposition = vec![g1, g2, g3, g4];

    let e = SplitAndRotate {
        rotation,
        i: input.0,
        aligned_variables: aligned_variables.map(|v| v.0),
        decompose_low,
        decompose_high,
        range_check: Some(range_check),
        recomposition,
    };
    cs.append_seq(Box::new(e));

    let mut result: [U4Var; 8] = [U4Var(Name::Unused); 8];

    // copy in proper places
    let full_rotations = rotation / 4;
    // e.g. if we rotate by 7, then 1st aligned variable will still become highest
    for (idx, el) in aligned_variables.into_iter().enumerate() {
        result[(8 - full_rotations + idx) % 8] = U4Var(el.0);
    }
    // and place merged piece
    result[(8 - full_rotations - 1) % 8] = merged;

    (result, U4Var(decompose_low), U4Var(decompose_high))
}

use base::optimizer::NF;

pub fn poseidon2_flattened<F: Field + 'static>(
    cs: &mut Env<F>,
    inputs: [Repr<F, SValue>; 12],
    outputs: [Repr<F, SValue>; 12],
    atomics: Vec<Atomic<NF<F>>>,
) {
    let inputs: [Name; 12] = inputs.map(|s| s.into());
    let outputs: [Name; 12] = outputs.map(|s| s.into());
    let atomics: [Atomic<NF<F>>; 118] = atomics.try_into().unwrap();
    let e = Poseidon2Flattened {
        inputs,
        outputs,
        atomics,
    };
    cs.append_seq(Box::new(e))
}

#[cfg(test)]
mod test {
    use base::field::Fi64;
    use boojum::field::goldilocks::GoldilocksField;

    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq)]
    struct Foo {
        bar: [(u32, bool); 4],
        baz: u8,
    }

    impl<F: SmallField + 'static> Valuable<F> for Foo {
        type V = PairValue<F, [PairValue<F, SValue, bool>; 4], SValue>;
        type Repr = Repr<F, ([(u32, bool); 4], u8)>;

        fn inject_repr((pairs, snd): Self::Repr) -> <Self::V as Value<F>>::Repr {
            let fst = <[(u32, bool); 4] as Valuable<F>>::inject_repr(pairs);
            let snd = <u8 as Valuable<F>>::inject_repr(snd);
            (fst, snd)
        }

        fn project_repr((pairs, snd): <Self::V as Value<F>>::Repr) -> Self::Repr {
            let fst = <[(u32, bool); 4] as Valuable<F>>::project_repr(pairs);
            let snd = <u8 as Valuable<F>>::project_repr(snd);
            (fst, snd)
        }

        fn inject_value(&self) -> Emb<F, Self> {
            (self.bar.inject_value(), self.baz.inject_value())
        }

        fn project_value(emb: &Emb<F, Self>) -> Self {
            Self {
                bar: <[(u32, bool); 4] as Valuable<F>>::project_value(&emb.0),
                baz: <u8 as Valuable<F>>::project_value(&emb.1),
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
        let serialized: Vec<GoldilocksField> = dummy.serialize();
        println!("serialized: {:?}", serialized);
        let (deserialized, rest) = <Foo as Valuable<GoldilocksField>>::deserialize(serialized);
        println!("deserialized: {:?}", deserialized);
        println!("rest: {:?}", rest);
        assert_eq!(deserialized, dummy);
        assert!(rest.is_empty())
    }

    fn add_point_spec<F: Field>(p1: PointS<F>, p2: PointS<F>) -> PointS<F> {
        let x3 = p1.0 + p2.0;
        let y3 = p1.1 + p2.1;
        (x3, y3)
    }
}
