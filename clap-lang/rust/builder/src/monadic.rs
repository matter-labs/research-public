use std::marker::PhantomData;
use std::mem::replace;

use base::circuit::*;
use base::expr::Expr;
use base::field::*;
use monadic::{
    state::{get, put, State},
    stdo,
};

pub trait Value<F: Field> {
    type Repr: Clone;
    type Emb;

    fn serialize(start: usize, e: &Self::Emb) -> (Self::Repr, usize);

    fn allocate(repr: &Self::Repr, emb: &Self::Emb) -> Circuit<F>;
}

// Types of values we support
pub struct SValue {}
pub struct BoolValue {}

pub struct PairValue<F: Field, Fst: Value<F>, Snd: Value<F>> {
    _phantom: PhantomData<(F, Fst, Snd)>,
}

impl<F: Field> Value<F> for SValue {
    type Repr = usize;
    type Emb = F;

    fn serialize(start: usize, _e: &Self::Emb) -> (Self::Repr, usize) {
        (start, 1)
    }

    fn allocate(repr: &Self::Repr, emb: &Self::Emb) -> Circuit<F> {
        Circuit::Var(*repr, Box::new(Expr::C(*emb)))
    }
}

impl<F: Field> Value<F> for BoolValue {
    type Repr = usize;
    type Emb = bool;

    fn serialize(start: usize, _e: &Self::Emb) -> (Self::Repr, usize) {
        (start, 1)
    }

    fn allocate(repr: &Self::Repr, emb: &Self::Emb) -> Circuit<F> {
        let s = if *emb { F::ONE } else { F::ZERO };
        // assert bool constraint?
        Circuit::Var(*repr, Box::new(Expr::C(s)))
    }
}

impl<F: Field, Fst: Value<F>, Snd: Value<F>> Value<F> for PairValue<F, Fst, Snd> {
    type Repr = (Fst::Repr, Snd::Repr);
    type Emb = (Fst::Emb, Snd::Emb);

    fn serialize(start: usize, (le, re): &Self::Emb) -> (Self::Repr, usize) {
        let (l, sl) = Fst::serialize(start, le);
        let (r, sr) = Snd::serialize(start + sl, re);
        ((l, r), sl + sr)
    }

    fn allocate((lr, rr): &Self::Repr, (le, re): &Self::Emb) -> Circuit<F> {
        let lc = Fst::allocate(lr, le);
        let rc = Snd::allocate(rr, re);
        Circuit::Par(Box::new(lc), Box::new(rc))
    }
}

pub struct Repr<F: Field, V: Value<F>>(V::Repr);
pub struct Emb<F: Field, V: Value<F>>(V::Emb);

#[derive(Debug, Clone)]
pub struct Env<F: Field> {
    c: Circuit<F>,
    next: usize,
    input_phase: bool,
}

impl<F: Field> Default for Env<F> {
    fn default() -> Self {
        Env {
            c: Circuit::Nil,
            next: 0,
            input_phase: true,
        }
    }
}

impl<F: Field> Env<F> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn get_circuit(self) -> Circuit<F> {
        self.c
    }
}

impl<F: Field> Env<F> {
    fn append_par_m(c: &Circuit<F>) -> State<'_, Env<F>, ()> {
        stdo!(
          old_env <- get();
          let old_c = old_env.c;
          let new_c =  Circuit::Par(
            Box::new(old_c),
            Box::new(c.clone())
          );
          let e = Env{c:new_c, next:0, input_phase:true};
          put(e)
        )
    }

    fn append_seq_m(c: &Circuit<F>) -> State<'_, Env<F>, ()> {
        stdo!(
          old_env <- get();
          let old_c = old_env.c;
          let new_c =  Circuit::Seq(
            Box::new(old_c),
            Box::new(c.clone())
          );
          let e = Env{c:new_c, next:0, input_phase:true};
          put(e)
        )
    }

    fn append_par(&mut self, c: Circuit<F>) {
        self.c = Circuit::Par(
            Box::new(replace(&mut self.c, Circuit::Nil)), // Temporarily replace `self.c` with a default value and use the old value
            Box::new(c),
        )
    }

    fn append_seq(&mut self, c: Circuit<F>) {
        self.c = Circuit::Seq(
            Box::new(replace(&mut self.c, Circuit::Nil)), // Temporarily replace `self.c` with a default value and use the old value
            Box::new(c),
        )
    }

    // pub fn cM<V: Value<F>>(e: &V::Emb) -> State<'_, Env<F>, Repr<F, V>> {
    //     stdo!(
    //       old_env <- get();
    //       // let x = V::serialize(old_env.next, &e);
    //       // let c = V::allocate(&x.0, &e);
    //       // self.append_par(c);
    //       // let next =  x.1 + old_env.next;
    //       todo!()
    //       // pure Repr(repr)
    //     )
    // }

    pub fn c<V: Value<F>>(&mut self, e: V::Emb) -> Repr<F, V> {
        let (repr, added) = V::serialize(self.next, &e);
        let c = V::allocate(&repr, &e);
        self.append_par(c);
        self.next += added;
        Repr(repr)
    }

    pub fn eq0(&mut self, Repr(i): Repr<F, SValue>) {
        self.append_seq(Circuit::Eq0(Box::new(Expr::V(i))));
        self.input_phase = false
    }

    pub fn input(&mut self) -> Repr<F, SValue> {
        assert!(self.input_phase);
        let var = self.next;
        self.next += 1;
        Repr(var)
    }

    pub fn input_bool(&mut self) -> Repr<F, BoolValue> {
        assert!(self.input_phase);
        let var = self.next;
        self.next += 1;
        Repr(var)
    }

    pub fn add(&mut self, Repr(l): Repr<F, SValue>, Repr(r): Repr<F, SValue>) -> Repr<F, SValue> {
        let o = self.next;
        self.next += 1;
        self.append_seq(Circuit::Var(
            o,
            Box::new(Expr::Add(Box::new(Expr::V(l)), Box::new(Expr::V(r)))),
        ));
        Repr(o)
    }

    // l ≠ 0  <=>  ∃ r ≠ 0 : l * r - 1 = 0
    pub fn assert_not_zero(&mut self, Repr(_s): Repr<F, SValue>) {
        todo!()
    }

    pub fn and(
        &mut self,
        Repr(_l): Repr<F, BoolValue>,
        Repr(_r): Repr<F, BoolValue>,
    ) -> Repr<F, BoolValue> {
        todo!()
    }
}

type Point<F> = PairValue<F, SValue, SValue>;

pub fn make_pair<F: Field, Fst: Value<F>, Snd: Value<F>>(
    fst: Repr<F, Fst>,
    snd: Repr<F, Snd>,
) -> Repr<F, PairValue<F, Fst, Snd>> {
    let Repr(x) = fst;
    let Repr(y) = snd;
    Repr((x, y))
}

impl<F: Field> Env<F> {
    // Point helpers
    pub fn input_point(&mut self) -> Repr<F, Point<F>> {
        assert!(self.input_phase);
        let Repr(x) = self.input();
        let Repr(y) = self.input();
        Repr((x, y))
    }

    // pub fn c_point(&mut self, x: F, y: F) -> Repr<F, Point<F>> {
    //     let Repr(x) = self.c(x);
    //     let Repr(y) = self.c(y);
    //     Repr((x, y))
    // }

    pub fn add_point(&mut self, p1: Repr<F, Point<F>>, p2: Repr<F, Point<F>>) -> Repr<F, Point<F>> {
        let Repr((x1, x2)) = p1;
        let Repr((y1, y2)) = p2;
        let Repr(o1) = self.add(Repr(x1), Repr(y1));
        let Repr(o2) = self.add(Repr(x2), Repr(y2));
        Repr((o1, o2))
    }
}
