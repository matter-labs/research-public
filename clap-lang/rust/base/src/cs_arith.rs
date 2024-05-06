use crate::{
    cs_constant::Const,
    expr::{Config, Constr, Gate, Name, NameContext, Trace, CV},
    field::Field,
};
use std::fmt;

#[derive(Debug, Clone)]
pub struct Arith<F: Field> {
    pub ql: F,
    pub l: usize,
    pub qr: F,
    pub r: usize,
    pub qm: F,
    pub qc: F,
    pub qo: F,
    pub o: usize,
}

// A simple gate of c0 * A * B + c1 * C -> D
#[derive(Debug, Clone)]
pub struct FMA<F: Field> {
    pub c0: F,
    pub a: usize,
    pub b: usize,
    pub c1: F,
    pub c: usize,
    pub d: usize,
}

impl<F: fmt::Display + Field> fmt::Display for Arith<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "ql: {}, l: {:?}, qr: {}, r: {:?}, qm: {}, qc: {}, qo:{}, o:{:?}",
            self.ql, self.l, self.qr, self.r, self.qm, self.qc, self.qo, self.o
        )
    }
}

impl<F: fmt::Display + Field> fmt::Display for FMA<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "c0: {}, a: {:?}, b: {:?}, c1: {}, c: {:?}, d:{:?}",
            self.c0, self.a, self.b, self.c1, self.c, self.d
        )
    }
}

impl<F: Field + 'static> CV<F> for Arith<F> {
    fn id(&self) -> String {
        "Arith".into()
    }

    fn width(&self) -> usize {
        3
    }

    fn sat(&self, witness: &Trace<F>) -> bool {
        let (okl, l) = witness.read(self.l);
        let (okr, r) = witness.read(self.r);
        let (oko, o) = witness.read(self.o);
        let s = okl
            && okr
            && oko
            && F::ZERO == self.ql * l + self.qr * r + self.qm * l * r + self.qc + self.qo * o;
        if s {
            true
        } else {
            println!("SAT failed {:?}", self);
            println!("Trace values: l:{:?} r:{:?} o:{:?}", l, r, o);
            false
        }
    }

    fn gen_table(&self, config: &crate::table::CsConfig) -> Vec<Constr<F>> {
        // TODO: selector binary tree
        let n_sels = config.gates.len();
        let qarith_index = config.gates.get_index(self.id());
        let fixed = config.compute_fixed(
            qarith_index.unwrap(),
            vec![self.ql, self.qr, self.qc, self.qm, self.qo],
        );
        let c = Constr {
            variable: vec![self.l, self.r, self.o],
            fixed,
        };
        vec![c]
    }
}

impl<F: Field + 'static> CV<F> for FMA<F> {
    fn id(&self) -> String {
        "FMA".into()
    }

    fn width(&self) -> usize {
        4
    }

    fn sat(&self, witness: &Trace<F>) -> bool {
        let (oka, a) = witness.read(self.a);
        let (okb, b) = witness.read(self.b);
        let (okc, c) = witness.read(self.c);
        let (okd, d) = witness.read(self.d);
        let s = oka && okb && okc && okd && F::ZERO == self.c0 * a * b + self.c1 * c - d;
        if s {
            true
        } else {
            println!("SAT failed {:?}", self);
            println!("Trace values: a:{:?} b:{:?} c:{:?} d:{:?}", a, b, c, d);
            false
        }
    }

    fn gen_table(&self, config: &crate::table::CsConfig) -> Vec<Constr<F>> {
        // TODO: selector binary tree
        let n_sels = config.gates.len();
        let qfma_index = config.gates.get_index(self.id());
        let fixed = config.compute_fixed(qfma_index.unwrap(), vec![self.c0, self.c1]);
        let c = Constr {
            variable: vec![self.a, self.b, self.c, self.d],
            fixed,
        };
        vec![c]
    }
}

// Output is resolved with the identity
// qo = -1
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct GenericArith<F: Field> {
    pub ql: F,
    pub l: Name,
    pub qr: F,
    pub r: Name,
    pub qm: F,
    pub qc: F,
    pub o: Name,
}

impl<F: Field + 'static> Gate<F> for GenericArith<F> {
    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        if config.use_fma {
            let mut all: Vec<Box<dyn CV<F>>> = if self.qm != F::ZERO {
                let a = ctxt.get(self.l);
                let b = ctxt.get(self.r);
                let d = ctxt.get(self.o);
                let (c1, c) = if self.ql != F::ZERO && self.qr == F::ZERO {
                    (self.ql, a)
                } else if self.ql == F::ZERO && self.qr != F::ZERO {
                    (self.qr, b)
                } else {
                    (F::ZERO, 0)
                };
                let fma = FMA {
                    a,
                    b,
                    d,
                    c0: self.qm,
                    c1,
                    c,
                };
                vec![Box::new(fma)]
            } else {
                vec![]
            };
            let add_part: Vec<Box<dyn CV<F>>> = if self.ql != F::ZERO && self.qr != F::ZERO {
                let a = ctxt.get(self.l);
                let c = ctxt.get(self.r);
                let d = ctxt.get(self.o);
                let (b, one_allocated) = ctxt.push_constant(F::ONE);
                let fma = FMA {
                    a,
                    b,
                    d,
                    c1: self.ql,
                    c0: self.qr,
                    c,
                };
                if one_allocated {
                    vec![Box::new(fma)]
                } else {
                    vec![Box::new(fma), Box::new(Const { x: b, v: F::ONE })]
                }
            } else {
                vec![]
            };
            let const_part: Vec<Box<dyn CV<F>>> = if self.qc != F::ZERO {
                let (x, allocated) = ctxt.push_constant(self.qc);
                if allocated {
                    vec![]
                } else {
                    let c = Const { x, v: self.qc };
                    vec![Box::new(c)]
                }
            } else {
                vec![]
            };
            all.extend(add_part);
            all.extend(const_part);
            all
        } else {
            let l = ctxt.get(self.l);
            let r = ctxt.get(self.r);
            let o = ctxt.get(self.o);
            let qo = F::MONE;
            let g = Arith {
                ql: self.ql,
                l,
                qr: self.qr,
                r,
                qc: self.qc,
                qm: self.qm,
                qo,
                o,
            };
            vec![Box::new(g)]
        }
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        if config.use_fma {
            let (okl, l) = ctxt.read_name(self.l, trace);
            let (okr, r) = ctxt.read_name(self.r, trace);
            ctxt.push(self.o);
            let e = self.ql * l + self.qr * r + self.qm * l * r + self.qc;
            trace.push(e);
            let push_1 = self.ql != F::ZERO && self.qr != F::ZERO;
            if push_1 {
                let (_, one_allocated) = ctxt.push_constant(F::ONE);
                if !one_allocated {
                    trace.push(F::ONE)
                }
            }
            okl && okr
        } else {
            let (okl, l) = ctxt.read_name(self.l, trace);
            let (okr, r) = ctxt.read_name(self.r, trace);
            ctxt.push(self.o);
            let e = self.ql * l + self.qr * r + self.qm * l * r + self.qc;
            trace.push(e);
            okl && okr
        }
    }

    fn input_vars(&self) -> Vec<Name> {
        vec![self.l, self.r]
    }

    fn clone_box(&self) -> Box<dyn Gate<F>> {
        Box::new(self.clone())
    }
}

impl<F: Field + 'static> std::fmt::Display for GenericArith<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
