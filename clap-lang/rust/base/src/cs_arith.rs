use crate::{
    cs_constant::Const,
    expr::{apply_renaming, Config, Constr, Gate, Name, NameContext, Renaming, Trace, CV},
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
            // println!("SAT passed {:?}", self);
            // println!("Trace values: a:{:?} b:{:?} c:{:?} d:{:?}", a, b, c, d);
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

// ql l + qr r + qm l r + qc -> c
// =
// if qc, ql, qr, qm /= 0
//   qr ONE r + qc ONE -> w1
//   ONE w1 + ql l -> w2
//   qm l r +  w2 -> d

// if  ql, qr, qm /= 0
//   qr ONE r + ql l -> w2
//   qm l r +  w2 -> d

// if qc, qr, qm /= 0 (or l)
//   qr ONE r + qc ONE -> w1
//   qm l r +  w1 -> d

// if  qr, qm /= 0 (or l)
//   qm l r +  qr r  -> d

// if qc, ql, qr /= 0
//   qr ONE r + qc ONE -> w1
//   ONE w1 + ql l -> d

// if qr /= 0 (or l)
//   qr ONE r + qc ONE -> d

// if ql, qr /= 0
//   qr ONE r + ql l -> d

// if qm /= 0
//   qm l r + qc ONE -> d

// if qc /= 0
//   qc -> d

#[allow(clippy::too_many_arguments)]
fn arith_to_fma_and_const<F: Field + 'static>(
    l: usize,
    r: usize,
    o: usize,
    ql: F,
    qr: F,
    qm: F,
    qc: F,
    ctxt: &mut NameContext<F>,
) -> Vec<Box<dyn CV<F>>> {
    if ql != F::ZERO && qr != F::ZERO && qm != F::ZERO && qc != F::ZERO {
        //   qr ONE r + qc ONE -> w1
        //   ONE w1 + ql l -> w2
        //   qm l r +  w2 -> d
        let (one, one_allocated) = ctxt.push_constant(F::ONE);
        let w1 = ctxt.push_unused();
        let w2 = ctxt.push_unused();
        let f1 = FMA {
            a: one,
            b: r,
            c: one,
            d: w1,
            c0: qr,
            c1: qc,
        };
        let f2 = FMA {
            a: one,
            b: w1,
            c: l,
            c0: F::ONE,
            c1: ql,
            d: w2,
        };
        let f3 = FMA {
            a: l,
            b: r,
            c: w2,
            c0: qm,
            c1: F::ONE,
            d: o,
        };
        let mut all: Vec<Box<dyn CV<F>>> = vec![Box::new(f1), Box::new(f2), Box::new(f3)];
        let c: Vec<Box<dyn CV<F>>> = if one_allocated {
            vec![]
        } else {
            vec![Box::new(Const { x: one, v: F::ONE })]
        };
        all.extend(c);
        all
    } else if ql != F::ZERO && qr != F::ZERO && qm != F::ZERO {
        //   qr ONE r + ql l -> w2
        //   qm l r +  w2 -> d
        let (one, one_allocated) = ctxt.push_constant(F::ONE);
        let w2 = ctxt.push_unused();
        let f2 = FMA {
            a: one,
            b: r,
            c: l,
            c0: qr,
            c1: ql,
            d: w2,
        };
        let f3 = FMA {
            a: l,
            b: r,
            c: w2,
            c0: qm,
            c1: F::ONE,
            d: o,
        };
        let mut all: Vec<Box<dyn CV<F>>> = vec![Box::new(f2), Box::new(f3)];
        let c: Vec<Box<dyn CV<F>>> = if one_allocated {
            vec![]
        } else {
            vec![Box::new(Const { x: one, v: F::ONE })]
        };
        all.extend(c);
        all
    } else if (ql != F::ZERO || qr != F::ZERO) && qm != F::ZERO && qc != F::ZERO {
        let (linear, no_linear, coeff) = if ql != F::ZERO {
            (l, r, ql)
        } else {
            (r, l, qr)
        };
        //   coeff ONE linear + qc ONE -> w1
        //   qm linear no_linear +  w1 -> d
        let (one, one_allocated) = ctxt.push_constant(F::ONE);
        let w1 = ctxt.push_unused();
        let f1 = FMA {
            a: one,
            b: linear,
            c: one,
            d: w1,
            c0: coeff,
            c1: qc,
        };
        let f2 = FMA {
            a: linear,
            b: no_linear,
            c: w1,
            c0: qm,
            c1: F::ONE,
            d: o,
        };
        let mut all: Vec<Box<dyn CV<F>>> = vec![Box::new(f1), Box::new(f2)];
        let c: Vec<Box<dyn CV<F>>> = if one_allocated {
            vec![]
        } else {
            vec![Box::new(Const { x: one, v: F::ONE })]
        };
        all.extend(c);
        all
    } else if (ql != F::ZERO || qr != F::ZERO) && qm != F::ZERO {
        //   qm l r +  qr r  -> d (or l)
        let (linear, no_linear, c1) = if ql != F::ZERO {
            (l, r, ql)
        } else {
            (r, l, qr)
        };
        let f = FMA {
            a: no_linear,
            b: linear,
            c: linear,
            c0: qm,
            c1,
            d: o,
        };
        vec![Box::new(f)]
    } else if ql != F::ZERO && qr != F::ZERO && qc != F::ZERO {
        //   qr ONE r + qc ONE -> w1
        //   ONE w1 + ql l -> d
        let (one, one_allocated) = ctxt.push_constant(F::ONE);
        let w1 = ctxt.push_unused();
        let f1 = FMA {
            a: one,
            b: r,
            c: one,
            d: w1,
            c0: qr,
            c1: qc,
        };
        let f2 = FMA {
            a: one,
            b: w1,
            c: l,
            c0: F::ONE,
            c1: ql,
            d: o,
        };
        let mut all: Vec<Box<dyn CV<F>>> = vec![Box::new(f1), Box::new(f2)];
        let c: Vec<Box<dyn CV<F>>> = if one_allocated {
            vec![]
        } else {
            vec![Box::new(Const { x: one, v: F::ONE })]
        };
        all.extend(c);
        all
    } else if ql != F::ZERO && qr != F::ZERO && qc == F::ZERO {
        let (one, one_allocated) = ctxt.push_constant(F::ONE);
        // ql ONE l + qr r -> w1
        let f = FMA {
            a: one,
            b: l,
            c: r,
            c0: ql,
            c1: qr,
            d: o,
        };
        let mut all: Vec<Box<dyn CV<F>>> = vec![Box::new(f)];
        let c: Vec<Box<dyn CV<F>>> = if one_allocated {
            vec![]
        } else {
            vec![Box::new(Const { x: one, v: F::ONE })]
        };
        all.extend(c);
        all
    } else if ql != F::ZERO || qr != F::ZERO {
        let (linear, coeff) = if ql != F::ZERO { (l, ql) } else { (r, qr) };
        //   coeff ONE linear + qc ONE -> w1
        let (one, one_allocated) = ctxt.push_constant(F::ONE);
        let f = FMA {
            a: one,
            b: linear,
            c: one,
            c0: coeff,
            c1: qc,
            d: o,
        };
        let mut all: Vec<Box<dyn CV<F>>> = vec![Box::new(f)];
        let c: Vec<Box<dyn CV<F>>> = if one_allocated {
            vec![]
        } else {
            vec![Box::new(Const { x: one, v: F::ONE })]
        };
        all.extend(c);
        all
    } else if qm != F::ZERO {
        //   qm l r + qc ONE -> d
        let (one, one_allocated) = ctxt.push_constant(F::ONE);
        let f = FMA {
            a: l,
            b: r,
            c: one,
            c0: qm,
            c1: qc,
            d: o,
        };
        let mut all: Vec<Box<dyn CV<F>>> = vec![Box::new(f)];
        let c: Vec<Box<dyn CV<F>>> = if one_allocated {
            vec![]
        } else {
            vec![Box::new(Const { x: one, v: F::ONE })]
        };
        all.extend(c);
        all
    } else {
        assert!(
            ql == F::ZERO && qr == F::ZERO && qm == F::ZERO,
            "ql: {:?}, l: {:?}, qr: {:?}, r: {:?}, qm: {:?}, qc: {:?}, o:{:?}",
            ql,
            l,
            qr,
            r,
            qm,
            qc,
            o
        );
        let c = Const { x: o, v: qc };
        vec![Box::new(c)]
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

fn gen_trace_fma<F: Field>(
    ga: &GenericArith<F>,
    ctxt: &mut NameContext<F>,
    trace: &mut Trace<F>,
    allocate_o: bool,
) -> bool {
    let (okl, l) = ctxt.read_name(ga.l, trace);
    let (okr, r) = ctxt.read_name(ga.r, trace);
    if allocate_o {
        ctxt.push(ga.o);
    }
    let GenericArith { ql, qr, qm, qc, .. } = *ga;

    if ql != F::ZERO && qr != F::ZERO && qm != F::ZERO && qc != F::ZERO {
        //   qr ONE r + qc ONE -> w1
        //   ONE w1 + ql l -> w2
        //   qm l r +  w2 -> d
        let (_, one_allocated) = ctxt.push_constant(F::ONE);
        ctxt.push_unused();
        ctxt.push_unused();
        let w1 = qr * r + qc;
        let w2 = w1 + ql * l;
        let o = qm * l * r + w2;
        if allocate_o {
            trace.push(o);
        }
        if !one_allocated {
            trace.push(F::ONE)
        }
        trace.push(w1);
        trace.push(w2)
    } else if ql != F::ZERO && qr != F::ZERO && qm != F::ZERO {
        //   qr ONE r + ql l -> w2
        //   qm l r +  w2 -> d
        let (_, one_allocated) = ctxt.push_constant(F::ONE);
        ctxt.push_unused();
        let w2 = qr * r + ql * l;
        let o = qm * l * r + w2;
        if allocate_o {
            trace.push(o);
        }
        if !one_allocated {
            trace.push(F::ONE)
        }
        trace.push(w2)
    } else if (ql != F::ZERO || qr != F::ZERO) && qm != F::ZERO && qc != F::ZERO {
        let (linear, no_linear, coeff) = if ql != F::ZERO {
            (l, r, ql)
        } else {
            (r, l, qr)
        };
        //   coeff ONE linear + qc ONE -> w1
        //   qm linear no_linear +  w1 -> d
        let (_, one_allocated) = ctxt.push_constant(F::ONE);
        ctxt.push_unused();
        let w1 = coeff * linear + qc;
        let o = qm * linear * no_linear + w1;
        if allocate_o {
            trace.push(o);
        }
        if !one_allocated {
            trace.push(F::ONE)
        }
        trace.push(w1);
    } else if (ql != F::ZERO || qr != F::ZERO) && qm != F::ZERO {
        //   qm linear no_linear + coeff linear  -> d
        let (linear, no_linear, coeff) = if ql != F::ZERO {
            (l, r, ql)
        } else {
            (r, l, qr)
        };
        let o = qm * linear * no_linear + coeff * linear;
        if allocate_o {
            trace.push(o);
        }
    } else if ql != F::ZERO && qr != F::ZERO && qc != F::ZERO {
        //   qr ONE r + qc ONE -> w1
        //   ONE w1 + ql l -> d
        let (_, one_allocated) = ctxt.push_constant(F::ONE);
        ctxt.push_unused();
        let w1 = qr * r + qc;
        let o = w1 * r + ql * l;
        if allocate_o {
            trace.push(o);
        }
        if !one_allocated {
            trace.push(F::ONE)
        }
        trace.push(w1);
    } else if ql != F::ZERO && qr != F::ZERO && qc == F::ZERO {
        // ql ONE l + qr r -> o
        let (_, one_allocated) = ctxt.push_constant(F::ONE);
        let o = ql * l + qr * r;
        if allocate_o {
            trace.push(o);
        }
        if !one_allocated {
            trace.push(F::ONE)
        }
    } else if ql != F::ZERO || qr != F::ZERO {
        let (linear, coeff) = if ql != F::ZERO { (l, ql) } else { (r, qr) };
        //   coeff ONE linear + qc ONE -> d
        let (_, one_allocated) = ctxt.push_constant(F::ONE);
        let o = coeff * linear + qc;
        if allocate_o {
            trace.push(o);
        }
        if !one_allocated {
            trace.push(F::ONE)
        }
    } else if qm != F::ZERO {
        //   qm l r + qc ONE -> d
        let (_, one_allocated) = ctxt.push_constant(F::ONE);
        let o = qm * l * r + qc;
        if allocate_o {
            trace.push(o);
        }
        if !one_allocated {
            trace.push(F::ONE)
        }
    } else {
        assert!(
            ql == F::ZERO && qr == F::ZERO && qm == F::ZERO,
            "ql: {:?}, l: {:?}, qr: {:?}, r: {:?}, qm: {:?}, qc: {:?}, o:{:?}",
            ql,
            ga.l,
            qr,
            ga.r,
            qm,
            qc,
            ga.o
        );
        trace.push(qc);
    }
    okl && okr
}

impl<F: Field + 'static> Gate<F> for GenericArith<F> {
    fn kind(&self) -> String {
        "GenericArith".into()
    }

    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        if config.use_fma {
            let l = ctxt.get(self.l);
            let r = ctxt.get(self.r);
            let o = ctxt.get(self.o);
            let all = arith_to_fma_and_const(l, r, o, self.ql, self.qr, self.qm, self.qc, ctxt);
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
            gen_trace_fma(self, ctxt, trace, true)
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

    fn output_vars(&self) -> Vec<Name> {
        vec![self.o]
    }

    fn other_params(&self) -> Vec<u8> {
        let consts = vec![self.ql, self.qr, self.qm, self.qc];
        consts
            .iter()
            .flat_map(|f| f.to_u64().to_be_bytes().to_vec())
            .collect()
    }

    fn rename(&mut self, renaming: &Renaming) {
        self.l = apply_renaming(self.l, renaming);
        self.r = apply_renaming(self.r, renaming);
        self.o = apply_renaming(self.o, renaming);
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

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Assertion<F: Field>(pub GenericArith<F>);

impl<F: Field + 'static> Gate<F> for Assertion<F> {
    fn kind(&self) -> String {
        "Assertion".into()
    }

    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        self.0.gen_cs(config, ctxt)
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        if config.use_fma {
            gen_trace_fma(&self.0, ctxt, trace, false)
        } else {
            true
        }
    }

    fn input_vars(&self) -> Vec<Name> {
        vec![self.0.l, self.0.r, self.0.o]
    }

    fn output_vars(&self) -> Vec<Name> {
        vec![]
    }

    fn other_params(&self) -> Vec<u8> {
        let consts = vec![self.0.ql, self.0.qr, self.0.qm, self.0.qc];
        consts
            .iter()
            .flat_map(|f| f.to_u64().to_be_bytes().to_vec())
            .collect()
    }

    fn clone_box(&self) -> Box<dyn Gate<F>> {
        Box::new(self.clone())
    }

    fn rename(&mut self, renaming: &Renaming) {
        self.0.rename(renaming);
    }
}

impl<F: Field + 'static> std::fmt::Display for Assertion<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
