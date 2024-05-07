use crate::{
    expr::{Config, Constr, Gate, Name, NameContext, Trace, CV},
    field::Field,
};

//  b should already be enforced to be boolean
//  [(1-b)·l + b·r - o1]
//  [b·l + (1-b)·r - o2]
#[derive(Debug, Clone)]
pub struct GSwap<V> {
    pub b: V,
    pub l: V,
    pub r: V,
    pub o1: V,
    pub o2: V,
}

pub type Swap = GSwap<Name>;

pub type SwapCV = GSwap<usize>;

impl<F: Field + 'static> CV<F> for SwapCV {
    fn id(&self) -> String {
        "Swap".into()
    }

    fn width(&self) -> usize {
        5
    }

    fn sat(&self, witness: &Trace<F>) -> bool {
        let (okl, b) = witness.read(self.b);
        let (okl, l) = witness.read(self.l);
        let (okr, r) = witness.read(self.r);
        let (oko1, o1) = witness.read(self.o1);
        let (oko2, o2) = witness.read(self.o2);
        okl && okr
            && oko1
            && oko2
            && F::ZERO == (F::ONE - b) * l + b * r - o1
            && F::ZERO == b * l + (F::ONE - b) * r - o2
    }

    fn gen_table(&self, config: &crate::table::CsConfig) -> Vec<Constr<F>> {
        let n_sels = config.gates.len();
        let qswap_index = config.gates.get_index(<Self as CV<F>>::id(self));
        let fixed = config.compute_fixed(qswap_index.unwrap(), vec![]);
        let c = Constr {
            variable: vec![self.b, self.l, self.r, self.o1, self.o2],
            fixed,
        };
        vec![c]
    }
}

impl<F: Field + 'static> Gate<F> for Swap {
    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        let b = ctxt.get(self.b);
        let l = ctxt.get(self.l);
        let r = ctxt.get(self.r);
        let o1 = ctxt.get(self.o1);
        let o2 = ctxt.get(self.o2);
        let g = GSwap { b, l, r, o1, o2 };
        vec![Box::new(g)]
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        let (bb, b) = ctxt.read_name(self.b, trace);
        let (bl, l) = ctxt.read_name(self.l, trace);
        let (br, r) = ctxt.read_name(self.r, trace);
        ctxt.push(self.o1);
        ctxt.push(self.o2);
        let (o1, o2) = if b == F::ZERO { (l, r) } else { (r, l) };
        trace.push(o1);
        trace.push(o2);
        bb && bl && br
    }

    fn input_vars(&self) -> Vec<Name> {
        vec![self.b, self.l, self.r]
    }

    fn clone_box(&self) -> Box<dyn Gate<F>> {
        Box::new(self.clone())
    }
}

impl<T: std::fmt::Debug> std::fmt::Display for GSwap<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
