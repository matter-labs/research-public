use crate::cs_arith::Arith;
use crate::expr::{Config, Gate, Name, NameContext, Trace, CV};
use crate::field::Field;

#[derive(Debug, Clone)]
pub struct Eq0(pub Name);

impl<F: Field + 'static> Gate<F> for Eq0 {
    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        let g = Arith {
            ql: F::ONE,
            l: ctxt.get(self.0),
            qr: F::ZERO,
            r: 0,
            qc: F::ZERO,
            qm: F::ZERO,
            qo: F::ZERO,
            o: 0,
        };
        vec![Box::new(g)]
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        let (b, v) = ctxt.read_name(self.0, trace);
        if v == F::ZERO {
            b
        } else {
            false
        }
    }

    fn input_vars(&self) -> Vec<Name> {
        vec![self.0]
    }

    fn clone_box(&self) -> Box<dyn Gate<F>> {
        Box::new(self.clone())
    }
}

impl std::fmt::Display for Eq0 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
