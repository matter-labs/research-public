use crate::cs_arith::Arith;
use crate::expr::{Config, Gate, Name, NameContext, Trace, CV};
use crate::field::Field;

#[derive(Debug, Clone)]
pub struct Inv {
    pub x: Name,
    pub i: Name,
}

impl<F: Field + 'static> Gate<F> for Inv {
    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        let l = self.x;
        let r = self.i;
        // l * r - 1 = 0

        // l ≠ 0  /\  r = 1/l  =>  sat
        // l ≠ 0  /\  r = 0    =>  unsat
        // l ≠ 0  /\  r = _    =>  unsat
        // l = 0  /\  r = _    =>  unsat
        let g = Arith {
            ql: F::ZERO,
            l: ctxt.get(l),
            qr: F::ZERO,
            r: ctxt.get(r),
            qc: F::MONE,
            qm: F::ONE,
            qo: F::ZERO,
            o: 0,
        };
        vec![Box::new(g)]
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        let (b, v) = ctxt.read_name(self.x, trace);
        ctxt.push(self.i);
        if v == F::ZERO {
            trace.push(F::ZERO);
            false
        } else {
            trace.push(F::ONE.div(v));
            b
        }
    }

    fn input_vars(&self) -> Vec<Name> {
        vec![self.x]
    }

    fn clone_box(&self) -> Box<dyn Gate<F>> {
        Box::new(self.clone())
    }
}

impl std::fmt::Display for Inv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
