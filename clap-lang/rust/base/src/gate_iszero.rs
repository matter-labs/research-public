use crate::cs_arith::Arith;
use crate::cs_boolcheck::GBoolCheck;
use crate::expr::{Config, Gate, Name, NameContext, Trace, CV};
use crate::field::Field;

#[derive(Debug, Clone)]
pub struct IsZero {
    pub x: Name,
    pub b: Name,
}

impl<F: Field + 'static> Gate<F> for IsZero {
    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        // 1) b = - l * r + 1
        // 2) b^2 - b = 0

        // l ≠ 0  /\  r = 1/l  /\  b = 0  =>  sat
        // l ≠ 0  /\  r = _    /\  b = 0  =>  unsat 1)
        // l ≠ 0  /\  r = _    /\  b = 1  =>  unsat 1)
        // l ≠ 0  /\  r = _    /\  b = _  =>  unsat 2)
        // l = 0  /\  r = _    /\  b = 1  =>  sat
        // l = 0  /\  r = _    /\  b = 0  =>  unsat 1)
        // l = 0  /\  r = _    /\  b = _  =>  unsat 1) and 2)
        let l = ctxt.get(self.x);
        let r = ctxt.allocate_pos();
        let b = ctxt.get(self.b);
        let g1 = Arith {
            ql: F::ZERO,
            l,
            qr: F::ZERO,
            r,
            qc: F::ONE,
            qm: F::MONE,
            qo: F::MONE,
            o: b,
        };
        let g2 = GBoolCheck(b);
        vec![Box::new(g1), Box::new(g2)]
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        let (ok, i) = ctxt.read_name(self.x, trace);
        ctxt.push(Name::Unused);
        ctxt.push(self.b);
        let b = if i == F::ZERO { F::ONE } else { F::ZERO };
        let r = if i == F::ZERO { F::ZERO } else { F::ONE.div(i) };
        trace.push(r);
        trace.push(b);
        ok
    }

    fn input_vars(&self) -> Vec<Name> {
        vec![self.x]
    }

    fn clone_box(&self) -> Box<dyn Gate<F>> {
        Box::new(self.clone())
    }
}

impl std::fmt::Display for IsZero {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
