use crate::{
    expr::{Constr, Trace, CV},
    field::Field,
};

#[derive(Debug, Clone)]
pub struct Const<F: Field> {
    pub x: usize,
    pub v: F,
}

impl<F: Field + 'static> CV<F> for Const<F> {
    fn id(&self) -> String {
        "Const".into()
    }

    fn width(&self) -> usize {
        1
    }

    fn sat(&self, witness: &Trace<F>) -> bool {
        let (okx, x) = witness.read(self.x);
        let s = okx && x == self.v;
        if s {
            true
        } else {
            println!("SAT failed {:?}", self);
            println!("Trace values: x:{:?}", x);
            false
        }
    }

    fn gen_table(&self, config: &crate::table::CsConfig) -> Vec<Constr<F>> {
        let n_sels = config.gates.len();
        let qconst_index = config.gates.get_index(self.id());
        let fixed = config.compute_fixed(qconst_index.unwrap(), vec![self.v]);
        let c = Constr {
            variable: vec![self.x],
            fixed,
        };
        vec![c]
    }
}
