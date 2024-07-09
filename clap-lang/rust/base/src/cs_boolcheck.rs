use std::vec;

use crate::{
    expr::{apply_renaming, Config, Constr, Gate, Name, NameContext, Trace, CV},
    field::Field,
};

#[derive(Debug, Clone, Copy)]
pub struct GBoolCheck<T>(pub T);

pub type BoolCheck = GBoolCheck<Name>;

pub type BoolCheckCV = GBoolCheck<usize>;

impl<F: Field + 'static> CV<F> for BoolCheckCV {
    fn id(&self) -> String {
        "BoolCheck".into()
    }

    fn width(&self) -> usize {
        1
    }

    fn sat(&self, witness: &Trace<F>) -> bool {
        let (okx, v) = witness.read(self.0);
        okx && (v == F::ZERO || v == F::ONE)
    }

    fn gen_table(&self, config: &crate::table::CsConfig) -> Vec<Constr<F>> {
        // TODO: selector binary tree
        let n_sels = config.gates.len();
        let qboolcheck_index = config.gates.get_index(<Self as CV<F>>::id(self));
        let fixed = config.compute_fixed(qboolcheck_index.unwrap(), vec![]);
        let c = Constr {
            variable: vec![self.0],
            fixed,
        };
        vec![c]
    }
}

impl<F: Field + 'static> Gate<F> for BoolCheck {
    fn kind(&self) -> String {
        "BoolCheck".into()
    }

    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        vec![Box::new(GBoolCheck(ctxt.get(self.0)))]
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        let (b, v) = ctxt.read_name(self.0, trace);
        b && (v == F::ZERO || v == F::ONE)
    }

    fn input_vars(&self) -> Vec<Name> {
        vec![self.0]
    }

    fn output_vars(&self) -> Vec<Name> {
        vec![]
    }

    fn clone_box(&self) -> Box<dyn Gate<F>> {
        Box::new(*self)
    }

    fn rename(&mut self, renaming: &crate::expr::Renaming) {
        self.0 = apply_renaming(self.0, renaming)
    }
}

impl<T: std::fmt::Debug> std::fmt::Display for GBoolCheck<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
