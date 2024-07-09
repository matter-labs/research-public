use crate::{
    expr::{apply_renaming, Config, Constr, Gate, Name, NameContext, Trace, CV},
    field::Field,
};

#[derive(Debug, Clone)]
pub struct GLinearCombination<F: Field, G, const N: usize> {
    pub coeffs: [F; N],
    pub vars: [G; N],
    pub o: G,
}

pub type LinearCombination<F, const N: usize> = GLinearCombination<F, Name, N>;

pub type LinearCombinationCV<F, const N: usize> = GLinearCombination<F, usize, N>;

impl<F: Field + 'static, const N: usize> CV<F> for LinearCombinationCV<F, N> {
    fn id(&self) -> String {
        format!("LinearCombination{}", N)
    }

    fn width(&self) -> usize {
        N + 1
    }

    fn sat(&self, witness: &Trace<F>) -> bool {
        let (ok_o, val_o) = witness.read(self.o);
        let (ok, sum) = self.vars.into_iter().zip(self.coeffs).fold(
            (true, F::ZERO),
            |(acc_b, acc_sum), (var, coeff)| {
                let (ok, input) = witness.read(var);
                (ok && acc_b, acc_sum + input * coeff)
            },
        );
        ok && ok_o && sum == val_o
    }

    fn gen_table(&self, config: &crate::table::CsConfig) -> Vec<Constr<F>> {
        let n_sels = config.gates.len();
        let qlc_index = config.gates.get_index(self.id());
        let fixed = config.compute_fixed(qlc_index.unwrap(), self.coeffs.to_vec());
        let mut variable = self.vars.to_vec();
        variable.push(self.o);
        let c = Constr { variable, fixed };
        vec![c]
    }
}

impl<F: Field + 'static, const N: usize> Gate<F> for LinearCombination<F, N> {
    fn kind(&self) -> String {
        "LinearCombination".into()
    }

    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        let vars = self.vars.map(|n| ctxt.get(n));
        let o = ctxt.get(self.o);
        let g = GLinearCombination {
            vars,
            coeffs: self.coeffs,
            o,
        };
        vec![Box::new(g)]
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        let (ok, sum) = self.vars.into_iter().zip(self.coeffs).fold(
            (true, F::ZERO),
            |(acc_b, acc_sum), (var, coeff)| {
                let (ok, input) = ctxt.read_name(var, trace);
                (ok && acc_b, acc_sum + input * coeff)
            },
        );
        ctxt.push(self.o);
        trace.push(sum);
        ok
    }

    fn input_vars(&self) -> Vec<Name> {
        self.vars.to_vec()
    }

    fn output_vars(&self) -> Vec<Name> {
        vec![self.o]
    }

    fn other_params(&self) -> Vec<u8> {
        let consts = self.coeffs;
        consts
            .iter()
            .flat_map(|f| f.to_u64().to_be_bytes().to_vec())
            .collect()
    }

    fn clone_box(&self) -> Box<dyn Gate<F>> {
        Box::new(self.clone())
    }

    fn rename(&mut self, renaming: &crate::expr::Renaming) {
        self.o = apply_renaming(self.o, renaming);
        self.vars = self.vars.map(|n| apply_renaming(n, renaming))
    }
}

impl<F: Field + 'static, const N: usize> std::fmt::Display for LinearCombination<F, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, Clone)]
pub struct AssertionLC<F: Field, const N: usize>(pub LinearCombination<F, N>);

impl<F: Field + 'static, const N: usize> Gate<F> for AssertionLC<F, N> {
    fn kind(&self) -> String {
        "Assertion".into()
    }

    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        self.0.gen_cs(config, ctxt)
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        true
    }

    fn input_vars(&self) -> Vec<Name> {
        let mut ins = self.0.vars.to_vec();
        ins.push(self.0.o);
        ins
    }

    fn output_vars(&self) -> Vec<Name> {
        vec![]
    }

    fn other_params(&self) -> Vec<u8> {
        let consts = self.0.coeffs;
        consts
            .iter()
            .flat_map(|f| f.to_u64().to_be_bytes().to_vec())
            .collect()
    }

    fn clone_box(&self) -> Box<dyn Gate<F>> {
        Box::new(self.clone())
    }

    fn rename(&mut self, renaming: &crate::expr::Renaming) {
        self.0.rename(renaming);
    }
}

impl<F: Field + 'static, const N: usize> std::fmt::Display for AssertionLC<F, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
