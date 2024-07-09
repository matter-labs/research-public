use std::env::var;

use crate::expr::{apply_renaming, Config, Constr, Gate, Name, NameContext, Renaming, Trace, CV};
use crate::field::Field;
use crate::optimizer::{Atomic, Atomic_, NF, NF_};

#[derive(Debug, Clone)]
pub struct Poseidon2Flattened<F: Field> {
    pub inputs: [Name; 12],
    pub outputs: [Name; 12],
    pub atomics: [Atomic<NF<F>>; 118],
}

#[derive(Debug, Clone)]
pub struct Poseidon2FlattenedCV<F: Field> {
    inputs: [usize; 12],
    atomics: [Atomic_<NF_<F, usize>, usize>; 118],
}

impl<F: Field> std::fmt::Display for Poseidon2Flattened<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut vars = self.inputs.to_vec();
        vars.extend(self.atomics.clone().map(|atomic| atomic.o).to_vec());
        write!(f, "Poseidon2Flattened {:?}", vars)
    }
}

fn eval_nf<F: Field + 'static>(nf: &NF_<F, usize>, witness: &Trace<F>) -> (bool, F) {
    let mut linear: Vec<F> = vec![];
    let read_ok = nf.s.iter().fold(true, |acc, (positions, coeff)| {
        let mut factors: Vec<F> = vec![];
        let inner_read_ok = positions.iter().fold(true, |acc, n| {
            let (ok, f) = witness.read(*n);
            factors.push(f);
            acc && ok
        });
        let r = factors.iter().fold(F::ONE, |acc, f| *f * acc) * *coeff;
        linear.push(r);
        acc && inner_read_ok
    });
    let sum = linear.iter().fold(nf.c, |acc, f| *f + acc);
    (read_ok, sum)
}

fn sat_atomic<F: Field + 'static>(
    atomic: &Atomic_<NF_<F, usize>, usize>,
    witness: &Trace<F>,
) -> bool {
    let (e_ok, e) = eval_nf(&atomic.e, witness);
    let (o_ok, o) = witness.read(atomic.o);
    e_ok && o_ok && F::ZERO == e - o
}

impl<F: Field + 'static> CV<F> for Poseidon2FlattenedCV<F> {
    fn id(&self) -> String {
        "Poseidon2Flattened".into()
    }

    fn width(&self) -> usize {
        130
    }

    fn sat(&self, witness: &Trace<F>) -> bool {
        self.atomics
            .iter()
            .all(|atomic| sat_atomic(atomic, witness))
    }

    fn gen_table(&self, config: &crate::table::CsConfig) -> Vec<crate::expr::Constr<F>> {
        let n_sels = config.gates.len();
        let q_index = config.gates.get_index(<Self as CV<F>>::id(self));
        let fixed = config.compute_fixed(q_index.unwrap(), vec![]);
        // TODO: this isn't quite right, we need inputs too
        let mut variable = self.inputs.clone().to_vec();
        variable.extend(self.atomics.clone().map(|atomic| atomic.o).to_vec());
        let c = Constr { variable, fixed };
        vec![c]
    }
}

impl<F: Field + 'static> Gate<F> for Poseidon2Flattened<F> {
    fn kind(&self) -> String {
        "Poseidon2Flattened".into()
    }

    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        let inputs = self.inputs.map(|n| ctxt.get(n));
        let atomics = self.atomics.clone().map(|atomic| {
            let o = ctxt.get(atomic.o);
            let s: Vec<(Vec<usize>, F)> = atomic
                .e
                .s
                .iter()
                .map(|(names, coeff)| {
                    let positions: Vec<usize> = names.iter().map(|n| ctxt.get(*n)).collect();
                    (positions, *coeff)
                })
                .collect();
            let e = NF_ { s, c: atomic.e.c };
            Atomic_ { e, o }
        });
        let cv = Poseidon2FlattenedCV { inputs, atomics };
        vec![Box::new(cv)]
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        self.atomics.iter().all(|atomic| {
            let mut linear: Vec<F> = vec![];
            let read_ok = atomic.e.s.iter().fold(true, |acc, (names, coeff)| {
                let mut factors: Vec<F> = vec![];
                let inner_read_ok = names.iter().fold(true, |acc, n| {
                    let (ok, f) = ctxt.read_name(*n, trace);
                    factors.push(f);
                    acc && ok
                });
                let r = factors.iter().fold(F::ONE, |acc, f| *f * acc) * *coeff;
                linear.push(r);
                acc && inner_read_ok
            });
            ctxt.push(atomic.o);
            let o = linear.iter().fold(atomic.e.c, |acc, f| *f + acc);
            trace.push(o);
            read_ok
        })
    }

    fn input_vars(&self) -> Vec<Name> {
        self.inputs.to_vec()
    }

    fn output_vars(&self) -> Vec<Name> {
        self.outputs.to_vec()
    }

    fn clone_box(&self) -> Box<dyn Gate<F>> {
        Box::new(self.clone())
    }

    fn rename(&mut self, renaming: &Renaming) {
        self.inputs = self.inputs.map(|i| apply_renaming(i, renaming));
        self.outputs = self.outputs.map(|i| apply_renaming(i, renaming));
        // TODO: rename atomics
    }
}
