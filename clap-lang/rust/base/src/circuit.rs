use crate::expr::{Config, Constr, Gate, Name, NameContext, Trace, CV};
use crate::table::{CVIdContainer, CsConfig, Table};
use crate::{field::*, optimizer};
use std::fmt;
use std::marker::PhantomData;

pub type CVItem<F> = Box<dyn Gate<F>>;

#[derive(Debug, Clone)]
pub enum Circuit<F: Field + 'static> {
    Nil(PhantomData<F>),
    Gate(Box<dyn Gate<F>>),
    Seq(Box<Self>, Box<Self>),
    Par(Box<Self>, Box<Self>),
}

impl<F: Field + 'static> fmt::Display for Circuit<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn print<F: Field + 'static>(
            circuit: &Circuit<F>,
            f: &mut fmt::Formatter<'_>,
        ) -> fmt::Result {
            match circuit {
                Circuit::Nil(_) => Ok(()),
                Circuit::Gate(base_case) => {
                    writeln!(f, "Gate: {}", base_case)
                }
                Circuit::Seq(a, b) => {
                    print(a, f)?;
                    print(b, f)
                }
                Circuit::Par(a, b) => {
                    print(a, f)?;
                    print(b, f)
                }
            }
        }

        print(self, f)
    }
}

impl<F: Field> Circuit<F> {
    pub fn empty() -> Self {
        Circuit::Nil(PhantomData)
    }

    pub fn for_each<G>(&self, f: &mut G)
    where
        G: FnMut(&Box<dyn Gate<F>>),
    {
        match self {
            Circuit::Nil(_) => (),
            Circuit::Gate(e) => f(e),
            Circuit::Seq(l, r) => {
                l.for_each(f);
                r.for_each(f)
            }
            Circuit::Par(l, r) => {
                l.for_each(f);
                r.for_each(f)
            }
        }
    }

    pub fn map<G>(&self, mut f: G) -> Self
    where
        G: FnMut(&Box<dyn Gate<F>>) -> Circuit<F>,
    {
        use Circuit::*;

        let mut stack = vec![(self, false)];
        let mut result_stack: Vec<Circuit<F>> = Vec::new();

        while let Some((current, is_processed)) = stack.pop() {
            match (current, is_processed) {
                (Nil(_), _) => {
                    result_stack.push(current.clone());
                }
                (Gate(gate), _) => {
                    result_stack.push(f(gate));
                }
                (Seq(l, r), false) => {
                    stack.push((current, true));
                    stack.push((r, false));
                    stack.push((l, false));
                }
                (Par(l, r), false) => {
                    stack.push((current, true));
                    stack.push((r, false));
                    stack.push((l, false));
                }
                (Seq(_, _), true) => {
                    let r = result_stack.pop().unwrap();
                    let l = result_stack.pop().unwrap();
                    result_stack.push(Seq(Box::new(l), Box::new(r)));
                }
                (Par(_, _), true) => {
                    let r = result_stack.pop().unwrap();
                    let l = result_stack.pop().unwrap();
                    result_stack.push(Par(Box::new(l), Box::new(r)));
                }
            }
        }

        result_stack.pop().unwrap()
    }

    fn gen_trace_aux(&self, config: &Config, ctxt: &mut NameContext<F>, t: &mut Trace<F>) -> bool {
        match self {
            Circuit::Nil(_) => true,
            Circuit::Gate(e) => e.gen_trace(config, ctxt, t),
            Circuit::Seq(l, r) => {
                let b1 = l.gen_trace_aux(config, ctxt, t);
                let b2 = r.gen_trace_aux(config, ctxt, t);
                b1 && b2
            }
            Circuit::Par(l, r) => {
                let b1 = l.gen_trace_aux(config, ctxt, t);
                let b2 = r.gen_trace_aux(config, ctxt, t);
                b1 && b2
            }
        }
    }

    pub fn gen_trace(&self, config: &Config, t: &mut Trace<F>) -> bool {
        let mut ctxt = self.inputs_ctxt();
        self.gen_trace_aux(config, &mut ctxt, t)
    }

    fn flatten_base_cases(&self, next: usize) -> (usize, Vec<Box<dyn Gate<F>>>) {
        match self {
            Self::Nil(_) => (next, vec![]),
            Self::Gate(e) => (next, vec![e.clone()]),
            Self::Seq(l, r) | Self::Par(l, r) => {
                let (next, mut csl) = l.flatten_base_cases(next);
                let (next, csr) = r.flatten_base_cases(next);
                csl.extend(csr);
                (next, csl)
            }
        }
    }

    pub fn size(&self) -> usize {
        let mut c = 0;
        self.for_each(&mut |_| c += 1);
        c
    }

    pub fn optimize(&self, config: &Config) -> Self {
        let max_iterations = 100;
        let mut i = 0;
        let mut done = false;
        let mut fin = self.clone();
        while (!done) && i < max_iterations {
            let before_size = fin.size();
            fin = optimizer::optimize::<F, 4>(&fin, config);
            let after_size = fin.size();
            i += 1;
            done = before_size == after_size;
        }
        fin
    }

    fn inputs_ctxt(&self) -> NameContext<F> {
        let mut ctxt = NameContext::empty();
        let mut is = vec![];
        self.for_each(&mut |g| {
            let inputs = g.input_vars();
            inputs.iter().for_each(|n| {
                if let Name::Input(_) = *n {
                    is.push(*n);
                }
            })
        });
        is.sort();
        is.iter().for_each(|n| {
            ctxt.get(*n);
        });
        ctxt
    }

    pub fn gen_cs(&self, config: &Config) -> Vec<Box<dyn CV<F>>> {
        let mut ctxt = self.inputs_ctxt();
        let (_, base_cases) = self.flatten_base_cases(0);
        base_cases
            .into_iter()
            .flat_map(|bc| bc.gen_cs(config, &mut ctxt))
            .collect()
    }

    fn derive_config(&self, config: &Config) -> CsConfig {
        let mut gate_ids = CVIdContainer::empty();
        let gates = self.gen_cs(config);
        // Geometry is derived for now, could be checked instead
        let n_wires = gates.iter().fold(0, |acc_width, bc| {
            let w = bc.width();
            let id = bc.id();
            gate_ids.add(id);
            if w > acc_width {
                w
            } else {
                acc_width
            }
        });
        CsConfig {
            n_wires,
            gates: gate_ids,
        }
    }

    pub fn sat(&self, config: &Config, t: &Trace<F>) -> bool {
        let gates = self.gen_cs(config);
        gates.iter().all(|g| g.sat(t))
    }

    pub fn gen_table(&self, config: &Config) -> Table<Constr<F>> {
        let mut cs = vec![];
        let cs_config = self.derive_config(config);
        let gates = self.gen_cs(config);
        gates.iter().for_each(|g| {
            let c = g.gen_table(&cs_config);
            cs.extend(c)
        });
        Table(cs)
    }
}
