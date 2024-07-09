use crate::cs_arith::Arith;
use crate::expr::{apply_renaming, Config, Gate, Name, NameContext, Renaming, Trace, CV};
use crate::field::SmallField;

#[derive(Debug, Clone)]
pub struct Split32<F: SmallField + 'static> {
    pub i: Name,
    pub oh: Name,
    pub ol: Name,
    pub range_check: Option<Box<dyn Gate<F>>>,
}

impl<F: SmallField + 'static> Gate<F> for Split32<F> {
    fn kind(&self) -> String {
        "Split32".into()
    }

    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        let mut cvs: Vec<Box<dyn CV<F>>> = self
            .range_check
            .iter()
            .flat_map(|rc| rc.gen_cs(config, ctxt))
            .collect(); // (1<<32) * high + low -> input
        let o = ctxt.get(self.i);
        let l = ctxt.get(self.ol);
        let r = ctxt.get(self.oh);
        let qr = F::from_u64(1u64 << 32);
        let g = Arith {
            ql: F::ONE,
            l,
            qr,
            r,
            qc: F::ZERO,
            qm: F::ZERO,
            qo: F::MONE,
            o,
        };
        cvs.push(Box::new(g));
        cvs
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        let ok_rc = self
            .range_check
            .iter()
            .all(|rc| rc.gen_trace(config, ctxt, trace));
        let (ok, input) = ctxt.read_name(self.i, trace);
        let input = input.to_u64();
        ctxt.push(self.ol);
        ctxt.push(self.oh);
        let low = input as u32;
        let high = input >> 32;
        trace.push(F::from_u64(low as u64));
        trace.push(F::from_u64(high));
        ok_rc && ok
    }

    fn input_vars(&self) -> Vec<Name> {
        vec![self.i]
    }

    fn output_vars(&self) -> Vec<Name> {
        vec![self.ol, self.oh]
    }

    fn range_checks(&self) -> Vec<(Name, usize)> {
        self.range_check.clone().unwrap().range_checks()
    }

    fn range_checks_required(&self) -> Vec<(Name, usize)> {
        vec![(self.i, 36)]
    }

    fn no_range_checks_unsound(&mut self) {
        self.range_check = None
    }

    fn can_drop_range_checks(&self) -> bool {
        true
    }

    fn clone_box(&self) -> Box<dyn Gate<F>> {
        Box::new(self.clone())
    }

    fn rename(&mut self, renaming: &Renaming) {
        self.i = apply_renaming(self.i, renaming);
        self.ol = apply_renaming(self.ol, renaming);
        self.oh = apply_renaming(self.oh, renaming);
        self.range_check
            .iter_mut()
            .for_each(|rc| rc.rename(renaming));
    }
}

impl<F: SmallField + 'static> std::fmt::Display for Split32<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
