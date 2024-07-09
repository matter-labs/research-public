use crate::expr::{apply_renaming, Config, Gate, Name, NameContext, Renaming, Trace, CV};
use crate::field::Field;

// our strategy is to output 8 4-bit chunks. When we decompose we actually
// split only parts of the word in a way that we can later re-merge into 4-bit chunks

// e.g. if we have rotate right by 7 bits, then we want to have the
// following after rotation (from lower bits)
// |4|4|4|4|4|4|4|4|, so we split lowest 7 bits as 3 + 4, and we need the highest bit as well,
// that we will later on re-merge as 4, so we do
// |1|4|4|4|4|4|4|4|3| decomposition, then rotate by renumeration,
// and then only merge once

#[derive(Debug, Clone)]
pub struct SplitAndRotate<F: Field + 'static> {
    pub rotation: usize,
    pub i: Name,
    pub aligned_variables: [Name; 7],
    pub decompose_low: Name,
    pub decompose_high: Name,
    //
    pub range_check: Option<Box<dyn Gate<F>>>,
    pub recomposition: Vec<Box<dyn Gate<F>>>,
}

impl<F: Field + 'static> Gate<F> for SplitAndRotate<F> {
    fn kind(&self) -> String {
        "SplitAndRotate".into()
    }

    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        ctxt.get(self.i);
        ctxt.push(self.decompose_low);
        self.aligned_variables.iter().for_each(|n| {
            ctxt.push(*n);
        });
        ctxt.push(self.decompose_high);

        let mut cvs: Vec<Box<dyn CV<F>>> = self
            .range_check
            .iter()
            .flat_map(|rc| rc.gen_cs(config, ctxt))
            .collect();
        let recomp: Vec<Box<dyn CV<F>>> = self
            .recomposition
            .iter()
            .flat_map(|rc| rc.gen_cs(config, ctxt))
            .collect();
        cvs.extend(recomp);
        cvs
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        const MASK_4: u32 = (1u32 << 4) - 1;

        let rotate_mod = self.rotation % 4;

        let (ok, input) = ctxt.read_name(self.i, trace);
        let mut input = input.to_u64();
        ctxt.push(self.decompose_low);
        self.aligned_variables.iter().for_each(|n| {
            ctxt.push(*n);
        });
        ctxt.push(self.decompose_high);

        let lowest_mask = (1u32 << rotate_mod) - 1;
        let mut result = [F::ZERO; 9];
        let lowest = input & (lowest_mask as u64);
        result[0] = F::from_u64(lowest);
        input >>= rotate_mod;
        for dst in result[1..8].iter_mut() {
            let chunk = input & (MASK_4 as u64);
            input >>= 4;
            *dst = F::from_u64(chunk);
        }
        let highest = input;
        result[8] = F::from_u64(highest);

        result.iter().for_each(|v| trace.push(*v));

        let ok_rc = self
            .range_check
            .iter()
            .all(|rc| rc.gen_trace(config, ctxt, trace));
        let ok_recomp = self
            .recomposition
            .iter()
            .all(|rc| rc.gen_trace(config, ctxt, trace));
        ok && ok_rc && ok_recomp
    }

    fn input_vars(&self) -> Vec<Name> {
        vec![self.i]
    }

    fn output_vars(&self) -> Vec<Name> {
        let mut v = self.aligned_variables.to_vec();
        v.push(self.decompose_low);
        v.push(self.decompose_high);
        self.recomposition
            .iter()
            .for_each(|r| v.extend(r.output_vars()));
        v
    }

    fn range_checks(&self) -> Vec<(Name, usize)> {
        let mut v = self.aligned_variables.map(|n| (n, 4)).to_vec();
        v.push((self.decompose_high, 4));
        v.push((self.decompose_low, 4));
        v.push((self.i, 32));
        v
    }

    fn other_params(&self) -> Vec<u8> {
        self.rotation.to_be_bytes().to_vec()
    }

    fn range_checks_required(&self) -> Vec<(Name, usize)> {
        vec![(self.i, 32)]
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
        self.aligned_variables = self.aligned_variables.map(|n| apply_renaming(n, renaming));
        self.decompose_low = apply_renaming(self.decompose_low, renaming);
        self.decompose_high = apply_renaming(self.decompose_high, renaming);
        self.range_check
            .iter_mut()
            .for_each(|rc| rc.rename(renaming));
        self.recomposition
            .iter_mut()
            .for_each(|rc| rc.rename(renaming));
    }
}

impl<F: Field + 'static> std::fmt::Display for SplitAndRotate<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
