use std::vec;

use crate::expr::{apply_renaming, Config, Gate, Name, NameContext, Renaming, Trace, CV};
use crate::field::Field;
use crate::lookups::TriXor4;

#[derive(Debug, Clone)]
pub struct LimbDecomposition<F: Field + 'static, const N: usize, const WIDTH: usize> {
    pub i: Name,
    pub o: [Name; N],
    pub recomposition: Vec<Box<dyn Gate<F>>>,
    pub u4_rcs: Vec<Name>,
    pub u32_part: Option<Name>,
}

impl<F: Field + 'static, const N: usize> Gate<F> for LimbDecomposition<F, N, 4> {
    fn kind(&self) -> String {
        "LimbDecomposition4".into()
    }

    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        let mut cvs: Vec<Box<dyn CV<F>>> = vec![];
        self.o.iter().for_each(|oi| {
            ctxt.push(*oi);
        });
        self.u4_rcs.chunks(3).for_each(|chunk| {
            let mut iter = chunk.iter();
            let n1 = iter.next().unwrap();
            let n2 = iter.next().unwrap_or(n1);
            let n3 = iter.next().unwrap_or(n1);
            let o = ctxt.internal_name();
            let g = TriXor4 {
                a: *n1,
                b: *n2,
                c: *n3,
                o,
            };
            cvs.extend(g.gen_cs(config, ctxt));
        });
        let recomp: Vec<Box<dyn CV<F>>> = self
            .recomposition
            .iter()
            .flat_map(|rc| rc.gen_cs(config, ctxt))
            .collect();
        cvs.extend(recomp);
        cvs
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        const MASK_4_U64: u64 = (1u64 << 4) - 1;
        let (ok, input) = ctxt.read_name(self.i, trace);
        let mut input = input.to_u64();
        self.o.iter().for_each(|oi| {
            ctxt.push(*oi);
            let chunk = input & MASK_4_U64;
            input >>= 4;
            trace.push(F::from_u64(chunk));
        });
        let ok_c = self.u4_rcs.chunks(3).all(|chunk| {
            let mut iter = chunk.iter();
            let n1 = iter.next().unwrap();
            let n2 = iter.next().unwrap_or(n1);
            let n3 = iter.next().unwrap_or(n1);
            let o = ctxt.internal_name();
            let g = TriXor4 {
                a: *n1,
                b: *n2,
                c: *n3,
                o,
            };
            g.gen_trace(config, ctxt, trace)
        });
        let ok_recomp = self
            .recomposition
            .iter()
            .all(|rc| rc.gen_trace(config, ctxt, trace));
        ok && ok_c && ok_recomp
    }

    fn input_vars(&self) -> Vec<Name> {
        vec![self.i]
    }

    fn output_vars(&self) -> Vec<Name> {
        let mut v = self.o.to_vec();
        self.recomposition
            .iter()
            .for_each(|r| v.extend(r.output_vars()));
        v
    }

    fn rename(&mut self, renaming: &Renaming) {
        self.i = apply_renaming(self.i, renaming);
        self.o = self.o.map(|n| apply_renaming(n, renaming));
        self.u4_rcs
            .iter_mut()
            .for_each(|n| *n = apply_renaming(*n, renaming));
        self.u32_part
            .iter_mut()
            .for_each(|n| *n = apply_renaming(*n, renaming));
        self.recomposition
            .iter_mut()
            .for_each(|rc| rc.rename(renaming));
    }

    fn range_checks(&self) -> Vec<(Name, usize)> {
        let mut rcs: Vec<(Name, usize)> = self.o.into_iter().map(|o| (o, 4)).collect();
        rcs.push((self.i, N * 4));
        rcs
    }

    fn range_checks_required(&self) -> Vec<(Name, usize)> {
        vec![]
    }

    fn droppable_range_checks(&self) -> Vec<(Name, usize)> {
        match N {
            9 => vec![(self.u32_part.unwrap(), 32)],
            _ => self.o.into_iter().map(|o| (o, 4)).collect(),
        }
    }

    fn can_drop_range_checks(&self) -> bool {
        true
    }

    fn no_range_checks_unsound(&mut self) {
        // self.range_checks = vec![];
        match N {
            9 => self.u4_rcs = vec![*self.u4_rcs.last().unwrap()],
            _ => self.u4_rcs = vec![],
        }
    }

    fn clone_box(&self) -> Box<dyn Gate<F>> {
        Box::new(self.clone())
    }
}

impl<F: Field + 'static, const N: usize, const WIDTH: usize> std::fmt::Display
    for LimbDecomposition<F, N, WIDTH>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
