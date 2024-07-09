use crate::{
    expr::{apply_renaming, Config, Constr, Gate, Name, NameContext, Trace, CV},
    field::Field,
};
use std::{fmt, vec};

#[derive(Debug, Clone)]
pub struct Lookup {
    table_id: usize,
    entry: Vec<usize>,
}

impl fmt::Display for Lookup {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "id:{}, entry:{:?}", self.table_id, self.entry)
    }
}

impl<F: Field + 'static> CV<F> for Lookup {
    fn id(&self) -> String {
        "Lookup".into()
    }

    fn width(&self) -> usize {
        1 + self.entry.len()
    }

    fn sat(&self, witness: &Trace<F>) -> bool {
        // TODO actually include tables...
        true
    }

    fn gen_table(&self, config: &crate::table::CsConfig) -> Vec<Constr<F>> {
        let n_sels = config.gates.len();
        let qlookup_index = config.gates.get_index(<Self as CV<F>>::id(self));
        let fixed = config.compute_fixed(
            qlookup_index.unwrap(),
            vec![F::from_u64(self.table_id as u64)],
        );
        let c = Constr {
            variable: self.entry.clone(),
            fixed,
        };
        vec![c]
    }
}

#[derive(Debug, Clone)]
pub struct TriXor4 {
    pub a: Name,
    pub b: Name,
    pub c: Name,
    pub o: Name,
}

impl<F: Field + 'static> Gate<F> for TriXor4 {
    fn kind(&self) -> String {
        "TriXor4".into()
    }

    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        let a = ctxt.get(self.a);
        let b = ctxt.get(self.b);
        let c = ctxt.get(self.c);
        let o = ctxt.get(self.o);
        let g = Lookup {
            table_id: 1,
            entry: vec![a, b, c, o],
        };
        vec![Box::new(g)]
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        const MASK: u8 = (1u8 << 4) - 1;

        let (oka, a) = ctxt.read_name(self.a, trace);
        let (okb, b) = ctxt.read_name(self.b, trace);
        let (okc, c) = ctxt.read_name(self.c, trace);
        ctxt.push(self.o);
        let result = (a.to_u64() as u8) ^ (b.to_u64() as u8) ^ (c.to_u64() as u8);
        let value = (result & MASK) as u64;
        trace.push(F::from_u64(value));
        oka && okb && okc
    }

    fn input_vars(&self) -> Vec<Name> {
        vec![self.a, self.b, self.c]
    }

    fn output_vars(&self) -> Vec<Name> {
        vec![self.o]
    }

    fn range_checks(&self) -> Vec<(Name, usize)> {
        vec![(self.a, 4), (self.b, 4), (self.c, 4)]
    }

    fn clone_box(&self) -> Box<dyn Gate<F>> {
        Box::new(self.clone())
    }

    fn rename(&mut self, renaming: &crate::expr::Renaming) {
        self.a = apply_renaming(self.a, renaming);
        self.b = apply_renaming(self.b, renaming);
        self.c = apply_renaming(self.c, renaming);
        self.o = apply_renaming(self.o, renaming);
    }
}

impl std::fmt::Display for TriXor4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, Clone)]
pub struct Ch4 {
    pub a: Name,
    pub b: Name,
    pub c: Name,
    pub o: Name,
}

impl<F: Field + 'static> Gate<F> for Ch4 {
    fn kind(&self) -> String {
        "Ch4".into()
    }

    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        let a = ctxt.get(self.a);
        let b = ctxt.get(self.b);
        let c = ctxt.get(self.c);
        let o = ctxt.get(self.o);
        let g = Lookup {
            table_id: 2,
            entry: vec![a, b, c, o],
        };
        vec![Box::new(g)]
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        const MASK: u8 = (1u8 << 4) - 1;

        let (oka, a) = ctxt.read_name(self.a, trace);
        let (okb, b) = ctxt.read_name(self.b, trace);
        let (okc, c) = ctxt.read_name(self.c, trace);
        ctxt.push(self.o);
        let a = a.to_u64() as u8;
        let b = b.to_u64() as u8;
        let c = c.to_u64() as u8;
        let result = (a & b) ^ (!a & c);
        let value = (result & MASK) as u64;
        trace.push(F::from_u64(value));
        oka && okb && okc
    }

    fn input_vars(&self) -> Vec<Name> {
        vec![self.a, self.b, self.c]
    }

    fn output_vars(&self) -> Vec<Name> {
        vec![self.o]
    }

    fn range_checks(&self) -> Vec<(Name, usize)> {
        vec![(self.a, 4), (self.b, 4), (self.c, 4)]
    }

    fn clone_box(&self) -> Box<dyn Gate<F>> {
        Box::new(self.clone())
    }

    fn rename(&mut self, renaming: &crate::expr::Renaming) {
        self.a = apply_renaming(self.a, renaming);
        self.b = apply_renaming(self.b, renaming);
        self.c = apply_renaming(self.c, renaming);
        self.o = apply_renaming(self.o, renaming);
    }
}

impl std::fmt::Display for Ch4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, Clone)]
pub struct Maj4 {
    pub a: Name,
    pub b: Name,
    pub c: Name,
    pub o: Name,
}

impl<F: Field + 'static> Gate<F> for Maj4 {
    fn kind(&self) -> String {
        "Maj4".into()
    }

    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        let a = ctxt.get(self.a);
        let b = ctxt.get(self.b);
        let c = ctxt.get(self.c);
        let o = ctxt.get(self.o);
        let g = Lookup {
            table_id: 3,
            entry: vec![a, b, c, o],
        };
        vec![Box::new(g)]
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        const MASK: u8 = (1u8 << 4) - 1;

        let (oka, a) = ctxt.read_name(self.a, trace);
        let (okb, b) = ctxt.read_name(self.b, trace);
        let (okc, c) = ctxt.read_name(self.c, trace);
        ctxt.push(self.o);
        let a = a.to_u64() as u8;
        let b = b.to_u64() as u8;
        let c = c.to_u64() as u8;
        let result = (a & b) ^ (a & c) ^ (b & c);
        let value = (result & MASK) as u64;
        trace.push(F::from_u64(value));
        oka && okb && okc
    }

    fn input_vars(&self) -> Vec<Name> {
        vec![self.a, self.b, self.c]
    }

    fn output_vars(&self) -> Vec<Name> {
        vec![self.o]
    }

    fn range_checks(&self) -> Vec<(Name, usize)> {
        vec![(self.a, 4), (self.b, 4), (self.c, 4)]
    }

    fn clone_box(&self) -> Box<dyn Gate<F>> {
        Box::new(self.clone())
    }

    fn rename(&mut self, renaming: &crate::expr::Renaming) {
        self.a = apply_renaming(self.a, renaming);
        self.b = apply_renaming(self.b, renaming);
        self.c = apply_renaming(self.c, renaming);
        self.o = apply_renaming(self.o, renaming);
    }
}

impl std::fmt::Display for Maj4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

// Note:
// we use one gate per functionality, we could have several gates that
// use the same table.
// We could generalize the gates to have only one for any lookup.
#[derive(Debug, Clone)]
pub struct Merge4BitChunk<const SPLIT_AT: usize> {
    pub low: Name,
    pub high: Name,
    pub reconstructed: Name,
    pub swapped: Name,
}

impl<F: Field + 'static, const SPLIT_AT: usize> Gate<F> for Merge4BitChunk<SPLIT_AT> {
    fn kind(&self) -> String {
        "Merge4BitChunk".into()
    }

    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>> {
        let low = ctxt.get(self.low);
        let high = ctxt.get(self.high);
        let reconstructed = ctxt.get(self.reconstructed);
        let swapped = ctxt.get(self.swapped);
        let g = Lookup {
            table_id: 4,
            entry: vec![reconstructed, low, high, swapped],
        };
        vec![Box::new(g)]
    }

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool {
        const MASK: u8 = (1u8 << 4) - 1;
        let (okl, low) = ctxt.read_name(self.low, trace);
        let (okh, high) = ctxt.read_name(self.high, trace);
        ctxt.push(self.reconstructed);
        ctxt.push(self.swapped);
        let reconstructed = (low.to_u64() as u8) | ((high.to_u64() as u8) << SPLIT_AT);
        let swapped = (high.to_u64() as u8) | ((low.to_u64() as u8) << SPLIT_AT);
        trace.push(F::from_u64(reconstructed as u64));
        trace.push(F::from_u64(swapped as u64));
        okl && okh
    }

    fn input_vars(&self) -> Vec<Name> {
        vec![self.low, self.high]
    }

    fn output_vars(&self) -> Vec<Name> {
        vec![self.reconstructed, self.swapped]
    }

    fn clone_box(&self) -> Box<dyn Gate<F>> {
        Box::new(self.clone())
    }

    fn rename(&mut self, renaming: &crate::expr::Renaming) {
        self.low = apply_renaming(self.low, renaming);
        self.high = apply_renaming(self.high, renaming);
        self.reconstructed = apply_renaming(self.reconstructed, renaming);
        self.swapped = apply_renaming(self.swapped, renaming);
    }

    fn other_params(&self) -> Vec<u8> {
        SPLIT_AT.to_le_bytes().to_vec()
    }
}

impl<const SPLIT_AT: usize> std::fmt::Display for Merge4BitChunk<SPLIT_AT> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
