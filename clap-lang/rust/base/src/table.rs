use crate::field::Field;
use std::{collections::HashMap, fmt::Display};

#[derive(Debug, Clone)]
pub struct Table<Constr>(pub Vec<Constr>);

impl<T: Display> std::fmt::Display for Table<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self
            .0
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<String>>()
            .join("");
        write!(f, "{s}")
    }
}

pub struct CVIdContainer {
    ids: Vec<String>,
    positions: HashMap<String, usize>,
}

impl CVIdContainer {
    pub fn empty() -> Self {
        Self {
            ids: Vec::new(),
            positions: HashMap::new(),
        }
    }

    pub fn add(&mut self, id: String) {
        let index = self.ids.len();
        // Only add if the ID does not already exist
        if let std::collections::hash_map::Entry::Vacant(e) = self.positions.entry(id.clone()) {
            self.ids.push(id);
            e.insert(index);
        }
    }

    // Retrieve an ID by index, assuming the index is always valid
    pub fn get(&self, i: usize) -> String {
        self.ids[i].clone()
    }

    pub fn len(&self) -> usize {
        self.ids.len()
    }

    // Returns an Option<usize> because the ID might not exist
    pub fn get_index(&self, id: String) -> Option<usize> {
        self.positions.get(&id).cloned()
    }

    pub fn is_empty(&self) -> bool {
        self.ids.is_empty()
    }
}

pub struct CsConfig {
    pub(crate) n_wires: usize,
    pub(crate) gates: CVIdContainer,
}

impl CsConfig {
    fn compute_selectors<F: Field>(&self, sel_index: usize) -> Vec<F> {
        let mut selectors = Vec::with_capacity(self.gates.len());
        for i in 0..self.gates.len() {
            if i == sel_index {
                selectors.push(F::ONE);
            } else {
                selectors.push(F::ZERO);
            }
        }
        selectors
    }

    pub fn compute_fixed<F: Field>(&self, sel_index: usize, constants: Vec<F>) -> Vec<F> {
        let mut sels = self.compute_selectors(sel_index);
        sels.extend(constants);
        sels
    }
}
