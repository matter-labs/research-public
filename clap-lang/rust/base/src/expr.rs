use std::collections::HashMap;
use std::fmt::{self, Debug};

use crate::field::*;
use crate::table::CsConfig;
use downcast_rs::impl_downcast;
use downcast_rs::Downcast;

#[derive(Debug, Clone, PartialEq)]
pub struct NameContext<F: Field> {
    map: HashMap<Name, usize>,
    const_cache: HashMap<F, usize>,
    next: usize,
}

impl<F: Field> NameContext<F> {
    pub fn empty() -> Self {
        NameContext {
            map: HashMap::new(),
            const_cache: HashMap::new(),
            next: 0,
        }
    }
    pub fn push(&mut self, k: Name) -> usize {
        let pos = self.next;
        self.next += 1;
        self.map.insert(k, pos);
        pos
    }

    pub fn get(&mut self, i: Name) -> usize {
        if i.unused() {
            UNUSED
        } else {
            match self.map.get(&i) {
                Some(pos) => *pos,
                None => self.push(i),
            }
        }
    }

    pub fn allocate_pos(&mut self) -> usize {
        let pos = self.next;
        self.next += 1;
        pos
    }

    pub fn read_name(&mut self, n: Name, trace: &Trace<F>) -> (bool, F) {
        let pos = self.get(n);
        trace.read(pos)
    }

    pub fn push_constant(&mut self, c: F) -> (usize, bool) {
        match self.const_cache.get(&c) {
            Some(i) => (*i, true),
            None => {
                let pos = self.allocate_pos();
                self.const_cache.insert(c, pos);
                (pos, false)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Trace<T: Clone>(Vec<T>);

impl<T: Field + Clone> Trace<T> {
    pub fn empty() -> Self {
        Trace(vec![])
    }
    pub fn push(&mut self, v: T) {
        self.0.push(v);
    }

    pub fn read(&self, i: usize) -> (bool, T) {
        if i == UNUSED {
            (true, T::ZERO)
        } else {
            self.0.get(i).map_or((false, T::MONE), |f| (true, *f))
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy, PartialOrd, Ord)]
pub enum Name {
    Input(usize),
    Wire(usize),
    Unused,
}

pub const UNUSED: usize = usize::max_value();

impl Name {
    pub fn unused(&self) -> bool {
        *self == Self::Unused
    }

    pub fn wire(&self) -> usize {
        if let Name::Wire(w) = *self {
            w
        } else if let Name::Input(w) = *self {
            // TODO: we should explode here
            w
        } else if let Name::Unused = *self {
            0
        } else {
            panic!("Name not a wire!")
        }
    }
}

pub struct Constr<F: Field> {
    pub variable: Vec<usize>,
    pub fixed: Vec<F>,
}

#[derive(Default)]
pub struct Config {
    // Will be generalized
    pub use_fma: bool,
    pub use_lc: bool,
}

// Constrained vector
pub trait CV<F: Field + 'static>: Downcast + Debug {
    fn id(&self) -> String;

    fn width(&self) -> usize;

    fn sat(&self, witness: &Trace<F>) -> bool;

    fn gen_table(&self, config: &CsConfig) -> Vec<Constr<F>>;
}
impl_downcast!(CV<F> where F :Field + 'static);

// Collection of constrained vectors
// Also adds oracles
// here we also add the "missing" new wires
pub trait Gate<F: Field + 'static>: Debug + Downcast + fmt::Display {
    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>>;

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool;

    fn input_vars(&self) -> Vec<Name>;

    fn clone_box(&self) -> Box<dyn Gate<F>>;
}
impl_downcast!(Gate<F> where F :Field + 'static);

impl<F: Field + 'static> Clone for Box<dyn Gate<F>> {
    fn clone(&self) -> Box<dyn Gate<F>> {
        self.clone_box()
    }
}

impl<F: fmt::Display + Field + 'static> fmt::Display for Constr<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Variable:")?;
        for index in &self.variable {
            write!(f, "{:3}, ", index)?;
        }
        write!(f, "Fixed: ")?;
        for val in &self.fixed {
            write!(f, "{:3}, ", val)?;
        }
        writeln!(f)?;

        Ok(())
    }
}
