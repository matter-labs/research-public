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
    internal: usize,
}

impl<F: Field> NameContext<F> {
    pub fn empty() -> Self {
        NameContext {
            map: HashMap::new(),
            const_cache: HashMap::new(),
            next: 0,
            internal: 0,
        }
    }

    pub fn new_name(&mut self) -> Name {
        let n = self.internal;
        self.internal += 1;
        Name::InternalW(n)
    }

    fn push_inner(&mut self, k: Name) -> usize {
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
                None => self.push_inner(i),
            }
        }
    }

    pub fn push_unused(&mut self) -> usize {
        self.push_inner(Name::Unused)
    }

    pub fn push(&mut self, i: Name) -> usize {
        self.get(i)
    }

    pub fn internal_name(&mut self) -> Name {
        let pos = self.next;
        let n = Name::InternalW(pos);
        self.push(n);
        n
    }

    pub fn allocate_pos(&mut self) -> usize {
        let pos = self.next;
        self.next += 1;
        pos
    }

    pub fn read_name(&mut self, n: Name, trace: &Trace<F>) -> (bool, F) {
        let pos = self.get(n);
        let (b, f) = trace.read(pos);
        if !b {
            println!("read_name failed for name {:?} at pos {}", n, pos)
        }
        (b, f)
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
pub struct Trace<T: Clone>(pub Vec<T>);

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

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy, PartialOrd, Ord)]
pub enum Name {
    Input(usize),
    Wire(usize),
    InternalW(usize),
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
        } else if let Name::InternalW(w) = *self {
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

pub type Renaming = HashMap<Name, Name>;

pub fn apply_renaming(n: Name, renaming: &Renaming) -> Name {
    *renaming.get(&n).unwrap_or(&n)
}

// Collection of constrained vectors
// Also adds oracles
// here we also add the "missing" new wires
pub trait Gate<F: Field + 'static>: Debug + Downcast + fmt::Display {
    fn kind(&self) -> String;

    fn gen_cs(&self, config: &Config, ctxt: &mut NameContext<F>) -> Vec<Box<dyn CV<F>>>;

    fn gen_trace(&self, config: &Config, ctxt: &mut NameContext<F>, trace: &mut Trace<F>) -> bool;

    fn input_vars(&self) -> Vec<Name>;

    fn output_vars(&self) -> Vec<Name>;

    // For optimization only
    fn rename(&mut self, renaming: &Renaming);

    fn other_params(&self) -> Vec<u8> {
        vec![]
    }

    fn range_checks(&self) -> Vec<(Name, usize)> {
        vec![]
    }

    fn range_checks_required(&self) -> Vec<(Name, usize)> {
        vec![]
    }

    fn droppable_range_checks(&self) -> Vec<(Name, usize)> {
        vec![]
    }

    fn no_range_checks_unsound(&mut self) {}

    fn can_drop_range_checks(&self) -> bool {
        false
    }

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
