use crate::circuit::Circuit;
use crate::cs_arith::GenericArith;
use crate::cs_boolcheck::BoolCheck;
use crate::cs_linear_combination::LinearCombination;
use crate::expr::{Config, Gate, Name, Renaming};
use crate::field::*;
use crate::gate_iszero::IsZero;
use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
enum AE<F: Field + 'static> {
    Const(F),
    Var(Name),
    Add(Box<AE<F>>, Box<AE<F>>),
    Mul(Box<AE<F>>, Box<AE<F>>),
}

#[derive(Debug, Clone)]
enum Shape<F: Field + 'static> {
    LinearTerm {
        c1: F,
        x: Name,
        c2: F,
        ga: GenericArith<F>,
    },
    LinearC(Box<dyn Gate<F>>),
    Full(Box<dyn Gate<F>>),
    Booleans(GenericArith<F>),
}

fn bc_to_shape<F: Field + 'static, const N: usize>(
    boxed: Box<dyn Gate<F>>,
    bool_wires: &HashSet<Name>,
) -> Option<(Name, Shape<F>)> {
    if let Some(ga) = boxed.downcast_ref::<GenericArith<F>>() {
        match *ga {
            GenericArith { l, r, .. }
                if (l.unused() || bool_wires.get(&l).is_some())
                    && (r.unused() || bool_wires.get(&r).is_some())
                    && !(l.unused() && r.unused()) =>
            {
                Some((ga.o, Shape::Booleans(ga.clone())))
            }
            GenericArith {
                ql,
                l,
                qr,
                r: Name::Unused,
                qm,
                qc,
                ..
            } if qr == F::ZERO && qm == F::ZERO => Some((
                ga.o,
                Shape::LinearTerm {
                    c1: ql,
                    x: l,
                    c2: qc,
                    ga: ga.clone(),
                },
            )),
            GenericArith {
                ql,
                l: Name::Unused,
                qr,
                r,
                qm,
                qc,
                ..
            } if ql == F::ZERO && qm == F::ZERO => Some((
                ga.o,
                Shape::LinearTerm {
                    c1: qr,
                    x: r,
                    c2: qc,
                    ga: ga.clone(),
                },
            )),
            GenericArith {
                ql,
                l,
                qr,
                r,
                qm,
                qc,
                ..
            } if qm == F::ZERO && qc == F::ZERO => Some((ga.o, Shape::LinearC(boxed))),
            _ => Some((ga.o, Shape::Full(boxed))),
        }
    } else if let Some(lc) = boxed.downcast_ref::<LinearCombination<F, N>>() {
        Some((lc.o, Shape::LinearC(boxed)))
    } else {
        None
    }
}

fn add_shape_to_map<F: Field + 'static, const N: usize>(
    map: &mut ShapeMap<F>,
    bool_wires: &HashSet<Name>,
    boxed: Box<dyn Gate<F>>,
) {
    if let Some((o, shape)) = bc_to_shape::<F, N>(boxed, bool_wires) {
        map.insert(o, shape);
    }
}

fn add_ref(m: &mut HashMap<Name, usize>, v: Name) {
    let old = m.get(&v).unwrap_or(&0);
    m.insert(v, old + 1);
}

fn decrease_ref(m: &mut HashMap<Name, usize>, v: Name) {
    let old = m.get(&v).unwrap();
    m.insert(v, old - 1);
}

fn get_linear_contribution<F: Field + 'static>(from: &GenericArith<F>, on: Name) -> Option<F> {
    if from.l == on {
        Some(from.ql)
    } else if from.r == on {
        Some(from.qr)
    } else {
        None
    }
}

fn get_m_contribution<F: Field + 'static>(from: &GenericArith<F>) -> Option<F> {
    if from.l.unused() || from.r.unused() {
        None
    } else {
        Some(from.qm)
    }
}

fn inline_bool_constraint<F: Field + 'static>(
    target: &GenericArith<F>,
    source1: &GenericArith<F>,
    source2: &GenericArith<F>,
    l: Name,
    r: Name,
) -> GenericArith<F> {
    let ql1 = get_linear_contribution(source1, l).unwrap_or(F::ZERO);
    let ql2 = get_linear_contribution(source2, l).unwrap_or(F::ZERO);
    let qr1 = get_linear_contribution(source1, r).unwrap_or(F::ZERO);
    let qr2 = get_linear_contribution(source2, r).unwrap_or(F::ZERO);
    let qm1 = get_m_contribution(source1).unwrap_or(F::ZERO);
    let qm2 = get_m_contribution(source2).unwrap_or(F::ZERO);
    let qc1 = source1.qc;
    let qc2 = source2.qc;
    let ql3 = target.ql;
    let qr3 = target.qr;
    let qm3 = target.qm;
    let qc3 = target.qc;

    let ql4 = ql3 * ql1 + qr3 * ql2 + qm3 * ql1 * ql2 + qm3 * ql1 * qc2 + qm3 * ql2 * qc1;
    let qr4 = ql3 * qr1 + qr3 * qr2 + qm3 * qr1 * qr2 + qm3 * qr1 * qc2 + qm3 * qr2 * qc1;
    let qm4 = ql3 * qm1 + qr3 * qm2 + qm3 * (ql1 * qr2 + qr1 * ql2 + ql1 * qm2 + qr1 * qm2);
    let qc4 = ql3 * qc1 + qr3 * qc2 + qm3 * qc1 * qc2 + qc3;
    GenericArith {
        ql: ql4,
        l,
        qr: qr4,
        r,
        qm: qm4,
        qc: qc4,
        o: target.o,
    }
}

fn inline_booleans<F: Field + 'static>(
    target: &GenericArith<F>,
    shapes: &ShapeMap<F>,
    bool_wires: &HashSet<Name>,
    refcount: &mut HashMap<Name, usize>,
) -> Option<GenericArith<F>> {
    match (shapes.get(&target.l), shapes.get(&target.r)) {
        (Some(Shape::Booleans(ga_l)), Some(Shape::Booleans(ga_r))) => {
            let l_vars: HashSet<Name> = ga_l
                .input_vars()
                .into_iter()
                .filter(|v| !v.unused())
                .collect();
            let r_vars: HashSet<Name> = ga_r
                .input_vars()
                .into_iter()
                .filter(|v| !v.unused())
                .collect();
            let vars: Vec<&Name> = l_vars.union(&r_vars).collect();
            if vars.len() == 2 {
                let l = vars[0];
                let r = vars[1];
                decrease_ref(refcount, ga_l.o);
                decrease_ref(refcount, ga_r.o);
                Some(inline_bool_constraint(target, ga_l, ga_r, *l, *r))
            } else {
                None
            }
        }
        (Some(Shape::Booleans(ga_l)), None) if target.r.unused() => {
            let vars = ga_l.input_vars();
            let l = vars[0];
            let r = vars[1];
            let dummy = GenericArith {
                ql: F::ZERO,
                l: Name::Unused,
                qr: F::ZERO,
                r: Name::Unused,
                qm: F::ONE,
                qc: F::ZERO,
                o: target.o,
            };
            decrease_ref(refcount, ga_l.o);
            Some(inline_bool_constraint(target, ga_l, &dummy, l, r))
        }
        (None, Some(Shape::Booleans(ga_r))) if target.l.unused() => {
            let vars = ga_r.input_vars();
            let l = vars[0];
            let r = vars[1];
            let dummy = GenericArith {
                ql: F::ZERO,
                l: Name::Unused,
                qr: F::ZERO,
                r: Name::Unused,
                qm: F::ONE,
                qc: F::ZERO,
                o: target.o,
            };
            decrease_ref(refcount, ga_r.o);
            Some(inline_bool_constraint(target, ga_r, &dummy, l, r))
        }
        (Some(Shape::Booleans(ga_l)), None) if bool_wires.get(&target.r).is_some() => {
            let mut l_vars: HashSet<Name> = ga_l
                .input_vars()
                .into_iter()
                .filter(|v| !v.unused())
                .collect();
            l_vars.insert(target.r);
            let dummy = GenericArith {
                qr: F::ONE,
                r: target.r,
                ql: F::ZERO,
                l: Name::Unused,
                qm: F::ZERO,
                qc: F::ZERO,
                o: Name::Unused,
            };
            let vars: Vec<&Name> = l_vars.iter().collect();
            if vars.len() == 2 {
                let l = vars[0];
                let r = vars[1];
                decrease_ref(refcount, ga_l.o);
                Some(inline_bool_constraint(target, &dummy, ga_l, *l, *r))
            } else {
                None
            }
        }
        (None, Some(Shape::Booleans(ga_r))) if bool_wires.get(&target.l).is_some() => {
            let mut r_vars: HashSet<Name> = ga_r
                .input_vars()
                .into_iter()
                .filter(|v| !v.unused())
                .collect();
            r_vars.insert(target.l);
            let dummy = GenericArith {
                qr: F::ONE,
                r: target.l,
                ql: F::ZERO,
                l: Name::Unused,
                qm: F::ZERO,
                qc: F::ZERO,
                o: Name::Unused,
            };
            let vars: Vec<&Name> = r_vars.iter().collect();
            if vars.len() == 2 {
                decrease_ref(refcount, ga_r.o);
                let l = vars[0];
                let r = vars[1];
                Some(inline_bool_constraint(target, &dummy, ga_r, *l, *r))
            } else {
                None
            }
        }
        (_, _) => None,
    }
}

type LinearTerms<F> = HashMap<Name, F>;

fn get_linear_terms<F: Field + 'static, const N: usize>(
    n: Name,
    coeff: F,
    shapes: &ShapeMap<F>,
) -> (Vec<(Name, F)>, Option<Name>) {
    match shapes.get(&n) {
        Some(Shape::LinearTerm { c1, x, c2, .. }) if *c2 == F::ZERO => {
            (vec![(*x, coeff * *c1)], Some(n))
        }
        Some(Shape::LinearC(boxed)) => {
            if let Some(ga) = boxed.downcast_ref::<GenericArith<F>>() {
                let mut terms = vec![];
                if !ga.l.unused() {
                    terms.push((ga.l, coeff * ga.ql));
                }
                if !ga.r.unused() {
                    terms.push((ga.r, coeff * ga.qr));
                }
                (terms, Some(n))
            } else if let Some(lc) = boxed.downcast_ref::<LinearCombination<F, N>>() {
                let terms = lc
                    .vars
                    .into_iter()
                    .zip(lc.coeffs)
                    .filter_map(|(n, q)| {
                        if !n.unused() {
                            Some((n, q * coeff))
                        } else {
                            None
                        }
                    })
                    .collect();
                (terms, Some(n))
            } else {
                unreachable!()
            }
        }
        _ => (vec![(n, coeff)], None),
    }
}

fn inline_lc<F: Field + 'static, const N: usize>(
    target: &GenericArith<F>,
    shapes: &ShapeMap<F>,
    bool_wires: &HashSet<Name>,
    refcount: &mut HashMap<Name, usize>,
    config: &Config,
    counter: &mut OptimizationCounter,
) -> Option<Box<dyn Gate<F>>> {
    if !config.use_lc {
        return None;
    }
    if let Some((_, Shape::LinearC(_))) = bc_to_shape::<F, N>(Box::new(target.clone()), bool_wires)
    {
        let mut lterms: LinearTerms<F> = LinearTerms::new();
        let (lterms_l, drop_l) = get_linear_terms::<F, N>(target.l, target.ql, shapes);
        let (lterms_r, drop_r) = get_linear_terms::<F, N>(target.r, target.qr, shapes);

        lterms_l.iter().for_each(|(name, new)| {
            lterms
                .entry(*name)
                .and_modify(|old| *old = *old + *new)
                .or_insert(*new);
        });
        lterms_r.iter().for_each(|(name, new)| {
            lterms
                .entry(*name)
                .and_modify(|old| *old = *old + *new)
                .or_insert(*new);
        });
        // ideally both, but only one if both don't fit
        let (drop_l, drop_r) = if lterms.len() > N {
            // Both don't fit
            if (lterms_l.len() >= lterms_r.len() || lterms_r.len() >= N) && lterms_l.len() < N {
                // inline l
                let drop_r = None;
                lterms.drain();
                lterms_l.into_iter().for_each(|(name, f)| {
                    lterms.insert(name, f);
                });
                lterms
                    .entry(target.r)
                    .and_modify(|old| *old = *old + target.qr)
                    .or_insert(target.qr);
                (drop_l, drop_r)
            } else if lterms_r.len() < N {
                // inline r
                let drop_l = None;
                lterms.drain();
                lterms_r.into_iter().for_each(|(name, f)| {
                    lterms.insert(name, f);
                });
                lterms
                    .entry(target.l)
                    .and_modify(|old| *old = *old + target.ql)
                    .or_insert(target.ql);
                (drop_l, drop_r)
            } else {
                // Too bad
                (None, None)
            }
        } else {
            (drop_l, drop_r)
        };

        if lterms.len() <= 2 {
            drop_l.iter().for_each(|n| decrease_ref(refcount, *n));
            drop_r.iter().for_each(|n| decrease_ref(refcount, *n));
            let lterms: Vec<(Name, F)> = lterms.drain().collect();
            let dft = (Name::Unused, F::ZERO);
            let (l, ql) = lterms.first().unwrap();
            let (r, qr) = lterms.get(1).unwrap_or(&dft);
            let ga = GenericArith {
                l: *l,
                ql: *ql,
                r: *r,
                qr: *qr,
                qm: F::ZERO,
                qc: F::ZERO,
                o: target.o,
            };
            drop_l
                .iter()
                .for_each(|_| counter.increment(OptimizationTag::ArithmeticInlining));
            drop_r
                .iter()
                .for_each(|_| counter.increment(OptimizationTag::ArithmeticInlining));
            Some(Box::new(ga))
        } else if lterms.len() <= N {
            drop_l.iter().for_each(|n| decrease_ref(refcount, *n));
            drop_r.iter().for_each(|n| decrease_ref(refcount, *n));
            let mut vars: [Name; N] = [Name::Unused; N];
            let mut coeffs: [F; N] = [F::ZERO; N];
            lterms.iter().enumerate().for_each(|(i, (var, q))| {
                vars[i] = *var;
                coeffs[i] = *q;
            });
            let lc = LinearCombination {
                coeffs,
                vars,
                o: target.o,
            };
            drop_l
                .iter()
                .for_each(|_| counter.increment(OptimizationTag::ArithmeticInlining));
            drop_r
                .iter()
                .for_each(|_| counter.increment(OptimizationTag::ArithmeticInlining));
            counter.increment(OptimizationTag::GateReplacement);
            Some(Box::new(lc))
        } else {
            // println!("LC too large, size {}", lterms.len());
            None
        }
    } else {
        None
    }
}

type ShapeMap<F> = HashMap<Name, Shape<F>>;

type RangeCheckMap = HashMap<Name, (usize, usize)>;

fn rc_map_push(rcm: &mut RangeCheckMap, n: Name, width: usize) {
    match rcm.get_mut(&n) {
        Some((current_width, count)) => {
            if width < *current_width {
                *current_width = width;
            }
            *count += 1;
        }
        None => {
            rcm.insert(n, (width, 1));
        }
    }
}

fn rc_map_decrement(rcm: &mut RangeCheckMap, n: &Name) {
    match rcm.get_mut(n) {
        Some((width, count)) => {
            if *count > 1 {
                *count -= 1
            } else {
                panic!("Dropping a range check with count 1")
            }
        }
        None => {
            panic!(
                "Warning: Attempted to decrement count for a non-existent name: {:?}",
                n
            );
        }
    }
}

fn can_drop_range_checks(rcm: &RangeCheckMap, req: Vec<(Name, usize)>) -> bool {
    req.iter().all(|(n, _)| {
        let (_, count) = rcm.get(n).unwrap_or(&(0, 0));
        *count > 1
    })
}

type GateCompId = (String, Vec<Name>, Vec<u8>);

type GateCompMap = HashMap<GateCompId, Vec<Name>>;

pub fn apply_cse<F: Field + 'static>(
    circ: &Circuit<F>,
    counter: &mut OptimizationCounter,
) -> Circuit<F> {
    // Create a computation map.
    // The tuple (kind, inputs, other) fully determines
    // a gate's computation.
    let mut compmap = GateCompMap::new();
    circ.for_each(&mut |boxed| {
        let kind = boxed.kind();
        let inputs = boxed.input_vars();
        let other = boxed.other_params();
        let _ = compmap
            .entry((kind, inputs, other))
            .or_insert_with(|| boxed.output_vars());
    });
    let mut renaming = Renaming::new();
    // Remove duplicated "computation", saving necessary renamings
    let circ = circ.map(|boxed| {
        let kind = boxed.kind();
        let inputs = boxed.input_vars();
        let other = boxed.other_params();
        let key = (kind, inputs, other);
        let comp_outputs = compmap.get(&key).unwrap();
        let outputs = boxed.output_vars();
        if *comp_outputs == outputs {
            Circuit::Gate(boxed.clone())
        } else {
            outputs
                .iter()
                .zip(comp_outputs.iter())
                .for_each(|(old, new)| {
                    renaming.insert(*old, *new);
                });
            counter.increment(OptimizationTag::CommonSubEl);
            Circuit::Nil(PhantomData)
        }
    });
    // Apply renaming
    circ.map(|boxed| {
        let mut boxed = boxed.clone();
        boxed.rename(&renaming);
        Circuit::Gate(boxed)
    })
}

fn inline_linear_term_on_l<F: Field + 'static, const N: usize>(
    target: &GenericArith<F>,
    shapes: &mut ShapeMap<F>,
    bool_wires: &HashSet<Name>,
    refcount: &mut HashMap<Name, usize>,
) -> Option<Circuit<F>> {
    if let Some(Shape::LinearTerm { c1, x, c2, .. }) = shapes.get(&target.l) {
        // LinearTerm on l:
        // Target: ql l + qr r + qm l r + qc
        // l = c1 x + c2
        // Inlined: ql (c1 x + c2) +  qr r + qm r (c1 x + c2)  + qc
        //        = ql c1 x + ql c2 + qr r + qm r c1 x + qm r c2 + qc
        //        = (ql c1) x + (qr + qm c2) r + (qm c1) x r + (ql c2 + qc)
        decrease_ref(refcount, target.l);
        let ql = target.ql * *c1;
        let l = *x;
        let qr = target.qr + target.qm * *c2;
        let qm = target.qm * *c1;
        let qc = target.qc + target.ql * *c2;
        let bc = GenericArith {
            ql,
            l,
            qr,
            qm,
            qc,
            ..target.clone()
        };
        let optimized: Box<dyn Gate<F>> = Box::new(bc);
        self::add_shape_to_map::<F, N>(shapes, bool_wires, optimized.clone());
        Some(Circuit::Gate(optimized))
    } else {
        None
    }
}

fn inline_linear_term_on_r<F: Field + 'static, const N: usize>(
    target: &GenericArith<F>,
    shapes: &mut ShapeMap<F>,
    bool_wires: &HashSet<Name>,
    refcount: &mut HashMap<Name, usize>,
) -> Option<Circuit<F>> {
    if let Some(Shape::LinearTerm { c1, x, c2, .. }) = shapes.get(&target.r) {
        // LinearTerm on r
        decrease_ref(refcount, target.r);
        let ql = target.ql + target.qm * *c2;
        let qr = target.qr * *c1;
        let r = *x;
        let qm = target.qm * *c1;
        let qc = target.qc + target.qr * *c2;
        let bc = GenericArith {
            ql,
            r,
            qr,
            qm,
            qc,
            ..target.clone()
        };
        let optimized: Box<dyn Gate<F>> = Box::new(bc);
        self::add_shape_to_map::<F, N>(shapes, bool_wires, optimized.clone());
        Some(Circuit::Gate(optimized))
    } else {
        None
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Hash)]
pub enum OptimizationTag {
    ArithmeticInlining,
    BooleanInlining,
    GateReplacement,
    CommonSubEl,
    CommonRCEl,
}

#[derive(Debug, Clone)]
pub struct OptimizationCounter(HashMap<OptimizationTag, usize>);

impl OptimizationCounter {
    pub fn new() -> Self {
        OptimizationCounter(HashMap::new())
    }

    fn increment(&mut self, tag: OptimizationTag) {
        let entry = self.0.entry(tag).or_insert(0);
        *entry += 1;
    }
}

pub fn optimize<F: Field + 'static, const N: usize>(
    circ: &Circuit<F>,
    config: &Config,
    counter: &mut OptimizationCounter,
) -> Circuit<F> {
    // Common-subexpression elimination
    let circ = apply_cse(circ, counter);

    // Contruct the refcount map
    let mut refcount = HashMap::<Name, usize>::new();
    circ.for_each(&mut |boxed| {
        let inputs = boxed.input_vars();
        inputs.iter().for_each(|v| add_ref(&mut refcount, *v))
    });

    // Construct bool wire set
    let mut bool_wires = HashSet::<Name>::new();
    circ.for_each(&mut |boxed| {
        if let Some(bc) = boxed.downcast_ref::<BoolCheck>() {
            bool_wires.insert(bc.0);
        } else if let Some(iz) = boxed.downcast_ref::<IsZero>() {
            bool_wires.insert(iz.b);
        }
    });
    // Range check map
    let mut rcm = RangeCheckMap::new();
    circ.for_each(&mut |boxed| {
        let rcs = boxed.range_checks();
        rcs.iter()
            .for_each(|(name, width)| rc_map_push(&mut rcm, *name, *width))
    });
    // Construct a map {name -> Shape}
    let mut shapes = ShapeMap::new();
    circ.for_each(&mut |boxed| {
        self::add_shape_to_map::<F, N>(&mut shapes, &bool_wires, boxed.clone())
    });
    // Iterate over map:
    // Generic garith optimization: (AE) -> map -> ()
    let circ = circ.map(|boxed| {
        if let Some(ga) = boxed.downcast_ref::<GenericArith<F>>() {
            if let Some(optimized) = inline_booleans(ga, &shapes, &bool_wires, &mut refcount) {
                counter.increment(OptimizationTag::BooleanInlining);
                let optimized: Box<dyn Gate<F>> = Box::new(optimized);
                self::add_shape_to_map::<F, N>(&mut shapes, &bool_wires, optimized.clone());
                Circuit::Gate(optimized)
            } else if let Some(optimized) =
                inline_lc::<F, N>(ga, &shapes, &bool_wires, &mut refcount, config, counter)
            {
                self::add_shape_to_map::<F, N>(&mut shapes, &bool_wires, optimized.clone());
                Circuit::Gate(optimized)
            } else if !config.use_fma {
                if let Some(inlined) =
                    inline_linear_term_on_l::<F, N>(ga, &mut shapes, &bool_wires, &mut refcount)
                {
                    counter.increment(OptimizationTag::ArithmeticInlining);
                    inlined
                } else if let Some(inlined) =
                    inline_linear_term_on_r::<F, N>(ga, &mut shapes, &bool_wires, &mut refcount)
                {
                    counter.increment(OptimizationTag::ArithmeticInlining);

                    inlined
                } else {
                    Circuit::Gate(boxed.clone())
                }
            } else {
                Circuit::Gate(boxed.clone())
            }
        } else if boxed.can_drop_range_checks() {
            // Drop redundant range-checks
            if can_drop_range_checks(&rcm, boxed.droppable_range_checks()) {
                boxed
                    .droppable_range_checks()
                    .iter()
                    .for_each(|(n, _w)| rc_map_decrement(&mut rcm, n));
                let mut new = boxed.clone();
                counter.increment(OptimizationTag::CommonRCEl);
                new.no_range_checks_unsound();
                Circuit::Gate(new)
            } else {
                Circuit::Gate(boxed.clone())
            }
        } else {
            Circuit::Gate(boxed.clone())
        }
    });
    let circ = circ.map(|boxed| {
        if let Some(ga) = boxed.downcast_ref::<GenericArith<F>>() {
            if let Some(0) = refcount.get(&ga.o) {
                Circuit::Nil(PhantomData)
            } else {
                Circuit::Gate(boxed.clone())
            }
        } else if let Some(lc) = boxed.downcast_ref::<LinearCombination<F, N>>() {
            if let Some(0) = refcount.get(&lc.o) {
                Circuit::Nil(PhantomData)
            } else {
                Circuit::Gate(boxed.clone())
            }
        } else {
            Circuit::Gate(boxed.clone())
        }
    });
    circ
}

use std::fmt::Display;
use std::fmt::Formatter;
use std::vec;

#[derive(Debug, Clone, std::cmp::PartialEq)]
pub struct NF_<F: Field, R> {
    pub s: Vec<(Vec<R>, F)>,
    pub c: F,
}

pub type NF<F> = NF_<F, Name>;

impl<F: Field> Display for NF<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut terms = vec![];

        // Format each term as "scalar * var1 * var2 * ..."
        for (vars, scalar) in &self.s {
            let vars_str = vars
                .iter()
                .map(|n| format!("{:?}", n))
                .collect::<Vec<String>>()
                .join(" * ");
            terms.push(format!("{:?} * {}", scalar, vars_str));
        }

        // Add the constant if it's not zero
        if !(self.c == F::ZERO) || terms.is_empty() {
            // Show the constant if it's non-zero or if it's the only term
            terms.push(format!("{:?}", self.c));
        }

        // Join all terms with " + "
        write!(f, "{}", terms.join(" + "))
    }
}

fn remove_name(names: &mut Vec<Name>, name_to_remove: &Name) -> usize {
    let initial_length = names.len();
    names.retain(|name| name != name_to_remove);
    let removed_count = initial_length - names.len();
    removed_count
}

fn multiply_nfs<F: Field>(polynomials: Vec<NF<F>>, coeff: F, degree_bound: usize) -> Option<NF<F>> {
    let mut term_map: HashMap<Vec<Name>, F> = std::collections::HashMap::new();

    assert!(!polynomials.is_empty());
    // First scale hd by coeff

    let (hd, tail) = polynomials.split_first().unwrap();
    // Multiply first by constant
    let mut c = hd.c * coeff;

    for (poly_vars, poly_coeff) in &hd.s {
        term_map.insert(poly_vars.clone(), *poly_coeff * coeff);
    }

    for poly in tail {
        let mut new_terms = Vec::new();

        // Multiply each term in the current result by each term in the polynomial
        for (res_vars, res_coeff) in &term_map {
            for (poly_vars, poly_coeff) in &poly.s {
                if res_vars.is_empty() && poly_vars.is_empty() {
                    panic!("What")
                } else {
                    let mut combined_vars = res_vars.clone();
                    combined_vars.extend(poly_vars.clone());
                    combined_vars.sort_unstable();

                    let new_coeff = *res_coeff * *poly_coeff;
                    if combined_vars.len() > degree_bound {
                        return None;
                    }

                    // Collect the new term
                    if new_coeff != F::ZERO {
                        new_terms.push((combined_vars, new_coeff));
                    }
                }
            }

            if !(*res_coeff * poly.c == F::ZERO) {
                new_terms.push((res_vars.clone(), poly.c * *res_coeff));
            }
        }

        for (poly_vars, poly_coeff) in &poly.s {
            // Multiply by constant
            if !(c * *poly_coeff == F::ZERO) {
                new_terms.push((poly_vars.clone(), c * *poly_coeff));
            }
        }
        c = c * poly.c; // Update the constant term

        term_map.drain();

        // Aggregate like terms by reducing terms with the same variable configuration
        for (vars, coeff) in new_terms {
            let entry = term_map.entry(vars).or_insert(F::ZERO);
            *entry = *entry + coeff;
        }
    }
    let s: Vec<(Vec<Name>, F)> = term_map
        .into_iter()
        .filter(|(names, _)| !names.is_empty())
        .collect();
    Some(NF_ { s, c })
}

#[derive(Debug, Clone)]
struct TermVec<F>(pub Vec<(Vec<Name>, F)>);

impl<F: Field> TermVec<F> {
    fn push(&mut self, x: (Vec<Name>, F)) {
        assert!(!x.0.is_empty());
        assert!(F::ZERO != x.1);
        self.0.push(x)
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}

fn inline_nf<F: Field>(
    on: Name,
    nf: &NF<F>,
    map: &HashMap<Name, NF<F>>,
    max_degree: usize,
) -> Option<NF<F>> {
    let mut new_s = Vec::new();
    let mut new_c = nf.c;

    let mut some_inlined = false;
    let mut resetted: HashSet<Name> = HashSet::new();

    // Process each term in s
    for (vars, coeff) in &nf.s {
        assert!(!vars.is_empty());
        let mut subterms = vec![(vars.clone(), *coeff)];
        let mut inlined_vars = vec![];
        let mut tmp_c = new_c;

        if *coeff == F::ZERO {
            continue;
        }

        let mut cont = false;

        // Inline each variable in the term
        for var in vars {
            if resetted.contains(var) {
                assert!(subterms.len() == 1);
                // Skip inlining for high-power variables
            } else if let Some(nf_var) = map.get(var) {
                // Check if the variable maps to essentially a constant
                if nf_var.s.is_empty() {
                    assert!(subterms.len() == 1);
                    some_inlined = true;
                    // Constant propagation case
                    if nf_var.c == F::ZERO {
                        cont = true;
                        // If the constant is zero, the term becomes zero and can be skipped
                        break; // This breaks out of the variable loop for the current term
                    } else {
                        // Multiply the term's coefficient by the constant
                        subterms.iter_mut().for_each(|(_, tc)| *tc = *tc * nf_var.c);
                    }
                } else {
                    // Normal inlining with variables
                    let old_subterms = subterms.clone();
                    let old_tmp_c = tmp_c;
                    subterms = vec![];

                    let mut degree_overflow = false;

                    for (mut other_term_vars, term_coeff) in old_subterms.clone() {
                        let n_occurrences = remove_name(&mut other_term_vars, var);
                        if n_occurrences == 0 {
                            subterms.push((other_term_vars, term_coeff))
                        } else {
                            let (mut nfs, q) = if other_term_vars.is_empty() {
                                (vec![], term_coeff)
                            } else {
                                (
                                    vec![NF_ {
                                        s: vec![(other_term_vars.clone(), term_coeff)],
                                        c: F::ZERO,
                                    }],
                                    F::ONE,
                                )
                            };
                            let inlined_nfs: Vec<NF<F>> =
                                (0..n_occurrences).map(|_| nf_var.clone()).collect();
                            nfs.extend(inlined_nfs);
                            if let Some(inlined) = multiply_nfs(nfs.clone(), q, max_degree) {
                                assert!(inlined.s.iter().all(|(n, _)| !n.is_empty()));
                                some_inlined = true;
                                subterms.extend(inlined.s);
                                tmp_c = tmp_c + inlined.c;
                            } else {
                                // No inlining available, keep the variable
                                degree_overflow = true;
                                break;
                            }
                        }

                        if degree_overflow {
                            break;
                        } else {
                            inlined_vars.push(*var);
                        }
                    }
                    if degree_overflow {
                        resetted.insert(*var);
                        subterms = old_subterms.clone();
                        tmp_c = old_tmp_c;
                        continue;
                    }
                }
            }
        }

        if cont {
            continue;
        }

        new_s.extend(subterms);
        if some_inlined {
            new_c = tmp_c;
        }
    }

    // Deduplicate and combine like terms
    let mut term_map: HashMap<Vec<Name>, F> = HashMap::new();
    for (vars, coeff) in new_s {
        let entry = term_map.entry(vars).or_insert(F::ZERO);
        *entry = *entry + coeff;
    }

    if some_inlined {
        Some(NF {
            s: term_map
                .into_iter()
                .filter(|&(_, coeff)| coeff != F::ZERO)
                .collect(),
            c: new_c,
        })
    } else {
        None
    }
}

#[derive(Debug, Clone)]
pub struct Atomic_<E, R> {
    pub e: E,
    pub o: R,
}

pub type Atomic<E> = Atomic_<E, Name>;

impl<F: Field> Atomic<NF<F>> {
    fn from_arith(ga: &GenericArith<F>) -> Self {
        match *ga {
            GenericArith {
                l: Name::Unused,
                r: Name::Unused,
                qc,
                ..
            } => Atomic {
                e: NF { s: vec![], c: qc },
                o: ga.o,
            },
            GenericArith {
                l: Name::Unused,
                r,
                qr,
                qc,
                ..
            } => {
                // qr * r + qc
                let e = NF {
                    s: vec![(vec![r], qr)],
                    c: qc,
                };
                Atomic { e, o: ga.o }
            }
            GenericArith {
                r: Name::Unused, ..
            } => {
                // ql * l + qc
                let e = NF {
                    s: vec![(vec![ga.l], ga.ql)],
                    c: ga.qc,
                };
                Atomic { e, o: ga.o }
            }
            GenericArith {
                ql,
                l,
                qr,
                r,
                qm,
                qc,
                o,
            } => {
                //  ql * l + qr * r + qm * l * r + qc
                let e = NF {
                    s: vec![
                        (vec![ga.l], ga.ql),
                        (vec![ga.r], ga.qr),
                        (vec![ga.l, ga.r], ga.qm),
                    ],
                    c: ga.qc,
                };
                Atomic { e, o }
            }
        }
    }
}

pub fn circuit_to_nfs<F: Field + 'static>(c: Circuit<F>) -> Vec<Atomic<NF<F>>> {
    let (_, gates) = c.flatten_base_cases_iterative(0);
    gates
        .iter()
        .filter_map(|g| g.downcast_ref::<GenericArith<F>>().map(Atomic::from_arith))
        .collect()
}

fn filter_atomics<F: Field>(atomics: Vec<Atomic<NF<F>>>, outputs: Vec<Name>) -> Vec<Atomic<NF<F>>> {
    let mut name_usage: HashSet<Name> = HashSet::from_iter(outputs);

    // Collect all names used in any NF
    for atomic in &atomics {
        for (vars, _) in &atomic.e.s {
            for var in vars {
                name_usage.insert(*var);
            }
        }
    }

    // Filter atomics to keep only those whose 'o' is in name_usage
    atomics
        .into_iter()
        .filter(|atomic| name_usage.contains(&atomic.o))
        .collect()
}

fn resolve_final_name(name: &Name, name_to_name: &HashMap<Name, Name>) -> Name {
    let mut current_name = name;
    while let Some(next_name) = name_to_name.get(current_name) {
        current_name = next_name;
    }
    *current_name
}

pub fn inline_atomics<F: Field>(c: Circuit<F>, outputs: Vec<Name>) -> Vec<Atomic<NF<F>>> {
    let atomic_nfs: Vec<Atomic<NF<F>>> = circuit_to_nfs(c);
    let mut atomic_map: HashMap<Name, NF<F>> = HashMap::new();

    let mut witness: HashMap<Name, F> = HashMap::new();

    (0..12).for_each(|i| {
        witness.insert(Name::Input(i), F::ZERO);
    });

    let mut atomics_copy = atomic_nfs.clone();
    atomic_nfs.into_iter().for_each(|Atomic { e, o }| {
        atomic_map.insert(o, e);
    });

    atomics_copy = atomics_copy
        .iter()
        .map(|Atomic { e, o }| {
            let v_before = eval_nf(e, &witness);
            if let Some(inlined) = inline_nf(*o, e, &atomic_map, 7) {
                let v = eval_nf(&inlined, &witness);
                if v == v_before {
                    witness.insert(*o, v);
                    atomic_map.insert(*o, inlined.clone());
                    Atomic { e: inlined, o: *o }
                } else {
                  println!("Inlining of {:?} failed.\nBefore it evaluated to {:?}, after {:?}.\nBefore:{:?}\nAfter{:?}", o, v_before, v, e, inlined);
                panic!()
                }
            } else {
                // println!("not inlined on {:?}", o);
                witness.insert(*o, v_before);
                Atomic {
                    e: e.clone(),
                    o: *o,
                }
            }
        })
        .collect();
    atomics_copy = filter_atomics(atomics_copy, outputs);
    println!("Round done, len {}", atomics_copy.len());
    atomics_copy
        .iter()
        .for_each(|Atomic { e, o }| println!("{:?} <- {}", o, e));
    atomics_copy
}

fn eval_nf<F: Field + 'static>(nf: &NF<F>, witness: &HashMap<Name, F>) -> F {
    let mut linear: Vec<F> = vec![];
    nf.s.iter().for_each(|(positions, coeff)| {
        let mut factors: Vec<F> = vec![];
        positions.iter().for_each(|n| {
            let f = witness
                .get(n)
                .expect(format!("{:?} not in witness", n).as_str());
            factors.push(*f);
        });
        let r = factors.iter().fold(F::ONE, |acc, f| *f * acc) * *coeff;
        linear.push(r);
    });
    linear.iter().fold(nf.c, |acc, f| *f + acc)
}

fn eval_atomics<F: Field + 'static>(
    atomics: &Vec<Atomic<NF<F>>>,
    witness: &HashMap<Name, F>,
) -> Vec<F> {
    let mut witness = witness.clone();
    atomics
        .iter()
        .map(|atomic| {
            let f = eval_nf(&atomic.e, &witness);
            witness.insert(atomic.o, f);
            f
        })
        .collect()
}

#[cfg(test)]
mod test {
    use boojum::field::{goldilocks::GoldilocksField, U64Representable};

    use crate::field::Field;

    use super::*;
    use std::sync::Arc;

    fn seq_chain<F: Field>(circuits: Vec<Circuit<F>>) -> Circuit<F> {
        circuits
            .into_iter()
            .fold(Circuit::Nil(PhantomData), |acc, c| {
                Circuit::Seq(Arc::new(acc), Arc::new(c))
            })
    }

    #[test]
    fn test_optimizer() {
        let ariths = [
            GenericArith {
                ql: Fi64(2),
                l: Name::Wire(17),
                qr: Fi64(1),
                r: Name::Wire(41),
                qm: Fi64(0),
                qc: Fi64(0),
                o: Name::Wire(87),
            },
            GenericArith {
                ql: Fi64(1),
                l: Name::Wire(87),
                qr: Fi64(1),
                r: Name::Wire(65),
                qm: Fi64(0),
                qc: Fi64(0),
                o: Name::Wire(88),
            },
            GenericArith {
                ql: Fi64(-5366611358089551806),
                l: Name::Wire(88),
                qr: Fi64(-5366611358089551806),
                r: Name::Wire(88),
                qm: Fi64(1),
                qc: Fi64(-996001545689788156),
                o: Name::Wire(156),
            },
            GenericArith {
                ql: Fi64(-5366611358089551806),
                l: Name::Wire(156),
                qr: Fi64(0),
                r: Name::Wire(88),
                qm: Fi64(1),
                qc: Fi64(0),
                o: Name::Wire(157),
            },
        ];
        let gates: Vec<Circuit<Fi64>> = ariths
            .iter()
            .map(|a| Circuit::Gate(Box::new(a.clone())))
            .collect();
        let c = seq_chain(gates);
        println!("Before {}", c);
        let config = Config::default();
        let mut counter = OptimizationCounter::new();
        let optimized = optimize::<Fi64, 4>(&c, &config, &mut counter);
        println!("After {}", optimized)
    }

    #[test]
    fn test_multiply_nfs() {
        let x = vec![Name::Wire(0)];
        let y = vec![Name::Wire(1)];

        let poly_x = NF {
            s: vec![(x.clone(), 1)],
            c: 0,
        };
        let poly_xy = NF {
            s: vec![(x.clone(), 1), (y.clone(), 1)],
            c: 0,
        }; // This is x + y

        // x * (x + y) * (x + y)

        let polys = vec![poly_x, poly_xy.clone(), poly_xy];

        let result = multiply_nfs(polys, 1, 3);
        // Expected: x^3 + 2 x^2 y + x y^2

        println!("result: {:?}", result);
    }

    #[test]
    fn test_inline_nf() {
        let a = Name::Input(0);
        let b = Name::Input(1);
        let c = Name::Input(2);
        let d = Name::Input(3);
        let x = Name::Wire(0);
        let y = Name::Wire(1);
        let z = Name::Wire(2);

        // x <- 4 a b + c + 2
        let x_a: Atomic<NF<GoldilocksField>> = Atomic_ {
            o: x.clone(),
            e: NF_ {
                s: vec![
                    (
                        vec![a.clone(), b.clone()],
                        GoldilocksField::from_nonreduced_u64(4),
                    ),
                    (vec![c.clone()], GoldilocksField::ONE),
                ],
                c: GoldilocksField::from_u64_unchecked(2),
            },
        };
        // y <- 5 ax + d + 3
        let y_a: Atomic<NF<GoldilocksField>> = Atomic_ {
            o: y.clone(),
            e: NF_ {
                s: vec![
                    (
                        vec![a.clone(), x.clone()],
                        GoldilocksField::from_nonreduced_u64(5),
                    ),
                    (vec![d.clone()], GoldilocksField::ONE),
                ],
                c: GoldilocksField::from_u64_unchecked(3),
            },
        };
        // z <-  x + 2 y * y
        let z_a: Atomic<NF<GoldilocksField>> = Atomic_ {
            o: z.clone(),
            e: NF_ {
                s: vec![
                    (vec![x.clone()], GoldilocksField::ONE),
                    (vec![y.clone(), y.clone()], GoldilocksField::TWO),
                ],
                c: GoldilocksField::from_u64_unchecked(0),
            },
        };
        let mut atomics = vec![x_a, y_a, z_a];
        let mut witness = HashMap::new();
        witness.insert(a, GoldilocksField::from_nonreduced_u64(6));
        witness.insert(b, GoldilocksField::from_nonreduced_u64(7));
        witness.insert(c, GoldilocksField::from_nonreduced_u64(8));
        witness.insert(d, GoldilocksField::from_nonreduced_u64(9));
        let first_vals = eval_atomics(&atomics, &witness);
        println!("First vals: {:?}", first_vals);

        let mut atomic_map: HashMap<Name, NF<GoldilocksField>> = HashMap::new();

        atomics.clone().into_iter().for_each(|Atomic { e, o }| {
            atomic_map.insert(o, e);
        });

        for _ in 1..3 {
            atomics = atomics
                .iter()
                .map(|Atomic { e, o }| {
                    if let Some(inlined) = inline_nf(*o, e, &atomic_map, 7) {
                        Atomic { e: inlined, o: *o }
                    } else {
                        Atomic {
                            e: e.clone(),
                            o: *o,
                        }
                    }
                })
                .collect();
        }
        atomics = filter_atomics(atomics, vec![z.clone()]);
        println!("{:?}", atomics);
        let vals = eval_atomics(&atomics, &witness);
        assert!(vals.last() == first_vals.last())
    }

    #[test]
    fn test_2inline_nf() {
        let a = Name::Input(0);
        let b = Name::Input(1);
        let c = Name::Input(2);
        let d = Name::Input(3);
        let x = Name::Wire(0);
        let y = Name::Wire(1);
        let z = Name::Wire(2);

        // x <- 3 a c + 2 b c + c
        let x_a: Atomic<NF<GoldilocksField>> = Atomic_ {
            o: x,
            e: NF_ {
                s: vec![
                    (vec![a, c], GoldilocksField::from_nonreduced_u64(3)),
                    (vec![b, c], GoldilocksField::from_nonreduced_u64(2)),
                    (vec![c], GoldilocksField::ONE),
                ],
                c: GoldilocksField::ZERO,
            },
        };
        // y <- c * c
        let y_a: Atomic<NF<GoldilocksField>> = Atomic_ {
            o: y,
            e: NF_ {
                s: vec![
                    (vec![c], GoldilocksField::ZERO),
                    (vec![c], GoldilocksField::ZERO),
                    (vec![c, c], GoldilocksField::ONE),
                ],
                c: GoldilocksField::ZERO,
            },
        };
        // z <- x * y
        let z_a: Atomic<NF<GoldilocksField>> = Atomic_ {
            o: z,
            e: NF_ {
                s: vec![(vec![y, x], GoldilocksField::ONE)],
                c: GoldilocksField::from_u64_unchecked(0),
            },
        };
        let mut atomics = vec![x_a, y_a, z_a];
        let mut witness = HashMap::new();
        witness.insert(a, GoldilocksField::from_nonreduced_u64(6));
        witness.insert(b, GoldilocksField::from_nonreduced_u64(7));
        witness.insert(c, GoldilocksField::from_nonreduced_u64(8));
        witness.insert(d, GoldilocksField::from_nonreduced_u64(9));
        let first_vals = eval_atomics(&atomics, &witness);
        println!("First vals: {:?}", first_vals);

        let mut atomic_map: HashMap<Name, NF<GoldilocksField>> = HashMap::new();

        atomics.clone().into_iter().for_each(|Atomic { e, o }| {
            atomic_map.insert(o, e);
        });

        for _ in 1..2 {
            atomics = atomics
                .iter()
                .map(|Atomic { e, o }| {
                    if let Some(inlined) = inline_nf(*o, e, &atomic_map, 7) {
                        Atomic { e: inlined, o: *o }
                    } else {
                        Atomic {
                            e: e.clone(),
                            o: *o,
                        }
                    }
                })
                .collect();
        }
        atomics = filter_atomics(atomics, vec![z.clone()]);
        println!("{:?}", atomics);
        let vals = eval_atomics(&atomics, &witness);
        println!("Final vals: {:?}", vals);
        assert!(
            vals.last() == first_vals.last(),
            "{:?} not equal to {:?}",
            vals.last(),
            first_vals.last()
        )
    }

    #[test]
    fn test_3inline_nf() {
        let nf1: NF<GoldilocksField> = NF_ {
            s: vec![
                (
                    vec![Name::Input(3)],
                    GoldilocksField::from_nonreduced_u64(0x0000000000000006),
                ),
                // (
                //     vec![Name::Input(11)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000003),
                // ),
                // (
                //     vec![Name::Input(4)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000005),
                // ),
                // (
                //     vec![Name::Input(1)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000000e),
                // ),
                // (
                //     vec![Name::Input(7)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000003),
                // ),
                // (
                //     vec![Name::Input(2)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000002),
                // ),
                // (
                //     vec![Name::Input(8)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000005),
                // ),
                // (
                //     vec![Name::Input(5)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000007),
                // ),
                // (
                //     vec![Name::Input(0)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000000a),
                // ),
                // (
                //     vec![Name::Input(6)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000001),
                // ),
                // (
                //     vec![Name::Input(10)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000001),
                // ),
                // (
                //     vec![Name::Input(9)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000007),
                // ),
            ],
            c: GoldilocksField::from_nonreduced_u64(0xb585f767417ee042),
        };

        let nf2: NF<GoldilocksField> = NF_ {
            s: vec![
                // (
                //     vec![Name::Input(1)],
                //     GoldilocksField::from_nonreduced_u64(0xdaa70f5e29e08725),
                // ),
                // (
                //     vec![Name::Input(7), Name::Input(7)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000009),
                // ),
                // (
                //     vec![Name::Input(5), Name::Input(8)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000046),
                // ),
                // (
                //     vec![Name::Input(1), Name::Input(3)],
                //     GoldilocksField::from_nonreduced_u64(0x00000000000000a8),
                // ),
                // (
                //     vec![Name::Input(9)],
                //     GoldilocksField::from_nonreduced_u64(0xed5387ae94f04393),
                // ),
                // (
                //     vec![Name::Input(2), Name::Input(7)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000000c),
                // ),
                // (
                //     vec![Name::Input(2), Name::Input(10)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000004),
                // ),
                // (
                //     vec![Name::Input(1), Name::Input(8)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000008c),
                // ),
                // (
                //     vec![Name::Input(6), Name::Input(7)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000006),
                // ),
                // (
                //     vec![Name::Input(1), Name::Input(6)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000001c),
                // ),
                // (
                //     vec![Name::Input(10), Name::Input(10)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000001),
                // ),
                // (
                //     vec![Name::Input(6), Name::Input(10)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000002),
                // ),
                // (
                //     vec![Name::Input(4), Name::Input(6)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000000a),
                // ),
                // (
                //     vec![Name::Input(8), Name::Input(10)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000000a),
                // ),
                // (
                //     vec![Name::Input(3), Name::Input(11)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000024),
                // ),
                // (
                //     vec![Name::Input(5), Name::Input(6)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000000e),
                // ),
                // (
                //     vec![Name::Input(9), Name::Input(9)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000031),
                // ),
                // (
                //     vec![Name::Input(0), Name::Input(3)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000078),
                // ),
                // (
                //     vec![Name::Input(5), Name::Input(10)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000000e),
                // ),
                // (
                //     vec![Name::Input(10)],
                //     GoldilocksField::from_nonreduced_u64(0x6b0beecf82fdc083),
                // ),
                // (
                //     vec![Name::Input(0)],
                //     GoldilocksField::from_nonreduced_u64(0x2e77541f1de9851a),
                // ),
                // (
                //     vec![Name::Input(10), Name::Input(11)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000006),
                // ),
                // (
                //     vec![Name::Input(8)],
                //     GoldilocksField::from_nonreduced_u64(0x173baa0f8ef4c28d),
                // ),
                // (
                //     vec![Name::Input(3), Name::Input(3)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000024),
                // ),
                // (
                //     vec![Name::Input(8), Name::Input(8)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000019),
                // ),
                // (
                //     vec![Name::Input(8), Name::Input(11)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000001e),
                // ),
                // (
                //     vec![Name::Input(1), Name::Input(2)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000038),
                // ),
                // (
                //     vec![Name::Input(5), Name::Input(7)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000002a),
                // ),
                // (
                //     vec![Name::Input(6), Name::Input(8)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000000a),
                // ),
                // (
                //     vec![Name::Input(6), Name::Input(6)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000001),
                // ),
                // (
                //     vec![Name::Input(3), Name::Input(8)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000003c),
                // ),
                // (
                //     vec![Name::Input(3), Name::Input(9)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000054),
                // ),
                // (
                //     vec![Name::Input(0), Name::Input(4)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000064),
                // ),
                // (
                //     vec![Name::Input(11), Name::Input(11)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000009),
                // ),
                // (
                //     vec![Name::Input(0), Name::Input(6)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000014),
                // ),
                // (
                //     vec![Name::Input(1), Name::Input(11)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000054),
                // ),
                // (
                //     vec![Name::Input(3), Name::Input(10)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000000c),
                // ),
                // (
                //     vec![Name::Input(7), Name::Input(11)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000012),
                // ),
                // (
                //     vec![Name::Input(0), Name::Input(10)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000014),
                // ),
                // (
                //     vec![Name::Input(0), Name::Input(7)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000003c),
                // ),
                // (
                //     vec![Name::Input(6)],
                //     GoldilocksField::from_nonreduced_u64(0x6b0beecf82fdc083),
                // ),
                // (
                //     vec![Name::Input(4), Name::Input(7)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000001e),
                // ),
                // (
                //     vec![Name::Input(2), Name::Input(3)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000018),
                // ),
                // (
                //     vec![Name::Input(4), Name::Input(8)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000032),
                // ),
                // (
                //     vec![Name::Input(1), Name::Input(1)],
                //     GoldilocksField::from_nonreduced_u64(0x00000000000000c4),
                // ),
                // (
                //     vec![Name::Input(8), Name::Input(9)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000046),
                // ),
                // (
                //     vec![Name::Input(9), Name::Input(10)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000000e),
                // ),
                // (
                //     vec![Name::Input(2), Name::Input(6)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000004),
                // ),
                // (
                //     vec![Name::Input(4), Name::Input(5)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000046),
                // ),
                // (
                //     vec![Name::Input(1), Name::Input(9)],
                //     GoldilocksField::from_nonreduced_u64(0x00000000000000c4),
                // ),
                // (
                //     vec![Name::Input(4)],
                //     GoldilocksField::from_nonreduced_u64(0x173baa0f8ef4c28d),
                // ),
                // (
                //     vec![Name::Input(3), Name::Input(5)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000054),
                // ),
                // (
                //     vec![Name::Input(7), Name::Input(9)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000002a),
                // ),
                // (
                //     vec![Name::Input(7)],
                //     GoldilocksField::from_nonreduced_u64(0x4123cc6f88f94188),
                // ),
                // (
                //     vec![Name::Input(1), Name::Input(10)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000001c),
                // ),
                // (
                //     vec![Name::Input(0), Name::Input(9)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000008c),
                // ),
                // (
                //     vec![Name::Input(0), Name::Input(5)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000008c),
                // ),
                // (
                //     vec![Name::Input(0), Name::Input(11)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000003c),
                // ),
                // (
                //     vec![Name::Input(4), Name::Input(4)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000019),
                // ),
                // (
                //     vec![Name::Input(1), Name::Input(5)],
                //     GoldilocksField::from_nonreduced_u64(0x00000000000000c4),
                // ),
                // (
                //     vec![Name::Input(7), Name::Input(8)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000001e),
                // ),
                // (
                //     vec![Name::Input(2), Name::Input(11)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000000c),
                // ),
                // (
                //     vec![Name::Input(1), Name::Input(7)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000054),
                // ),
                // (
                //     vec![Name::Input(7), Name::Input(10)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000006),
                // ),
                // (
                //     vec![Name::Input(0), Name::Input(1)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000118),
                // ),
                // (
                //     vec![Name::Input(2), Name::Input(4)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000014),
                // ),
                // (
                //     vec![Name::Input(0), Name::Input(2)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000028),
                // ),
                // (
                //     vec![Name::Input(3), Name::Input(6)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000000c),
                // ),
                // (
                //     vec![Name::Input(2), Name::Input(9)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000001c),
                // ),
                // (
                //     vec![Name::Input(1), Name::Input(4)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000008c),
                // ),
                // (
                //     vec![Name::Input(2)],
                //     GoldilocksField::from_nonreduced_u64(0xd617dd9f05fb8106),
                // ),
                // (
                //     vec![Name::Input(3), Name::Input(7)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000024),
                // ),
                // (
                //     vec![Name::Input(2), Name::Input(5)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000001c),
                // ),
                // (
                //     vec![Name::Input(6), Name::Input(9)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000000e),
                // ),
                // (
                //     vec![Name::Input(2), Name::Input(2)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000004),
                // ),
                // (
                //     vec![Name::Input(5), Name::Input(11)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000002a),
                // ),
                // (
                //     vec![Name::Input(4), Name::Input(9)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000046),
                // ),
                // (
                //     vec![Name::Input(2), Name::Input(8)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000014),
                // ),
                // (
                //     vec![Name::Input(5), Name::Input(5)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000031),
                // ),
                // (
                //     vec![Name::Input(9), Name::Input(11)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000002a),
                // ),
                // (
                //     vec![Name::Input(0), Name::Input(8)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000064),
                // ),
                // (
                //     vec![Name::Input(6), Name::Input(11)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000006),
                // ),
                // (
                //     vec![Name::Input(5), Name::Input(9)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000062),
                // ),
                // (
                //     vec![Name::Input(3), Name::Input(4)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000003c),
                // ),
                // (
                //     vec![Name::Input(3)],
                //     GoldilocksField::from_nonreduced_u64(0x824798df11f28310),
                // ),
                // (
                //     vec![Name::Input(0), Name::Input(0)],
                //     GoldilocksField::from_nonreduced_u64(0x0000000000000064),
                // ),
                // (
                //     vec![Name::Input(5)],
                //     GoldilocksField::from_nonreduced_u64(0xed5387ae94f04393),
                // ),
                // (
                //     vec![Name::Input(11)],
                //     GoldilocksField::from_nonreduced_u64(0x4123cc6f88f94188),
                // ),
                // (
                //     vec![Name::Input(4), Name::Input(10)],
                //     GoldilocksField::from_nonreduced_u64(0x000000000000000a),
                // ),
                (
                    vec![Name::Input(4), Name::Input(11)],
                    GoldilocksField::from_nonreduced_u64(0x000000000000001e),
                ),
            ],
            c: GoldilocksField::from_nonreduced_u64(0xf52d5ed885b4fa17),
        };

        let nf3: NF<GoldilocksField> = NF_ {
            s: vec![
                (vec![Name::Wire(168)], GoldilocksField::ZERO),
                (vec![Name::Wire(156)], GoldilocksField::ZERO),
                (vec![Name::Wire(168), Name::Wire(156)], GoldilocksField::ONE),
            ],
            c: GoldilocksField::ZERO,
        };

        let mut witness = HashMap::new();
        (0..12).for_each(|i| {
            witness.insert(Name::Input(i), GoldilocksField::ZERO);
        });

        let mut atomic_map: HashMap<Name, NF<GoldilocksField>> = HashMap::new();

        atomic_map.insert(Name::Wire(156), nf1.clone());
        atomic_map.insert(Name::Wire(168), nf2.clone());

        let v156 = eval_nf(&nf1, &witness);
        witness.insert(Name::Wire(156), v156);
        let v168 = eval_nf(&nf2, &witness);
        witness.insert(Name::Wire(168), v168);

        let v_before = eval_nf(&nf3, &witness);

        if let Some(inlined) = inline_nf(Name::Wire(169), &nf3, &atomic_map, 7) {
            let v = eval_nf(&inlined, &witness);
            println!("inlined: {:?}", inlined);
            assert!(v_before == v, "{:?} not equal to {:?}", v_before, v)
        }
    }
}
