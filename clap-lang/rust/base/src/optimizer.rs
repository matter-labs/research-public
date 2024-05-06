use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;

use crate::circuit::Circuit;
use crate::cs_arith::GenericArith;
use crate::cs_boolcheck::BoolCheck;
use crate::cs_linear_combination::LinearCombination;
use crate::expr::{Config, Gate, Name};
use crate::field::*;
use crate::gate_iszero::IsZero;

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
                    .filter(|(n, q)| !n.unused())
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
                lterms.insert(target.r, target.qr);
                (drop_l, drop_r)
            } else if lterms_r.len() < N {
                // inline r
                let drop_l = None;
                lterms.drain();
                lterms_r.into_iter().for_each(|(name, f)| {
                    lterms.insert(name, f);
                });
                lterms.insert(target.l, target.ql);
                (drop_l, drop_r)
            } else {
                // Too bad
                (drop_l, drop_r)
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

pub fn optimize<F: Field + 'static, const N: usize>(
    circ: &Circuit<F>,
    config: &Config,
) -> Circuit<F> {
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
                let optimized: Box<dyn Gate<F>> = Box::new(optimized);
                self::add_shape_to_map::<F, N>(&mut shapes, &bool_wires, optimized.clone());
                Circuit::Gate(optimized)
            } else if let Some(optimized) =
                inline_lc::<F, N>(ga, &shapes, &bool_wires, &mut refcount, config)
            {
                self::add_shape_to_map::<F, N>(&mut shapes, &bool_wires, optimized.clone());
                Circuit::Gate(optimized)
            } else if !config.use_fma {
                if let Some(Shape::LinearTerm { c1, x, c2, ga: cga }) = shapes.get(&ga.l) {
                    // LinearTerm on l
                    decrease_ref(&mut refcount, ga.l);
                    let ql = ga.ql * *c1;
                    let l = *x;
                    let qr = ga.qr + ga.qm * *c2;
                    let qm = ga.qm * *c1;
                    let qc = ga.qc + ga.ql * *c2;
                    let bc = GenericArith {
                        ql,
                        l,
                        qr,
                        qm,
                        qc,
                        ..ga.clone()
                    };
                    let optimized: Box<dyn Gate<F>> = Box::new(bc);
                    self::add_shape_to_map::<F, N>(&mut shapes, &bool_wires, optimized.clone());
                    Circuit::Gate(optimized)
                } else if let Some(Shape::LinearTerm { c1, x, c2, ga: cga }) = shapes.get(&ga.r) {
                    // LinearTerm on r
                    decrease_ref(&mut refcount, ga.r);
                    let ql = ga.ql + ga.qm * *c2;
                    let qr = ga.qr * *c1;
                    let r = *x;
                    let qm = ga.qm * *c1;
                    let qc = ga.qc + ga.qr * *c2;
                    let bc = GenericArith {
                        ql,
                        r,
                        qr,
                        qm,
                        qc,
                        ..ga.clone()
                    };
                    let optimized: Box<dyn Gate<F>> = Box::new(bc);
                    self::add_shape_to_map::<F, N>(&mut shapes, &bool_wires, optimized.clone());
                    Circuit::Gate(optimized)
                } else {
                    Circuit::Gate(boxed.clone())
                }
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

#[cfg(test)]
mod test {
    use super::*;

    fn seq_chain<F: Field>(circuits: Vec<Circuit<F>>) -> Circuit<F> {
        circuits
            .into_iter()
            .fold(Circuit::Nil(PhantomData), |acc, c| {
                Circuit::Seq(Box::new(acc), Box::new(c))
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
        let optimized = optimize::<Fi64, 4>(&c, &config);
        println!("After {}", optimized)
    }
}
