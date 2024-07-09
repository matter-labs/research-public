use base::expr::{Config, Trace};
use boojum::field::goldilocks::GoldilocksField;
use builder::vanilla::{PointS, SValue, Valuable};

fn main() {
    let mut e = builder::vanilla::TLEnv::new();
    let v = SValue::input(&mut e);
    let _b = bool::input(&mut e);
    let mut e = e.seal_inputs();
    let l = e.c::<SValue>(GoldilocksField(3));
    let r = e.c::<SValue>(GoldilocksField(5));

    let o = e.add(l, r);
    let _o2 = e.add(v, o);
    let z = e.c::<SValue>(GoldilocksField(0));
    e.eq0(z);

    let x1 = e.c::<SValue>(GoldilocksField(1));
    let y1 = e.c::<SValue>(GoldilocksField(2));
    let _ = e.c::<bool>(false);
    let p1 = (x1, y1);
    let p2 = e.c::<PointS<GoldilocksField>>((GoldilocksField(3), GoldilocksField(4)));
    let _z = e.add_point(p1, p2);

    let c = e.get_circuit();

    let mut t = Trace::empty();
    let config = Config::default();
    t.push(GoldilocksField(7));
    t.push(GoldilocksField(1));
    let valid = c.gen_trace(&config, &mut t);
    assert!(valid);
    println!("{:?}", t);

    // assert!(t.0 == [7, 3, 5, 8, 15, 0, 1, 2, 0, 3, 4, 4, 6]);

    assert!(c.sat(&config, &t));
    let table = c.gen_table(&config);
    let s = table.to_string();
    println!("{s}");
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use base::{
        circuit::Circuit,
        expr::{Config, CV},
        field::Field,
        optimizer::inline_atomics,
    };

    use super::*;

    type F = GoldilocksField;

    fn trace_from_inputs<F: Field>(inputs: &[F]) -> Trace<F> {
        let mut t = Trace::empty();
        inputs.iter().fold(0, |acc, v| {
            t.push(*v);
            acc + 1
        });
        t
    }

    fn to_f(x: i64) -> F {
        let av: u64 = x.abs().try_into().unwrap();
        let av_f = <GoldilocksField as boojum::field::Field>::from_u64_with_reduction(av);
        let neg = if x < 0 { F::MONE } else { F::ONE };
        F::mul(neg, av_f)
    }

    fn print_cs_info<F: Field + 'static>(cs: &Vec<Box<dyn CV<F>>>) {
        let mut count: HashMap<String, usize> = HashMap::new();
        println!("CV size: {}", cs.len());
        cs.iter().for_each(|cs| {
            let pcount = count.get(&cs.id()).unwrap_or(&0);
            count.insert(cs.id(), pcount + 1);
        });
        count
            .iter()
            .for_each(|(id, c)| println!("Gate {}: {} instances", id, c))
    }

    // Test helpers
    fn sat_with_config<F: Field>(
        c: &Circuit<F>,
        inputs: &[F],
        size: usize,
        size_optimized: usize,
        config: &Config,
        skip_sat: bool,
    ) {
        let mut t_before = trace_from_inputs(inputs);
        println!("Circ size: {}", c.size());
        // println!("Circ: {}", c);
        let b = c.gen_trace(config, &mut t_before);

        assert!(b, "sat no trace");
        // assert!(*trace == rest, "sat wrong trace");
        let (cs, mut ctxt_before) = c.gen_cs(config);
        // println!("{:?}", cs);
        // println!("Trace {:?}", t_before);
        print_cs_info(&cs);
        assert!(cs.len() == size, "sat wrong size");
        if !skip_sat {
            assert!(c.sat(config, &t_before), "sat unsat")
        }

        let c = c.optimize(config);
        println!("optimized Circ size: {}", c.size());
        // println!("Circ: {}", c);
        let names = c.names();

        let mut t = trace_from_inputs(inputs);
        let b = c.gen_trace(config, &mut t);

        assert!(b, "optimized sat no trace");
        // assert!(*trace == rest, "sat wrong trace");
        let (cs, mut ctxt) = c.gen_cs(config);

        // for name in names {
        //     let v_b = t_before.0.get(ctxt_before.get(name)).unwrap();
        //     let v = t.0.get(ctxt.get(name)).unwrap();
        //     assert!(
        //         v_b == v,
        //         "Values for name {:?} differs {:?}  {:?}",
        //         name,
        //         v_b,
        //         v
        //     )
        // }
        // println!("{:?}", cs);
        // println!("Trace {:?}", t);
        print_cs_info(&cs);
        // We give it a 5% margin for some non-deterministic optimization
        let upper_bound = size_optimized + (size_optimized / 5);
        assert!(cs.len() <= upper_bound, "optimized sat wrong size");
        if !skip_sat {
            assert!(c.sat(config, &t), "optimized sat unsat")
        }
    }

    fn sat(c: &Circuit<F>, inputs: &[F], size: usize, size_optimized: usize) {
        sat_with_config(c, inputs, size, size_optimized, &Config::default(), false)
    }

    fn unsat(c: &Circuit<F>, inputs: &[F]) {
        println!("{}", c);
        let mut t = trace_from_inputs(inputs);
        let config = Config::default();
        let b = c.gen_trace(&config, &mut t);
        if b {
            assert!(!c.sat(&config, &t), "unsat sat")
        }
    }

    #[test]
    fn test_c() {
        let c = {
            let e = builder::vanilla::TLEnv::new();
            let mut e = e.seal_inputs();
            let _l = e.c::<SValue>(GoldilocksField(3));
            e.get_circuit()
        };
        let inputs = vec![];
        // let trace = Trace(vec![3]);
        sat(&c, &inputs, 1, 1)
    }

    #[test]
    fn test_add_constant() {
        let c = {
            let e = builder::vanilla::TLEnv::new();
            let mut e = e.seal_inputs();
            let l = e.c::<SValue>(GoldilocksField(3));
            let r = e.c::<SValue>(GoldilocksField(5));
            let _o = e.add(l, r);
            e.get_circuit()
        };
        let inputs = vec![];
        // let trace = Trace(vec![3, 5, 8]);
        sat(&c, &inputs, 3, 1)
    }

    #[test]
    fn test_add_input() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let v = SValue::input(&mut e);
            let mut e = e.seal_inputs();
            let r = e.c::<SValue>(GoldilocksField(5));
            let _o = e.add(v, r);
            e.get_circuit()
        };
        let inputs = vec![GoldilocksField(3)];
        // let trace = Trace(vec![5, 8]);
        sat(&c, &inputs, 2, 1)
    }

    #[test]
    fn test_nested_add() {
        let c = {
            let e = builder::vanilla::TLEnv::new();
            let mut e = e.seal_inputs();
            let l = e.c::<SValue>(GoldilocksField(3));
            let r = e.c::<SValue>(GoldilocksField(5));
            let o = e.add(l, r);
            let t = e.c::<SValue>(GoldilocksField(7));
            let _o2 = e.add(o, t);
            e.get_circuit()
        };
        let inputs = vec![];
        // let trace = Trace(vec![3, 5, 8, 7, 15]);
        sat(&c, &inputs, 5, 1)
    }

    #[test]
    fn test_eq0() {
        let c = {
            let e = builder::vanilla::TLEnv::new();
            let mut e = e.seal_inputs();
            let l = e.c::<SValue>(GoldilocksField(0));
            e.eq0(l);
            e.get_circuit()
        };
        let inputs = vec![];
        // let trace = Trace(vec![0]);
        sat(&c, &inputs, 2, 2)
    }

    #[test]
    fn test_input_eq0() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let l = SValue::input(&mut e);
            let mut e = e.seal_inputs();
            e.eq0(l);
            e.get_circuit()
        };
        let inputs = vec![to_f(0)];
        // let trace = Trace(vec![]);
        sat(&c, &inputs, 1, 1)
    }

    #[test]
    fn test_adds_eq0() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            // let l = SValue::input(&mut e);
            let v = SValue::input(&mut e);
            let mut e = e.seal_inputs();
            let l = e.c::<SValue>(to_f(3));
            let r = e.c::<SValue>(to_f(5));
            let o = e.add(l, r);
            let o2 = e.add(v, o);
            e.eq0(o2);
            e.get_circuit()
        };
        let inputs = vec![to_f(-8)];
        // let trace = Trace(vec![3, 5, 8, 15, 0]);
        sat(&c, &inputs, 5, 2)
    }

    #[test]
    fn test_boolcheck_on_input() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            // Should add a boolcheck
            let _v = bool::input(&mut e);
            let e = e.seal_inputs();
            e.get_circuit()
        };
        let inputs = vec![to_f(0)];
        // let trace = Trace(vec![]);
        sat(&c, &inputs, 1, 1);

        let inputs = vec![to_f(1)];
        sat(&c, &inputs, 1, 1);

        let inputs = vec![to_f(2)];
        unsat(&c, &inputs);
    }

    #[test]
    fn test_arith_boolcheck_on_input() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            // Shouldn't add a boolcheck
            let v = SValue::input(&mut e);
            let mut e = e.seal_inputs();
            e.assert_bool_arith(v);
            e.get_circuit()
        };
        let inputs = vec![to_f(0)];
        // let trace = Trace(vec![0]);
        sat(&c, &inputs, 2, 2);

        let inputs = vec![to_f(1)];
        sat(&c, &inputs, 2, 2);

        let inputs = vec![to_f(2)];
        unsat(&c, &inputs);
    }

    #[test]
    fn test_input_inversion() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let v = SValue::input(&mut e);
            let mut e = e.seal_inputs();
            let _ = e.inv(v);
            e.get_circuit()
        };
        let inputs = vec![to_f(0)];
        unsat(&c, &inputs);

        let inputs = vec![to_f(1)];
        // let trace = Trace(vec![1]);
        sat(&c, &inputs, 1, 1);
    }

    #[test]
    fn test_is_zero() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let v = SValue::input(&mut e);
            let mut e = e.seal_inputs();
            let _ = e.is_zero(v);
            e.get_circuit()
        };
        let inputs = vec![to_f(0)];
        // let trace = Trace(vec![0, 1]);
        sat(&c, &inputs, 2, 2);

        let inputs = vec![to_f(1)];
        // let trace = Trace(vec![1, 0]);
        sat(&c, &inputs, 2, 2);
    }

    #[test]
    fn test_assert_not_zero() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let v = SValue::input(&mut e);
            let mut e = e.seal_inputs();
            e.assert_not_zero(v);
            e.get_circuit()
        };
        let inputs = vec![to_f(0)];
        unsat(&c, &inputs);

        let inputs = vec![to_f(1)];
        // let trace = Trace(vec![1]);
        sat(&c, &inputs, 1, 1);
    }

    #[test]
    fn test_assert_not_zero_naive() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let v = SValue::input(&mut e);
            let mut e = e.seal_inputs();
            e.assert_not_zero_naive(v);
            e.get_circuit()
        };
        let inputs = vec![to_f(0)];
        unsat(&c, &inputs);

        let inputs = vec![to_f(1)];
        // let trace = Trace(vec![1, 0]);
        sat(&c, &inputs, 3, 3);
    }

    #[test]
    fn test_ifthenelse() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let b = bool::input(&mut e);
            let mut e = e.seal_inputs();
            let l = e.c::<SValue>(to_f(3));
            let r = e.c::<SValue>(to_f(5));
            let x = e.ifthenelse::<SValue>(b, l, r);
            let _ = e.add(x, x);
            e.get_circuit()
        };
        let inputs = vec![to_f(0)];
        // let trace = Trace(vec![3, 5, 3, 5, 10]);
        sat(&c, &inputs, 5, 5);

        let inputs = vec![to_f(1)];
        // let trace = Trace(vec![3, 5, 5, 3, 6]);
        sat(&c, &inputs, 5, 5);
    }

    #[test]
    fn test_xor() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let l = bool::input(&mut e);
            let r = bool::input(&mut e);
            let mut e = e.seal_inputs();
            let _ = e.xor(l, r);
            e.get_circuit()
        };
        let size = 9;
        let size_compressed = 5;

        let inputs = vec![to_f(0), to_f(1)];
        // sat(&c, &inputs, size, size_compressed);
        let config = Config {
            use_fma: true,
            use_lc: false,
        };
        sat_with_config(&c, &inputs, size, size_compressed, &config, false);

        // let inputs = vec![to_f(1), to_f(0)];
        // sat(&c, &inputs, size, size_compressed);

        // let inputs = vec![to_f(1), to_f(1)];
        // sat(&c, &inputs, size, size_compressed);

        // let inputs = vec![to_f(0), to_f(0)];
        // sat(&c, &inputs, size, size_compressed);
    }

    #[test]
    fn test_nor() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let l = bool::input(&mut e);
            let r = bool::input(&mut e);
            let mut e = e.seal_inputs();
            let _ = e.nor(l, r);
            e.get_circuit()
        };
        let size = 4;
        let size_compressed = 3;

        let inputs = vec![to_f(0), to_f(1)];
        sat(&c, &inputs, size, size_compressed);
    }

    #[test]
    fn test_lc() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let x1 = SValue::input(&mut e);
            let x2 = SValue::input(&mut e);
            let x3 = SValue::input(&mut e);
            let x4 = SValue::input(&mut e);
            let x5 = SValue::input(&mut e);

            let mut e = e.seal_inputs();
            let _ = e.linear_combination(vec![
                (x1, to_f(2)),
                (x2, to_f(3)),
                (x3, to_f(4)),
                (x4, to_f(5)),
                (x5, to_f(6)),
            ]);
            e.get_circuit()
        };
        let size = 6;
        let size_compressed = 2;

        let inputs: Vec<F> = vec![2, 3, 4, 5, 6].into_iter().map(to_f).collect();
        let config = Config {
            use_lc: true,
            use_fma: false,
        };
        sat_with_config(&c, &inputs, size, size_compressed, &config, false);
    }

    #[test]
    fn test_paper() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let s = SValue::input(&mut e);
            let b = bool::input(&mut e);
            let mut e = e.seal_inputs();
            let y = e.is_zero(s);
            let _ = e.xor(b, y);
            e.get_circuit()
        };
        let size = 8;
        let size_compressed = 4;

        let inputs = vec![to_f(0), to_f(1)];
        sat(&c, &inputs, size, size_compressed);
    }

    use boojum::{
        config,
        field::{goldilocks::GoldilocksField, U64RawRepresentable},
    };

    type PoseidonState = [GoldilocksField; 12];
    use builder::{
        poseidon2::compute_round_function,
        sha256::sha256,
        vanilla::{range_check_36_bits_using_sha256_tables, range_check_u8, split_36_bits},
    };

    #[test]
    fn test_poseidon2() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let input = PoseidonState::input(&mut e);
            let expected = PoseidonState::input(&mut e);
            let mut e = e.seal_inputs();
            let r = compute_round_function(&mut e, input, false);
            r.iter()
                .zip(expected.iter())
                .for_each(|(x, y)| e.assert_eq(*x, *y));
            e.get_circuit()
        };
        let size = 2125;
        // Boojum is 1163
        // This is without the added assert_eq
        // let size_compressed = 1054;
        let size_compressed = 1066;

        let mut inputs = vec![GoldilocksField(0); 12];

        let outputs = vec![
            GoldilocksField::from_raw_u64_unchecked(0x78e86c27e831c353),
            GoldilocksField::from_raw_u64_unchecked(0xc4c13a505ffd93b8),
            GoldilocksField::from_raw_u64_unchecked(0xc3a6d7d7f7971adc),
            GoldilocksField::from_raw_u64_unchecked(0xf6ff8f53ab94d8c7),
            GoldilocksField::from_raw_u64_unchecked(0x303ac75657e46867),
            GoldilocksField::from_raw_u64_unchecked(0x46ba4a78ec511686),
            GoldilocksField::from_raw_u64_unchecked(0x3c3d14c26ded4c8a),
            GoldilocksField::from_raw_u64_unchecked(0x94e9facb98358b24),
            GoldilocksField::from_raw_u64_unchecked(0x0bc0f0927b77ed81),
            GoldilocksField::from_raw_u64_unchecked(0x539d02a84fe77b34),
            GoldilocksField::from_raw_u64_unchecked(0x08f782d5fd75ff38),
            GoldilocksField::from_raw_u64_unchecked(0x292838440f8a0e5e),
        ];
        inputs.extend(outputs);
        let config = Config {
            use_fma: true,
            use_lc: true,
        };
        sat_with_config(&c, &inputs, size, size_compressed, &config, false);
    }

    #[test]
    fn test_flatten_poseidon2() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let input = PoseidonState::input(&mut e);
            let expected = PoseidonState::input(&mut e);
            let mut e = e.seal_inputs();
            let r = compute_round_function(&mut e, input, true);
            println!("r: {:?}", r);
            r.iter()
                .zip(expected.iter())
                .for_each(|(x, y)| e.assert_eq(*x, *y));
            e.get_circuit()
        };

        let size = 13;
        let size_compressed = 13;

        let mut inputs = vec![GoldilocksField(0); 12];
        let outputs = vec![
            GoldilocksField::from_raw_u64_unchecked(0x78e86c27e831c353),
            GoldilocksField::from_raw_u64_unchecked(0xc4c13a505ffd93b8),
            GoldilocksField::from_raw_u64_unchecked(0xc3a6d7d7f7971adc),
            GoldilocksField::from_raw_u64_unchecked(0xf6ff8f53ab94d8c7),
            GoldilocksField::from_raw_u64_unchecked(0x303ac75657e46867),
            GoldilocksField::from_raw_u64_unchecked(0x46ba4a78ec511686),
            GoldilocksField::from_raw_u64_unchecked(0x3c3d14c26ded4c8a),
            GoldilocksField::from_raw_u64_unchecked(0x94e9facb98358b24),
            GoldilocksField::from_raw_u64_unchecked(0x0bc0f0927b77ed81),
            GoldilocksField::from_raw_u64_unchecked(0x539d02a84fe77b34),
            GoldilocksField::from_raw_u64_unchecked(0x08f782d5fd75ff38),
            GoldilocksField::from_raw_u64_unchecked(0x292838440f8a0e5e),
        ];
        inputs.extend(outputs);

        let config = Config {
            use_fma: false,
            use_lc: true,
        };
        sat_with_config(&c, &inputs, size, size_compressed, &config, false);
    }

    #[test]
    fn test_rangechecks() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let input = SValue::input(&mut e);
            let mut e = e.seal_inputs();
            let _ = range_check_36_bits_using_sha256_tables(&mut e, input);
            let _ = split_36_bits(&mut e, input);
            e.get_circuit()
        };
        let size = 16;
        let size_compressed = 9;

        let inputs = vec![GoldilocksField(2); 1];
        let config = Config {
            use_fma: true,
            use_lc: true,
        };
        sat_with_config(&c, &inputs, size, size_compressed, &config, true);
    }

    type SHAInput = [u8; 42];

    #[test]
    fn test_sha256() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let input = SHAInput::input(&mut e);
            let mut e = e.seal_inputs();
            let _ = sha256(&mut e, &input);
            e.get_circuit()
        };
        let size = 14152;
        let size_compressed = 7928;

        let inputs = vec![GoldilocksField(0); 42];
        let config = Config {
            use_fma: true,
            use_lc: true,
        };
        sat_with_config(&c, &inputs, size, size_compressed, &config, true);
    }
}
