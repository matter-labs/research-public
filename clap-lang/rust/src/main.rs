use base::expr::{Config, Trace};
use base::field::Fi64;
use builder::vanilla::{PointS, SValue, Valuable};

fn main() {
    let mut e = builder::vanilla::TLEnv::new();
    let v = SValue::input(&mut e);
    let _b = bool::input(&mut e);
    let mut e = e.seal_inputs();
    let l = e.c::<SValue>(Fi64(3_i64));
    let r = e.c::<SValue>(Fi64(5_i64));

    let o = e.add(l, r);
    let _o2 = e.add(v, o);
    let z = e.c::<SValue>(Fi64(0_i64));
    e.eq0(z);

    let x1 = e.c::<SValue>(Fi64(1_i64));
    let y1 = e.c::<SValue>(Fi64(2_i64));
    let _ = e.c::<bool>(false);
    let p1 = (x1, y1);
    let p2 = e.c::<PointS<Fi64>>((Fi64(3_i64), Fi64(4_i64)));
    let _z = e.add_point(p1, p2);

    let c = e.get_circuit();

    let mut t = Trace::empty();
    let config = Config::default();
    t.push(Fi64(7_i64));
    t.push(Fi64(1_i64));
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
        expr::{Config, Gate, CV},
        field::Field,
    };

    use super::*;

    type F = Fi64;

    fn trace_from_inputs(inputs: &[F]) -> Trace<F> {
        let mut t = Trace::empty();
        inputs.iter().fold(0, |acc, v| {
            t.push(*v);
            acc + 1
        });
        t
    }

    fn to_f(x: i64) -> F {
        Fi64(x)
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
    fn sat_with_config(
        c: &Circuit<F>,
        inputs: &[F],
        size: usize,
        size_optimized: usize,
        config: &Config,
        skip_sat: bool,
    ) {
        let mut t = trace_from_inputs(inputs);
        println!("Circ size: {}", c.size());
        let b = c.gen_trace(&config, &mut t);
        assert!(b, "sat no trace");
        // assert!(*trace == rest, "sat wrong trace");
        let cs = c.gen_cs(&config);
        print_cs_info(&cs);
        assert!(cs.len() == size, "sat wrong size");
        if !skip_sat {
            assert!(c.sat(&config, &t), "sat unsat")
        }

        let c = c.optimize(&config);
        println!("optimized Circ size: {}", c.size());

        let mut t = trace_from_inputs(inputs);
        let b = c.gen_trace(&config, &mut t);
        assert!(b, "optimized sat no trace");
        // assert!(*trace == rest, "sat wrong trace");
        let cs = c.gen_cs(&config);
        print_cs_info(&cs);
        assert!(cs.len() == size_optimized, "optimized sat wrong size");
        if !skip_sat {
            assert!(c.sat(&config, &t), "optimized sat unsat")
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
            let _l = e.c::<SValue>(Fi64(3_i64));
            e.get_circuit()
        };
        let inputs = vec![];
        // let trace = Trace(vec![3_i64]);
        sat(&c, &inputs, 1, 1)
    }

    #[test]
    fn test_add_constant() {
        let c = {
            let e = builder::vanilla::TLEnv::new();
            let mut e = e.seal_inputs();
            let l = e.c::<SValue>(Fi64(3_i64));
            let r = e.c::<SValue>(Fi64(5_i64));
            let _o = e.add(l, r);
            e.get_circuit()
        };
        let inputs = vec![];
        // let trace = Trace(vec![3_i64, 5_i64, 8_i64]);
        sat(&c, &inputs, 3, 1)
    }

    #[test]
    fn test_add_input() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let v = SValue::input(&mut e);
            let mut e = e.seal_inputs();
            let r = e.c::<SValue>(Fi64(5_i64));
            let _o = e.add(v, r);
            e.get_circuit()
        };
        let inputs = vec![Fi64(3_i64)];
        // let trace = Trace(vec![5_i64, 8_i64]);
        sat(&c, &inputs, 2, 1)
    }

    #[test]
    fn test_nested_add() {
        let c = {
            let e = builder::vanilla::TLEnv::new();
            let mut e = e.seal_inputs();
            let l = e.c::<SValue>(Fi64(3_i64));
            let r = e.c::<SValue>(Fi64(5_i64));
            let o = e.add(l, r);
            let t = e.c::<SValue>(Fi64(7_i64));
            let _o2 = e.add(o, t);
            e.get_circuit()
        };
        let inputs = vec![];
        // let trace = Trace(vec![3_i64, 5_i64, 8_i64, 7_i64, 15_i64]);
        sat(&c, &inputs, 5, 1)
    }

    #[test]
    fn test_eq0() {
        let c = {
            let e = builder::vanilla::TLEnv::new();
            let mut e = e.seal_inputs();
            let l = e.c::<SValue>(Fi64(0_i64));
            e.eq0(l);
            e.get_circuit()
        };
        let inputs = vec![];
        // let trace = Trace(vec![0_i64]);
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
        let inputs = vec![to_f(0_i64)];
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
            let l = e.c::<SValue>(to_f(3_i64));
            let r = e.c::<SValue>(to_f(5_i64));
            let o = e.add(l, r);
            let o2 = e.add(v, o);
            e.eq0(o2);
            e.get_circuit()
        };
        let inputs = vec![to_f(-8_i64)];
        // let trace = Trace(vec![3_i64, 5_i64, 8_i64, 15_i64, 0_i64]);
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
        let inputs = vec![to_f(0_i64)];
        // let trace = Trace(vec![]);
        sat(&c, &inputs, 1, 1);

        let inputs = vec![to_f(1_i64)];
        sat(&c, &inputs, 1, 1);

        let inputs = vec![to_f(2_i64)];
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
        let inputs = vec![to_f(0_i64)];
        // let trace = Trace(vec![0]);
        sat(&c, &inputs, 2, 2);

        let inputs = vec![to_f(1_i64)];
        sat(&c, &inputs, 2, 2);

        let inputs = vec![to_f(2_i64)];
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
        let inputs = vec![to_f(0_i64)];
        unsat(&c, &inputs);

        let inputs = vec![to_f(1_i64)];
        // let trace = Trace(vec![1_i64]);
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
        let inputs = vec![to_f(0_i64)];
        // let trace = Trace(vec![0_i64, 1]);
        sat(&c, &inputs, 2, 2);

        let inputs = vec![to_f(1_i64)];
        // let trace = Trace(vec![1_i64, 0]);
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
        let inputs = vec![to_f(0_i64)];
        unsat(&c, &inputs);

        let inputs = vec![to_f(1_i64)];
        // let trace = Trace(vec![1_i64]);
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
        let inputs = vec![to_f(0_i64)];
        unsat(&c, &inputs);

        let inputs = vec![to_f(1_i64)];
        // let trace = Trace(vec![1_i64, 0_i64]);
        sat(&c, &inputs, 3, 3);
    }

    #[test]
    fn test_ifthenelse() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let b = bool::input(&mut e);
            let mut e = e.seal_inputs();
            let l = e.c::<SValue>(to_f(3_i64));
            let r = e.c::<SValue>(to_f(5_i64));
            let x = e.ifthenelse::<SValue>(b, l, r);
            let _ = e.add(x, x);
            e.get_circuit()
        };
        let inputs = vec![to_f(0_i64)];
        // let trace = Trace(vec![3_i64, 5_i64, 3_i64, 5_i64, 10_i64]);
        sat(&c, &inputs, 5, 5);

        let inputs = vec![to_f(1_i64)];
        // let trace = Trace(vec![3_i64, 5_i64, 5_i64, 3_i64, 6_i64]);
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
        let size = 7;
        let size_compressed = 3;

        let inputs = vec![to_f(0_i64), to_f(1_i64)];
        sat(&c, &inputs, size, size_compressed);

        let inputs = vec![to_f(1_i64), to_f(0_i64)];
        sat(&c, &inputs, size, size_compressed);

        let inputs = vec![to_f(1_i64), to_f(1_i64)];
        sat(&c, &inputs, size, size_compressed);

        let inputs = vec![to_f(0_i64), to_f(0_i64)];
        sat(&c, &inputs, size, size_compressed);
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

        let inputs = vec![to_f(0_i64), to_f(1_i64)];
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

        let inputs: Vec<F> = vec![2_i64, 3_i64, 4_i64, 5_i64, 6_i64]
            .into_iter()
            .map(to_f)
            .collect();
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

    type State = [Fi64; 12];
    use builder::poseidon2::compute_round_function;

    #[test]
    fn test_poseidon2() {
        let c = {
            let mut e = builder::vanilla::TLEnv::new();
            let input = State::input(&mut e);
            let mut e = e.seal_inputs();
            let _ = compute_round_function(&mut e, input);
            // let _ = compute_round_function(&mut e, input);
            e.get_circuit()
        };
        let size = 1875;
        // Boojum is 1163
        let size_compressed = 1054;

        let inputs = vec![to_f(0); 12];
        let config = Config {
            use_fma: true,
            use_lc: true,
        };
        sat_with_config(&c, &inputs, size, size_compressed, &config, true);
    }
}
