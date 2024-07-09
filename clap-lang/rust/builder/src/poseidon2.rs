use std::marker::PhantomData;

use crate::poseidon2_params::*;
use crate::vanilla;
use base::expr::Name;
use base::field::Field;
use boojum::field::goldilocks::GoldilocksField;
use vanilla::*;

type F = GoldilocksField;

pub type State = [Repr<F, SValue>; 12];

const NUM_FULL_ROUNDS: usize = NUM_FULL_ROUNDS_TOTAL;

pub fn compute_round_function(cs: &mut Env<F>, input: State, flatten: bool) -> State {
    // Temporarily collect the circuit in isolation, in case we want
    // to flatten it
    let mut tmp_cs = cs.clone();
    tmp_cs.c = base::circuit::Circuit::Nil(PhantomData);

    let mut state = input;
    let mut round_counter = 0;

    // first external MDS
    mul_by_external_matrix(&mut tmp_cs, &mut state);

    for _ in 0..NUM_FULL_ROUNDS / 2 {
        full_round(&mut tmp_cs, &mut state, &mut round_counter);
    }

    round_counter -= NUM_FULL_ROUNDS / 2;
    for _ in 0..NUM_PARTIAL_ROUNDS {
        partial_round(&mut tmp_cs, &mut state, &mut round_counter);
    }

    round_counter -= NUM_PARTIAL_ROUNDS;
    round_counter += NUM_FULL_ROUNDS / 2;
    for _ in 0..NUM_FULL_ROUNDS / 2 {
        full_round(&mut tmp_cs, &mut state, &mut round_counter);
    }

    if flatten {
        let atomics = base::optimizer::inline_atomics(tmp_cs.c, state.map(|s| s.into()).to_vec());
        poseidon2_flattened(cs, input, state, atomics)
    } else {
        cs.sync_env(tmp_cs)
    }

    state
}

fn reduce_terms(cs: &mut Env<F>, coeffs: [F; 3], vars: [SVar; 3]) -> SVar {
    let terms: Vec<(SVar, F)> = vars.into_iter().zip(coeffs).collect();
    cs.linear_combination(terms)
}

fn mul_by_external_matrix(cs: &mut Env<F>, state: &mut State) {
    // compute block circuilant matrix block by block
    let mut tmp: [SVar; 12] = [DUMMY_SVAR; 12];
    // multiplication of 4-element words
    for (dst, src) in tmp.array_chunks_mut::<4>().zip(state.array_chunks::<4>()) {
        for (dst, coeffs) in dst.iter_mut().zip(EXTERNAL_MDS_MATRIX_BLOCK.iter()) {
            let v: Vec<(SVar, F)> = (*src).into_iter().zip(*coeffs).collect();
            *dst = cs.linear_combination(v.clone());
        }
    }

    let [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] = tmp;

    state[0] = reduce_terms(cs, [F::TWO, F::ONE, F::ONE], [x0, x4, x8]);
    state[1] = reduce_terms(cs, [F::TWO, F::ONE, F::ONE], [x1, x5, x9]);
    state[2] = reduce_terms(cs, [F::TWO, F::ONE, F::ONE], [x2, x6, x10]);
    state[3] = reduce_terms(cs, [F::TWO, F::ONE, F::ONE], [x3, x7, x11]);

    state[4] = reduce_terms(cs, [F::TWO, F::ONE, F::ONE], [x4, x0, x8]);
    state[5] = reduce_terms(cs, [F::TWO, F::ONE, F::ONE], [x5, x1, x9]);
    state[6] = reduce_terms(cs, [F::TWO, F::ONE, F::ONE], [x6, x2, x10]);
    state[7] = reduce_terms(cs, [F::TWO, F::ONE, F::ONE], [x7, x3, x11]);

    state[8] = reduce_terms(cs, [F::TWO, F::ONE, F::ONE], [x8, x0, x4]);
    state[9] = reduce_terms(cs, [F::TWO, F::ONE, F::ONE], [x9, x1, x5]);
    state[10] = reduce_terms(cs, [F::TWO, F::ONE, F::ONE], [x10, x2, x6]);
    state[11] = reduce_terms(cs, [F::TWO, F::ONE, F::ONE], [x11, x3, x7]);
}

fn mul_by_inner_matrix(cs: &mut Env<F>, state: &mut State) {
    // make full linear combination
    let input: Vec<_> = state
        .iter()
        .copied()
        .zip(std::iter::repeat(F::ONE))
        .collect();

    let full_lc = cs.linear_combination(input);

    // now FMA with every diagonal term

    for (dst, coeff) in state
        .iter_mut()
        .zip(INNER_ROUNDS_MATRIX_DIAGONAL_ELEMENTS_MINUS_ONE.iter())
    {
        *dst = cs.add_with_coeff(full_lc, *dst, *coeff);
    }
}

fn full_round(cs: &mut Env<F>, state: &mut State, full_round_counter: &mut usize) -> Vec<Name> {
    // apply non-linearity
    // multiply by MDS
    let to_reset = apply_nonlinearity(cs, state, full_round_counter);
    // Mul by external matrix
    mul_by_external_matrix(cs, state);
    *full_round_counter += 1;
    to_reset
}

fn pow_7(cs: &mut Env<F>, x: &mut Repr<F, SValue>) {
    let square = cs.mul(*x, *x);
    let third = cs.mul(square, *x);
    let quad = cs.mul(square, square);
    *x = cs.mul(quad, third);
}

fn partial_round(cs: &mut Env<F>, state: &mut State, partial_round_counter: &mut usize) -> Name {
    // add constants
    // apply non-linearity
    // multiply by MDS
    let round_constant = PARTIAL_ROUND_CONSTANTS[..][*partial_round_counter];

    // only first element undergoes non-linearity
    // now just raise to the power
    // with FMA of the form c0 * A * B + c1 * D and we can not make a term of (A + k) ^ k
    let to_reset = state[0];
    state[0] = cs.add_constant(state[0], round_constant);
    pow_7(cs, &mut state[0]);

    mul_by_inner_matrix(cs, state);

    *partial_round_counter += 1;
    to_reset.into()
}

fn apply_nonlinearity(
    cs: &mut Env<F>,
    state: &mut State,
    full_round_counter: &mut usize,
) -> Vec<Name> {
    let round_constants = FULL_ROUND_CONSTANTS[..][*full_round_counter];
    // with FMA of the form c0 * A * B + c1 * D and we can not make a term of (A + k) ^ k
    let to_reset: Vec<Name> = state.map(|s| s.into()).to_vec();

    for (a, b) in state.iter_mut().zip(round_constants.iter()) {
        *a = cs.add_constant(*a, *b);
    }

    for dst in state.iter_mut() {
        pow_7(cs, dst);
    }
    to_reset
}
