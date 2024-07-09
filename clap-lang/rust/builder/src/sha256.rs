use crate::vanilla::*;
use base::field::SmallField;

// in contrast to Blake2s we actually keep words packed as UInt32,
// because we need quite "wide" additions

pub const SHA256_ROUNDS: usize = 64;
pub const SHA256_BLOCK_SIZE: usize = 64;
pub const SHA256_DIGEST_SIZE: usize = 32;

pub const INITIAL_STATE: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

pub const ROUND_CONSTANTS: [u32; SHA256_ROUNDS] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

const MASK_4: u32 = (1u32 << 4) - 1;

type State<F> = [Repr<F, u32>; 8];

pub fn sha256<F: SmallField>(
    cs: &mut Env<F>,
    input: &[Repr<F, u8>],
) -> [Repr<F, u8>; SHA256_DIGEST_SIZE] {
    // pad first
    let last_block_size = input.len() % SHA256_BLOCK_SIZE;
    let num_zeroes_to_add = if last_block_size <= (64 - 1 - 8) {
        64 - 1 - 8 - last_block_size
    } else {
        128 - 1 - 8 - last_block_size
    };

    let mut full_message = Vec::with_capacity(input.len() + 1 + 8 + num_zeroes_to_add);
    full_message.extend_from_slice(input);
    full_message.push(cs.c::<u8>(F::from_u64(0x80)));
    if num_zeroes_to_add > 0 {
        let zero = cs.c::<u8>(F::ZERO);
        full_message.extend(std::iter::repeat(zero).take(num_zeroes_to_add));
    }
    let bit_length_be = (input.len() as u64 * 8u64).to_be_bytes();
    for el in bit_length_be {
        let el = cs.c::<u8>(F::from_u64(el as u64));
        full_message.push(el);
    }
    assert_eq!(full_message.len() % SHA256_BLOCK_SIZE, 0);
    let num_rounds = full_message.len() / SHA256_BLOCK_SIZE;

    let mut final_4bit_chunks = None;

    let mut state = INITIAL_STATE.map(|el| cs.c::<u32>(F::from_u64(el as u64)));

    for (round, input_bytes) in full_message.array_chunks::<SHA256_BLOCK_SIZE>().enumerate() {
        let last_round = round == num_rounds - 1;

        let mut message_block = [U32Var::default(); 16];
        for (dst, src) in message_block
            .iter_mut()
            .zip(input_bytes.array_chunks::<4>())
        {
            *dst = uint32_from_bytes(cs, src, false);
        }

        final_4bit_chunks = self::round_function(cs, &mut state, &message_block, last_round);
    }

    let final_4bit_chunks = final_4bit_chunks.expect("must create decompositions");
    let mut output = [U8Var::default(); SHA256_DIGEST_SIZE];
    let shift_4 = F::from_u64(1u64 << 4);
    for (le_4bit_chunks, dst) in final_4bit_chunks
        .array_chunks::<8>()
        .zip(output.array_chunks_mut::<4>())
    {
        for (dst, [low, high]) in dst.iter_mut().zip(le_4bit_chunks.array_chunks::<2>()) {
            // dst <- low + high * shift_4
            let s = cs.add_with_coeff(SVar::from(*low), SVar::from(*high), shift_4);
            *dst = unsafe { U8Var::from_variable_unchecked(s) };
        }

        dst.reverse();
    }

    output
}

pub fn round_function<F: SmallField>(
    cs: &mut Env<F>,
    state: &mut State<F>,
    message_block: &[Repr<F, u32>; 16],
    range_check_final_state: bool,
) -> Option<[Repr<F, U4>; 64]> {
    // first we create message schedule (expand)
    let mut expanded = [U32Var::default(); 64];
    for (dst, src) in expanded[..16].iter_mut().zip(message_block.iter()) {
        *dst = *src;
    }

    let zero = cs.c::<U4>(F::ZERO);

    for idx in 16..SHA256_ROUNDS {
        let t0 = expanded[idx - 15];
        // here we can reuse for rotation
        let (t0_rotated_7, _t0_rot_7_decompose_low, t0_rot_7_decompose_high) =
            split_and_rotate(cs, t0, 7);
        let (t0_rotated_18, _, _) = split_and_rotate(cs, t0, 18);
        // we can create t0 >> 3 by properly changing rotation
        let mut t0_shifted_3 = [U4Var::default(); 8];
        for idx in 0..7 {
            t0_shifted_3[idx] = t0_rotated_7[(7 + idx) % 8];
        }
        // and instead of highest word we use 1 bit piece that rotation made for us
        t0_shifted_3[7] = t0_rot_7_decompose_high;
        // assert_no_placeholder_variables(&t0_shifted_3);

        let s0_chunks = tri_xor_many::<_, U4, 8>(cs, &t0_rotated_7, &t0_rotated_18, &t0_shifted_3);

        // for s1 we can not reuse it, so we do all
        let t1 = expanded[idx - 2];
        let (t1_rotated_17, _, _) = split_and_rotate(cs, t1, 17);
        let (t1_rotated_19, _, _) = split_and_rotate(cs, t1, 19);
        let (t1_rotated_10, _, t1_rotated_10_decompose_high) = split_and_rotate(cs, t1, 10);

        let mut t1_shifted_10 = t1_rotated_10;
        t1_shifted_10[7] = zero;
        t1_shifted_10[6] = zero;
        t1_shifted_10[5] = t1_rotated_10_decompose_high;

        for idx in 0..7 {
            t0_shifted_3[idx] = t0_rotated_7[(7 + idx) % 8];
        }

        let s1_chunks =
            tri_xor_many::<_, U4, 8>(cs, &t1_rotated_17, &t1_rotated_19, &t1_shifted_10);

        let s0 = uint32_from_4bit_chunks(cs, &s0_chunks);
        let s1 = uint32_from_4bit_chunks(cs, &s1_chunks);

        // note that message expansion only shows up in rounds
        // as part of addition, so we need to range check here

        let expanded_word = reduce_terms::<_, u32>(
            cs,
            [F::ONE; 4],
            [s0, s1, expanded[idx - 7], expanded[idx - 16]],
        );

        let (u32_part, _) = range_check_36_bits_using_sha256_tables(cs, expanded_word);

        expanded[idx] = u32_part;
    }

    // main part
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;

    for round in 0..SHA256_ROUNDS {
        let (e_rot_6, _, _) = split_and_rotate(cs, e, 6);
        let (e_rot_11, _, _) = split_and_rotate(cs, e, 11);
        let (e_rot_25, _, _) = split_and_rotate(cs, e, 25);
        let s1 = tri_xor_many::<_, U4, 8>(cs, &e_rot_6, &e_rot_11, &e_rot_25);
        let s1 = uint32_from_4bit_chunks(cs, &s1);

        let e_decompose = uint32_into_4bit_chunks(cs, e);
        let f_decompose = uint32_into_4bit_chunks(cs, f);
        let g_decompose = uint32_into_4bit_chunks(cs, g);
        let ch = ch_many::<_, U4, 8>(cs, &e_decompose, &f_decompose, &g_decompose);
        let ch = uint32_from_4bit_chunks(cs, &ch);

        // add 5 terms first
        let rc = cs.c::<u32>(F::from_u64(ROUND_CONSTANTS[round] as u64));
        let mut tmp1 = reduce_terms::<_, u32>(cs, [F::ONE; 4], [h, s1, ch, rc]);

        // tmp1 <- tmp1 + expanded[round]
        tmp1 = cs.add(tmp1, expanded[round].into());

        // t <- tmp1 + d
        let t = cs.add(tmp1, d.into());

        let (new_e, _) = range_check_36_bits_using_sha256_tables(cs, t);

        let (a_rot_2, _, _) = split_and_rotate(cs, a, 2);
        let (a_rot_13, _, _) = split_and_rotate(cs, a, 13);
        let mut a_rot_22 = [U4Var::default(); 8];
        for idx in 0..8 {
            a_rot_22[idx] = a_rot_2[(idx + 5) % 8];
        }
        let s0 = tri_xor_many::<_, U4, 8>(cs, &a_rot_2, &a_rot_13, &a_rot_22);
        let s0 = uint32_from_4bit_chunks(cs, &s0);

        let a_decompose = uint32_into_4bit_chunks(cs, a);
        let b_decompose = uint32_into_4bit_chunks(cs, b);
        let c_decompose = uint32_into_4bit_chunks(cs, c);
        let maj = maj_many::<_, U4, 8>(cs, &a_decompose, &b_decompose, &c_decompose);
        let maj = uint32_from_4bit_chunks(cs, &maj);

        let t = reduce_terms::<_, SValue>(
            cs,
            [F::ONE, F::ONE, F::ONE, F::ZERO],
            [s0.into(), maj.into(), tmp1, zero.into()],
        );
        let (new_a, _) = range_check_36_bits_using_sha256_tables(cs, t);

        h = g;
        g = f;
        f = e;
        e = new_e;
        d = c;
        c = b;
        b = a;
        a = new_a;
    }

    // add into state

    let mut le_4bit_chunks = [U4Var::default(); 64];
    for (_idx, ((dst, src), res)) in state
        .iter_mut()
        .zip([a, b, c, d, e, f, g, h].into_iter())
        .zip(le_4bit_chunks.array_chunks_mut::<8>())
        .enumerate()
    {
        // tmp <- dst + src
        let tmp = cs.add(SVar::from(*dst), src.into());
        let (_u32_tmp, chunks) = range_check_36_bits_using_sha256_tables(cs, tmp);
        *res = chunks[..8].try_into().unwrap();
    }

    if range_check_final_state {
        Some(le_4bit_chunks)
    } else {
        None
    }
}

fn uint8_from_4bit_chunks<F: SmallField>(
    cs: &mut Env<F>,
    chunks: &[Repr<F, U4>; 2],
) -> Repr<F, u8> {
    // chunks[0] + chunks[1] & 1 << 4 -> result
    let result = cs.add_with_coeff(chunks[0].into(), chunks[1].into(), F::from_u64(1u64 << 4));
    unsafe { U8Var::from_variable_unchecked(result) }
}

fn uint32_from_4bit_chunks<F: SmallField>(
    cs: &mut Env<F>,
    chunks: &[Repr<F, U4>; 8],
) -> Repr<F, u32> {
    let (low_u16, high_u16) = chunks_into_u16_low_high(cs, *chunks);
    // low_16 + 1<<16 * high_u16 -> result
    let result = cs.add_with_coeff(low_u16.into(), high_u16.into(), F::from_u64(1u64 << 16));
    unsafe { U32Var::from_variable_unchecked(result) }
}

fn uint32_from_bytes<F: SmallField>(
    cs: &mut Env<F>,
    bytes: &[Repr<F, u8>; 4],
    le: bool,
) -> Repr<F, u32> {
    let mut bytes = *bytes;
    if !le {
        bytes.reverse()
    };
    let result = reduce_terms_by_constant::<_, u8>(cs, F::from_u64(1u64 << 8), bytes);
    unsafe { U32Var::from_variable_unchecked(result) }
}
