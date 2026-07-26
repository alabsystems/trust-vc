// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Partial executable TrustVc port for upstream
// source/rust_verify_test/tests/bitvector.rs.
//
// This file intentionally ports only the finite-width executable integer cases
// that current TrustVc can express directly with `trust_vc::assert_by_bit_vector!`.
// Known unsupported upstream areas left out of this focused slice:
// - Verus-only `proof fn` syntax and `==>` implication syntax.
// - Broader quantified bit-vector assertions with trigger syntax.
// - Full `#[verifier(bit_vector)]`, `#[verifier::decreases_by]`, recursive
//   spec-function, and Verus global `size_of usize` parity. This file now pins
//   narrow Rust-valid TrustVc surrogates for the first three boundaries.
// - Expected diagnostic tests for unsupported `int` and datatype operands.
// - Large generated signed-arithmetic extreme-case suites. The concrete
//   arithmetic and mixed-signedness coverage below is still a targeted subset
//   rather than the whole upstream stress surface.

use trust_vc_types::int;

pub type BitvectorRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type BitvectorRsFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const BITVECTOR_RS_EXPECTED_CASES: &[BitvectorRsExpectedCase] = &[
    ("mask_and_basic_identities", "test1", "verified", 13),
    ("shift_left_times_four", "test2", "verified", 3),
    (
        "bounded_shift_left_matches_math_product",
        "test2",
        "verified",
        2,
    ),
    ("shift_right_divide_by_two", "test2", "verified", 3),
    ("reflexive_and_compound_bitwise", "test3", "verified", 7),
    (
        "verus_wrapping_free_function_identities",
        "test3",
        "verified",
        7,
    ),
    ("pack_u32_pair", "test4", "verified", 4),
    ("unpack_u64_upper_word", "test5", "verified", 3),
    ("xor_cancellation", "test6", "verified", 3),
    ("not_identities", "test7", "verified", 9),
    ("commuted_mask_bound", "test8", "verified", 3),
    (
        "quantified_bitwise_and_commutativity_u32",
        "test8",
        "verified",
        1,
    ),
    ("unsigned_max_tautologies", "test9", "verified", 5),
    ("signed_reflexive_le", "test8_ok", "verified", 2),
    (
        "usize_in_by_bit_vector",
        "usize_in_by_bit_vector",
        "verified",
        1,
    ),
    (
        "const_usize_in_by_bit_vector",
        "const_usize_in_by_bit_vector",
        "verified",
        1,
    ),
    (
        "usize_cast_in_by_bit_vector",
        "usize_cast_in_by_bit_vector",
        "verified",
        1,
    ),
    (
        "const_math_int_in_by_bit_vector",
        "const_int_in_by_bit_vector",
        "verified",
        1,
    ),
    (
        "finite_width_cast_to_larger_word",
        "test_casting_to_higher_width_issue386",
        "verified",
        5,
    ),
    (
        "bool_guarded_bitwise_identity",
        "test_bool_variable_issue369",
        "verified",
        4,
    ),
    ("shift_right_upper_bound_issue415", "test_issue415", "verified", 1),
    (
        "positive_shift_right_decreases",
        "bitvector_in_decreases_by",
        "verified",
        1,
    ),
    (
        "signed_euclidean_div_constants",
        "div_signed_euclidean",
        "verified",
        9,
    ),
    (
        "signed_euclidean_rem_constants",
        "mod_signed_euclidean",
        "verified",
        9,
    ),
    (
        "signed_cast_to_math_int_div_neg_one_i8",
        "div_mod_signed_properties",
        "verified",
        1,
    ),
    (
        "signed_min_div_neg_one_math_int_i8",
        "div_mod_signed_properties",
        "verified",
        1,
    ),
    (
        "signed_min_div_neg_one_math_int_i16",
        "div_signed_overflow",
        "verified",
        1,
    ),
    (
        "signed_euclidean_div_rem_constants_i16",
        "div_signed_euclidean",
        "verified",
        4,
    ),
    (
        "unsigned_division_nonzero_guards",
        "div0_underspecified",
        "verified",
        3,
    ),
    (
        "unsigned_remainder_nonzero_guards",
        "mod0_underspecified",
        "verified",
        3,
    ),
    (
        "unsigned_div_rem_identity_u8",
        "div_mod_unsigned_properties",
        "verified",
        1,
    ),
    (
        "unsigned_div_rem_unit_divisor_u16",
        "div_mod_unsigned_properties",
        "verified",
        2,
    ),
    (
        "unsigned_remainder_bound_u8",
        "div_mod_unsigned_properties",
        "verified",
        1,
    ),
    ("unsigned_div_rem_constants_u16", "div0", "verified", 4),
    (
        "concrete_signed_extreme_arithmetic_4_4_subset",
        "test_extreme_cases_arithmetic1",
        "verified",
        1,
    ),
    (
        "concrete_signed_extreme_arithmetic_8_8_subset",
        "test_extreme_cases_arithmetic2",
        "verified",
        1,
    ),
    (
        "concrete_signed_extreme_arithmetic_8_16_subset",
        "test_extreme_cases_arithmetic3",
        "verified",
        1,
    ),
    (
        "concrete_signed_extreme_arithmetic_15_16_subset",
        "test_extreme_cases_arithmetic5",
        "verified",
        1,
    ),
    (
        "concrete_by_equating_add_subset",
        "test_by_equating_add",
        "verified",
        1,
    ),
    (
        "concrete_by_equating_sub_subset",
        "test_by_equating_sub",
        "verified",
        1,
    ),
    (
        "concrete_by_equating_mul_subset",
        "test_by_equating_mul",
        "verified",
        1,
    ),
    (
        "concrete_by_equating_le_subset",
        "test_by_equating_le",
        "verified",
        1,
    ),
    (
        "concrete_unsigned_by_equating_shr_subset",
        "test_by_equating_shr",
        "verified",
        1,
    ),
    (
        "concrete_by_equating_shl_subset",
        "test_by_equating_shl",
        "verified",
        1,
    ),
    (
        "signed_unsigned_div_rem_concrete_subset",
        "test_signed_and_unsigned",
        "verified",
        1,
    ),
    ("bitnot_u64_subtraction_identity", "bitnot", "verified", 1),
    (
        "signed_bitnot_i64_subtraction_identity",
        "bitnot",
        "verified",
        1,
    ),
    ("signed_bitnot_i32_constant", "bitnot", "verified", 1),
    (
        "clipping_and_casting_valid_subset",
        "test_clipping_and_casting",
        "verified",
        1,
    ),
    (
        "cross_width_unsigned_ineq_valid_subset",
        "bitvector_ineq_different_bitwidth",
        "verified",
        1,
    ),
    (
        "mixed_signed_unsigned_ineq_valid_subset",
        "test_eq_ineq",
        "verified",
        1,
    ),
    (
        "mixed_signed_unsigned_reflexive_cast_valid_subset",
        "test_eq_ineq",
        "verified",
        1,
    ),
    (
        "mixed_u32_i32_comparison_valid_subset",
        "test_eq_ineq2",
        "verified",
        1,
    ),
    ("cross_width_bitnot_valid_subset", "bitnot", "verified", 1),
    (
        "mixed_width_or_and_xor_valid_subset",
        "test_or",
        "verified",
        1,
    ),
    (
        "u16_bitwise_zero_extend_valid_subset",
        "test_normal_solver",
        "verified",
        1,
    ),
    ("mixed_width_shift_valid_subset", "test_shl", "verified", 1),
    ("u16_shift_right_cast_valid_subset", "test_shr", "verified", 2),
    (
        "u32_shift_right_matches_low_u16_when_bounded",
        "test_shr",
        "verified",
        1,
    ),
    (
        "signed_shift_left_valid_subset",
        "test_shl_signed",
        "verified",
        4,
    ),
    (
        "signed_shift_right_valid_subset",
        "test_shr_signed",
        "verified",
        2,
    ),
    (
        "signed_i16_shift_right_sign_extend_valid_subset",
        "test_shr_signed",
        "verified",
        1,
    ),
    ("let_bound_shift_valid_subset", "test_let_binder", "verified", 1),
    ("forall_shift_right_equal_width_subset", "test_forall", "verified", 1),
    (
        "mixed_width_shift_keeps_lhs_width_valid_subset",
        "test_shl",
        "verified",
        1,
    ),
    (
        "function_level_bit_vector_attribute_valid_subset",
        "test_issue415",
        "verified",
        4,
    ),
    (
        "recursive_bitvector_spec_compute_verified",
        "bitvector_in_decreases_by",
        "verified",
        2,
    ),
    (
        "finite_width_cast_to_larger_word_counterexample",
        "test_casting_to_higher_width_issue386",
        "counterexample",
        3,
    ),
    ("b_or_b_greater_counterexample", "test1_fails", "counterexample", 1),
    (
        "b_and_zero_positive_counterexample",
        "test3_fails",
        "counterexample",
        1,
    ),
    (
        "wrapping_increment_identity_counterexample",
        "test2_fails",
        "counterexample",
        1,
    ),
    (
        "shift_roundtrip_counterexample",
        "test4_fails",
        "counterexample",
        1,
    ),
    (
        "shift_left_wrong_multiplier_counterexample",
        "test5_fails",
        "counterexample",
        3,
    ),
    (
        "bitnot_constants_then_false_counterexample",
        "test7_fails",
        "counterexample",
        1,
    ),
    (
        "clipping_cast_u32_to_u16_counterexample",
        "test_clipping_and_casting",
        "counterexample",
        1,
    ),
    (
        "clipping_cast_i32_to_i16_counterexample",
        "test_clipping_and_casting",
        "counterexample",
        1,
    ),
    (
        "cross_width_unsigned_ineq_counterexample",
        "bitvector_ineq_different_bitwidth",
        "counterexample",
        1,
    ),
    (
        "mixed_signed_unsigned_eq_counterexample",
        "test_eq_ineq",
        "counterexample",
        1,
    ),
    (
        "mixed_signed_unsigned_ineq_counterexample",
        "test_eq_ineq",
        "counterexample",
        1,
    ),
    (
        "mixed_u32_i32_comparison_counterexample",
        "test_eq_ineq2",
        "counterexample",
        1,
    ),
    ("cross_width_bitnot_counterexample", "bitnot", "counterexample", 1),
    (
        "mixed_width_or_and_xor_counterexample",
        "test_or",
        "counterexample",
        1,
    ),
    (
        "i16_bitwise_unsigned_cast_counterexample",
        "test_normal_solver",
        "counterexample",
        1,
    ),
    (
        "mixed_width_shift_counterexample",
        "test_shl",
        "counterexample",
        1,
    ),
    (
        "mixed_width_shift_lhs_width_counterexample",
        "test_shl",
        "counterexample",
        1,
    ),
    (
        "u16_shift_right_low_byte_counterexample",
        "test_shr",
        "counterexample",
        1,
    ),
    (
        "u32_shift_right_low_u16_counterexample",
        "test_shr",
        "counterexample",
        1,
    ),
    (
        "signed_shift_left_width_counterexample",
        "test_shl_signed",
        "counterexample",
        1,
    ),
    (
        "signed_i16_shift_right_zero_extend_counterexample",
        "test_shr_signed",
        "counterexample",
        1,
    ),
    (
        "positive_shift_right_decreases_counterexample",
        "bitvector_in_decreases_by",
        "counterexample",
        1,
    ),
    (
        "signed_shift_amount_left_diagnostic",
        "test_shl_signed_unsupported",
        "counterexample",
        1,
    ),
    (
        "signed_shift_amount_right_diagnostic",
        "test_shr_signed_unsupported",
        "counterexample",
        1,
    ),
    (
        "casting_u16_to_u8_counterexample",
        "test_clipping_and_casting",
        "counterexample",
        1,
    ),
    (
        "casting_i16_to_i8_counterexample",
        "test_clipping_and_casting",
        "counterexample",
        1,
    ),
    (
        "verus_wrapping_free_function_counterexample",
        "test1_fails",
        "counterexample",
        1,
    ),
    (
        "quantified_shift_positive_counterexample_u64",
        "test10_fails",
        "counterexample",
        1,
    ),
    (
        "unsigned_div_rem_identity_counterexample_u8",
        "div_mod_unsigned_properties",
        "counterexample",
        1,
    ),
    (
        "unsigned_div_rem_unit_divisor_counterexample_u16",
        "div_mod_unsigned_properties",
        "counterexample",
        1,
    ),
    (
        "unsigned_division_zero_guard_missing_counterexample",
        "div0_underspecified",
        "counterexample",
        1,
    ),
    (
        "concrete_signed_extreme_arithmetic_counterexample",
        "test_extreme_cases_arithmetic2",
        "counterexample",
        1,
    ),
    (
        "concrete_by_equating_arithmetic_counterexample",
        "test_by_equating_mul",
        "counterexample",
        1,
    ),
    (
        "signed_unsigned_div_rem_concrete_counterexample",
        "test_signed_and_unsigned",
        "counterexample",
        1,
    ),
    (
        "function_level_bit_vector_attribute_counterexample",
        "test10_fails",
        "counterexample",
        1,
    ),
    (
        "recursive_bitvector_spec_compute_counterexample",
        "bitvector_in_decreases_by",
        "counterexample",
        1,
    ),
    (
        "mixed_signed_unsigned_cast_guard_diagnostic",
        "test_eq_ineq",
        "error",
        0,
    ),
    (
        "mixed_u32_i32_reverse_guard_diagnostic",
        "test_eq_ineq2",
        "error",
        0,
    ),
    (
        "signed_unsigned_bitnot_cast_guard_diagnostic",
        "bitnot",
        "error",
        0,
    ),
    (
        "bitvector_function_shaped_helpers",
        "test_functions",
        "verified",
        2,
    ),
    (
        "bitvector_decreases_by_clause_currently_fail_closed",
        "bitvector_in_decreases_by",
        "error",
        0,
    ),
    (
        "bitvector_mut_ref_deref_diagnostic",
        "test_dereference_mut_ref_2",
        "error",
        0,
    ),
    (
        "bitvector_old_mut_ref_diagnostic",
        "test_old_not_supported",
        "error",
        0,
    ),
];

pub const BITVECTOR_RS_FAIL_CLOSED_ERROR_PATTERNS: &[BitvectorRsFailClosedErrorPatterns] = &[
    (
        "mixed_signed_unsigned_cast_guard_diagnostic",
        &["sort metadata mismatch"],
    ),
    (
        "mixed_u32_i32_reverse_guard_diagnostic",
        &["sort metadata mismatch"],
    ),
    (
        "signed_unsigned_bitnot_cast_guard_diagnostic",
        &["sort metadata mismatch"],
    ),
    (
        "bitvector_decreases_by_clause_currently_fail_closed",
        &["decreases_by"],
    ),
    ("bitvector_mut_ref_deref_diagnostic", &["dereference"]),
    ("bitvector_old_mut_ref_diagnostic", &["old"]),
];

pub fn bitvector_rs_expected_cases() -> &'static [BitvectorRsExpectedCase] {
    BITVECTOR_RS_EXPECTED_CASES
}

pub fn bitvector_rs_fail_closed_error_patterns(
) -> &'static [BitvectorRsFailClosedErrorPatterns] {
    BITVECTOR_RS_FAIL_CLOSED_ERROR_PATTERNS
}

fn forall<F>(_f: F) -> bool {
    true
}

fn add(x: u32, y: u32) -> u32 {
    x.wrapping_add(y)
}

fn add64(x: u64, y: u64) -> u64 {
    x.wrapping_add(y)
}

fn sub(x: u32, y: u32) -> u32 {
    x.wrapping_sub(y)
}

fn mul(x: u32, y: u32) -> u32 {
    x.wrapping_mul(y)
}

fn shifter(x: u32) -> u32 {
    x >> 1u32
}

fn bitand_alias(x: u32, y: u32) -> u32 {
    x & y
}

#[trust_vc::decreases(steps)]
#[trust_vc::spec]
fn recursive_shift_down(x: u64, steps: usize) -> u64 {
    if steps == 0usize {
        x
    } else {
        recursive_shift_down(x >> 1u32, steps - 1usize)
    }
}

#[trust_vc::ensures(true)]
fn mask_and_basic_identities(b: u32) {
    trust_vc::assert_by_bit_vector!(b & 7u32 == b % 8u32);
    trust_vc::assert!(b & 7u32 == b % 8u32);

    trust_vc::assert_by_bit_vector!(b ^ b == 0u32);
    trust_vc::assert!(b ^ b == 0u32);

    trust_vc::assert_by_bit_vector!(b & b == b);
    trust_vc::assert!(b & b == b);

    trust_vc::assert_by_bit_vector!(add(add(b, !b), 1u32) == 0u32);
    trust_vc::assert!(add(add(b, !b), 1u32) == 0u32);

    trust_vc::assert_by_bit_vector!(b | b == b);
    trust_vc::assert!(b | b == b);

    trust_vc::assert_by_bit_vector!(b & 0xffu32 < 0x100u32);
    trust_vc::assert!(b & 0xffu32 < 0x100u32);
}

#[trust_vc::ensures(true)]
fn shift_left_times_four(b: u32) {
    trust_vc::assert_by_bit_vector!((b << 2u32) == mul(b, 4u32));
    trust_vc::assert!((b << 2u32) == mul(b, 4u32));
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(b < 256u32)]
fn bounded_shift_left_matches_math_product(b: u32) {
    trust_vc::assert!(b << 2u32 == b * 4u32);
}

#[trust_vc::ensures(true)]
fn shift_right_divide_by_two(b: u32) {
    trust_vc::assert_by_bit_vector!((b >> 1u32) == b / 2u32);
    trust_vc::assert!((b >> 1u32) == b / 2u32);
}

#[trust_vc::ensures(true)]
fn reflexive_and_compound_bitwise(b: u32) {
    trust_vc::assert_by_bit_vector!(b <= b);
    trust_vc::assert!(b <= b);

    trust_vc::assert_by_bit_vector!(b >= b);
    trust_vc::assert!(b >= b);

    trust_vc::assert_by_bit_vector!(b & b & b == b | b | (b ^ b));
    trust_vc::assert!(b & b & b == b | b | (b ^ b));
}

#[trust_vc::ensures(true)]
fn verus_wrapping_free_function_identities(x: u32, y: u32) {
    trust_vc::assert_by_bit_vector!(sub(add(x, y), y) == x);
    trust_vc::assert!(sub(add(x, y), y) == x);

    trust_vc::assert_by_bit_vector!(sub(mul(2u32, x), x) == x);
    trust_vc::assert!(sub(mul(2u32, x), x) == x);

    trust_vc::assert_by_bit_vector!(mul(x, 1u32) == x);
    trust_vc::assert!(mul(x, 1u32) == x);
}

#[trust_vc::ensures(true)]
fn pack_u32_pair(u1: u32, u2: u32) {
    let packed: u64 = (u1 as u64) << 32u64 | (u2 as u64);
    trust_vc::assert_by_bit_vector!(
        packed == (u1 as u64) * 0x1_0000_0000u64 + (u2 as u64);
        requires packed == ((u1 as u64) << 32u64 | (u2 as u64))
    );
    trust_vc::assert!(packed == (u1 as u64) * 0x1_0000_0000u64 + (u2 as u64));
}

#[trust_vc::ensures(true)]
fn unpack_u64_upper_word(u: u64) {
    trust_vc::assert_by_bit_vector!((u >> 32u64) as u32 == (u / 0x1_0000_0000u64) as u32);
    trust_vc::assert!((u >> 32u64) as u32 == (u / 0x1_0000_0000u64) as u32);
}

#[trust_vc::ensures(true)]
fn xor_cancellation(a: u64, b: u64, c: u64) {
    trust_vc::assert_by_bit_vector!((a ^ b != a ^ c) || (b == c));
    trust_vc::assert!((a ^ b != a ^ c) || (b == c));
}

#[trust_vc::ensures(true)]
fn not_identities(b1: u64, b2: u64, b3: u64) {
    trust_vc::assert_by_bit_vector!(!(!b1 != !b2) || !(b1 == b2));
    trust_vc::assert!(!(!b1 != !b2) || !(b1 == b2));

    trust_vc::assert_by_bit_vector!(!(b1 == 1u64 && b2 == b3) || add64(b1, b2) == add64(b3, 1u64));
    trust_vc::assert!(!(b1 == 1u64 && b2 == b3) || add64(b1, b2) == add64(b3, 1u64));

    trust_vc::assert_by_bit_vector!((b1 != b2) || (!b1 == !b2));
    trust_vc::assert!((b1 != b2) || (!b1 == !b2));

    trust_vc::assert_by_bit_vector!(b1 == !(!b1));
    trust_vc::assert!(b1 == !(!b1));
}

#[trust_vc::ensures(true)]
fn commuted_mask_bound(b: u32) {
    trust_vc::assert_by_bit_vector!(0xffu32 & b < 0x100u32);
    trust_vc::assert!(0xffu32 & b < 0x100u32);
}

#[trust_vc::ensures(true)]
fn quantified_bitwise_and_commutativity_u32() {
    trust_vc::assert_by_bit_vector!(forall(|a: u32, b: u32| (a & b) == (b & a)));
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(y < 32u32)]
fn unsigned_max_tautologies(x: u32, y: u32) {
    let max: u32 = 0xffff_ffffu32;
    trust_vc::assert!(x >> 1u32 >= 0u32);
    trust_vc::assert!(x & y <= max);
    trust_vc::assert!(x | y >= 0u32);
    trust_vc::assert!(x << y <= max);
}

#[trust_vc::ensures(true)]
fn signed_reflexive_le(b: i32) {
    trust_vc::assert_by_bit_vector!(b <= b);
}

#[trust_vc::ensures(true)]
fn usize_in_by_bit_vector(x: usize) {
    trust_vc::assert_by_bit_vector!(x & x == x);
}

#[trust_vc::ensures(true)]
fn const_usize_in_by_bit_vector() {
    trust_vc::assert_by_bit_vector!(1usize == 1usize);
}

#[trust_vc::ensures(true)]
fn usize_cast_in_by_bit_vector(x: u64) {
    trust_vc::assert_by_bit_vector!((x as usize) == (x as usize));
}

#[trust_vc::ensures(true)]
fn const_math_int_in_by_bit_vector() {
    trust_vc::assert_by_bit_vector!((0 as int) == (0 as int));
}

#[trust_vc::ensures(true)]
fn finite_width_cast_to_larger_word() {
    let b: u8 = 20u8;
    let w: u64 = 20u64;
    trust_vc::assert_by_bit_vector!((b as u64) == w; requires b == 20u8, w == 20u64);
    trust_vc::assert!((b as u64) == w);
}

#[trust_vc::ensures(true)]
fn finite_width_cast_to_larger_word_counterexample() {
    let b: u8 = 20u8;
    let w: u64 = 200u64;
    trust_vc::assert_by_bit_vector!((b as u64) == w; requires b == 20u8, w == 200u64);
}

#[trust_vc::ensures(true)]
fn bool_guarded_bitwise_identity() {
    let b: bool = true;
    trust_vc::assert_by_bit_vector!(!b || ((0u8 | 1u8 == 1u8) == b); requires b == true);
    trust_vc::assert!(!b || ((0u8 | 1u8 == 1u8) == b));
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(amt < 64u64)]
#[trust_vc::requires(val <= upper_bound)]
fn shift_right_upper_bound_issue415(val: u64, amt: u64, upper_bound: u64) {
    trust_vc::assert_by_bit_vector!(
        (val >> amt) <= (upper_bound >> amt);
        requires amt < 64u64, val <= upper_bound
    );
    trust_vc::assert!((val >> amt) <= (upper_bound >> amt));
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(n > 0u64)]
fn positive_shift_right_decreases(n: u64) {
    trust_vc::assert_by_bit_vector!((n >> 1u64) < n; requires n > 0u64);
}

#[trust_vc::ensures(true)]
fn signed_euclidean_div_constants() {
    trust_vc::assert_by_bit_vector!(7i32.div_euclid(3i32) == 2i32);
    trust_vc::assert!(7i32.div_euclid(3i32) == 2i32);

    trust_vc::assert_by_bit_vector!((-7i32).div_euclid(3i32) == -3i32);
    trust_vc::assert!((-7i32).div_euclid(3i32) == -3i32);

    trust_vc::assert_by_bit_vector!(7i32.div_euclid(-3i32) == -2i32);
    trust_vc::assert!(7i32.div_euclid(-3i32) == -2i32);

    trust_vc::assert_by_bit_vector!((-7i32).div_euclid(-3i32) == 3i32);
    trust_vc::assert!((-7i32).div_euclid(-3i32) == 3i32);
}

#[trust_vc::ensures(true)]
fn signed_euclidean_rem_constants() {
    trust_vc::assert_by_bit_vector!(7i32.rem_euclid(3i32) == 1i32);
    trust_vc::assert!(7i32.rem_euclid(3i32) == 1i32);

    trust_vc::assert_by_bit_vector!((-7i32).rem_euclid(3i32) == 2i32);
    trust_vc::assert!((-7i32).rem_euclid(3i32) == 2i32);

    trust_vc::assert_by_bit_vector!(7i32.rem_euclid(-3i32) == 1i32);
    trust_vc::assert!(7i32.rem_euclid(-3i32) == 1i32);

    trust_vc::assert_by_bit_vector!((-7i32).rem_euclid(-3i32) == 2i32);
    trust_vc::assert!((-7i32).rem_euclid(-3i32) == 2i32);
}

#[trust_vc::ensures(true)]
fn signed_cast_to_math_int_div_neg_one_i8(x: i8) {
    trust_vc::assert_by_bit_vector!((x as int) / (-1 as int) == -(x as int));
}

#[trust_vc::ensures(true)]
fn signed_min_div_neg_one_math_int_i8() {
    trust_vc::assert_by_bit_vector!(((-128i8) as int) / (-1 as int) == 128 as int);
}

#[trust_vc::ensures(true)]
fn signed_min_div_neg_one_math_int_i16() {
    trust_vc::assert_by_bit_vector!(((-32768i16) as int) / (-1 as int) == 32768 as int);
}

#[trust_vc::ensures(true)]
fn signed_euclidean_div_rem_constants_i16() {
    trust_vc::assert_by_bit_vector!((-32768i16).div_euclid(257i16) == -128i16);
    trust_vc::assert_by_bit_vector!((-32768i16).rem_euclid(257i16) == 128i16);
    trust_vc::assert_by_bit_vector!(32767i16.div_euclid(-257i16) == -127i16);
    trust_vc::assert_by_bit_vector!(32767i16.rem_euclid(-257i16) == 128i16);
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(y != 0i8)]
#[trust_vc::requires(!(x == i8::MIN && y == -1i8))]
fn signed_div_rem_identity_i8(x: i8, y: i8) {
    trust_vc::assert_by_bit_vector!(
        (x.div_euclid(y) as i16) * (y as i16) + (x.rem_euclid(y) as i16) == (x as i16);
        requires y != 0i8, !(x == i8::MIN && y == -1i8)
    );
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(y > 0i8)]
fn signed_remainder_positive_divisor_bounds_i8(x: i8, y: i8) {
    trust_vc::assert_by_bit_vector!(
        x.rem_euclid(y) >= 0i8 && x.rem_euclid(y) < y;
        requires y > 0i8
    );
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(y < 0i8)]
#[trust_vc::requires(y != i8::MIN)]
#[trust_vc::requires(!(x == i8::MIN && y == -1i8))]
fn signed_remainder_negative_divisor_bounds_i8(x: i8, y: i8) {
    trust_vc::assert_by_bit_vector!(
        x.rem_euclid(y) >= 0i8 && x.rem_euclid(y) < -y;
        requires y < 0i8, y != i8::MIN, !(x == i8::MIN && y == -1i8)
    );
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(y != 0u32)]
fn unsigned_division_nonzero_guards(y: u32) {
    trust_vc::assert_by_bit_vector!(0u32.div_euclid(y) == 0u32);
    trust_vc::assert_by_bit_vector!(y.div_euclid(y) == 1u32);
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(y != 0u32)]
fn unsigned_remainder_nonzero_guards(y: u32) {
    trust_vc::assert_by_bit_vector!(0u32.rem_euclid(y) == 0u32);
    trust_vc::assert_by_bit_vector!(y.rem_euclid(y) == 0u32);
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(y != 0u8)]
fn unsigned_div_rem_identity_u8(x: u8, y: u8) {
    trust_vc::assert_by_bit_vector!(
        x.div_euclid(y) * y + x.rem_euclid(y) == x;
        requires y != 0u8
    );
}

#[trust_vc::ensures(true)]
fn unsigned_div_rem_unit_divisor_u16(x: u16) {
    trust_vc::assert_by_bit_vector!(x.div_euclid(1u16) == x);
    trust_vc::assert_by_bit_vector!(x.rem_euclid(1u16) == 0u16);
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(y != 0u8)]
fn unsigned_remainder_bound_u8(x: u8, y: u8) {
    trust_vc::assert_by_bit_vector!(x.rem_euclid(y) < y; requires y != 0u8);
}

#[trust_vc::ensures(true)]
fn unsigned_div_rem_constants_u16() {
    trust_vc::assert_by_bit_vector!(65535u16.div_euclid(257u16) == 255u16);
    trust_vc::assert_by_bit_vector!(65535u16.rem_euclid(257u16) == 0u16);
    trust_vc::assert_by_bit_vector!(65535u16.div_euclid(256u16) == 255u16);
    trust_vc::assert_by_bit_vector!(65535u16.rem_euclid(256u16) == 255u16);
}

#[trust_vc::ensures(true)]
fn concrete_signed_extreme_arithmetic_4_4_subset() {
    trust_vc::assert_by_bit_vector!((((-1i32) ^ 7i32) + ((-1i32) ^ 7i32)) == -16i32);
    trust_vc::assert_by_bit_vector!((((-1i32) ^ 7i32) - !(-8i32)) == -15i32);
    trust_vc::assert_by_bit_vector!((!(-8i32) * ((-1i32) ^ 7i32)) == -56i32);
}

#[trust_vc::ensures(true)]
fn concrete_signed_extreme_arithmetic_8_8_subset() {
    trust_vc::assert_by_bit_vector!((!(-128i32) * !(-128i32)) == 16129i32);
    trust_vc::assert_by_bit_vector!((255i32 * !(-128i32)) == 32385i32);
}

#[trust_vc::ensures(true)]
fn concrete_signed_extreme_arithmetic_8_16_subset() {
    trust_vc::assert_by_bit_vector!((((-1i32) ^ 127i32) * ((-1i32) ^ 32767i32)) == 4194304i32);
}

#[trust_vc::ensures(true)]
fn concrete_signed_extreme_arithmetic_15_16_subset() {
    trust_vc::assert_by_bit_vector!((32767i32 * 65535i32) == 2147385345i32);
}

#[trust_vc::ensures(true)]
fn concrete_by_equating_add_subset() {
    let ai: i8 = -7i8;
    let bi: i8 = 12i8;
    let x: i32 = -7i32;
    let y: i32 = 12i32;

    trust_vc::assert_by_bit_vector!(
        ((ai + bi) as i32) == x + y;
        requires ai == -7i8, bi == 12i8, x == -7i32, y == 12i32
    );
}

#[trust_vc::ensures(true)]
fn concrete_by_equating_sub_subset() {
    let ai: i8 = -7i8;
    let bi: i8 = 12i8;
    let x: i32 = -7i32;
    let y: i32 = 12i32;

    trust_vc::assert_by_bit_vector!(
        ((ai - bi) as i32) == x - y;
        requires ai == -7i8, bi == 12i8, x == -7i32, y == 12i32
    );
}

#[trust_vc::ensures(true)]
fn concrete_by_equating_mul_subset() {
    let au: u8 = 200u8;
    let bu: u8 = 3u8;

    trust_vc::assert_by_bit_vector!(
        ((au as i32) * (bu as i32)) == 600i32;
        requires au == 200u8, bu == 3u8
    );
}

#[trust_vc::ensures(true)]
fn concrete_by_equating_le_subset() {
    let ai: i8 = -7i8;
    let bi: i8 = 12i8;
    let x: i32 = -7i32;
    let y: i32 = 12i32;

    trust_vc::assert_by_bit_vector!(
        (ai <= bi) == (x <= y);
        requires ai == -7i8, bi == 12i8, x == -7i32, y == 12i32
    );
}

#[trust_vc::ensures(true)]
fn concrete_unsigned_by_equating_shr_subset() {
    let au: u8 = 64u8;
    let bi: u8 = 2u8;
    let x_pos: i32 = 64i32;
    let y: u32 = 2u32;

    trust_vc::assert_by_bit_vector!(
        ((au >> bi) as i32) == (x_pos >> y);
        requires au == 64u8, bi == 2u8, x_pos == 64i32, y == 2u32
    );
}

#[trust_vc::ensures(true)]
fn concrete_by_equating_shl_subset() {
    let ai: i8 = -7i8;
    let au: u8 = 7u8;
    let bi: u8 = 2u8;
    let x_neg: i32 = -7i32;
    let x_pos: i32 = 7i32;
    let y: u32 = 2u32;

    trust_vc::assert_by_bit_vector!(
        (ai << bi) == ((x_neg << y) as i8);
        requires ai == -7i8, bi == 2u8, x_neg == -7i32, y == 2u32
    );
    trust_vc::assert_by_bit_vector!(
        (au << bi) == ((x_pos << y) as u8);
        requires au == 7u8, bi == 2u8, x_pos == 7i32, y == 2u32
    );
}

#[trust_vc::ensures(true)]
fn signed_unsigned_div_rem_concrete_subset() {
    let neg: i8 = -7i8;
    let pos: i8 = 3i8;
    let mag: u8 = 7u8;
    let div: u8 = 3u8;

    trust_vc::assert_by_bit_vector!(
        neg.div_euclid(pos) == -((mag.div_euclid(div)) as i8) - 1i8
            && neg.rem_euclid(pos) == (div - mag.rem_euclid(div)) as i8;
        requires neg == -7i8, pos == 3i8, mag == 7u8, div == 3u8
    );

    let neg_both: i8 = -8i8;
    let neg_divisor: i8 = -3i8;
    let mag_both: u8 = 8u8;
    let unsigned_divisor: u8 = 3u8;

    trust_vc::assert_by_bit_vector!(
        neg_both.div_euclid(neg_divisor)
            == (mag_both.div_euclid(unsigned_divisor) as i8) + 1i8
            && neg_both.rem_euclid(neg_divisor)
                == (unsigned_divisor - mag_both.rem_euclid(unsigned_divisor)) as i8;
        requires neg_both == -8i8,
            neg_divisor == -3i8,
            mag_both == 8u8,
            unsigned_divisor == 3u8
    );
}

#[trust_vc::ensures(true)]
fn concrete_signed_extreme_arithmetic_counterexample() {
    trust_vc::assert_by_bit_vector!((!(-128i32) * !(-128i32)) == 16128i32);
}

#[trust_vc::ensures(true)]
fn concrete_by_equating_arithmetic_counterexample() {
    let au: u8 = 200u8;
    let bu: u8 = 3u8;
    trust_vc::assert_by_bit_vector!(
        ((au as i32) * (bu as i32)) == 601i32;
        requires au == 200u8, bu == 3u8
    );
}

#[trust_vc::ensures(true)]
fn signed_unsigned_div_rem_concrete_counterexample() {
    let neg: i8 = -7i8;
    let pos: i8 = 3i8;
    let mag: u8 = 7u8;
    let div: u8 = 3u8;

    trust_vc::assert_by_bit_vector!(
        neg.div_euclid(pos) == -((mag.div_euclid(div)) as i8)
            && neg.rem_euclid(pos) == mag.rem_euclid(div) as i8;
        requires neg == -7i8, pos == 3i8, mag == 7u8, div == 3u8
    );
}

#[trust_vc::ensures(true)]
fn bitnot_u64_subtraction_identity(y: u64) {
    trust_vc::assert_by_bit_vector!((!y) == 0xffff_ffff_ffff_ffffu64 - y);
}

#[trust_vc::ensures(true)]
fn signed_bitnot_i64_subtraction_identity(y: i64) {
    trust_vc::assert_by_bit_vector!((!y) == -1i64 - y);
}

#[trust_vc::ensures(true)]
fn signed_bitnot_i32_constant() {
    trust_vc::assert_by_bit_vector!(!0xffffi32 == -0x10000i32);
}

#[trust_vc::ensures(true)]
fn clipping_and_casting_valid_subset(a: u32, b: i32, x: u16, y: i16) {
    trust_vc::assert_by_bit_vector!((a as u16) == ((a as i32) as u16));
    trust_vc::assert_by_bit_vector!((b as i16) == ((b as u64) as i16));
    trust_vc::assert_by_bit_vector!((x as i8 as u8) == (x as u8));
    trust_vc::assert_by_bit_vector!((y as u8 as i8) == (y as i8));
}

#[trust_vc::ensures(true)]
fn cross_width_unsigned_ineq_valid_subset() {
    let b: u8 = 5u8;
    trust_vc::assert_by_bit_vector!((b as u64) >= 3u64; requires b == 5u8);
    trust_vc::assert_by_bit_vector!(3u64 <= (b as u64); requires b == 5u8);
}

#[trust_vc::ensures(true)]
fn mixed_signed_unsigned_ineq_valid_subset(x: u8, y: i8) {
    trust_vc::assert_by_bit_vector!(!(y == -5i8) || ((x as i16) >= (y as i16)));
}

#[trust_vc::ensures(true)]
fn mixed_signed_unsigned_cast_guard_diagnostic(x: u8, y: i8) {
    trust_vc::assert_by_bit_vector!(!(x >= (y as u8)) || ((x as i16) >= (y as i16)));
}

#[trust_vc::ensures(true)]
fn mixed_signed_unsigned_reflexive_cast_valid_subset(x: u8) {
    trust_vc::assert_by_bit_vector!((x as i16) >= ((x as i8) as i16));
}

#[trust_vc::ensures(true)]
fn mixed_u32_i32_comparison_valid_subset(a: u32, b: i32) {
    trust_vc::assert_by_bit_vector!(
        ((a as i64) < (b as i64)) == ((b & (-0x8000_0000i32) == 0i32) && (a < (b as u32)))
    );
    trust_vc::assert_by_bit_vector!(!((a as i64) < (b as i64)) || a < (b as u32));
    trust_vc::assert_by_bit_vector!(
        ((a as i64) > (b as i64)) == ((b & (-0x8000_0000i32) != 0i32) || (a > (b as u32)))
    );
}

#[trust_vc::ensures(true)]
fn mixed_u32_i32_reverse_guard_diagnostic(a: u32, b: i32) {
    trust_vc::assert_by_bit_vector!(!(a > (b as u32)) || (a as i64) > (b as i64));
}

#[trust_vc::ensures(true)]
fn cross_width_bitnot_valid_subset(x: u32, y: u64) {
    trust_vc::assert_by_bit_vector!(
        !((x as u64) == y)
            || ((((0xffff_ffffu32 - x) as u64) ^ 0xffff_ffff_0000_0000u64)
                == (0xffff_ffff_ffff_ffffu64 - y))
    );
}

#[trust_vc::ensures(true)]
fn signed_unsigned_bitnot_cast_guard_diagnostic(a: u32, b: i32) {
    trust_vc::assert_by_bit_vector!(
        !(a == (b as u32)) || (0xffff_ffffu32 - a) == ((-1i32 - b) as u32)
    );
}

#[trust_vc::ensures(true)]
fn mixed_width_or_and_xor_valid_subset(x: u16, y: u16, z: i16) {
    trust_vc::assert_by_bit_vector!((x | y) == ((x as i16 | y as i16) as u16));
    trust_vc::assert_by_bit_vector!((x & y) == ((x as i16 & y as i16) as u16));
    trust_vc::assert_by_bit_vector!((x ^ y) == ((x as i16 ^ y as i16) as u16));

    trust_vc::assert_by_bit_vector!((x | 0x7777u16) & 0x8000u16 == x & 0x8000u16);
    trust_vc::assert_by_bit_vector!((x & 0x7777u16) & 0x8000u16 == 0u16);
    trust_vc::assert_by_bit_vector!((x ^ 0x7777u16) & 0x8000u16 == x & 0x8000u16);

    trust_vc::assert_by_bit_vector!((z | 0x7777i16) & (0x8000u16 as i16) == z & (0x8000u16 as i16));
    trust_vc::assert_by_bit_vector!((z & 0x7777i16) & (0x8000u16 as i16) == 0i16);
    trust_vc::assert_by_bit_vector!((z ^ 0x7777i16) & (0x8000u16 as i16) == z & (0x8000u16 as i16));
}

#[trust_vc::ensures(true)]
fn u16_bitwise_zero_extend_valid_subset(x: u16, y: u16) {
    trust_vc::assert_by_bit_vector!(((x | y) as u32) == ((x as u32) | (y as u32)));
    trust_vc::assert_by_bit_vector!(((x & y) as u32) == ((x as u32) & (y as u32)));
    trust_vc::assert_by_bit_vector!(((x ^ y) as u32) == ((x as u32) ^ (y as u32)));

    trust_vc::assert_by_bit_vector!(((x | y) as i64) == ((x as i64) | (y as i64)));
    trust_vc::assert_by_bit_vector!(((x & y) as i64) == ((x as i64) & (y as i64)));
    trust_vc::assert_by_bit_vector!(((x ^ y) as i64) == ((x as i64) ^ (y as i64)));
}

#[trust_vc::ensures(true)]
fn mixed_width_shift_valid_subset(x: u32, y: u16) {
    trust_vc::assert_by_bit_vector!((x << 2u32) as i32 == (x as i32) << 2u32);
    trust_vc::assert_by_bit_vector!(((x as u64) << 2u32) == (x as u64) * 4u64);
    trust_vc::assert_by_bit_vector!(((y as u64) << 2u32) == (y as u64) * 4u64);
    trust_vc::assert_by_bit_vector!((x >> 2u32) == x / 4u32);
}

#[trust_vc::ensures(true)]
fn mixed_width_shift_keeps_lhs_width_valid_subset() {
    let x: u32 = 0x8000_0000u32;
    let n: u64 = 1u64;
    trust_vc::assert_by_bit_vector!((x << n) == 0u32; requires x == 0x8000_0000u32, n == 1u64);
    trust_vc::assert_by_bit_vector!(
        (x >> n) == 0x4000_0000u32;
        requires x == 0x8000_0000u32, n == 1u64
    );
}

#[trust_vc::ensures(true)]
fn u16_shift_right_cast_valid_subset(y: u16) {
    trust_vc::assert_by_bit_vector!((y >> 2u32) == (((y as u32) >> 2u32) as u16));
    trust_vc::assert_by_bit_vector!((y >> 2u32) == (((y as i32) >> 2u32) as u16));
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(x <= 0xffffu32)]
fn u32_shift_right_matches_low_u16_when_bounded(x: u32) {
    trust_vc::assert_by_bit_vector!(
        ((x >> 2u32) as u16) == ((x as u16) >> 2u32);
        requires x <= 0xffffu32
    );
}

#[trust_vc::ensures(true)]
fn signed_shift_left_valid_subset(x: i32, z: i32) {
    trust_vc::assert_by_bit_vector!(
        !((x & (0xff00_0000u32 as i32)) == 0i32) || (x << 2u32) == (x * 4i32) as i32
    );
    trust_vc::assert_by_bit_vector!((x << 2u32) == (x * 4i32) as i32);
    trust_vc::assert_by_bit_vector!((x << 2u32) as u32 == (x as u32) << 2u32);
    trust_vc::assert_by_bit_vector!(!(z == 2i32) || (x << (z as u32)) == (x * 4i32) as i32);
}

#[trust_vc::ensures(true)]
fn signed_shift_right_valid_subset(x: i32, z: i32) {
    trust_vc::assert_by_bit_vector!(!((x & 0x3i32) == 0i32) || ((x >> 2u32) * 4i32) == x);
    trust_vc::assert_by_bit_vector!(
        !(z == 2i32) || !((x & 0x3i32) == 0i32) || ((x >> (z as u32)) * 4i32) == x
    );
}

#[trust_vc::ensures(true)]
fn signed_i16_shift_right_sign_extend_valid_subset(y: i16) {
    trust_vc::assert_by_bit_vector!(((y >> 2u32) as i32) == ((y as i32) >> 2u32));
}

#[trust_vc::ensures(true)]
fn let_bound_shift_valid_subset(x: i32, y: i16) {
    let z = y;
    trust_vc::assert_by_bit_vector!(!(x == (y as i32)) || (x >> 2u32) == ((z >> 2u32) as i32));
}

#[trust_vc::ensures(true)]
fn forall_shift_right_equal_width_subset() {
    trust_vc::assert_by_bit_vector!(forall(
        |x: u32, y: u32| !(x == y) || (x >> 2u32) == (y >> 2u32)
    ));
}

#[trust_vc::verifier(bit_vector)]
#[trust_vc::ensures(true)]
fn function_level_bit_vector_attribute_valid_subset(x: u32) {
    trust_vc::assert!(x & x == x);
    trust_vc::assert!((x ^ !x) == !0u32);
    trust_vc::assert!((x & 0xffu32) < 0x100u32);
}

#[trust_vc::ensures(true)]
fn recursive_bitvector_spec_compute_verified() {
    trust_vc::assert_by_compute!(recursive_shift_down(0x80u64, 3usize) == 0x10u64; compute_only);
}

#[trust_vc::ensures(true)]
fn bitvector_function_shaped_helpers(u: u32, v: u32) {
    trust_vc::assert_by_bit_vector!(shifter(42u32) == 21u32);
    trust_vc::assert_by_bit_vector!(bitand_alias(add(u, v), add(v, u)) == add(u, v));
}

#[trust_vc::ensures(true)]
fn signed_shift_amount_left_diagnostic(x: i32, y: i32) {
    trust_vc::assert_by_bit_vector!(x << y == x);
}

#[trust_vc::ensures(true)]
fn signed_shift_amount_right_diagnostic(x: i32, y: i32) {
    trust_vc::assert_by_bit_vector!(x >> y == x);
}

#[trust_vc::proof]
fn bitvector_decreases_by_check(_n: u64) {
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn bitvector_decreases_by_clause_currently_fail_closed() {
    trust_vc::decreases_by!(bitvector_decreases_by_check);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn b_or_b_greater_counterexample(b: u32) {
    trust_vc::assert_by_bit_vector!(b | b > b);
}

#[trust_vc::ensures(true)]
fn b_and_zero_positive_counterexample(b: u32) {
    trust_vc::assert_by_bit_vector!(b & 0u32 > 0u32);
}

#[trust_vc::ensures(true)]
fn wrapping_increment_identity_counterexample(b: u32) {
    trust_vc::assert_by_bit_vector!(add(b, 1u32) == b);
}

#[trust_vc::ensures(true)]
fn shift_roundtrip_counterexample(b: u32) {
    trust_vc::assert_by_bit_vector!((b << 2u32) >> 2u32 == b);
}

#[trust_vc::ensures(true)]
fn shift_left_wrong_multiplier_counterexample(b: u32) {
    trust_vc::assert_by_bit_vector!((b << 1u32) == mul(b, 2u32));
    trust_vc::assert!((b << 1u32) == mul(b, 4u32));
}

#[trust_vc::ensures(true)]
fn bitnot_constants_then_false_counterexample() {
    trust_vc::assert_by_bit_vector!(!0u32 == 0xffff_ffffu32);
    trust_vc::assert_by_bit_vector!(!0u64 == 0xffff_ffff_ffff_ffffu64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn clipping_cast_u32_to_u16_counterexample(a: u32) {
    trust_vc::assert_by_bit_vector!((a as u16 as u32) == a);
}

#[trust_vc::ensures(true)]
fn clipping_cast_i32_to_i16_counterexample(b: i32) {
    trust_vc::assert_by_bit_vector!((b as i16 as i32) == b);
}

#[trust_vc::ensures(true)]
fn cross_width_unsigned_ineq_counterexample() {
    let b: u8 = 5u8;
    trust_vc::assert_by_bit_vector!((b as u64) <= 3u64; requires b == 5u8);
}

#[trust_vc::ensures(true)]
fn mixed_signed_unsigned_eq_counterexample() {
    trust_vc::assert_by_bit_vector!(!(255u8 == (-1i8 as u8)) || (-1i8 as i16) == (255u8 as i16));
}

#[trust_vc::ensures(true)]
fn mixed_signed_unsigned_ineq_counterexample() {
    trust_vc::assert_by_bit_vector!(!((0u8 as i16) >= ((255u8 as i8) as i16)) || 0u8 >= 255u8);
}

#[trust_vc::ensures(true)]
fn mixed_u32_i32_comparison_counterexample() {
    trust_vc::assert_by_bit_vector!(
        !((2147483647u32 as i64) > (-1i32 as i64)) || 2147483647u32 > (-1i32 as u32)
    );
}

#[trust_vc::ensures(true)]
fn cross_width_bitnot_counterexample() {
    trust_vc::assert_by_bit_vector!(
        !((20u32 as u64) == 20u64)
            || ((0xffff_ffffu32 - 20u32) as u64) == (0xffff_ffff_ffff_ffffu64 - 20u64)
    );
    trust_vc::assert_by_bit_vector!(
        !(0u32 == (0i32 as u32)) || ((0xffff_ffffu32 - 0u32) as i64) == ((-1i32 - 0i32) as i64)
    );
}

#[trust_vc::ensures(true)]
fn mixed_width_or_and_xor_counterexample(x: u16, y: u16, z: i16) {
    trust_vc::assert_by_bit_vector!(((x | y) as i32) == ((x as i16 | y as i16) as i32));
    trust_vc::assert_by_bit_vector!(((x & y) as i32) == ((x as i16 & y as i16) as i32));
    trust_vc::assert_by_bit_vector!(((x as i32 | z as i32) as u16) == (x | z as u16));
}

#[trust_vc::ensures(true)]
fn i16_bitwise_unsigned_cast_counterexample() {
    trust_vc::assert_by_bit_vector!(
        (((-1i16) | 0i16) as int) == (((-1i16 as u32) | (0i16 as u32)) as int)
    );
}

#[trust_vc::ensures(true)]
fn mixed_width_shift_counterexample() {
    trust_vc::assert_by_bit_vector!(
        !(32768u32 == (32768u16 as u32))
            || ((32768u32 << 2u32) == ((((32768u16 as u32) * 4u32) as u16) as u32))
    );
}

#[trust_vc::ensures(true)]
fn mixed_width_shift_lhs_width_counterexample() {
    let x: u32 = 0x8000_0000u32;
    let n: u64 = 1u64;
    trust_vc::assert_by_bit_vector!(
        ((x << n) as u64) == 0x1_0000_0000u64;
        requires x == 0x8000_0000u32, n == 1u64
    );
}

#[trust_vc::ensures(true)]
fn u16_shift_right_low_byte_counterexample() {
    let y: u16 = 1024u16;
    trust_vc::assert_by_bit_vector!(
        (y >> 2u32) == (((((y as u32) >> 2u32) as u8) as u16));
        requires y == 1024u16
    );
}

#[trust_vc::ensures(true)]
fn u32_shift_right_low_u16_counterexample() {
    let x: u32 = 0x1_0000u32;
    trust_vc::assert_by_bit_vector!(
        ((x >> 2u32) as u16) == ((x as u16) >> 2u32);
        requires x == 0x1_0000u32
    );
}

#[trust_vc::ensures(true)]
fn signed_shift_left_width_counterexample() {
    trust_vc::assert_by_bit_vector!((32767i32 << 2u32) == -4i32);
}

#[trust_vc::ensures(true)]
fn signed_i16_shift_right_zero_extend_counterexample(y: i16) {
    trust_vc::assert_by_bit_vector!(((y >> 2u32) as u32) == ((y as u32) >> 2u32));
}

#[trust_vc::ensures(true)]
fn positive_shift_right_decreases_counterexample(n: u64) {
    trust_vc::assert_by_bit_vector!((n >> 1u64) < n);
}

#[trust_vc::ensures(true)]
fn casting_u16_to_u8_counterexample(x: u16) {
    trust_vc::assert_by_bit_vector!((x as u8 as u16) == x);
}

#[trust_vc::ensures(true)]
fn casting_i16_to_i8_counterexample(y: i16) {
    trust_vc::assert_by_bit_vector!((y as i8 as i16) == y);
}

#[trust_vc::ensures(true)]
fn verus_wrapping_free_function_counterexample(x: u32) {
    trust_vc::assert_by_bit_vector!(add(x, 1u32) > x);
}

#[trust_vc::ensures(true)]
fn quantified_shift_positive_counterexample_u64() {
    trust_vc::assert_by_bit_vector!(forall(|i: u64| (1u64 << i) > 0u64));
}

#[trust_vc::ensures(true)]
#[trust_vc::requires(y != 0u8)]
fn unsigned_div_rem_identity_counterexample_u8(x: u8, y: u8) {
    trust_vc::assert_by_bit_vector!(
        x.div_euclid(y) * y + x.rem_euclid(y) == 0u8;
        requires y != 0u8
    );
}

#[trust_vc::ensures(true)]
fn unsigned_div_rem_unit_divisor_counterexample_u16(x: u16) {
    trust_vc::assert_by_bit_vector!(x.div_euclid(1u16) == 0u16);
}

#[trust_vc::ensures(true)]
fn unsigned_division_zero_guard_missing_counterexample(y: u32) {
    trust_vc::assert_by_bit_vector!(0u32.div_euclid(y) == 0u32);
}

#[trust_vc::verifier(bit_vector)]
#[trust_vc::ensures(true)]
fn function_level_bit_vector_attribute_counterexample(x: u32) {
    trust_vc::assert!(x + 1u32 == x);
}

#[trust_vc::ensures(true)]
fn recursive_bitvector_spec_compute_counterexample() {
    trust_vc::assert_by_compute!(recursive_shift_down(0x80u64, 3usize) == 0x20u64; compute_only);
}

#[trust_vc::ensures(true)]
fn bitvector_mut_ref_deref_diagnostic(x: &mut u64, y: &mut u64) {
    trust_vc::assert_by_bit_vector!(!(*x == *y) || x == y);
}

#[trust_vc::ensures(true)]
fn bitvector_old_mut_ref_diagnostic(x: &mut u64) {
    trust_vc::assert_by_bit_vector!(*old(x) == *x);
}
