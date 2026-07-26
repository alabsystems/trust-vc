// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn fixed_native_array_length_is_available() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("[u8; 3]"));
    ctx.push_obligation(ProofObligation::assert(
        "array_len_fixed",
        "a.view().len() == 3usize",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fixed native array length should be tracked");
}

#[test]
fn fixed_native_array_wrong_length_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("[u8; 3]"));
    ctx.push_obligation(ProofObligation::assert(
        "array_len_wrong",
        "a.view().len() == 4usize",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "wrong fixed native array length should not verify");
}

#[test]
fn native_array_index_uses_element_type_and_bounds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("[u8; 3]"));
    ctx.push_obligation(ProofObligation::assume(
        "array_index_value",
        "a[1usize] == 9u8",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "array_index_value_again",
        "a.view().index(1usize) == 9u8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "native array indexing should use Seq-like element semantics",
    );
}

#[test]
fn array_to_slice_view_len_and_index_tracks_alias() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ar", crate::ir::TrustVcType::parse_or_opaque("[u8; 3]"));
    ctx.declare_var_typed("sl", crate::ir::TrustVcType::parse_or_opaque("[u8]"));
    ctx.push_obligation(ProofObligation::assume("array_slice_alias", "sl == ar"));
    ctx.push_obligation(ProofObligation::assume(
        "array_index_value",
        "ar[1usize] == 9u8",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "slice_len_from_array",
        "sl.view().len() == 3usize",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "slice_index_from_array",
        "sl.view().index(1usize) == 9u8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "array-to-slice view should preserve fixed length and index facts",
    );
}

#[test]
fn array_to_slice_view_wrong_index_value_not_verified() {
    // SOUNDNESS (no false Verified): the alias congruence is EXACT. With
    // sl == ar and ar[1] == 9, the true element value is 9, so asserting
    // sl.view().index(1) == 8 (a WRONG value) must NOT verify — the ground seed
    // yields sl[1] == ar[1] == 9, which contradicts == 8. ay surfaces this as a
    // model-less Unknown rather than a concrete counterexample (its model
    // validator cannot evaluate the extensional-equality forall + array selects;
    // the same Unknown-not-Counterexample shows even for a plain unconstrained
    // fixed-array element, see `non_aliased_slice_does_not_propagate_array_element`),
    // but the critical property — never a false Verified — holds.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ar", crate::ir::TrustVcType::parse_or_opaque("[u8; 3]"));
    ctx.declare_var_typed("sl", crate::ir::TrustVcType::parse_or_opaque("[u8]"));
    ctx.push_obligation(ProofObligation::assume("array_slice_alias", "sl == ar"));
    ctx.push_obligation(ProofObligation::assume(
        "array_index_value",
        "ar[1usize] == 9u8",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "slice_index_wrong_value",
        "sl.view().index(1usize) == 8u8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(
        &result,
        "array-to-slice alias must reject a wrong element value (exact congruence)",
    );
}

#[test]
fn array_to_slice_view_unknown_index_value_not_spuriously_verified() {
    // SOUNDNESS: a DIFFERENT index whose value is not known must NOT be
    // spuriously verified. ar[1] == 9 says nothing about ar[2], so asserting a
    // concrete value for sl.view().index(2) must not verify. (The propagation
    // gives sl[2] == ar[2], but ar[2] is unconstrained.)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ar", crate::ir::TrustVcType::parse_or_opaque("[u8; 3]"));
    ctx.declare_var_typed("sl", crate::ir::TrustVcType::parse_or_opaque("[u8]"));
    ctx.push_obligation(ProofObligation::assume("array_slice_alias", "sl == ar"));
    ctx.push_obligation(ProofObligation::assume(
        "array_index_value",
        "ar[1usize] == 9u8",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "slice_index_unknown_value",
        "sl.view().index(2usize) == 9u8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(
        &result,
        "array-to-slice alias must not invent a value for an unconstrained index",
    );
}

#[test]
fn array_to_slice_view_cross_index_congruence_holds() {
    // SOUNDNESS (positive): even without a concrete value, the alias still
    // entails the pointwise congruence sl@.index(i) == ar[i] for an in-bounds i.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ar", crate::ir::TrustVcType::parse_or_opaque("[u8; 3]"));
    ctx.declare_var_typed("sl", crate::ir::TrustVcType::parse_or_opaque("[u8]"));
    ctx.push_obligation(ProofObligation::assume("array_slice_alias", "sl == ar"));
    ctx.push_obligation(ProofObligation::assert(
        "slice_index_equals_array_index",
        "sl.view().index(2usize) == ar[2usize]",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "array-to-slice alias should entail pointwise element congruence",
    );
}

#[test]
fn non_aliased_slice_does_not_propagate_array_element() {
    // SOUNDNESS: the propagation must NOT fire for a slice that does NOT alias
    // the array. Here sl and ar are independent (no sl == ar assumption), so
    // ar[1] == 9 says nothing about sl[1]; asserting sl.view().index(1) == 9
    // must not verify.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ar", crate::ir::TrustVcType::parse_or_opaque("[u8; 3]"));
    ctx.declare_var_typed("sl", crate::ir::TrustVcType::parse_or_opaque("[u8; 3]"));
    ctx.push_obligation(ProofObligation::assume(
        "array_index_value",
        "ar[1usize] == 9u8",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "slice_index_no_alias",
        "sl.view().index(1usize) == 9u8",
    ));
    let result = AYEncoder::verify(&ctx);
    // No `sl == ar`, so `encode_seq_extensional_eq` is never reached and no
    // element-agreement seed is emitted: sl[1] is unconstrained, so the goal
    // must NOT verify. (This path does not touch the alias fix at all; ay
    // surfaces the undischargeable goal as Unknown rather than a concrete
    // counterexample, the same as any unconstrained symbolic array element.)
    expect_not_verified(
        &result,
        "element propagation must not fire without an aliasing equality",
    );
}

#[test]
fn array_to_slice_view_wrong_len_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ar", crate::ir::TrustVcType::parse_or_opaque("[u8; 3]"));
    ctx.declare_var_typed("sl", crate::ir::TrustVcType::parse_or_opaque("[u8]"));
    ctx.push_obligation(ProofObligation::assume("array_slice_alias", "sl == ar"));
    ctx.push_obligation(ProofObligation::assert(
        "slice_len_wrong",
        "sl.view().len() == 4usize",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "array-to-slice view must not accept wrong fixed length",
    );
}

#[test]
fn array_literal_inequality_uses_element_values() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "array_literal_neq",
        "[10u8, 20u8, 30u8] != [10u8, 20u8, 40u8]",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "array_literal_view_neq",
        "[10u8, 20u8, 30u8].view() != [10u8, 20u8, 40u8].view()",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "array literal inequality should compare finite element values",
    );
}

#[test]
fn array_literal_wrong_equality_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "array_literal_wrong_eq",
        "[10u8, 20u8, 30u8].view() == [10u8, 20u8, 40u8].view()",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "array literal equality must reject differing element values",
    );
}

#[test]
fn array_literal_view_to_seq_conversion_indexes_elements() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "array_literal_as_seq_len",
        "([10u8, 20u8, 30u8].view() as Seq<u8>).len() == 3usize",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "array_literal_as_seq_index",
        "([10u8, 20u8, 30u8].view() as Seq<u8>).index(2usize) == 30u8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "array literal view should support explicit Seq conversion",
    );
}

#[test]
fn nested_fixed_array_literal_reads_inner_elements() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "nested_array_literal_read",
        "{ let x: [[u64; 2]; 2] = [[0u64, 1u64], [2u64, 3u64]]; x[1usize][0usize] == 2u64 && x[0usize][1usize] == 1u64 }",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nested fixed-array literal reads should preserve inner array length and element values",
    );
}

#[test]
fn nested_fixed_array_literal_wrong_inner_element_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "nested_array_literal_wrong_read",
        "{ let x: [[u64; 2]; 2] = [[0u64, 1u64], [2u64, 3u64]]; x[1usize][0usize] == 3u64 }",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "nested fixed-array literal reads must reject wrong inner element values",
    );
}

#[test]
fn array_literal_wrong_index_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "array_literal_wrong_index",
        "[10u8, 20u8, 30u8].view().index(2usize) == 40u8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "array literal view indexing must reject wrong element values",
    );
}

#[test]
fn array_literal_view_contains_unrolls_elements() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "array_literal_view_contains_value",
        "[10u8, 20u8, 30u8].view().contains(20u8)",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "array_literal_view_does_not_contain_missing_value",
        "![10u8, 20u8, 30u8].view().contains(40u8)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "array literal view contains should range over finite literal elements",
    );
}

#[test]
fn array_literal_view_wrong_contains_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "array_literal_view_wrong_contains",
        "[10u8, 20u8, 30u8].view().contains(40u8)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "array literal view contains must reject missing literal elements",
    );
}

#[test]
fn named_array_view_contains_unrolls_elements() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "named_array_view_contains_value",
        "{ let a: [u8; 3] = [10u8, 20u8, 30u8]; a.view().contains(30u8) }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "named_array_view_does_not_contain_missing_value",
        "!{ let a: [u8; 3] = [10u8, 20u8, 40u8]; a.view().contains(30u8) }",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "named array view contains should range over fixed array elements",
    );
}

#[test]
fn named_array_view_wrong_contains_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "named_array_view_wrong_contains",
        "{ let a: [u8; 3] = [10u8, 20u8, 40u8]; a.view().contains(30u8) }",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "named array view contains must reject missing fixed array elements",
    );
}

#[test]
fn array_literal_view_seq_binding_contains_unrolls_elements() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "array_literal_view_seq_binding_contains_value",
        "{ let s: Seq<u8> = [10u8, 20u8, 30u8].view(); s.contains(30u8) }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "array_literal_view_seq_binding_does_not_contain_missing_value",
        "!{ let s: Seq<u8> = [10u8, 20u8, 30u8].view(); s.contains(40u8) }",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq binding from array literal view should preserve finite contains semantics",
    );
}

#[test]
fn array_literal_view_seq_binding_wrong_contains_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "array_literal_view_seq_binding_wrong_contains",
        "{ let s: Seq<u8> = [10u8, 20u8, 30u8].view(); s.contains(40u8) }",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Seq binding from array literal view must reject missing elements",
    );
}

#[test]
fn fixed_native_array_contains_uses_element_semantics() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("[u8; 3]"));
    ctx.push_obligation(ProofObligation::assume(
        "array_index_value",
        "a[1usize] == 9u8",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "array_contains_value",
        "a.contains(9u8)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "native array contains should range over fixed array elements",
    );
}

#[test]
fn fixed_native_array_first_uses_index_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("[u8; 3]"));
    ctx.push_obligation(ProofObligation::assume(
        "array_first_value",
        "a[0usize] == 7u8",
    ));
    ctx.push_obligation(ProofObligation::assert("array_first", "a.first() == 7u8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "native array first() should read index 0");
}

#[test]
fn fixed_native_array_last_uses_final_index() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("[u8; 3]"));
    ctx.push_obligation(ProofObligation::assume(
        "array_last_value",
        "a[2usize] == 8u8",
    ));
    ctx.push_obligation(ProofObligation::assert("array_last", "a.last() == 8u8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "native array last() should read len - 1");
}

#[test]
fn zero_length_native_array_first_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("[u8; 0]"));
    ctx.push_obligation(ProofObligation::assert(
        "array_first_empty",
        "a.first() == a.first()",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "native array first() requires a nonempty array");
}

#[test]
fn zero_length_native_array_last_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("[u8; 0]"));
    ctx.push_obligation(ProofObligation::assert(
        "array_last_empty",
        "a.last() == a.last()",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "native array last() requires a nonempty array");
}

#[test]
fn index_within_length() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_typed("len", u32_ty());
    ctx.declare_var_typed("idx", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_ten", "len == 10"));
    ctx.push_obligation(ProofObligation::assume("idx_in_bounds", "idx < len"));
    ctx.push_obligation(ProofObligation::assert("idx_lt_ten", "idx < 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "idx < len with len == 10 should imply idx < 10");
}

#[test]
fn index_plus_one_within_length() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_typed("len", u32_ty());
    ctx.declare_var_typed("idx", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_ten", "len == 10"));
    // Guard against BV wrapping: idx must be small enough that idx+1 doesn't wrap.
    ctx.push_obligation(ProofObligation::assume("idx_bounded", "idx < 4294967295"));
    ctx.push_obligation(ProofObligation::assume(
        "idx_plus_one_in_bounds",
        "idx + 1 < len",
    ));
    ctx.push_obligation(ProofObligation::assert("idx_lt_ten", "idx < 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "idx + 1 < len with len == 10 and no wrapping should keep idx below 10",
    );
}

#[test]
fn zero_always_valid_index() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_typed("len", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_positive", "len > 0"));
    ctx.push_obligation(ProofObligation::assert("zero_in_bounds", "0 < len"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a positive length should admit index zero");
}

#[test]
fn last_index_valid() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_typed("len", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_five", "len == 5"));
    ctx.push_obligation(ProofObligation::assert("last_index", "len - 1 == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "len - 1 should equal 4 when len == 5");
}

#[test]
fn midpoint_within_bounds() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_typed("len", u32_ty());
    ctx.declare_var_typed("mid", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_hundred", "len == 100"));
    ctx.push_obligation(ProofObligation::assume("mid_def", "mid == len / 2"));
    ctx.push_obligation(ProofObligation::assert("mid_in_bounds", "mid < len"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "len / 2 should stay within len for len == 100");
}

#[test]
fn two_indices_ordered() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_typed("i", u32_ty());
    ctx.declare_var_typed("j", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ordered", "i < j && j < 10"));
    ctx.push_obligation(ProofObligation::assert("i_lt_ten", "i < 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i < j && j < 10 should imply i < 10");
}

#[test]
fn index_after_push() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_typed("old_len", u32_ty());
    ctx.declare_var_typed("new_len", u32_ty());
    ctx.push_obligation(ProofObligation::assume("old_len_five", "old_len == 5"));
    ctx.push_obligation(ProofObligation::assume("new_len_six", "new_len == 6"));
    ctx.push_obligation(ProofObligation::assert("len_grows", "old_len < new_len"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pushing should increase the length from 5 to 6");
}

#[test]
fn binary_search_midpoint() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_typed("lo", u32_ty());
    ctx.declare_var_typed("hi", u32_ty());
    ctx.declare_var_typed("mid", u32_ty());
    ctx.push_obligation(ProofObligation::assume("lo_zero", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_hundred", "hi == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "mid_def",
        "mid == lo + (hi - lo) / 2",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mid_ordered",
        "mid >= lo && mid <= hi",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "binary-search midpoint should stay between lo and hi",
    );
}

#[test]
fn index_subtraction_valid() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_typed("len", u32_ty());
    ctx.declare_var_typed("idx", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_ten", "len == 10"));
    ctx.push_obligation(ProofObligation::assume("idx_seven", "idx == 7"));
    ctx.push_obligation(ProofObligation::assert("remaining", "len - idx == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 - 7 should equal 3 for an in-bounds index");
}

#[test]
fn double_index_within_double_length() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_typed("len", u32_ty());
    ctx.declare_var_typed("idx", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounded_len_and_idx",
        "len > 0 && len <= 50 && idx < len",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "scaled_bounds",
        "idx * 2 < len * 2",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "doubling both sides should preserve strict index bounds",
    );
}
