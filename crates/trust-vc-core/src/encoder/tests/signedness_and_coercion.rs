//! Regression tests for signedness semantics (#1769) and BV width coercion (#1768).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// #1769: Mixed signed/unsigned operands — AND semantics (both must be unsigned)
// ========================================================================

/// Mixed-sign comparison: AND semantics defaults to signed, giving correct result.
/// Before fix (OR semantics): i32(-1) < u32(1) used bvult, treating -1 as
/// 0xFFFFFFFF > 1 → false (WRONG).
/// After fix (AND semantics): mixed types default to signed comparison,
/// so bvslt(-1, 1) → true (CORRECT).
#[test]
fn test_mixed_signedness_defaults_to_signed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_neg", "x == -1"));
    ctx.push_obligation(ProofObligation::assume("y_pos", "y == 1"));
    ctx.push_obligation(ProofObligation::assert("mixed_cmp", "x < y"));

    let result = AYEncoder::verify(&ctx);
    // With AND semantics, mixed i32/u32 defaults to signed comparison (bvslt).
    // bvslt(-1, 1) = true, so this should verify.
    // Previously with OR semantics, bvult(0xFFFFFFFF, 1) = false (WRONG).
    expect_verified(&result, "Mixed i32/u32 comparison should use signed semantics (#1769) — bvslt(-1, 1) should be true");
}

/// Same-sign comparison (both signed) should still work correctly.
#[test]
fn test_same_signed_comparison_works() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -1"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 1"));
    ctx.push_obligation(ProofObligation::assert("signed_cmp", "x < y"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Same-sign (i32/i32) comparison should verify");
}

/// Same-sign comparison (both unsigned) should still work correctly.
#[test]
fn test_same_unsigned_comparison_works() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 2"));
    ctx.push_obligation(ProofObligation::assert("unsigned_cmp", "x < y"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Same-sign (u32/u32) comparison should verify");
}

// ========================================================================
// #1768: ITE/match branch BV width coercion
// ========================================================================

/// If-else branches with different BV widths should be width-coerced.
/// Before fix: ay sort mismatch panic → caught as Unknown.
/// After fix: branches coerced to matching width, verification succeeds.
#[test]
fn test_if_else_different_width_branches() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("flag", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 10"));
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    // flag > 0 selects the u8 branch (x=5), which must be zero-extended
    // to match the u32 branch width before ay ITE construction.
    ctx.push_obligation(ProofObligation::assert(
        "ite_check",
        "if flag > 0 { x } else { y } == 5",
    ));

    let result = AYEncoder::verify(&ctx);
    // After fix: should verify (flag>0 is true, x is 5, zero-extended to u32)
    // Before fix: would return Unknown from ay sort mismatch
    expect_verified(
        &result,
        "if-else with different-width branches should verify after coercion (#1768)",
    );
}

/// Match arms with different BV widths should be width-coerced.
#[test]
fn test_match_different_width_arms() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("small", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.declare_var_typed("big", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(ProofObligation::assume("small_val", "small == 10"));
    ctx.push_obligation(ProofObligation::assume("big_val", "big == 20"));
    // match x { 1 => small, _ => big } — u8 and u32 arms need width coercion.
    // The u8 arm (small=10) is zero-extended to u32 before the ITE.
    ctx.push_obligation(ProofObligation::assert(
        "match_check",
        "match x { 1 => small, _ => big } == 10",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "match with different-width arms should verify after coercion (#1768)",
    );
}

// ========================================================================
// #1954: Integer literal suffix handling — width/signedness from suffix
// ========================================================================

/// REGRESSION (#1954): `42u8` suffix must produce BV8, not context-inferred BV32.
/// Without suffix handling, both `42u8` and `42` produce BV32 when context
/// variables are i32/u32, requiring width coercion that loses the user's intent.
#[test]
fn test_u8_suffix_produces_narrow_bv() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    // 200u8 is valid as unsigned (0xC8) but overflows signed i8 range.
    // With suffix: BV8 unsigned, value 200. Without: BV32 signed (wrong width).
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 200u8"));
    // x > 100 should verify: 200 > 100 in unsigned BV8.
    ctx.push_obligation(ProofObligation::assert("check", "x > 100u8"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u8 suffix should produce correct BV8 width (#1954)",
    );
}

/// REGRESSION (#1954): `42u64` must produce BV64, not narrower BV32.
/// When no u64 variables are in scope, `infer_int_width()` returns 32.
/// The suffix must override this to prevent silent truncation.
#[test]
fn test_u64_suffix_overrides_infer_width() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    // 5_000_000_000 exceeds u32 range. With suffix: BV64. Without: widened
    // from BV32 to BV64 by fits_in_bv check — but signedness would default
    // to signed (incorrect for u64 suffix).
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5000000000u64"));
    ctx.push_obligation(ProofObligation::assert("check", "x > 4000000000u64"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u64 suffix should produce BV64 with unsigned signedness (#1954)",
    );
}

/// REGRESSION (#1954): `42i32` vs `42u32` must produce different signedness.
/// Before fix: both produced (32, true) — signed. After fix: u32 suffix
/// produces (32, false) — unsigned.
#[test]
fn test_signed_vs_unsigned_suffix_distinction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    // -1i32 reinterpreted as u32 is 4294967295 (0xFFFFFFFF).
    // This test verifies that unsigned suffix comparison uses bvult, not bvslt.
    // With correct signedness from suffix: x < 4294967295u32 in unsigned
    // BV32 is satisfiable for most x values.
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0u32"));
    ctx.push_obligation(ProofObligation::assert("unsigned_cmp", "x < 4294967295u32"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u32 suffix should mark literal as unsigned for correct comparison (#1954)",
    );
}

// ========================================================================
// #2068: Unsigned comparison with unsuffixed integer literals
// ========================================================================

/// REGRESSION (#2068): `u32 x >= 0` must verify — tautology for unsigned.
///
/// Before fix: unsuffixed `0` lowered as `Int{32}` (signed), AND semantics
/// made both operands "signed", selecting `bvsge`. Values near u32::MAX
/// interpreted as negative → spurious counterexample.
/// After fix: literal coerced to `Uint{32}` at lowering, `encode_compare`
/// reads IR types directly → `bvuge` selected → tautology verified.
#[test]
fn test_u32_ge_unsuffixed_zero_is_tautology() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assert("nonneg", "x >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u32 x >= 0 is a tautology (unsigned can never be < 0)",
    );
}

/// REGRESSION (#2068): `u8 x > 0` with x == 255 must verify.
///
/// Before fix: `0` defaulted to Int{32} (signed), AND semantics → signed
/// comparison. 255 in signed BV8 is -1, so `bvsgt(-1, 0)` = false → wrong.
/// After fix: literal coerced to Uint{8}, `bvugt(255, 0)` = true → correct.
#[test]
fn test_u8_gt_unsuffixed_zero_with_max_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_is_max", "x == 255"));
    ctx.push_obligation(ProofObligation::assert("positive", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u8(255) > 0 should verify with unsigned comparison (#2068)",
    );
}

/// REGRESSION (#2068): `u64 x <= 100` with x == 50 must verify.
///
/// Tests unsigned comparison with unsuffixed literal on the right side
/// for a different width (u64) and a different operator (<=).
#[test]
fn test_u64_le_unsuffixed_literal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 50"));
    ctx.push_obligation(ProofObligation::assert("bounded", "x <= 100"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u64(50) <= 100 should verify with unsigned comparison (#2068)",
    );
}

/// DISCRIMINATING (#2068): `i32 x >= 0` must NOT verify — signed can be negative.
///
/// This is the discriminating counterpart: if the fix incorrectly made ALL
/// comparisons unsigned, this would pass when it should fail.
#[test]
fn test_i32_ge_zero_does_not_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("nonneg", "x >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "i32 x >= 0 should produce counterexample (x can be negative)",
    );
}

/// DISCRIMINATING (#2068): Mixed `u32 x > i32 y` still uses signed comparison.
///
/// AND semantics (#1769): mixed signedness defaults to signed. This ensures
/// the #2068 fix (literal coercion) doesn't break mixed-type comparisons.
/// With signed comparison: -1 < 1 is true. With unsigned: 0xFFFFFFFF > 1 (wrong).
#[test]
fn test_mixed_u32_i32_comparison_stays_signed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_neg", "x == -1"));
    ctx.push_obligation(ProofObligation::assume("y_pos", "y == 1"));
    ctx.push_obligation(ProofObligation::assert("signed_cmp", "x < y"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Mixed i32/u32 comparison must stay signed (#1769 AND semantics)",
    );
}

// ========================================================================
// #2084: coerce_to_len_width — narrow BV widths in collection operations
// ========================================================================

/// REGRESSION: Seq::take(n) where n is u8 must not produce sort mismatch.
///
/// coerce_to_len_width (collection_shared.rs) widens 8-bit terms to
/// pointer_width before the bvule comparison against collection length.
/// Before fix (20f9ea04), only widths 32 and 64 were handled; 8/16/128
/// passed through unchanged, causing ay sort mismatch errors.
#[test]
fn test_2084_seq_take_u8_no_sort_mismatch() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 10"));
    ctx.push_obligation(ProofObligation::assume("n_bound", "n <= 5"));
    ctx.push_obligation(ProofObligation::assert("take_u8", "s.take(n).len() == n"));

    let result = AYEncoder::verify(&ctx);
    // Under native-seq, ay-dpll's Seq theory reports (incomplete quantifier-unhandled)
    // for overflow checks involving bv2int coercion + Seq operations. The encoding
    // is correct; the solver capability is the limit. Part of #2680.
    #[cfg(feature = "native-seq")]
    expect_verified_or_unknown(
        &result,
        "#2680: native-seq take(u8) overflow check may exceed solver capability",
    );
    #[cfg(not(feature = "native-seq"))]
    expect_verified(
        &result,
        "Seq::take(u8) must coerce to pointer width without sort mismatch (#2084)",
    );
}

/// REGRESSION: Seq::skip(n) where n is u16 must not produce sort mismatch.
#[test]
fn test_2084_seq_skip_u16_no_sort_mismatch() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u16"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 10"));
    ctx.push_obligation(ProofObligation::assume("n_bound", "n <= 3"));
    ctx.push_obligation(ProofObligation::assert(
        "skip_u16",
        "s.skip(n).len() == s.len() - n",
    ));

    let result = AYEncoder::verify(&ctx);
    #[cfg(feature = "native-seq")]
    expect_verified_or_unknown(
        &result,
        "#2680: native-seq skip(u16) overflow check may exceed solver capability",
    );
    #[cfg(not(feature = "native-seq"))]
    expect_verified(
        &result,
        "Seq::skip(u16) must coerce to pointer width without sort mismatch (#2084)",
    );
}

// ========================================================================
// coerce_to_len_width — Sort::Int passthrough in quantifier bodies
// ========================================================================

/// REGRESSION: Seq::take() with an exists-quantifier-bound variable must
/// convert Sort::Int index to BitVec(pointer_width) via int2bv. Exists
/// quantifiers are never Skolemized (only Forall is), so bound vars always
/// get Sort::Int sort. Without the coerce_to_len_width fix, the Int-typed
/// variable passes through unchanged, causing sort mismatch at try_bvule.
#[test]
fn test_seq_take_in_exists_body_int_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assume("elem2", "s.index(2) == 42"));
    // exists n: u64. n < 5 && s.take(n).len() == n
    // TRUE: n=3 satisfies (take(3).len() == 3).
    // Exists bound var n has Sort::Int; take(n) needs int2bv for len comparison.
    ctx.push_obligation(ProofObligation::assert(
        "take_exists",
        "exists(|n: u64| n < 5 && s.take(n).len() == n)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_encodes_without_error(
        &result,
        "Seq::take() in exists body must not produce sort mismatch error",
    );
}

/// DISCRIMINATING: Seq::take() in exists with impossible property must NOT verify.
#[test]
fn test_seq_take_in_exists_body_false_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    // exists n: u64. n <= 5 && s.take(n).len() > 5
    // FALSE: take(n).len() == n, so take(n).len() can be at most 5, never > 5.
    ctx.push_obligation(ProofObligation::assert(
        "take_false_exists",
        "exists(|n: u64| n <= 5 && s.take(n).len() > 5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "Impossible take() in exists should NOT verify");
}

// ========================================================================
// Seq::subrange bounds check — mixed BV/Int operands (Route A #2779)
// ========================================================================

/// REGRESSION (vec.rs insert/remove/append/swap_remove models): a
/// length-derived subrange bound (`s.len()`) stays Sort::Int under Route A
/// and `coerce_to_len_width` passes it through outside quantifier bodies.
/// The `start <= end` bounds check used a raw `bvule`, constructing an
/// ill-sorted term (`BitVec(64)` vs `Int`) that ay correctly rejects,
/// failing the whole obligation with a SolverPanic Unknown. The mixed-sort
/// comparison must lift the BV side to Int (exact) instead.
#[test]
fn test_seq_subrange_int_len_end_bound_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "sub_len",
        "s.subrange(1usize, s.len()).len() == 2",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq::subrange with a Sort::Int length-derived end bound must not \
         produce an ill-sorted bvule (BV64 vs Int)",
    );
}

/// DISCRIMINATING negative: the mixed-sort `start <= end` check must still
/// BITE. With `s.len() == 0`, `s.subrange(1, s.len())` violates
/// `start <= end` (1 <= 0 is false in exact Int semantics), so the claim
/// must NOT verify. A wrapping `int2bv` lowering of the Int bound could
/// have masked this; the exact `bv2int` lift refutes it.
#[test]
fn test_seq_subrange_int_len_end_bound_violated_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "sub_len_bad",
        "s.subrange(1usize, s.len()).len() == 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Seq::subrange(1, len) with len == 0 violates start <= end and must NOT verify",
    );
}

// ========================================================================
// NC4 class: huge-length (>= 2^64) Int -> BV carrier-index crossings
// (aa97668 adversarial-review follow-up). A spec Seq length is unbounded
// Int; the Array(BV(pw), T) carrier index is BV(pw). `len_as_index_bv` /
// `coerce_seq_index` lower a length-derived Int index via a WRAPPING
// `int2bv`, so with an assumed `len == 2^64 + 2` the true-semantics read
// of s[2^64] (unconstrained) would alias the carrier cell of s[0] if the
// solver ever constant-folds `int2bv` over bigints — a wrong-verify.
// These pins assert the verdict is NEVER Verified for the huge-len
// regime, so any future ay folding improvement trips them loudly. The
// representability obligation (`0 <= idx <= 2^pw - 1` at the crossing)
// makes them honest counterexamples rather than luck-based Unknowns.
// ========================================================================

/// `s.len() == 2^64 + 2`, constructed with pure spec (Int) arithmetic so no
/// fixed-width literal overflow is involved. Stated as subtractions from the
/// symbolic (Int-sorted) length — `len - i64::MAX - i64::MAX == 4` — because
/// a literal-literal sum (`i64::MAX + i64::MAX + 4`) is constant-folded with
/// wrapping i64 semantics by the string-expression harness and would pin
/// `len == 2` instead. Each subtraction has a non-literal LHS, so it stays a
/// symbolic Int term and the assumption genuinely pins `len == 2^64 + 2`
/// (probed: `s.len() > i64::MAX` verifies under this assumption).
const HUGE_SEQ_LEN_ASSUME: &str = "s.len() - 9223372036854775807 - 9223372036854775807 == 4";

/// The failure must be pinned on the carrier-representability obligation
/// pushed at the Int -> BV(pw) crossing (`push_index_representability_check`)
/// — an HONEST labelled failure, not a luck-based Unknown from ay's current
/// inability to fold `int2bv` over bigints. Accepts either a labelled
/// Unknown (today: the refutation query still carries the cross-theory
/// `int2bv` terms ay is incomplete on) or a labelled Counterexample (a
/// future ay that folds the bridge refutes the check outright); never
/// Verified and never an unlabelled failure.
#[track_caller]
fn expect_fails_on_carrier_representability(result: &VerifyResult, context: &str) {
    expect_not_verified(result, context);
    let message = match result {
        // Either inconclusive shape carries the pinned obligation text in
        // `reason`; the assertion below is what makes the failure honest.
        VerifyResult::NotProved { reason, .. } | VerifyResult::Unknown { reason, .. } => {
            reason.clone()
        }
        VerifyResult::Counterexample {
            obligation_name, ..
        } => obligation_name.clone(),
        VerifyResult::Error { message } => message.clone(),
        VerifyResult::Verified => unreachable!("expect_not_verified rejects Verified"),
    };
    assert!(
        message.contains("not representable in the BitVec"),
        "{context}: the failure must be pinned on the carrier-representability \
         obligation (honest labelled failure, not a luck-based Unknown), got: {message}"
    );
}

/// NC4: subrange whose Int `start` (= len - 2 = 2^64) crosses into the BV
/// carrier index via `len_as_index_bv` (encode_subrange shift offset). A
/// wrapping fold of `int2bv(2^64)` -> 0 would read the assumed `s[0] == 5`
/// instead of the unconstrained true-semantics `s[2^64]`, wrongly verifying
/// the claim. Must NOT verify — the representability obligation
/// (`start <= 2^pw - 1`) is genuinely violated here.
#[test]
fn test_seq_subrange_huge_len_start_crossing_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("huge_len", HUGE_SEQ_LEN_ASSUME));
    ctx.push_obligation(ProofObligation::assume("first_elem", "s.index(0) == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "nc4_subrange",
        "s.subrange(s.len() - 2, s.len()).index(0) == 5",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fails_on_carrier_representability(
        &result,
        "NC4: subrange(len-2, len).index(0) with len == 2^64 + 2 reads the \
         unconstrained s[2^64]; a wrapping int2bv fold of the start offset \
         would alias it to the assumed s[0]",
    );
}

/// NC4b twin: DIRECT indexing at the same huge-len regime — the class
/// predates the subrange fix and is shared with `coerce_seq_index`
/// (width_coercion.rs), which lowers a ground Int index via the same
/// wrapping `int2bv`. Must NOT verify.
#[test]
fn test_seq_direct_index_huge_len_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("huge_len", HUGE_SEQ_LEN_ASSUME));
    ctx.push_obligation(ProofObligation::assume("first_elem", "s.index(0) == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "nc4b_direct_index",
        "s.index(s.len() - 2) == 5",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fails_on_carrier_representability(
        &result,
        "NC4b: s.index(len - 2) with len == 2^64 + 2 reads the unconstrained \
         s[2^64]; a wrapping int2bv fold of the index would alias it to the \
         assumed s[0]",
    );
}

/// NC4c PUSH-THEN-INDEX-0 twin — the (c) guard for the same-index read-back
/// recognizer (`try_encode_push_same_index_readback`). `s.push(7)` at
/// `len == 2^64 + 2` stores the pushed value at the WRAPPED carrier cell
/// `int2bv(2^64 + 2)`; reading `index(0)` reads carrier cell `int2bv(0)`, a
/// DIFFERENT cell. The read-back recognizer MUST NOT fire here (the select
/// index `int2bv(0)` is not structurally the store index `int2bv(2^64 + 2)`),
/// so the store-side carrier-representability obligation stays queued and the
/// query fails closed. A recognizer that keyed on "a push happened recently"
/// (rather than strict index identity) would reuse the store cell and wrongly
/// prove `index(0) == 7` — the exact prior-attempt false-verify this pin
/// catches. Must NOT verify, at baseline AND after the recognizer landed.
#[test]
fn test_seq_push_then_index_zero_huge_len_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("huge_len", HUGE_SEQ_LEN_ASSUME));
    ctx.push_obligation(ProofObligation::assume("first_elem", "s.index(0) == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "nc4c_push_index_zero",
        "s.push(7).index(0) == 7",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fails_on_carrier_representability(
        &result,
        "NC4c: s.push(7).index(0) with len == 2^64 + 2 stores at the wrapped \
         cell int2bv(2^64 + 2) but reads carrier cell int2bv(0) — a DIFFERENT \
         cell; the same-index read-back recognizer must not fire, so the \
         store-side representability obligation keeps the query fail-closed",
    );
}

/// NC4d — the read-back RETRACTION-SCOPE guard. The same-index read-back
/// recognizer (`try_encode_push_same_index_readback`) drops the store-side
/// carrier-representability obligation for a push whose result is read back at
/// its own store index. This pin proves that scope does NOT leak to a DIFFERENT
/// index: a same-index readback (which fires the recognizer) followed by a read
/// of the SAME push term at the wrapped different index `old_len mod 2^64`
/// (== 2 when len == 2^64+2) must STAY fail-closed — the different-index read
/// re-emits its own representability obligation, so the wrapped carrier cell
/// int2bv(2^64+2) == int2bv(2) is NOT read as the pushed value without a guard.
/// (Spec: the push at index 2^64+2 does not change s[2], so `s.push(7)[2] == 7`
/// is false.) This is the exact residual-hole the read-back implementation
/// flagged; the pin confirms it is not exploitable. Must NOT verify.
#[test]
fn test_seq_readback_retract_then_wrapped_different_index_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("huge_len", HUGE_SEQ_LEN_ASSUME));
    ctx.push_obligation(ProofObligation::assume("orig_elem_2", "s.index(2) == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "readback_retract",
        "s.push(7).index(s.push(7).len() - 1) == 7",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "exploit",
        "s.push(7).index(2) == 7",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fails_on_carrier_representability(
        &result,
        "NC4d: a same-index read-back (which retracts the store-side \
         representability obligation) must NOT leak that scope to a wrapped \
         different-index read — s.push(7).index(2) at len == 2^64+2 targets the \
         wrapped store cell int2bv(2), but the different-index read re-emits its \
         own carrier-representability obligation, so it stays fail-closed and \
         never reads the pushed value without a guard",
    );
}

/// NC4 subrange-VIEW variant: the same huge-len start crossing through the
/// `encode_seq_view` subrange branch (compare_seq.rs) — a Seq equality whose
/// LHS view offset is the wrapped `int2bv(len - 2)`. Under a wrapping fold
/// both views alias byte-for-byte (start -> 0), wrongly proving
/// `s[2^64] == s[0]`. Must NOT verify.
#[test]
fn test_seq_subrange_view_eq_huge_len_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("huge_len", HUGE_SEQ_LEN_ASSUME));
    ctx.push_obligation(ProofObligation::assume("first_elem", "s.index(0) == 5"));
    ctx.push_obligation(ProofObligation::assume("second_elem", "s.index(1) == 6"));
    ctx.push_obligation(ProofObligation::assert(
        "nc4_subrange_view_eq",
        "s.subrange(s.len() - 2, s.len()) == s.subrange(0, 2)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fails_on_carrier_representability(
        &result,
        "NC4 view: subrange(len-2, len) == subrange(0, 2) with len == 2^64 + 2 \
         claims s[2^64] == s[0]; a wrapping int2bv fold of the view offset \
         would alias the two views",
    );
}

/// NC4c ASSUMPTION-side twin: the wrapped crossing sits inside an ASSUMED
/// fact instead of the goal. Overflow checks pushed while encoding an
/// assumption are dropped by the pipeline (only the assertion re-encode's
/// checks are solved), so the representability obligation cannot cover this
/// shape — this PIN is the coverage. Under a wrapping fold the assumption
/// `subrange(len-2, len).index(0) == 7` would seed `s[0] == 7` (aliased
/// carrier cell), wrongly proving the goal `s.index(0) == 7`; true
/// semantics constrain only the unconstrained `s[2^64]`. Any ay
/// bigint-int2bv folding improvement must trip this pin loudly.
#[test]
fn test_seq_assumption_side_huge_len_crossing_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("huge_len", HUGE_SEQ_LEN_ASSUME));
    ctx.push_obligation(ProofObligation::assume(
        "tail_elem",
        "s.subrange(s.len() - 2, s.len()).index(0) == 7",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "nc4c_aliased_cell",
        "s.index(0) == 7",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_not_verified(
        &result,
        "NC4c: an ASSUMED subrange fact at len == 2^64 + 2 constrains only the \
         true-semantics s[2^64]; a wrapping int2bv fold would alias it onto \
         s[0] and wrongly prove the goal",
    );
}

/// POSITIVE control for the representability guard: the same subrange-start
/// crossing shape with a REPRESENTABLE length must keep verifying — the
/// pushed `0 <= start <= 2^pw - 1` obligation discharges against
/// `len == 3` for free. Guards against over-restriction of ordinary
/// length-derived bounds.
#[test]
fn test_seq_subrange_int_start_crossing_representable_len_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "sub_len_from_int_start",
        "s.subrange(s.len() - 2, s.len()).len() == 2",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq::subrange with an Int length-derived start (len - 2) and a \
         representable len == 3 must stay Verified (representability \
         obligation discharges free)",
    );
}

// ========================================================================
// #2565: Match/ITE signedness merge uses declared type, not arm order
// ========================================================================

/// DISCRIMINATING (#2565): Match with mixed-signedness arms must record the
/// declared type's signedness, not the arm-order-dependent signedness.
///
/// Setup: 2-arm match where arm 1 body is i32 (signed) and arm 2 body is u32
/// (unsigned), with declared type Int{32} (signed). Before fix, the last
/// source-order arm processed first in reverse sets signedness — so arm 2 (u32)
/// wins and the result is tracked as unsigned. After fix, ty=Int{32} overrides
/// to signed.
#[test]
fn test_match_mixed_signedness_uses_declared_type() {
    use crate::ir::TrustVcType;
    use crate::ir_expr::{MatchArm, MatchPattern, TrustVcExpr};

    let signed_ty = i32_ty();
    let unsigned_ty = u32_ty();

    // Scrutinee: x: i32
    let x_var = TrustVcExpr::Var {
        name: "x".into(),
        ty: signed_ty.clone(),
    };

    // Arm 1 body: a (i32, signed)
    let a_var = TrustVcExpr::Var {
        name: "a".into(),
        ty: signed_ty.clone(),
    };

    // Arm 2 body (wildcard): b (u32, unsigned)
    let b_var = TrustVcExpr::Var {
        name: "b".into(),
        ty: unsigned_ty.clone(),
    };

    // match x { 1 => a, _ => b } with declared type Int{32} (signed)
    let match_expr = TrustVcExpr::Match {
        scrutinee: Box::new(x_var),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Lit(TrustVcExpr::IntLit {
                    value: 1,
                    ty: signed_ty.clone(),
                }),
                body: a_var,
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Wildcard,
                body: b_var,
                guard: None,
            },
        ],
        ty: TrustVcType::Int { width: 32 }, // declared type is signed
    };

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let a = solver.declare_const("a", Sort::bitvec(32));
    let b = solver.declare_const("b", Sort::bitvec(32));

    let mut variables = std::collections::HashMap::new();
    variables.insert("x".into(), x);
    variables.insert("a".into(), a);
    variables.insert("b".into(), b);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".into(), signed_ty.clone());
    var_types.insert("a".into(), signed_ty);
    var_types.insert("b".into(), unsigned_ty);
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    parser.term_widths.insert(x, (32, true)); // i32 signed
    parser.term_widths.insert(a, (32, true)); // i32 signed
    parser.term_widths.insert(b, (32, false)); // u32 unsigned

    let match_term = parser
        .encode_trust_vc_expr(&match_expr)
        .expect("encode_match should succeed");

    // The match result must be tracked as signed (from ty=Int{32}),
    // regardless of which arm was processed first.
    let &(width, signed) = parser
        .term_widths
        .get(&match_term)
        .expect("match result must have term_widths entry");
    assert_eq!(width, 32, "match result width should be 32");
    assert!(
        signed,
        "match result signedness should be true (signed) from declared type Int{{32}}, \
         not false (unsigned) from arm processing order (#2565)"
    );
}

/// DISCRIMINATING (#2565): ITE with mixed-signedness branches must record the
/// declared type's signedness, not the then-branch-first preference.
///
/// Setup: ITE where then-branch is u32 (unsigned) and else-branch is i32
/// (signed), with declared type Int{32} (signed). Before fix, then_coerced's
/// signedness always wins — so the result is tracked as unsigned. After fix,
/// ty=Int{32} overrides to signed.
#[test]
fn test_ite_mixed_signedness_uses_declared_type() {
    use crate::ir::TrustVcType;
    use crate::ir_expr::TrustVcExpr;

    let signed_ty = i32_ty();
    let unsigned_ty = u32_ty();

    // cond: flag (bool)
    let flag_var = TrustVcExpr::Var {
        name: "flag".into(),
        ty: TrustVcType::Bool,
    };

    // then: c (u32, unsigned)
    let c_var = TrustVcExpr::Var {
        name: "c".into(),
        ty: unsigned_ty.clone(),
    };

    // else: d (i32, signed)
    let d_var = TrustVcExpr::Var {
        name: "d".into(),
        ty: signed_ty.clone(),
    };

    // if flag { c } else { d } with declared type Int{32} (signed)
    let ite_expr = TrustVcExpr::Ite {
        cond: Box::new(flag_var),
        then_branch: Box::new(c_var),
        else_branch: Box::new(d_var),
        ty: TrustVcType::Int { width: 32 }, // declared type is signed
    };

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let flag = solver.declare_const("flag", Sort::Bool);
    let c = solver.declare_const("c", Sort::bitvec(32));
    let d = solver.declare_const("d", Sort::bitvec(32));

    let mut variables = std::collections::HashMap::new();
    variables.insert("flag".into(), flag);
    variables.insert("c".into(), c);
    variables.insert("d".into(), d);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("flag".into(), TrustVcType::Bool);
    var_types.insert("c".into(), unsigned_ty);
    var_types.insert("d".into(), signed_ty);
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    parser.term_widths.insert(c, (32, false)); // u32 unsigned
    parser.term_widths.insert(d, (32, true)); // i32 signed

    let ite_term = parser
        .encode_trust_vc_expr(&ite_expr)
        .expect("encode_ite should succeed");

    // The ITE result must be tracked as signed (from ty=Int{32}),
    // not unsigned (from then-branch preference).
    let &(width, signed) = parser
        .term_widths
        .get(&ite_term)
        .expect("ITE result must have term_widths entry");
    assert_eq!(width, 32, "ITE result width should be 32");
    assert!(
        signed,
        "ITE result signedness should be true (signed) from declared type Int{{32}}, \
         not false (unsigned) from then-branch preference (#2565)"
    );
}

// ========================================================================
// casts-bitvec: out-of-signed-range positive literal must NOT silently wrap
// ========================================================================
//
// A positive literal like `200` fits the UNSIGNED byte range `[0, 255]` but NOT
// the SIGNED `i8` range `[-128, 127]`. `encode_int_lit` previously picked the BV
// width with `fits_in_bv` (signed-OR-unsigned), so a SIGNED-typed `200` became
// the width-8 constant `0xC8` tagged signed (= `-56`), silently redefining the
// constraint and manufacturing false `Verified`s. The fix selects the width by
// the signedness-correct predicate and widens (value-preserving) when the value
// does not fit the signed range. These tests pin both directions through the
// full encode + solve path (`AYEncoder::verify`).

/// DISCRIMINATING: an out-of-signed-range literal in an INEQUALITY precondition
/// must not weaken the precondition. `requires(x < 200)` admits every `i8`, so
/// `assert!(x < 0)` is genuinely false (witness `x = 100`). Before the fix the
/// literal `200` wrapped to `-56`, turning the precondition into `x < -56` and
/// spuriously verifying.
#[test]
fn test_signed_literal_inequality_precondition_not_wrapped() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("x_lt", "x < 200"));
    ctx.push_obligation(ProofObligation::assert("neg", "x < 0"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "requires(x < 200) on i8 must NOT wrap 200 to -56; assert!(x < 0) is \
         genuinely false (x = 100 is a legal i8 with 100 < 200 and 100 >= 0)",
    );
}

/// DISCRIMINATING: a signed var pinned to `-56` must not be proved equal to the
/// out-of-signed-range literal `200` (they share the `0xC8` bit pattern only
/// under an unsound width-8 signed encoding).
#[test]
fn test_signed_var_not_equal_out_of_range_literal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == -56"));
    ctx.push_obligation(ProofObligation::assert("eq200", "x == 200"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "x == -56 must NOT prove x == 200 (200 does not fit signed i8)",
    );
}

/// CONTROL (no over-rejection): an in-signed-range literal precondition still
/// verifies a true goal. Every `x < 50` satisfies `x < 100`.
#[test]
fn test_signed_literal_in_range_precondition_still_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("x_lt", "x < 50"));
    ctx.push_obligation(ProofObligation::assert("lt100", "x < 100"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "in-range i8 precondition x < 50 should still verify x < 100 (no over-rejection)",
    );
}

/// CONTROL (no over-rejection): the same literal `200` against an UNSIGNED `u8`
/// var is legitimately in range and must keep verifying. `200 > 100` in u8.
#[test]
fn test_unsigned_literal_200_in_range_still_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 200"));
    ctx.push_obligation(ProofObligation::assert("gt", "x > 100"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "200 fits u8; x == 200 |- x > 100 must still verify (no over-rejection)",
    );
}
/// SANITY pin for the NC4 fixtures: `HUGE_SEQ_LEN_ASSUME` must genuinely pin
/// `s.len() > i64::MAX` (i.e. the string harness must NOT constant-fold the
/// arithmetic back into i64 range — a literal-literal sum form previously
/// folded with wrapping i64 semantics to `len == 2`, silently trivialising
/// the huge-len pins). If this test fails, the NC4 pins above are no longer
/// exercising the unrepresentable-length regime.
#[test]
fn test_huge_len_assume_genuinely_pins_huge_len() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("huge_len", HUGE_SEQ_LEN_ASSUME));
    ctx.push_obligation(ProofObligation::assert(
        "len_gt_i64max",
        "s.len() > 9223372036854775807",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "HUGE_SEQ_LEN_ASSUME must pin s.len() == 2^64 + 2 (> i64::MAX); a \
         harness constant-fold regression here would trivialise the NC4 pins",
    );

    let mut ctx2 = VerificationContext::new();
    ctx2.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx2.push_obligation(ProofObligation::assume("huge_len", HUGE_SEQ_LEN_ASSUME));
    ctx2.push_obligation(ProofObligation::assert("len_small", "s.len() < 100"));
    let result2 = AYEncoder::verify(&ctx2);
    expect_not_verified(
        &result2,
        "HUGE_SEQ_LEN_ASSUME pins a huge length, so s.len() < 100 must be refuted",
    );
}

// ========================================================================
// Vec/Seq length-boundedness: the Vec-only `usize` length bound.
//
// An exec `Vec`/slice/array has a `usize`-bounded length, so its length term
// gets `len <= 2^pointer_width - 1` asserted at declaration (gated on
// `VariableDecl::bounded_len`); that discharges the NC4 carrier-index
// representability side condition for length-derived index reads. A spec
// `Seq<T>` stays UNBOUNDED and gets NO such bound — the huge-length guards
// above depend on that boundary holding.
//
// The `bounded_len == true` decls below simulate the extraction seam's output
// for a `Vec<i32>`/`[i32]`/`[i32; N]` param: `parse_or_opaque` collapses the
// origin `Vec` to `TrustVcType::Seq`, and the seam threads `bounded_len = true`
// alongside (see `param_extract::syn_type_string_is_bounded_len_collection`).
// ========================================================================

/// POSITIVE: a bounded-len collection (exec `Vec`/slice/array origin, modeled as
/// `Seq` with `bounded_len == true`) with a SYMBOLIC length `>= 2` proves a
/// subrange whose Int start (`len - 2`) crosses to the BV carrier index. The
/// crossing pushes `start <= 2^pw - 1`, dischargeable ONLY by the Vec length
/// bound (`len <= 2^pw - 1`). The length is NOT pinned to a literal, so the
/// bound is LOAD-BEARING — contrast the unbounded-`Seq` control below (identical
/// shape, `bounded_len == false`), which stays fail-closed.
#[test]
fn test_bounded_vec_subrange_int_start_symbolic_len_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed_bounded(
        "v",
        crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"),
        true,
    );
    ctx.push_obligation(ProofObligation::assume("len_ge_2", "v.len() >= 2"));
    ctx.push_obligation(ProofObligation::assert(
        "sub_len_from_int_start",
        "v.subrange(v.len() - 2, v.len()).len() == 2",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "a bounded-len Vec (bounded_len == true) with symbolic len >= 2: the \
         subrange Int-start representability (start <= 2^pw-1) discharges against \
         the Vec length bound, so subrange width == 2 verifies",
    );
}

/// LOAD-BEARING CONTROL for the POSITIVE: the SAME shape over an UNBOUNDED spec
/// `Seq` (`bounded_len == false`). Without the Vec bound the symbolic
/// `len - 2 <= 2^pw-1` representability obligation is genuinely unprovable, so
/// the query fails closed on the carrier-representability check — the exact
/// obligation the Vec bound discharges in the POSITIVE. This is the toggle that
/// proves the bound is what does the work.
#[test]
fn test_unbounded_seq_subrange_int_start_symbolic_len_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len_ge_2", "s.len() >= 2"));
    ctx.push_obligation(ProofObligation::assert(
        "sub_len_from_int_start",
        "s.subrange(s.len() - 2, s.len()).len() == 2",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fails_on_carrier_representability(
        &result,
        "an UNBOUNDED spec Seq (bounded_len == false) with only symbolic len >= 2 \
         cannot discharge start <= 2^pw-1, so the subrange Int-start crossing \
         stays fail-closed — proving the Vec bound in the POSITIVE is load-bearing",
    );
}

/// SPEC-SEQ NON-LEAK probe: an unbounded spec `Seq` at a HUGE length
/// (`len == 2^64 + 2`) must NOT admit `len <= usize::MAX`. If the Vec length
/// bound ever leaked to a `Seq`, that `Seq`'s context would become UNSAT (the
/// bound contradicts the huge len) and this goal would VACUOUSLY verify — the
/// precise poison the Vec-only boundary forbids. Must stay not-verified.
#[test]
fn test_unbounded_seq_len_not_usize_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("huge_len", HUGE_SEQ_LEN_ASSUME));
    ctx.push_obligation(ProofObligation::assert(
        "len_le_usize_max",
        "s.len() <= 18446744073709551615",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_not_verified(
        &result,
        "an unbounded spec Seq must NOT be constrained to usize::MAX — no Vec bound \
         leaks to Seq, so `len <= 2^64-1` is refuted at len == 2^64 + 2",
    );
}
