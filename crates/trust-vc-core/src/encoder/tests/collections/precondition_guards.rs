//! Seq precondition guard tests: bounds checks (#1805) and nonempty
//! positive controls (#1988).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from collections/mod.rs (#2145).

use super::*;

// ========================================================================
// Seq precondition guards (#1805)
// ========================================================================

// ========================================================================
// Ground (constant) Seq::new(..).index(..) out-of-bounds reclassification.
//
// A fully-constant `Seq::<int>::new(len, f).index(i)` has NO free variable.
// When `i >= len` the always-on element-index bound `i < len` is ground-FALSE,
// so its negation is ground-TRUE and ay-dpll CEGQI returns validated-SAT with
// an EMPTY model (nothing to assign). Before the fix this empty-model SAT sank
// into `Unknown(EmptyModel)`; now the Seq element-index bound label
// (`requires i < len`) reclassifies it to a definite Counterexample — the
// out-of-bounds access upstream Verus rejects. Mirrors the unsigned over-shift
// empty-model reclassification in `verification/overflow.rs`.
//
// SOUNDNESS, both directions:
//  * an in-range ground index makes the bound ground-TRUE → negation UNSAT →
//    decided Verified ABOVE the empty-model guard, never reclassified;
//  * only a genuine ground OOB (bound definitively violated) reclassifies;
//  * a Seq with a free variable yields a non-empty model and keeps its rich
//    model-rendered counterexample (covered by the var-seq tests below);
//  * the gate is the element-index label only — Seq length-prefix bounds
//    (`take`/`skip`/`subrange`, `requires n <= len`) do NOT reclassify.
// ========================================================================

/// DISCRIMINATING (regression): a constant `Seq::new(5, f).index(5)` is the
/// first out-of-bounds index (i == len). Before the fix this was
/// `Unknown(EmptyModel)`; it must now be a definite Counterexample.
#[test]
fn test_seq_new_ground_oob_index_first_oob_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "oob",
        "trust_vc_types::Seq::<int>::new(5usize, |i: usize| i as int).index(5usize) \
         == trust_vc_types::Seq::<int>::new(5usize, |i: usize| i as int).index(5usize)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "constant Seq::new(5).index(5) (i == len, first OOB) must be a definite \
         counterexample, not Unknown",
    );
}

/// DISCRIMINATING (regression): a constant `Seq::new(5, f).index(7)` (well past
/// the end) must be a definite Counterexample, not Unknown.
#[test]
fn test_seq_new_ground_oob_index_7_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "oob7",
        "trust_vc_types::Seq::<int>::new(5usize, |i: usize| i as int).index(7usize) \
         == trust_vc_types::Seq::<int>::new(5usize, |i: usize| i as int).index(7usize)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "constant Seq::new(5).index(7) (i > len, OOB) must be a definite counterexample",
    );
}

/// CONTROL (must NOT regress): an in-bounds constant `Seq::new(5, f).index(3)`
/// with the true value `f(3) == 3` must stay Verified — the in-range bound is
/// decided UNSAT above the empty-model guard and is never reclassified.
#[test]
fn test_seq_new_ground_inbounds_index_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "inb",
        "trust_vc_types::Seq::<int>::new(5usize, |i: usize| i as int).index(3usize) == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "in-bounds constant Seq::new(5).index(3) == f(3) == 3 must verify (no false \
         counterexample)",
    );
}

/// BOUNDARY (must NOT regress): the last valid index `i == len - 1 == 4` must
/// stay Verified (in-range), pinned to its true value `f(4) == 4`.
#[test]
fn test_seq_new_ground_boundary_last_valid_index_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "b4",
        "trust_vc_types::Seq::<int>::new(5usize, |i: usize| i as int).index(4usize) == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "boundary constant Seq::new(5).index(4) (last valid, i == len - 1) must verify",
    );
}

/// CONTROL (unchanged): a wrong in-bounds value claim must stay a
/// Counterexample — the bound holds (index 3 is in range) but `f(3) == 3 != 4`,
/// so the value obligation is refuted on the merits.
#[test]
fn test_seq_new_ground_wrong_inbounds_value_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "inb_wrong",
        "trust_vc_types::Seq::<int>::new(5usize, |i: usize| i as int).index(3usize) == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "in-bounds Seq::new(5).index(3) == 4 (true value 3) must be a counterexample",
    );
}

/// NON-BLEED (e): a Seq length-prefix bounds check is NOT an element-index
/// check. A constant `Seq::new(3, f).take(5)` over-take hits the SAME
/// empty-model guard but carries the `requires n <= len` label, so the
/// element-index reclassification (`requires i < len`) must NOT capture it —
/// it stays Unknown(EmptyModel), exactly as before this change.
#[test]
fn test_seq_new_ground_take_oob_not_reclassified_as_index_cex() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "take_oob",
        "trust_vc_types::Seq::<int>::new(3usize, |i: usize| i as int).take(5usize).len() \
         == trust_vc_types::Seq::<int>::new(3usize, |i: usize| i as int).take(5usize).len()",
    ));
    let result = AYEncoder::verify(&ctx);
    // Stays the SAME non-index empty-model Unknown — proves the index gate did
    // not bleed onto the `requires n <= len` length-prefix label.
    expect_unknown_containing(
        &result,
        "requires n <= len",
        "ground Seq::take(5) over-take must NOT be reclassified by the element-index gate",
    );
}

/// CONTROL (unchanged): a free-variable Seq OOB index keeps its rich
/// model-rendered counterexample — the empty-model reclassification is reserved
/// for the constant case and does not disturb this path.
#[test]
fn test_seq_var_oob_index_keeps_model_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assert("oob", "s.index(5) == s.index(5)"));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "free-variable Seq len==5 .index(5) OOB must be a counterexample (model-rendered)",
    );
}

/// DISCRIMINATING: Seq::index() out of bounds must NOT verify (#1805).
/// In Verus, s.index(n) requires n < s.len(). Without the bounds check,
/// the SMT array theory returns an arbitrary value for out-of-range indices.
#[test]
fn test_seq_index_out_of_bounds_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    // Index 5 is out of bounds (len == 3)
    ctx.push_obligation(ProofObligation::assert("oob", "s.index(5) == s.index(5)"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Seq::index(5) on len-3 Seq must NOT verify — out of bounds (#1805)",
    );
}

/// DISCRIMINATING: A fully constructed finite Seq with an out-of-bounds index
/// should produce a stable counterexample, not Unknown.
#[test]
fn test_constructed_seq_index_out_of_bounds_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "constructed_oob",
        "trust_vc_types::Seq::<i32>::empty()\
            .push(0i32)\
            .push(10i32)\
            .push(20i32)\
            .push(30i32)\
            .push(40i32)\
            .index(5usize)\
            == trust_vc_types::Seq::<i32>::empty()\
                .push(0i32)\
                .push(10i32)\
                .push(20i32)\
                .push(30i32)\
                .push(40i32)\
                .index(5usize)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "constructed len-5 Seq::index(5) must produce a concrete bounds counterexample",
    );
}

/// CONTROL: Seq::index() in bounds should verify with genuine reasoning.
/// Fixes tautology (#1944): previously assumed s.index(0) == 42 and asserted
/// s.index(0) == 42. Now assumes the value and asserts a consequence (> 0).
#[test]
fn test_seq_index_in_bounds_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("elem", "s.index(0) == 42"));
    // Assert a consequence: 42 > 0, requires BV arithmetic reasoning.
    ctx.push_obligation(ProofObligation::assert("positive", "s.index(0) > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Seq::index(0) == 42 should imply index(0) > 0");
}

/// CONTROL: Seq::get() is a public alias for Seq::index() and shares bounds.
#[test]
fn test_seq_get_in_bounds_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("elem", "s.get(0) == 42"));
    ctx.push_obligation(ProofObligation::assert("positive", "s.get(0) > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Seq::get(0) == 42 should imply get(0) > 0");
}

/// DISCRIMINATING: Seq::first() on empty Seq must NOT verify (#1805).
#[test]
fn test_seq_first_empty_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("empty", "s.len() == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "first_tautology",
        "s.first() == s.first()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "Seq::first() on empty Seq must NOT verify (#1805)");
}

/// DISCRIMINATING: Seq::last() on empty Seq must NOT verify (#1805).
#[test]
fn test_seq_last_empty_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("empty", "s.len() == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "last_tautology",
        "s.last() == s.last()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "Seq::last() on empty Seq must NOT verify (#1805)");
}

/// DISCRIMINATING: Seq::drop_last() on empty Seq must NOT verify (#1805).
#[test]
fn test_seq_drop_last_empty_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("empty", "s.len() == 0"));
    // drop_last on empty should fail the precondition check
    ctx.push_obligation(ProofObligation::assert(
        "drop_last_taut",
        "s.drop_last().len() == s.drop_last().len()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Seq::drop_last() on empty Seq must NOT verify (#1805)",
    );
}

/// DISCRIMINATING: Seq::drop_first() on empty Seq must NOT verify (#1805).
#[test]
fn test_seq_drop_first_empty_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("empty", "s.len() == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "drop_first_taut",
        "s.drop_first().len() == s.drop_first().len()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Seq::drop_first() on empty Seq must NOT verify (#1805)",
    );
}

/// DISCRIMINATING: Seq::take(n) with n > len must NOT verify (#1805).
#[test]
fn test_seq_take_exceeds_len_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    // take(5) exceeds length 3
    ctx.push_obligation(ProofObligation::assert(
        "take_oob",
        "s.take(5).len() == s.take(5).len()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "Seq::take(5) on len-3 Seq must NOT verify (#1805)");
}

/// CONTROL: Seq::take(n) with n <= len should verify.
#[test]
fn test_seq_take_in_range_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assert("take_len", "s.take(3).len() == 3"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Seq::take(3) on len-5 Seq should verify");
}

/// DISCRIMINATING: Seq::skip(n) with n > len must NOT verify (#1805).
#[test]
fn test_seq_skip_exceeds_len_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    // skip(5) exceeds length 3
    ctx.push_obligation(ProofObligation::assert(
        "skip_oob",
        "s.skip(5).len() == s.skip(5).len()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "Seq::skip(5) on len-3 Seq must NOT verify (#1805)");
}

/// DISCRIMINATING: Seq::subrange with inverted range must NOT verify (#1805).
#[test]
fn test_seq_subrange_inverted_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    // subrange(3, 1) has start > end
    ctx.push_obligation(ProofObligation::assert(
        "inverted",
        "s.subrange(3, 1).len() == s.subrange(3, 1).len()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "Seq::subrange(3");
}

/// DISCRIMINATING: Seq::subrange with end > len must NOT verify (#1805).
#[test]
fn test_seq_subrange_end_exceeds_len_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    // subrange(0, 10) has end > len
    ctx.push_obligation(ProofObligation::assert(
        "end_oob",
        "s.subrange(0, 10).len() == s.subrange(0, 10).len()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "Seq::subrange(0");
}

/// CONTROL: Seq::subrange with valid range should verify.
#[test]
fn test_seq_subrange_valid_range_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_len",
        "s.subrange(1, 3).len() == 2",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Seq::subrange(1, 3) on len-5 Seq should verify");
}

/// DISCRIMINATING: Seq::update() out of bounds must NOT verify (#1805).
#[test]
fn test_seq_update_out_of_bounds_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    // update at index 5 is out of bounds
    ctx.push_obligation(ProofObligation::assert(
        "update_oob",
        "s.update(5, 99).index(0) == s.update(5, 99).index(0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "Seq::update(5");
}

// ========================================================================
// Seq nonempty check positive control tests (#1988)
// The negative tests above verify that first/last/drop_first/drop_last
// on empty sequences are rejected. These positive tests verify that the
// nonempty check does not block valid operations on non-empty sequences.
// ========================================================================

/// CONTROL: Seq::first() on non-empty Seq should verify.
/// Exercises add_seq_nonempty_check happy path — len >= 1 holds, so the
/// nonempty overflow check passes and the assertion can succeed.
#[test]
fn test_seq_first_nonempty_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("elem", "s.index(0) == 42"));
    ctx.push_obligation(ProofObligation::assert("first_value", "s.first() == 42"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq::first() on non-empty Seq should verify (#1988)",
    );
}

/// CONTROL: Seq::last() on non-empty Seq should verify.
/// Exercises add_seq_nonempty_check happy path for last().
/// Uses a well-definedness check instead of index arithmetic so this test
/// stays focused on nonempty precondition handling.
#[test]
fn test_seq_last_nonempty_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "last_defined",
        "s.last() == s.last()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq::last() on non-empty Seq should be well-defined (#1988)",
    );
}

/// CONTROL: Seq::drop_last() on non-empty Seq should verify length - 1.
/// Exercises add_seq_nonempty_check happy path for drop_last().
#[test]
fn test_seq_drop_last_nonempty_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "drop_last_len",
        "s.drop_last().len() == 2",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq::drop_last() on non-empty Seq should verify len - 1 (#1988)",
    );
}

/// CONTROL: Seq::drop_first() on non-empty Seq should verify length - 1.
/// Exercises add_seq_nonempty_check happy path for drop_first().
#[test]
fn test_seq_drop_first_nonempty_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "drop_first_len",
        "s.drop_first().len() == 2",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq::drop_first() on non-empty Seq should verify len - 1 (#1988)",
    );
}

// ========================================================================
// Length-DECREASING precondition soundness (#soundness skip/subrange/drop).
//
// REGRESSION: `skip(n)` (`len - n`), `subrange(start, end)` (`end - start`),
// and `drop_first`/`drop_last` (`len - 1`) compute a length-DECREASING result.
// When the precondition is violated that result is NEGATIVE, and the shifted
// carrier's `bv2int(companion) == new_len` bridge (`len_index_companion`) was
// asserted UNCONDITIONALLY — `bv2int` is always `>= 0`, so a negative `new_len`
// made the bridge UNSAT and POISONED the whole solver context, vacuously
// discharging both the surrounding assertion AND the pushed precondition guard
// (`n <= len` / `start <= end` / `len >= 1`). That was a FALSE-VERIFIED
// soundness hole. The fix guards the bridge by `new_len >= 0`, so a violated
// precondition adds no constraint (no poison) and the guard refutes against the
// asserted SOURCE length. Both soundness directions are pinned below:
//  (a) every precondition VIOLATION must fail closed (no false Verified);
//  (b) every VALID length-decreasing op must STILL verify (no over-correction).
// ========================================================================

/// SOUNDNESS (a): skip(len + 1) — one past the source length — must fail
/// closed. Mirrors the catastrophic direction: the result length `3 - 4 = -1`
/// must NOT poison the context into a vacuous proof.
#[test]
fn test_seq_skip_len_plus_one_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "skip_oob",
        "s.skip(4).len() == s.skip(4).len()",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Seq::skip(4) on len-3 Seq (n == len + 1) must NOT verify",
    );
}

/// SOUNDNESS (a): subrange(2, 1) — start > end with BOTH endpoints in range —
/// must fail closed. Isolates the `start <= end` guard from the `end <= len`
/// guard (here `end == 1 <= len == 5`, so only `start <= end` can refute).
#[test]
fn test_seq_subrange_inverted_in_range_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "inverted_in_range",
        "s.subrange(2, 1).len() == s.subrange(2, 1).len()",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Seq::subrange(2, 1) (start > end, both <= len) must NOT verify",
    );
}

/// SOUNDNESS (b): boundary skip(len) — the LAST valid argument — yields the
/// empty Seq and must verify (`3 - 3 == 0`). Guards against over-correcting
/// the fix into a never-verify for the `n == len` boundary.
#[test]
fn test_seq_skip_equals_len_empty_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert("skip_all", "s.skip(3).len() == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq::skip(3) on len-3 Seq (n == len) must verify to the empty Seq",
    );
}

/// SOUNDNESS (b): valid skip(2) on len-3 must verify `len - n == 1`.
#[test]
fn test_seq_skip_in_range_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert("skip_len", "s.skip(2).len() == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq::skip(2) on len-3 Seq should verify len - n == 1",
    );
}

/// SOUNDNESS (b): full subrange(0, len) must verify `end - start == len`.
#[test]
fn test_seq_subrange_full_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "full_len",
        "s.subrange(0, 5).len() == 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq::subrange(0, 5) on len-5 Seq (full range) should verify",
    );
}

/// SOUNDNESS (b): boundary empty subrange(start, start) must verify
/// `end - start == 0` (start == end is valid in Verus: 0 <= start <= end).
#[test]
fn test_seq_subrange_empty_at_start_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "empty_sub",
        "s.subrange(2, 2).len() == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq::subrange(2, 2) (start == end) should verify to the empty Seq",
    );
}

/// SOUNDNESS (b): drop_first / drop_last on a len-2 Seq must verify `len - 1`.
#[test]
fn test_seq_drop_first_last_len2_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "drop_first_len",
        "s.drop_first().len() == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq::drop_first() on len-2 Seq should verify len - 1 == 1",
    );

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "drop_last_len",
        "s.drop_last().len() == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq::drop_last() on len-2 Seq should verify len - 1 == 1",
    );
}
