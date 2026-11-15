// Bit-precise layout / unsafe-contract tests — capability #6.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Run with: targo --unverified test -p trust-vc-driver --features layout
//
// These tests drive real layout invariants (field-fit, power-of-two alignment
// masking, array-stride monotonicity, niche/discriminant range) through the
// trust-vc-core encoder + ay backend over bitvector/integer variables. They are
// the capability that makes trust-vc *better* than Verus on `unsafe` layout
// reasoning: Verus models Rust's surface semantics and does not consume the
// compiler's resolved size/align/niche facts, whereas trust-vc discharges them
// directly on ay's bitvector theory.
//
// Each capability is exercised both ways: a TRUE invariant must VERIFY, and a
// deliberately FALSE one must be REFUTED with a counterexample — so the builders
// are fail-closed (a wrong layout claim can never be rubber-stamped).
#![cfg(feature = "layout")]

use trust_vc_core::ir::CompareOp;
use trust_vc_driver::layout::{
    aligned_mask, array_element_monotonic, discriminant_in_range, field_fits, LayoutFact,
    ADDR_WIDTH,
};
use trust_vc_driver::lower::{cmp, lit, uint, Outcome};

// --- Field-fit: offset + field_size <= size ---------------------------------

/// A 4-byte field placed within a 16-byte type, with the offset bounded by the
/// compiler's placement fact, always fits: `offset + 4 <= 16`. Must VERIFY.
#[test]
fn field_within_type_fits_verifies() {
    let f = field_fits(LayoutFact::new(16, 8), 4);
    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
}

/// A FALSE field-fit claim: drop the placement precondition by asserting a
/// stronger, false postcondition. We tighten the ensures to `result <= 15`
/// while the field can legitimately end exactly at 16, so the backend must
/// REFUTE it with a counterexample (offset = 12 → end = 16 > 15).
#[test]
fn field_fit_off_by_one_is_refuted() {
    let mut f = field_fits(LayoutFact::new(16, 8), 4);
    // Replace the true `result <= 16` with the false `result <= 15`.
    f.ensures = vec![cmp(
        CompareOp::Le,
        f.result.as_var(),
        lit(15, uint(ADDR_WIDTH)),
    )];
    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Refuted, "raw verdict: {raw:?}");
}

// --- Alignment mask: addr & (align - 1) == 0 --------------------------------

/// Power-of-two alignment masking: given `addr & 7 == 0`, the low three bits
/// are clear. This is the canonical pointer-alignment predicate, proven through
/// the real BV `bvand` path. Must VERIFY.
#[test]
fn aligned_address_mask_verifies() {
    let fact = LayoutFact::new(16, 8);
    assert!(fact.align_is_power_of_two());
    let f = aligned_mask(fact);
    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
}

/// A FALSE alignment claim: assert the masked value equals a *non-zero*
/// constant. `addr & 7` can be 0 (e.g. addr = 8), contradicting `== 1`, so the
/// backend must REFUTE it. This proves the BV mask is genuinely reasoned about,
/// not assumed.
#[test]
fn aligned_mask_wrong_residue_is_refuted() {
    let fact = LayoutFact::new(16, 8);
    let mut f = aligned_mask(fact);
    // Drop the aligning precondition so `addr & 7` is unconstrained, and claim
    // it is always 1 — refutable by addr = 0 (masked value 0 != 1).
    f.requires.clear();
    f.ensures = vec![cmp(
        CompareOp::Eq,
        f.result.as_var(),
        lit(1, uint(ADDR_WIDTH)),
    )];
    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Refuted, "raw verdict: {raw:?}");
}

// --- Array-stride monotonicity: base <= base + index*size -------------------

/// For a `[T; N]` with element stride 8 and a bounded index/base, the element
/// address never underflows below the base: `base <= base + index*8`. Must
/// VERIFY (the preconditions keep the BV product/sum from wrapping).
#[test]
fn array_element_address_monotonic_verifies() {
    let f = array_element_monotonic(LayoutFact::new(8, 8), 1024);
    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
}

/// A FALSE monotonicity claim: assert the element address is *strictly greater*
/// than the base. At index = 0 the element address equals the base, so `>` is
/// false and the backend must REFUTE it.
#[test]
fn array_element_strict_increase_is_refuted() {
    let mut f = array_element_monotonic(LayoutFact::new(8, 8), 1024);
    let base = f.params[0].as_var();
    f.ensures = vec![cmp(CompareOp::Gt, f.result.as_var(), base)];
    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Refuted, "raw verdict: {raw:?}");
}

// --- Niche / discriminant range (signed int path) ---------------------------

/// A signed discriminant bounded by `-1 <= d <= 2` stays in range after the
/// identity body. Exercises the `int` (signed) builder. Must VERIFY.
#[test]
fn discriminant_range_verifies() {
    let f = discriminant_in_range(-1, 2);
    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
}

/// A FALSE niche claim: assert the discriminant is `>= 0` although the valid
/// range starts at `-1`. The backend must REFUTE it (d = -1 is a counterexample).
#[test]
fn discriminant_wrong_lower_bound_is_refuted() {
    let mut f = discriminant_in_range(-1, 2);
    f.ensures = vec![cmp(
        CompareOp::Ge,
        f.result.as_var(),
        lit(0, trust_vc_driver::lower::int(ADDR_WIDTH)),
    )];
    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Refuted, "raw verdict: {raw:?}");
}
