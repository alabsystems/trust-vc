// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// FV-C: the scope-wide quantifier wrap context leaked onto `int`/`nat`
// arithmetic. See `tests/data/quantifier_scope_wrap_leak_probe.rs` for the
// mechanism; the fix is in `encoder/arith_semantics.rs::resolve_expr_wrap`,
// which now DECLINES the scope fallback for the unbounded math sorts instead
// of adopting the binder's bit width.
//
// Every case below was measured against the production CLI at the defective
// HEAD (6545b8fe, cache off): all four `fv_*` reported `verified`, and every
// `pin_*` plus the `control_*` already had the verdict asserted here — so the
// pins are a real anti-degeneration guard, not a restatement of the fix.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx() -> String {
    format!(
        "{}/tests/data/quantifier_scope_wrap_leak_probe.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn assert_not_verified(name: &str, why: &str) {
    let v = verify_function_from_file(&fx(), name);
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY ({name}): {why} — got {v:?}"
    );
}

fn assert_verified(name: &str, why: &str) {
    let v = verify_function_from_file(&fx(), name);
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "OVER-REJECTION ({name}): {why} — got {v:?}"
    );
}

// ---------------------------------------------------------------------------
// The defect: `int` arithmetic reduced mod 2^(binder width).

#[test]
fn int_cast_sum_must_not_wrap_to_binder_width() {
    assert_not_verified(
        "fv_int_cast_sum_bound",
        "(a as int) + (b as int) <= 255 is refuted by a == b == 200",
    );
}

#[test]
fn spec_fn_int_return_must_not_wrap_to_binder_width() {
    assert_not_verified(
        "fv_spec_fn_int_sum",
        "no cast is needed to reach the hole: 200 + 200 == 400, not 144",
    );
}

#[test]
fn arithmetic_not_mentioning_the_binder_must_not_wrap() {
    assert_not_verified(
        "fv_binder_unused",
        "the binder `i` appears nowhere in `(y as int) * 2`, yet a scope-wide \
         modulus made 400 < 256 true",
    );
}

#[test]
fn int_cast_difference_must_not_wrap_to_binder_width() {
    assert_not_verified(
        "fv_int_cast_diff_nonneg",
        "(a as int) - (b as int) is -1 for a == 0, b == 1, never 255",
    );
}

// The binder-side neighbour that already declined correctly. Keeping it here
// pins the symmetry the fix restores: an `int`/`nat` BINDER contributes no
// wrap, and now neither does an `int`/`nat` EXPRESSION.
#[test]
fn control_nat_binder_still_refuted() {
    assert_not_verified(
        "control_nat_binder_never_wrapped",
        "a `nat` binder never contributed a wrap context",
    );
}

// ---------------------------------------------------------------------------
// FV-B: these two ASSERTED THE FALSE VERIFY. They used to demand that
// fixed-width `+`/`*` under a binder keep wrapping; a quantifier body is spec
// code, where Verus types `u8 + u8` as `int`, so `a + b <= 255` is refuted by
// `a == b == 200`. Verdicts inverted; see the fixture note.

#[test]
fn fixed_width_add_under_binder_must_not_wrap() {
    assert_not_verified(
        "fv_u8_add_wraps_into_range",
        "spec `a + b` on u8 binders is `int`: 200 + 200 == 400, not 144",
    );
}

#[test]
fn fixed_width_mul_under_binder_must_not_wrap() {
    assert_not_verified(
        "fv_u8_mul_wraps_into_range",
        "spec `a * b` on u8 binders is `int`: 200 * 200 == 40000, not 64",
    );
}

// ---------------------------------------------------------------------------
// NARROWNESS PINS — the fix must not degenerate into "quantifier bodies never
// wrap at all". An explicit `wrapping_*` op IS defined as finite-width
// truncation and must keep truncating under a binder.

#[test]
fn pin_explicit_wrapping_add_still_wraps() {
    assert_verified(
        "pin_u8_wrapping_add_still_wraps",
        "`a.wrapping_add(b)` is a u8 BY DEFINITION and must stay <= 255",
    );
}

#[test]
fn pin_true_int_sum_bound_still_verifies() {
    assert_verified(
        "pin_int_cast_sum_true_bound",
        "255 + 255 == 510 — the honest bound must be provable",
    );
}

#[test]
fn pin_int_sum_nonneg_still_verifies() {
    assert_verified("pin_int_cast_sum_nonneg", "both operands are non-negative");
}

#[test]
fn pin_true_int_mul_bound_still_verifies() {
    assert_verified(
        "pin_int_cast_mul_true_bound",
        "255 * 255 == 65025 — the honest bound must be provable",
    );
}
