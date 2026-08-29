// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// FV-B: quantifier-body arithmetic wrapped AND suppressed its overflow
// obligation. See `tests/data/quantifier_body_arith_wrap_soundness.rs` for the
// mechanism. The fix is in
//   * `encoder/ir_encoder/arith/int_arith.rs` — `arith_wrap_ctx` declines the
//     modulus for `+`/`-`/`*` at `quantifier_depth > 0`;
//   * `encoder/ir_encoder/logic.rs::encode_neg` — same rule for unary `-`;
//   * `encoder/ir_encoder/arith/compare.rs::simplify_unsigned_zero_compare` —
//     the `expr >= 0 => true` fold rested on the (now dead) wrapping premise
//     and is restricted to subtraction-free operands;
//   * `encoder/ir_encoder/wrapping.rs` — explicit `wrapping_*` applies the
//     type-derived truncation itself instead of inheriting it.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx() -> String {
    format!(
        "{}/tests/data/quantifier_body_arith_wrap_soundness.rs",
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
// The defect, soundness direction: FALSE claims reported `verified`.

#[test]
fn u64_add_must_not_wrap_under_binder() {
    assert_not_verified(
        "fv_u64_add_stays_under_max",
        "i == u64::MAX gives i + 1 == 2^64, which is not <= u64::MAX",
    );
}

#[test]
fn u64_sub_must_not_wrap_under_binder() {
    assert_not_verified(
        "fv_u64_sub_is_nonnegative",
        "i == 0 gives i - 1 == -1, which is not >= 0",
    );
}

#[test]
fn negated_unsigned_zero_compare_must_not_fold() {
    assert_not_verified(
        "fv_u64_sub_negated_zero_compare",
        "`i - 1 < 0` folded to false, so its negation verified; i == 0 refutes",
    );
}

#[test]
fn zero_le_unsigned_sub_must_not_fold() {
    assert_not_verified(
        "fv_u64_zero_le_sub",
        "the `0 <= expr` spelling of the same fold; i == 0 refutes",
    );
}

#[test]
fn i32_add_must_not_wrap_under_binder() {
    assert_not_verified(
        "fv_i32_add_stays_under_max",
        "i == i32::MAX gives 2147483648, which is not <= i32::MAX",
    );
}

#[test]
fn i8_negation_must_not_wrap_under_binder() {
    assert_not_verified(
        "fv_i8_neg_stays_under_max",
        "x == i8::MIN gives -x == 128; -(-128) must not wrap back to -128",
    );
}

#[test]
fn exists_witness_must_not_come_from_a_wrap() {
    assert_not_verified(
        "fv_i8_exists_wrapped_witness",
        "x + 1 ranges over -127..=128 mathematically, so -128 is unreachable",
    );
}

// ---------------------------------------------------------------------------
// The SAME one-site change is the capability win: these were wrongly REFUTED.

#[test]
fn true_u64_increment_now_verifies() {
    assert_verified(
        "pin_true_u64_increment_is_greater",
        "i + 1 > i holds for every u64 under mathematical semantics",
    );
}

#[test]
fn true_i32_increment_now_verifies() {
    assert_verified(
        "pin_true_i32_increment_is_greater",
        "i + 1 > i holds for every i32 under mathematical semantics",
    );
}

#[test]
fn true_u8_honest_sum_bound_now_verifies() {
    assert_verified(
        "pin_true_u8_add_honest_bound",
        "u8::MAX + u8::MAX == 510 — the bound the modulus was hiding",
    );
}

// ---------------------------------------------------------------------------
// NARROWNESS PINS.

#[test]
fn pin_explicit_wrapping_add_still_truncates() {
    assert_verified(
        "pin_wrapping_add_still_truncates",
        "`wrapping_add` is finite-width BY DEFINITION and must stay <= u64::MAX",
    );
}

#[test]
fn pin_wrapping_add_is_not_silently_opaque() {
    assert_not_verified(
        "fv_wrapping_add_not_treated_as_math",
        "u64::MAX.wrapping_add(1) == 0, which is not >= 1 — the pin above must \
         not be satisfiable by making `wrapping_add` unconstrained",
    );
}

#[test]
fn pin_unsigned_zero_compare_fold_survives() {
    assert_verified(
        "pin_zero_compare_fold_survives_for_add",
        "the #2062 fold must survive for subtraction-free operands",
    );
}

#[test]
fn pin_false_fixed_width_claim_still_refuted() {
    assert_not_verified(
        "fv_control_false_claim_still_refuted",
        "i * 2 > i is refuted by i == 0; the fix must not prove everything",
    );
}

#[test]
fn pin_reflexivity_still_verifies() {
    assert_verified(
        "pin_reflexive_still_verifies",
        "the plainest true quantifier body must keep verifying",
    );
}

// ---------------------------------------------------------------------------
// Machine semantics OUTSIDE a quantifier is untouched.

#[test]
fn pin_exec_overflow_obligation_still_fires() {
    assert_not_verified(
        "fv_exec_add_overflow_still_caught",
        "a == 191 gives 291 — the exec-path addition-overflow obligation must \
         still fail closed outside a quantifier",
    );
}

#[test]
fn pin_exec_in_range_addition_still_verifies() {
    assert_verified(
        "pin_exec_add_in_range_still_verifies",
        "a <= 100 keeps a + 100 inside u8; exec arithmetic must not regress",
    );
}
