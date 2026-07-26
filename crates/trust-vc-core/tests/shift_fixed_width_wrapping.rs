// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Soundness regression battery for the P1-E "shifts" cluster.
//!
//! Fixed-width `<<`/`>>` must wrap/truncate to the result width in two's
//! complement (Rust semantics, mirrored by Verus). A sign-bit-landing left
//! shift is `i32::MIN` (negative), and a signed `>>` is arithmetic
//! (sign-preserving). A FALSE goal built on those facts must NEVER verify; the
//! TRUE companion must still verify (no over-rejection).
//!
//! See `crates/trust-vc-core/src/ir_lowering/operators.rs` (`lower_special`),
//! `crates/trust-vc-core/src/encoder/ir_encoder/arith/int_mode.rs`
//! (`apply_int_shift_wrapping`), and
//! `crates/trust-vc-core/src/encoder/ir_encoder/arith/bv_arith.rs`
//! (`encode_bv_shift`).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn path() -> String {
    format!(
        "{}/tests/data/shift_fixed_width_wrapping.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> VerifyResult {
    verify_function_from_file(&path(), func)
        .unwrap_or_else(|err| panic!("extract/verify {func} failed: {err:?}"))
}

/// FALSE goals that depend on the missing fixed-width wrap. A `Verified` here is
/// the catastrophic false-Verified this fix closes.
#[test]
fn false_shift_goals_never_verify() {
    for func in [
        "ensures_shl31_gt0_FALSE",
        "assert_shl31_gt0_FALSE",
        "assert_2shl30_gt0_FALSE",
        "assert_hexshl1_gt0_FALSE",
        "assert_shl31_as_int_eq_pos_FALSE",
        "bv_shr_neg1_eq_logical_FALSE",
        "bv_shr_neg4_eq_logical_FALSE",
        "bv_shl31_gt0_FALSE",
    ] {
        let result = verdict(func);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "UNSOUND: {func} verified a FALSE shift goal (missing fixed-width wrap). \
             Verdict: {result:?}"
        );
    }
}

/// TRUE companions of the same shift facts must still verify — the fix must not
/// over-reject correctly-modeled shifts.
#[test]
fn true_shift_goals_still_verify() {
    for func in [
        "ensures_shl31_lt0_TRUE",
        "ensures_shl30_gt0_TRUE",
        "assert_shl30_gt0_TRUE",
        "assert_shl31_as_int_eq_min_TRUE",
        "assert_shl31_lt0_TRUE",
        "bv_shr_neg1_eq_neg1_TRUE",
        "bv_shr_neg4_eq_neg2_TRUE",
        "bv_shr_unsigned_TRUE",
        "bv_shl3_eq_8_TRUE",
    ] {
        let result = verdict(func);
        assert!(
            matches!(result, VerifyResult::Verified),
            "OVER-REJECTION: {func} is a genuinely-true shift fact but did not \
             verify. Verdict: {result:?}"
        );
    }
}
