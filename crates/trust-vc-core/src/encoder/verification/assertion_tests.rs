// Tests for assertion verification orchestration.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Split from `assertion.rs` for the 500-line limit (#2621).

use super::*;

#[test]
fn test_convert_setup_error_ay_panic_becomes_unknown() {
    let result = convert_setup_error(TrustVcError::Encoding {
        context: "ay solver panic",
        detail: "sort mismatch: expected Bool, got BV32".to_string(),
    });

    assert!(
        matches!(result, Ok(AssertionOutcome::Unknown { .. })),
        "caught ay panics should stay in the outcome channel as Unknown: {:?}",
        result
    );
}

#[test]
fn test_convert_setup_error_sort_mismatch_stays_trust_vc_error() {
    let result = convert_setup_error(TrustVcError::Encoding {
        context: "encode typed assumption",
        detail: "Failed to encode assumption 'return_value': sort mismatch in apply".to_string(),
    });

    match result {
        Err(TrustVcError::Encoding { context, detail }) => {
            assert_eq!(context, "encode typed assumption");
            assert!(detail.contains("return_value"));
        }
        other => panic!(
            "ordinary setup encoding failures should remain TrustVcError::Encoding, got: {:?}",
            other
        ),
    }
}

#[test]
fn test_convert_setup_error_non_ay_error_stays_trust_vc_error() {
    let result = convert_setup_error(TrustVcError::Encoding {
        context: "verification setup",
        detail: "division by zero".to_string(),
    });

    match result {
        Err(TrustVcError::Encoding { context, detail }) => {
            assert_eq!(context, "verification setup");
            assert_eq!(detail, "division by zero");
        }
        other => panic!(
            "non-ay setup failures should remain TrustVcError::Encoding, got: {:?}",
            other
        ),
    }
}

// ── NRA dispatch-gate boundary (real_nonlinear1 vs real_nonlinear2) ──────────
//
// `is_nonlinear_arith_mode` is the soundness-critical switch that decides
// whether the nonlinear-real certificate pre-pass (`nonlinear_real::
// try_prove_nonlinear_real_outcome`) runs for an obligation. Upstream
// `real.rs` carries the *same* goal twice:
//   * real_nonlinear1 — `by (nonlinear_arith)` ⇒ SolverMode::NonlinearArith
//     ⇒ gate open ⇒ certificate search discharges it (=> Ok(())),
//   * real_nonlinear2 — no hint ⇒ SolverMode::Default/None ⇒ gate CLOSED
//     ⇒ falls through to the ordinary solver, which cannot prove it (=> FAILS).
// These tests pin both directions of that gate.

use crate::vc::SolverMode;

/// should-VERIFY direction: the `by (nonlinear_arith)` hint (the real_nonlinear1
/// case) opens the gate so the certificate pre-pass is consulted.
#[test]
fn nra_gate_open_for_nonlinear_arith_mode() {
    assert!(
        is_nonlinear_arith_mode(Some(SolverMode::NonlinearArith)),
        "an explicit by(nonlinear_arith) hint must open the NRA certificate pre-pass \
         (this is the real_nonlinear1 path)"
    );
}

/// should-FAIL direction: every non-`NonlinearArith` mode must keep the gate
/// CLOSED. The `None` default is the real_nonlinear2 case — the identical goal
/// with no hint must NOT reach the NRA pre-pass, so it falls through to the
/// ordinary solver and fails exactly as Verus expects. A leak in any of these
/// rows would silently prove real_nonlinear2 and diverge from upstream.
#[test]
fn nra_gate_closed_for_every_non_nonlinear_arith_mode() {
    // The default/hint-free obligation: the real_nonlinear2 shape.
    assert!(
        !is_nonlinear_arith_mode(None),
        "SOUNDNESS: a hint-free obligation (None) must NOT trigger the NRA pre-pass \
         — this is the real_nonlinear2 case that Verus expects to FAIL"
    );
    for mode in [
        SolverMode::Default,
        SolverMode::BitVector,
        SolverMode::Compute,
    ] {
        assert!(
            !is_nonlinear_arith_mode(Some(mode)),
            "SOUNDNESS: {mode:?} must NOT open the NRA pre-pass; only NonlinearArith may"
        );
    }
}
