//! Soundness tests: opaque type rejection, assumptions-only guards,
//! cast-to-bool error handling.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// Opaque type rejection tests (Issue #1926)
// ========================================================================

/// String-like variables are now recognized, but only through the explicit
/// Seq<char> view surface.
#[cfg(not(feature = "native-strings"))]
#[test]
fn test_string_view_no_longer_hits_opaque_guard() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("String"));
    ctx.push_obligation(ProofObligation::assert(
        "view_len_reflexive",
        "s.view().len() == s.view().len()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "String view should verify through the typed encoder",
    );
}

/// SOUNDNESS (#1926): If multiple opaque variables exist, diagnostics should
/// include all of them.
#[test]
fn test_multiple_opaque_types_all_reported() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("v", crate::ir::TrustVcType::parse_or_opaque("Gadget"));
    ctx.declare_var_typed("name", crate::ir::TrustVcType::parse_or_opaque("Widget"));
    ctx.push_obligation(ProofObligation::assert("trivial", "true"));

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Unknown { reason, .. } => {
            assert!(
                reason.contains("Gadget") && reason.contains("Widget"),
                "Unknown reason should list both opaque types: {}",
                reason
            );
        }
        other => {
            panic!("Expected Unknown for Opaque types, got: {:?}", other);
        }
    }
}

/// Regression guard: recognized types should still verify.
#[test]
fn test_recognized_types_still_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("flag", crate::ir::TrustVcType::parse_or_opaque("bool"));
    ctx.push_obligation(ProofObligation::assert("x_reflexive", "x == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Recognized types should still verify");
}

/// SOUNDNESS (#1926): Seq<Widget> has nested Opaque — the guard must catch
/// it via contains_opaque(), not just top-level pattern matching.
#[test]
fn test_nested_opaque_seq_returns_unknown() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<Widget>"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("trivial", "x == x"));

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Unknown { reason, .. } => {
            assert!(
                reason.contains("unrecognized") && reason.contains("Seq<Widget>"),
                "Unknown reason should mention unrecognized nested Opaque type: {}",
                reason
            );
        }
        VerifyResult::Verified => {
            panic!("SOUNDNESS BUG: Seq<Widget> must not return Verified");
        }
        other => {
            panic!("Expected Unknown for nested Opaque type, got: {:?}", other);
        }
    }
}

/// SOUNDNESS (#1926): Map<Widget, i32> has nested Opaque key — guard must
/// catch it before encoding reaches the solver.
#[test]
fn test_nested_opaque_map_returns_unknown() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<Widget, i32>"),
    );
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("trivial", "x == x"));

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Unknown { reason, .. } => {
            assert!(
                reason.contains("unrecognized") && reason.contains("Map<Widget, i32>"),
                "Unknown reason should mention unrecognized nested Opaque type: {}",
                reason
            );
        }
        VerifyResult::Verified => {
            panic!("SOUNDNESS BUG: Map<Widget, i32> must not return Verified");
        }
        other => {
            panic!(
                "Expected Unknown for nested Opaque Map key, got: {:?}",
                other
            );
        }
    }
}

/// Direct runtime string methods stay out of scope until byte semantics are modeled.
#[cfg(not(feature = "native-strings"))]
#[test]
fn test_string_len_is_rejected_without_view() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("String"));
    ctx.push_obligation(ProofObligation::assert("len_without_view", "s.len() == 0"));

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("view()"),
                "Direct string len error should point callers to view(), got: {}",
                message
            );
        }
        other => panic!("Direct String::len() must fail closed, got: {:?}", other),
    }
}

/// Direct runtime str methods stay out of scope until byte semantics are modeled.
#[cfg(not(feature = "native-strings"))]
#[test]
fn test_str_len_is_rejected_without_view() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("str"));
    ctx.push_obligation(ProofObligation::assert("len_without_view", "s.len() == 0"));

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("view()"),
                "Direct str len error should point callers to view(), got: {}",
                message
            );
        }
        other => panic!("Direct str::len() must fail closed, got: {:?}", other),
    }
}

// ========================================================================
// Assumptions-only soundness tests (Issue #1859)
// ========================================================================

/// SOUNDNESS (#1859): Context with only assumptions (no assertions) must NOT
/// return Verified. A requires() without ensures() has nothing to prove —
/// returning Verified masks missing postconditions.
#[test]
fn test_assumptions_only_returns_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("precond", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "Assumptions-only context must return Error, not Verified",
    );
}

/// SOUNDNESS (#1859): assume!(false) with no assertions must NOT return
/// Verified. Contradictory assumptions without anything to prove should be
/// an error, not silent acceptance.
#[test]
fn test_assume_false_no_assertions_returns_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("contradiction", "false"));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "assume!(false) with no assertions must return Error",
    );
}

/// SOUNDNESS (#1950): Casting to bool must produce an error, not crash with
/// bvextract(inner, u32::MAX, 0). Previously, bit_width() returned Some(0)
/// for Bool, causing a narrowing-cast underflow: target_width - 1 = u32::MAX.
#[test]
fn test_cast_to_bool_returns_error_not_crash() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert(
        "cast_bool",
        "(x as bool) == (x as bool)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "Cast to bool should return Error (unsupported cast target)",
    );
}
