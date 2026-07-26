// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proc-macro integration tests for datatype and multi-type spec functions.
//!
//! These tests exercise the full `#[trust_vc::proof]` → `VerificationPipeline` → ay
//! pipeline for features that previously only had encoder-level coverage (#2429).
//!
//! Findings from pipeline investigation:
//! - Option<u64> TYPE STRING threads correctly through extract_type_string
//!   (spaces removed by `.replace(' ', "")`) and parses via TrustVcType::from_str.
//! - Option CONSTRUCTOR expressions (None, Some) now resolve through ir_lowering
//!   via DatatypeVariantMeta registration (#2487).
//! - Bool-branching spec functions verify correctly through the full pipeline.
//!
//! Part of #2429, #2487.

mod common;

use trust_vc::{proof, spec};

// === Spec function with bool/u64 branching through pipeline ===

#[spec]
fn double_or_zero(x: u64, flag: bool) -> u64 {
    if flag {
        x + x
    } else {
        0u64
    }
}

#[proof]
fn proof_double_or_zero_when_true() {
    let _ = double_or_zero(0u64, true);
    trust_vc::assert!(double_or_zero(5u64, true) == 10u64);
}

/// Spec function with if-else branching verifies for the true branch.
#[test]
fn test_double_or_zero_when_true_verifies() {
    let _ = common::verify_should_pass(proof_double_or_zero_when_true);
}

#[proof]
fn proof_double_or_zero_when_false() {
    let _ = double_or_zero(0u64, false);
    trust_vc::assert!(double_or_zero(5u64, false) == 0u64);
}

/// Spec function with if-else branching verifies for the false branch.
#[test]
fn test_double_or_zero_when_false_verifies() {
    let _ = common::verify_should_pass(proof_double_or_zero_when_false);
}

// === Multi-argument spec function ===

#[spec]
fn bounded_add(x: u64, y: u64) -> u64 {
    x + y
}

#[proof]
fn proof_bounded_add_basic() {
    let _ = bounded_add(0u64, 0u64);
    trust_vc::assert!(bounded_add(3u64, 4u64) == 7u64);
}

/// Multi-argument spec function verifies through pipeline.
#[test]
fn test_bounded_add_basic_verifies() {
    let _ = common::verify_should_pass(proof_bounded_add_basic);
}

// === Negative test: incorrect spec assertion ===

#[proof]
fn proof_double_or_zero_incorrect() {
    let _ = double_or_zero(0u64, true);
    trust_vc::assert!(double_or_zero(5u64, true) == 11u64);
}

/// Incorrect assertion about spec function should produce counterexample.
#[test]
fn test_double_or_zero_incorrect_fails() {
    let _ = common::verify_should_fail(proof_double_or_zero_incorrect);
}

// === Datatype constructor path lowering (#2487) ===

/// Helper: builds `TrustVcType::Datatype` for `Option<u64>`.
fn option_u64_type() -> trust_vc_core::ir::TrustVcType {
    use trust_vc_core::ir::{DatatypeVariant, TrustVcType};
    TrustVcType::Datatype {
        name: "Option<u64>".to_string(),
        variants: vec![
            DatatypeVariant::new("None", vec![]),
            DatatypeVariant::new(
                "Some",
                vec![("0".to_string(), TrustVcType::Uint { width: 64 })],
            ),
        ],
    }
}

/// Proof that `None` constructor resolves through the full pipeline.
///
/// Uses VerificationContext directly. A `u64` companion variable ensures the
/// encoder uses BV mode (not int_mode) so constructor field sorts match.
#[test]
fn test_option_none_constructor_verifies() {
    use trust_vc_core::vc::VerificationContext;
    use trust_vc_core::VerifyResult;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opt", option_u64_type());
    ctx.declare_var_parsed("val", "u64");
    ctx.push_assume("setup", "opt == None");
    ctx.push_assert("check", "opt == None");

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Option None constructor should verify, got: {:?}",
        result,
    );
}

/// Proof that `Some(42u64)` constructor call resolves through the full pipeline.
#[test]
fn test_option_some_constructor_verifies() {
    use trust_vc_core::vc::VerificationContext;
    use trust_vc_core::VerifyResult;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opt", option_u64_type());
    ctx.declare_var_parsed("val", "u64");
    ctx.push_assume("setup", "opt == Some(42u64)");
    ctx.push_assert("check", "opt == Some(42u64)");

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Option Some constructor should verify, got: {:?}",
        result,
    );
}

/// Negative: `Some(42)` should not equal `Some(99)`.
#[test]
fn test_option_some_mismatch_fails() {
    use trust_vc_core::vc::VerificationContext;
    use trust_vc_core::VerifyResult;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opt", option_u64_type());
    ctx.declare_var_parsed("val", "u64");
    ctx.push_assume("setup", "opt == Some(42u64)");
    ctx.push_assert("check", "opt == Some(99u64)");

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "Option Some(42) != Some(99), should not verify, got: {:?}",
        result,
    );
}
