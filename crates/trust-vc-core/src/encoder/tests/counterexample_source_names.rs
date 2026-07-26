// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! End-to-end tests for source-level counterexample variable names.
//!
//! Verifies that `AYEncoder::verify` produces counterexample strings with
//! user-facing variable names instead of raw solver helper names.
//!
//! Part of #2651.

use super::*;

// ---------------------------------------------------------------------------
// Test 1: old!() captures display as `old(x)` instead of `__trust_vc_old_x`
// ---------------------------------------------------------------------------

#[test]
fn test_counterexample_old_capture_shows_source_name() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    ctx.declare_var_typed(
        "__trust_vc_old_x",
        crate::ir::TrustVcType::Int { width: 32 },
    );

    // Register the display alias as collect_old_value would.
    ctx.register_counterexample_alias("__trust_vc_old_x", "old(x)", true);

    // Assume old(x) == x (simulating the old!() capture assumption)
    ctx.push_obligation(ProofObligation::assume(
        "old_capture_x",
        "__trust_vc_old_x == x",
    ));
    // Assert something false: x > old(x) + 100 (always false when x == old(x))
    ctx.push_obligation(ProofObligation::assert(
        "post_check",
        "x > __trust_vc_old_x + 100",
    ));

    let result = AYEncoder::verify(&ctx);
    match &result {
        VerifyResult::Counterexample { model, .. } => {
            let model_str = model.as_deref().unwrap_or("");
            assert!(
                model_str.contains("old(x)"),
                "counterexample should show 'old(x)', got: {model_str}"
            );
            assert!(
                !model_str.contains("__trust_vc_old_x"),
                "raw helper name should not appear, got: {model_str}"
            );
        }
        other => panic!("should be Counterexample, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Test 2: hidden helper variables are excluded from counterexample
// ---------------------------------------------------------------------------

#[test]
fn test_counterexample_hides_extern_temp_variables() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    ctx.declare_var_typed(
        "__trust_vc_extern_call_value_42_5",
        crate::ir::TrustVcType::Int { width: 32 },
    );

    // The extern temp should be hidden by the default classifier.
    // Assert x > 0 — this is falsifiable since x can be negative.
    ctx.push_obligation(ProofObligation::assert("nonneg", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    match &result {
        VerifyResult::Counterexample { model, .. } => {
            let model_str = model.as_deref().unwrap_or("");
            assert!(
                !model_str.contains("__trust_vc_extern"),
                "extern temp should be hidden, got: {model_str}"
            );
            assert!(
                model_str.contains("x = "),
                "user variable 'x' should appear, got: {model_str}"
            );
        }
        other => panic!("should be Counterexample, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Test 3: mut-ref SSA version displays as `place@version`
// ---------------------------------------------------------------------------

#[test]
fn test_counterexample_mutref_shows_place_at_version() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "__trust_vc_mutref_counter_0",
        crate::ir::TrustVcType::Int { width: 32 },
    );

    // Assert the mut-ref version is non-negative — falsifiable
    ctx.push_obligation(ProofObligation::assert(
        "mutref_check",
        "__trust_vc_mutref_counter_0 >= 0",
    ));

    let result = AYEncoder::verify(&ctx);
    match &result {
        VerifyResult::Counterexample { model, .. } => {
            let model_str = model.as_deref().unwrap_or("");
            assert!(
                model_str.contains("counter@0"),
                "mutref should show 'counter@0', got: {model_str}"
            );
            assert!(
                !model_str.contains("__trust_vc_mutref"),
                "raw helper name should not appear, got: {model_str}"
            );
        }
        other => panic!("should be Counterexample, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Test 4: explicit alias overrides default classifier for closure params
// ---------------------------------------------------------------------------

#[test]
fn test_counterexample_explicit_alias_shows_original_closure_param() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "__trust_vc_closure_arg0",
        crate::ir::TrustVcType::Uint { width: 8 },
    );

    // Register explicit alias: show `item` instead of hiding closure param
    ctx.register_counterexample_alias("__trust_vc_closure_arg0", "item", true);

    // Assert the param is > 200 — falsifiable for u8 (0..=255)
    ctx.push_obligation(ProofObligation::assert(
        "closure_check",
        "__trust_vc_closure_arg0 > 200",
    ));

    let result = AYEncoder::verify(&ctx);
    match &result {
        VerifyResult::Counterexample { model, .. } => {
            let model_str = model.as_deref().unwrap_or("");
            assert!(
                model_str.contains("item = "),
                "explicit alias should show 'item', got: {model_str}"
            );
            assert!(
                !model_str.contains("__trust_vc_closure"),
                "raw helper name should not appear, got: {model_str}"
            );
        }
        other => panic!("should be Counterexample, got: {other:?}"),
    }
}
