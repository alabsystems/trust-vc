// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for inline spec function body substitution (#2488).
//!
//! Validates that:
//! - `#[inline]` body axioms are extracted into the substitution table
//! - Inline function calls are replaced with the body expression
//! - Non-inline functions still use the normal UF + body axiom path
//! - The inline function name does not appear as a declared UF

use super::*;
use crate::prepared_context::prepare_context;
use crate::vc::ObligationKind;
use crate::vc::{FunctionContext, ProofObligation};

/// Helper: set up a context with a spec function body axiom.
fn setup_inline_spec_context(
    fn_name: &str,
    body_condition: &str,
    is_inline: bool,
) -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: fn_name.to_string(),
        params: vec![("x".to_string(), i32_ty())],
        return_type: i32_ty(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    let axiom_name = format!("__body_axiom_{}", fn_name);
    let call_expr = format!("{}(x)", fn_name);
    let condition = format!("{} == {}", call_expr, body_condition);
    ctx.obligations.push(
        ProofObligation::broadcast_assume(axiom_name, condition)
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec![call_expr]])
            .with_inline(is_inline),
    );
    ctx
}

#[test]
fn test_inline_spec_simple_verifies() {
    // inline spec fn double(x: i32) -> i32 { x + x }
    // Assert: double(3) == 6 should verify via body substitution.
    let mut ctx = setup_inline_spec_context("double", "x + x", true);
    ctx.push_obligation(ProofObligation::assert("check", "double(3) == 6"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inline double(3)==6 should verify via body substitution",
    );
}

#[test]
fn test_inline_spec_no_uf_declared() {
    // When a function is inline, its name should NOT appear as a declared UF
    // in the encoder's function registry — calls are substituted, not dispatched.
    let mut ctx = setup_inline_spec_context("is_pos", "(x > 0)", true);
    ctx.push_obligation(ProofObligation::assert("check", "is_pos(5)"));

    let prepared = prepare_context(&ctx).expect("inline spec context should prepare");
    let broadcast_assumptions: Vec<_> = prepared
        .obligations
        .iter()
        .filter(|obligation| matches!(obligation.kind, ObligationKind::BroadcastAssume))
        .collect();
    let slices = crate::encoder::verification::VerificationSlices::new(
        &prepared,
        &[],
        &broadcast_assumptions,
        &[],
        &[],
        &[],
    );
    let encoder = AYEncoder::setup_from_prepared(&slices, false, None)
        .expect("inline spec setup should succeed");

    assert!(
        !encoder.fn_ctx.functions.contains_key("is_pos"),
        "inline spec should not be declared as a ay UF"
    );
    assert!(
        encoder.fn_ctx.return_types.contains_key("is_pos"),
        "inline spec should still retain return-type metadata"
    );
    assert!(
        encoder.state.inline_bodies.contains_key("is_pos"),
        "inline spec body should be extracted for call-site substitution"
    );

    let result = AYEncoder::verify_prepared(&prepared);
    expect_verified(&result, "inline is_pos(5) should verify via substitution");
}

#[test]
fn test_inline_spec_module_suffixed_body_axiom_still_skips_broadcast() {
    // Proc-macro expansion names body axioms as "__body_axiom_<fn>_<module_path>".
    // Extraction is keyed by the call expression name ("double"), so the skip
    // logic must not rely on the raw obligation suffix matching exactly.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "double".to_string(),
        params: vec![("x".to_string(), i32_ty())],
        return_type: i32_ty(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });
    ctx.obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_double_test_inline_spec",
            "double(x) == x + x",
        )
        .with_bound_vars(vec!["x".to_string()])
        .with_trigger_patterns(vec![vec!["double(x)".to_string()]])
        .with_inline(true),
    );
    ctx.push_obligation(ProofObligation::assert("check", "double(3) == 6"));

    let prepared = prepare_context(&ctx).expect("suffixed inline spec context should prepare");
    let broadcast_assumptions: Vec<_> = prepared
        .obligations
        .iter()
        .filter(|obligation| matches!(obligation.kind, ObligationKind::BroadcastAssume))
        .collect();
    let slices = crate::encoder::verification::VerificationSlices::new(
        &prepared,
        &[],
        &broadcast_assumptions,
        &[],
        &[],
        &[],
    );
    let encoder = AYEncoder::setup_from_prepared(&slices, false, None)
        .expect("suffixed inline spec setup should succeed");

    assert!(
        encoder.state.inline_bodies.contains_key("double"),
        "inline extraction should be keyed by the call expression name"
    );
    assert!(
        !encoder.fn_ctx.functions.contains_key("double"),
        "inline spec should still avoid UF declaration for the extracted function"
    );
    assert_eq!(
        encoder.state.broadcast_count, 0,
        "module-suffixed inline body axioms must not consume a broadcast slot after extraction"
    );
}

#[test]
fn test_non_inline_spec_uses_axiom() {
    // Control case: same function WITHOUT inline uses normal UF + body axiom path.
    let mut ctx = setup_inline_spec_context("double", "x + x", false);
    ctx.push_obligation(ProofObligation::assert("check", "double(3) == 6"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "non-inline double still verifies via body axiom");
}

#[test]
fn test_inline_spec_nested_call_substituted() {
    // Two inline functions: double(x) = x + x, quad(x) = double(double(x))
    // Assert: quad(2) == 8 should verify with nested substitution.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "quad".to_string(),
        params: vec![("x".to_string(), i32_ty())],
        return_type: i32_ty(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Register double as helper function so it's available for encoding.
    ctx.declare_helper_function_typed("double", i32_ty(), vec![("x".to_string(), i32_ty())]);

    // double body axiom (inline)
    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_double", "double(x) == x + x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["double(x)".to_string()]])
            .with_inline(true),
    );

    // quad body axiom (inline)
    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_quad", "quad(x) == double(double(x))")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["quad(x)".to_string()]])
            .with_inline(true),
    );

    ctx.push_obligation(ProofObligation::assert("check", "quad(2) == 8"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nested inline quad(2)==8 should verify");
}

#[test]
fn test_inline_spec_counterexample_still_works() {
    // Inline function: double(x) = x + x
    // Assert: double(3) == 7 should produce a counterexample.
    let mut ctx = setup_inline_spec_context("double", "x + x", true);
    ctx.push_obligation(ProofObligation::assert("check", "double(3) == 7"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "double(3)==7 is false, should produce counterexample",
    );
}

#[test]
fn test_malformed_inline_body_falls_through_to_broadcast() {
    // A body axiom marked is_inline=true but with a shape that
    // extract_inline_body cannot parse (reversed equality: body == FnCall
    // instead of FnCall == body). Before #2568, this would silently drop
    // the axiom from BOTH paths (inline substitution returns None because
    // left is Arith not FnCall, broadcast loop skips all is_inline axioms).
    // After #2568, it falls through to the broadcast axiom path.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "test_fn".to_string(),
        params: vec![("x".to_string(), i32_ty())],
        return_type: i32_ty(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Register helper so it's available for encoding.
    ctx.declare_helper_function_typed("magic", i32_ty(), vec![("x".to_string(), i32_ty())]);

    // Reversed body axiom: "x + x == magic(x)" parses to
    // Compare { Eq, Arith { Add, Var("x"), Var("x") }, FnCall { "magic", [Var("x")] } }.
    // extract_inline_body expects FnCall on the LEFT, so returns None.
    // Trigger "magic(x)" structurally matches ground term "magic(3)".
    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_magic", "x + x == magic(x)")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["magic(x)".to_string()]])
            .with_inline(true),
    );

    // If the axiom is silently dropped: magic(3) is uninterpreted, assertion fails.
    // If the axiom falls through to broadcast: forall x. {magic(x)} x + x == magic(x),
    // instantiate with x=3: 3 + 3 == magic(3), so magic(3) == 6 is provable.
    ctx.push_obligation(ProofObligation::assert("check", "magic(3) == 6"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "malformed inline body should fall through to broadcast path (Part of #2568)",
    );
}
