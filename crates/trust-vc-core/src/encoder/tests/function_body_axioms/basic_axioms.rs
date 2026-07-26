//! Basic spec-function body axiom tests: double, identity, multi-param,
//! symbolic reasoning, recursive without base case, non-recursive acceptance,
//! and missing bound variable validation.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from function_body_axioms/mod.rs (#2145).

use super::*;

#[test]
fn test_spec_fn_double_body_axiom_verified() {
    let mut ctx = VerificationContext::new();
    register_spec_function(&mut ctx, "double", &[("x", "i32")], "i32");
    add_body_axiom(
        &mut ctx,
        "double",
        &[("x", "i32")],
        "double(x) == x + x",
        "double(x)",
    );

    ctx.push_obligation(ProofObligation::assert("double_3_is_6", "double(3) == 6"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "double(3) == 6 should verify with body axiom");
}

#[test]
fn test_uninterpreted_fn_double_not_provable() {
    let mut ctx = VerificationContext::new();
    register_spec_function(&mut ctx, "double", &[("x", "i32")], "i32");

    ctx.push_obligation(ProofObligation::assert("double_3_is_6", "double(3) == 6"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "double(3) == 6 should not verify without body axiom",
    );
}

#[test]
fn test_spec_fn_identity_body_axiom_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));

    register_spec_function(&mut ctx, "id", &[("x", "i32")], "i32");
    add_body_axiom(&mut ctx, "id", &[("x", "i32")], "id(x) == x", "id(x)");

    ctx.push_obligation(ProofObligation::assert("id_y_is_y", "id(y) == y"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "id(y) == y should verify with body axiom");
}

#[test]
fn test_spec_fn_multi_param_body_axiom_verified() {
    let mut ctx = VerificationContext::new();

    register_spec_function(&mut ctx, "add", &[("a", "i32"), ("b", "i32")], "i32");
    add_body_axiom(
        &mut ctx,
        "add",
        &[("a", "i32"), ("b", "i32")],
        "add(a, b) == a + b",
        "add(a, b)",
    );

    ctx.push_obligation(ProofObligation::assert("add_2_3_is_5", "add(2, 3) == 5"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "add(2, 3) == 5 should verify with body axiom");
}

#[test]
fn test_spec_fn_body_axiom_with_symbolic_reasoning() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));

    register_spec_function(&mut ctx, "double", &[("x", "i32")], "i32");
    add_body_axiom(
        &mut ctx,
        "double",
        &[("x", "i32")],
        "double(x) == x + x",
        "double(x)",
    );

    ctx.push_obligation(ProofObligation::assert(
        "double_y_def",
        "double(y) == y + y",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "double(y) == y + y should verify with body axiom");
}

/// Recursive body axioms without a base case are handled via the direct
/// defining axiom, but the solver cannot prove assertions that require
/// base case knowledge. Without `fact(0) == 1`, the E-matching chain
/// terminates at an unknown value, so `fact(3) == 6` is not provable
/// from `fact(x) == x * fact(x - 1)` alone.
/// Part of #2155, #2577.
#[test]
fn test_recursive_body_axiom_without_base_case_not_provable() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // Cap per-assertion hard timeout at 2s to keep the 3-stage retry cascade
    // under 10s total (2s × 3 stages = 6s). Part of #2577.
    ctx.set_rlimit(2_000);

    // Register function context as recursive
    ctx.set_function_context(FunctionContext {
        name: "fact".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: true,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Body axiom without base case — the recursive axiom unfolds, but the
    // solver still cannot determine the terminal value.
    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_fact", "fact(x) == x * fact(x - 1)")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["fact(x)".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::assert("fact_3_is_6", "fact(3) == 6"));

    let result = AYEncoder::verify(&ctx);
    // Recursive body-axiom encoding succeeds (no Error), but the assertion
    // is not provable because the base case is missing.
    expect_fail_closed(
        &result,
        "recursive body axiom without base case should not verify",
    );
    expect_encodes_without_error(&result, "recursive body-axiom encoding");
}

/// Confirms non-recursive body axioms remain accepted (guard is targeted).
/// Paired with `test_recursive_body_axiom_rejected` to prevent over-broad
/// rejection. Part of #2155.
#[test]
fn test_nonrecursive_body_axiom_still_accepted() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));

    // Register function context as NON-recursive
    ctx.set_function_context(FunctionContext {
        name: "double".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Body axiom is safe for non-recursive functions
    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_double", "double(x) == x + x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["double(x)".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::assert("double_3_is_6", "double(3) == 6"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "non-recursive body axiom should still verify");
}

#[test]
fn test_body_axiom_requires_bound_var_declaration() {
    let mut ctx = VerificationContext::new();

    register_spec_function(&mut ctx, "double", &[("x", "i32")], "i32");
    // Intentionally omit ctx.declare_var("x", "i32") to validate fail-closed behavior.
    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_double", "double(x) == x + x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["double(x)".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::assert("double_3_is_6", "double(3) == 6"));

    let result = AYEncoder::verify(&ctx);
    expect_error(&result, "missing bound variable declaration should error");
}
