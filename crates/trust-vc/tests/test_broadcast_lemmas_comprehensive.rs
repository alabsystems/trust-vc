// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Comprehensive discriminatory tests for broadcast lemma verification.
//!
//! Every positive test uses an uninterpreted function (via set_function_context)
//! where the broadcast axiom is the SOLE source of semantic information. Without
//! the broadcast, the assertion is NOT provable. This ensures each test actually
//! exercises the broadcast mechanism (discriminatory per #2230/#1638).
//!
//! Pattern from test_vt_tier11a_spec_body_axiom_double_property.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationContext.

use trust_vc_core::mode::FunctionMode;
use trust_vc_core::vc::{FunctionContext, ProofObligation, VerificationContext};
use trust_vc_core::VerifyResult;

/// Helper: create a FunctionContext for a single-arg i32 → i32 function.
fn i32_unary_fn(name: &str) -> FunctionContext {
    FunctionContext::new(
        name,
        vec![(
            "x".to_string(),
            trust_vc_core::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        trust_vc_core::ir::TrustVcType::from_str("i32").unwrap(),
        FunctionMode::Spec,
    )
}

fn i32_fn(name: &str, params: &[&str]) -> FunctionContext {
    FunctionContext::new(
        name,
        params
            .iter()
            .map(|param| {
                (
                    (*param).to_string(),
                    trust_vc_core::ir::TrustVcType::from_str("i32").unwrap(),
                )
            })
            .collect(),
        trust_vc_core::ir::TrustVcType::from_str("i32").unwrap(),
        FunctionMode::Spec,
    )
}

/// Test 1: Broadcast auto-application — uninterpreted square function.
///
/// square(x) is uninterpreted. The broadcast axiom `forall x: square(x) >= 0`
/// is the only info about square. Without it, square(5) >= 0 is unprovable.
#[test]
fn test_broadcast_basic_auto_apply() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.set_function_context(i32_unary_fn("square"));

    ctx.push_obligation(
        ProofObligation::broadcast_assume("broadcast_square_nonneg", "square(x) >= 0")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["square(x)".to_string()]]),
    );

    ctx.push_assert("square_5_nonneg", "square(5) >= 0");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Broadcast square(x) >= 0 should verify square(5) >= 0. Got: {:?}",
        result,
    );
}

/// Test 2: Broadcast instantiated for multiple arguments.
///
/// sq(x) is uninterpreted. The broadcast applies to different concrete args.
#[test]
fn test_broadcast_multiple_instantiations() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.set_function_context(i32_unary_fn("sq"));

    ctx.push_obligation(
        ProofObligation::broadcast_assume("broadcast_sq_nonneg", "sq(x) >= 0")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["sq(x)".to_string()]]),
    );

    ctx.push_assert("sq_5_nonneg", "sq(5) >= 0");
    ctx.push_assert("sq_neg3_nonneg", "sq(-3) >= 0");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Broadcast should verify sq(5) >= 0 and sq(-3) >= 0. Got: {:?}",
        result,
    );
}

/// Test 3: Multi-argument uninterpreted function.
///
/// combine(a, b) is uninterpreted with two parameters. The broadcast provides
/// combine(a, b) >= a.
#[test]
fn test_broadcast_multi_arg_function() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");
    ctx.set_function_context(i32_fn("combine", &["a", "b"]));

    ctx.push_obligation(
        ProofObligation::broadcast_assume("broadcast_combine_ge", "combine(a, b) >= a")
            .with_bound_vars(vec!["a".to_string(), "b".to_string()])
            .with_trigger_patterns(vec![vec!["combine(a, b)".to_string()]]),
    );

    ctx.push_assert("combine_ge", "combine(3, 7) >= 3");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Multi-arg broadcast should verify combine(3, 7) >= 3. Got: {:?}",
        result,
    );
}

/// Test 4: Broadcast contribution — with vs without broadcast.
///
/// Demonstrates broadcast is essential: same assertion with broadcast passes,
/// without broadcast fails. Paired positive/negative pattern per #2230.
#[test]
fn test_broadcast_contribution_paired() {
    // WITH broadcast → Verified
    {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "i32");
        ctx.set_function_context(i32_unary_fn("f"));

        ctx.push_obligation(
            ProofObligation::broadcast_assume("broadcast_f_pos", "f(x) > 0")
                .with_bound_vars(vec!["x".to_string()])
                .with_trigger_patterns(vec![vec!["f(x)".to_string()]]),
        );

        ctx.push_assert("f_5_pos", "f(5) > 0");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "With broadcast, f(5) > 0 should verify. Got: {:?}",
            result,
        );
    }

    // WITHOUT broadcast → not Verified
    {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "i32");
        ctx.set_function_context(i32_unary_fn("f"));

        ctx.push_assert("f_5_pos", "f(5) > 0");

        let result = ctx.verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Without broadcast, f(5) > 0 must NOT verify. Got: {:?}",
            result,
        );
    }
}

/// Test 5: Two broadcast axioms about the same function.
///
/// g(x) is uninterpreted. Two broadcasts provide different properties:
/// g(x) >= 0 AND g(x) <= 100. Both are needed for the range assertion.
#[test]
fn test_multiple_broadcast_axioms() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.set_function_context(i32_unary_fn("g"));

    // Broadcast 1: g(x) >= 0
    ctx.push_obligation(
        ProofObligation::broadcast_assume("broadcast_g_lower", "g(x) >= 0")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["g(x)".to_string()]]),
    );

    // Broadcast 2: g(x) <= 100
    ctx.push_obligation(
        ProofObligation::broadcast_assume("broadcast_g_upper", "g(x) <= 100")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["g(x)".to_string()]]),
    );

    // Both broadcasts needed: g(5) >= 0 AND g(5) <= 100
    ctx.push_assert("g_lower", "g(5) >= 0");
    ctx.push_assert("g_upper", "g(5) <= 100");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Two broadcasts should verify g(5) in [0, 100]. Got: {:?}",
        result,
    );
}

/// Test 6: Broadcast with sum formula — uninterpreted sum_fn.
///
/// sum_fn(n) is uninterpreted. The broadcast provides sum_fn(n) == n * (n + 1) / 2.
/// Without the broadcast, sum_fn(5) == 15 is unprovable.
#[test]
fn test_broadcast_sum_formula() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("n", "i32");
    ctx.set_function_context(i32_unary_fn("sum_fn"));

    ctx.push_obligation(
        ProofObligation::broadcast_assume("broadcast_sum_formula", "sum_fn(n) == n * (n + 1) / 2")
            .with_bound_vars(vec!["n".to_string()])
            .with_trigger_patterns(vec![vec!["sum_fn(n)".to_string()]]),
    );

    ctx.push_assert("sum_5", "sum_fn(5) == 15");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Broadcast sum formula should verify sum_fn(5) == 15. Got: {:?}",
        result,
    );
}

/// Test 7: Negative case — wrong broadcast should NOT verify.
///
/// The broadcast claims wrong_fn(x) < 0, but we assert wrong_fn(5) >= 0.
#[test]
fn test_broadcast_negative_case() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.set_function_context(i32_unary_fn("wrong_fn"));

    ctx.push_obligation(
        ProofObligation::broadcast_assume("broadcast_wrong", "wrong_fn(x) < 0")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["wrong_fn(x)".to_string()]]),
    );

    ctx.push_assert("wrong_fn_nonneg", "wrong_fn(5) >= 0");

    let result = ctx.verify();
    assert!(
        !matches!(result, VerifyResult::Verified),
        "Wrong broadcast must NOT verify contradictory assertion. Got: {:?}",
        result,
    );
}

/// Test 8: Broadcast identity — uninterpreted id_fn.
///
/// id_fn(x) is uninterpreted. The broadcast provides id_fn(x) == x.
#[test]
fn test_broadcast_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.set_function_context(i32_unary_fn("id_fn"));

    ctx.push_obligation(
        ProofObligation::broadcast_assume("broadcast_id", "id_fn(x) == x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["id_fn(x)".to_string()]]),
    );

    ctx.push_assert("id_42", "id_fn(42) == 42");
    ctx.push_assert("id_neg7", "id_fn(-7) == -7");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Broadcast id_fn(x) == x should verify id_fn(42) == 42. Got: {:?}",
        result,
    );
}

/// Test 9: Broadcast applied to multiple distinct arguments.
///
/// h(x) is uninterpreted. The broadcast provides h(x) == x + 2.
/// The assertion combines two applications: h(5) + h(3) == 12.
#[test]
fn test_broadcast_combined_applications() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.set_function_context(i32_unary_fn("h"));

    ctx.push_obligation(
        ProofObligation::broadcast_assume("broadcast_h_def", "h(x) == x + 2")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["h(x)".to_string()]]),
    );

    // Requires two instantiations: h(5)==7 and h(3)==5, so h(5)+h(3)==12
    ctx.push_assert("h_sum", "h(5) + h(3) == 12");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Broadcast h(x)==x+2 should verify h(5)+h(3)==12. Got: {:?}",
        result,
    );
}

/// Test 10: Broadcast with conditional axiom (implication pattern).
///
/// safe_div(x, y) is uninterpreted. The broadcast provides:
/// y != 0 ==> safe_div(x, y) == x / y.
#[test]
fn test_broadcast_conditional() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("y", "i32");
    ctx.set_function_context(i32_fn("safe_div", &["x", "y"]));

    // Broadcast: y != 0 implies safe_div(x, y) == x / y
    ctx.push_obligation(
        ProofObligation::broadcast_assume(
            "broadcast_safe_div",
            "y == 0 || safe_div(x, y) == x / y",
        )
        .with_bound_vars(vec!["x".to_string(), "y".to_string()])
        .with_trigger_patterns(vec![vec!["safe_div(x, y)".to_string()]]),
    );

    ctx.push_assume("divisor_nonzero", "2 != 0");
    ctx.push_assert("safe_div_10_2", "safe_div(10, 2) == 5");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Conditional broadcast should verify safe_div(10, 2) == 5. Got: {:?}",
        result,
    );
}

/// Test 11: Broadcast with absolute value property.
///
/// abs_fn(x) is uninterpreted. The broadcast provides abs_fn(x) >= 0.
/// Tests broadcast across positive, negative, and zero arguments.
#[test]
fn test_broadcast_abs_nonneg() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.set_function_context(i32_unary_fn("abs_fn"));

    ctx.push_obligation(
        ProofObligation::broadcast_assume("broadcast_abs_nonneg", "abs_fn(x) >= 0")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["abs_fn(x)".to_string()]]),
    );

    ctx.push_assert("abs_pos", "abs_fn(7) >= 0");
    ctx.push_assert("abs_neg", "abs_fn(-3) >= 0");
    ctx.push_assert("abs_zero", "abs_fn(0) >= 0");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Broadcast abs_fn(x) >= 0 should verify for all arguments. Got: {:?}",
        result,
    );
}

/// Test 12: Broadcast definition axiom — double_fn(x) == x + x.
///
/// double_fn(x) is uninterpreted. The broadcast provides its definition.
/// The assertion requires the broadcast to compute concrete values.
#[test]
fn test_broadcast_definition_axiom() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.set_function_context(i32_unary_fn("double_fn"));

    ctx.push_obligation(
        ProofObligation::broadcast_assume("broadcast_double_def", "double_fn(x) == x + x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["double_fn(x)".to_string()]]),
    );

    ctx.push_assert("double_5", "double_fn(5) == 10");
    ctx.push_assert("double_neg2", "double_fn(-2) == -4");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Broadcast double_fn(x)==x+x should verify concrete values. Got: {:?}",
        result,
    );
}
