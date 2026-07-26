//! Recursive body-axiom integration tests: GCD variants and fuel
//! exhaustion. Part of #2155, #2187.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from function_body_axioms/mod.rs (#2145).

use super::*;

/// GCD with the direct recursive axiom: gcd(a, b) == if b == 0 { a } else { gcd(b, a % b) }.
/// gcd(6,4) needs 3 unfoldings: gcd(6,4) → gcd(4,2) → gcd(2,0) → 2.
/// This is the key competition test — directly addresses the VerifyThis
/// gcd challenge failure. Part of #2155.
#[test]
fn test_recursive_gcd_verifies_with_direct_axiom() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("i32"));

    ctx.set_function_context(FunctionContext {
        name: "gcd".to_string(),
        params: vec![
            (
                "a".to_string(),
                crate::ir::TrustVcType::from_str("i32").unwrap(),
            ),
            (
                "b".to_string(),
                crate::ir::TrustVcType::from_str("i32").unwrap(),
            ),
        ],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: true,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_gcd",
            "gcd(a, b) == { if b == 0 { a } else { gcd(b, a % b) } }",
        )
        .with_bound_vars(vec!["a".to_string(), "b".to_string()])
        .with_trigger_patterns(vec![vec!["gcd(a, b)".to_string()]]),
    );

    // gcd(6,4): gcd(6,4) → gcd(4,2) → gcd(2,0) → 2  (3 unfoldings / E-matching rounds)
    ctx.push_obligation(ProofObligation::assert("gcd_6_4_is_2", "gcd(6, 4) == 2"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gcd(6, 4) == 2 should verify with the direct recursive axiom",
    );
}

/// GCD base case: gcd(a, 0) == a is trivially the base case, verifiable
/// with a single E-matching instantiation.
#[test]
fn test_recursive_gcd_base_case_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("i32"));

    ctx.set_function_context(FunctionContext {
        name: "gcd".to_string(),
        params: vec![
            (
                "a".to_string(),
                crate::ir::TrustVcType::from_str("i32").unwrap(),
            ),
            (
                "b".to_string(),
                crate::ir::TrustVcType::from_str("i32").unwrap(),
            ),
        ],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: true,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_gcd",
            "gcd(a, b) == { if b == 0 { a } else { gcd(b, a % b) } }",
        )
        .with_bound_vars(vec!["a".to_string(), "b".to_string()])
        .with_trigger_patterns(vec![vec!["gcd(a, b)".to_string()]]),
    );

    // gcd(7, 0) == 7: just the base case, 1 unfolding
    ctx.push_obligation(ProofObligation::assert("gcd_base", "gcd(7, 0) == 7"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gcd(7, 0) == 7 should verify (base case)");
}

/// GCD with medium inputs: gcd(48, 18) == 6 requires 4 unfoldings:
/// gcd(48,18) → gcd(18,12) → gcd(12,6) → gcd(6,0) = 6.
/// This formerly failed under too-shallow stratified unfolding, but succeeds
/// with the direct recursive axiom because ay can chain four rounds.
/// Directly addresses the VerifyThis gcd_2015_c2 counterexample failure.
/// Part of #2187.
#[test]
fn test_recursive_gcd_medium_inputs_verifies_with_multiround_ematching() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("i32"));

    ctx.set_function_context(FunctionContext {
        name: "gcd".to_string(),
        params: vec![
            (
                "a".to_string(),
                crate::ir::TrustVcType::from_str("i32").unwrap(),
            ),
            (
                "b".to_string(),
                crate::ir::TrustVcType::from_str("i32").unwrap(),
            ),
        ],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: true,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_gcd",
            "gcd(a, b) == { if b == 0 { a } else { gcd(b, a % b) } }",
        )
        .with_bound_vars(vec!["a".to_string(), "b".to_string()])
        .with_trigger_patterns(vec![vec!["gcd(a, b)".to_string()]]),
    );

    // gcd(48,18): 4 unfoldings / E-matching rounds.
    ctx.push_obligation(ProofObligation::assert(
        "gcd_48_18_is_6",
        "gcd(48, 18) == 6",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gcd(48, 18) == 6 should verify with multi-round E-matching",
    );
}

/// Symbolic one-step GCD reasoning: the direct defining axiom enables
/// `gcd(a, b) == gcd(b, a % b)` for symbolic `a, b` via E-matching.
/// Part of #2187, #2386.
#[test]
fn test_recursive_gcd_symbolic_one_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("i32"));

    ctx.set_function_context(FunctionContext {
        name: "gcd".to_string(),
        params: vec![
            (
                "a".to_string(),
                crate::ir::TrustVcType::from_str("i32").unwrap(),
            ),
            (
                "b".to_string(),
                crate::ir::TrustVcType::from_str("i32").unwrap(),
            ),
        ],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: true,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_gcd",
            "gcd(a, b) == { if b == 0 { a } else { gcd(b, a % b) } }",
        )
        .with_bound_vars(vec!["a".to_string(), "b".to_string()])
        .with_trigger_patterns(vec![vec!["gcd(a, b)".to_string()]]),
    );

    ctx.push_obligation(ProofObligation::assume("b_pos", "b > 0"));
    ctx.push_obligation(ProofObligation::assert(
        "gcd_one_step",
        "gcd(a, b) == gcd(b, a % b)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Symbolic gcd one-step should verify with recursive ground instantiation",
    );
}

/// E-matching round exhaustion: with 8 E-matching rounds, fact(12)==479001600
/// needs 12 recursive unfoldings — beyond the implicit fuel limit.
/// Part of #2187, #2577.
#[test]
fn test_recursive_fuel_exhaustion_not_provable() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // Cap per-assertion hard timeout at 2s to keep the 3-stage retry cascade
    // under 10s total (2s × 3 stages = 6s). Part of #2577.
    ctx.set_rlimit(2_000);

    ctx.set_function_context(FunctionContext {
        name: "fact".to_string(),
        params: vec![(
            "n".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: true,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_fact",
            "fact(n) == { if n == 0 { 1 } else { n * fact(n - 1) } }",
        )
        .with_bound_vars(vec!["n".to_string()])
        .with_trigger_patterns(vec![vec!["fact(n)".to_string()]]),
    );

    // fact(12) needs 12 unfoldings (12→...→0→base). The direct defining
    // axiom's implicit fuel is bounded by MAX_EMATCHING_ROUNDS (8), so
    // this exceeds the solver's reach.
    ctx.push_obligation(ProofObligation::assert(
        "fact_12_is_479001600",
        "fact(12) == 479001600",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "fact(12) should NOT verify with 8 E-matching rounds",
    );
}
