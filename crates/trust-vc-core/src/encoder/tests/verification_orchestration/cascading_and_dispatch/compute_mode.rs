// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Compute mode with an equality assumption discharging the variable.
/// After #2454, compute mode collects bindings from assumptions and
/// substitutes before evaluation. `assume(x == 42)` + `assert(x == 42)`
/// in compute mode should verify (42 == 42 → true). Part of #2154, #2405, #2454.
#[test]
fn test_compute_mode_with_assumption_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("known_x", "x == 42"));

    let obligation = crate::vc::ProofObligation::new(
        "compute_check".to_string(),
        "x == 42".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Compute mode with assumption x==42 should verify x==42",
    );
}

/// Compute mode: concrete arithmetic evaluates to true → Verified.
/// Equivalent to `assert_by_compute!(2 + 3 == 5)`. Part of #2405.
#[test]
fn test_compute_mode_concrete_true_returns_verified() {
    let mut ctx = VerificationContext::new();
    let obligation = crate::vc::ProofObligation::new(
        "compute_arith".to_string(),
        "2 + 3 == 5".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Compute mode: 2+3==5 should verify via const eval");
}

/// Compute mode: concrete arithmetic evaluates to false → Counterexample.
/// Equivalent to `assert_by_compute!(2 + 3 == 6)`. Part of #2405.
#[test]
fn test_compute_mode_concrete_false_returns_counterexample() {
    let mut ctx = VerificationContext::new();
    let obligation = crate::vc::ProofObligation::new(
        "compute_arith_false".to_string(),
        "2 + 3 == 6".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "Compute mode: 2+3==6 should return Counterexample");
}

/// Compute mode: symbolic variable → Unknown (not fully concrete).
/// Equivalent to `assert_by_compute!(x + 1 == 2)` with symbolic x.
/// Part of #2405.
#[test]
fn test_compute_mode_symbolic_returns_unknown() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    let obligation = crate::vc::ProofObligation::new(
        "compute_symbolic".to_string(),
        "x + 1 == 2".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_unknown(
        &result,
        "Compute mode with symbolic x should return Unknown",
    );
}

/// `assert_by_compute!(...; compute_only)` lowers to the same Compute solver
/// mode but must retain compute_only's fail-closed requirement: any symbolic
/// residue after substitution is Unknown, not an SMT proof attempt.
#[test]
fn test_compute_only_alias_symbolic_residue_returns_unknown() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    let obligation = crate::vc::ProofObligation::new(
        "compute_only_symbolic".to_string(),
        "x + 1 == 2".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_unknown(
        &result,
        "compute_only alias with symbolic residue should return Unknown",
    );
}

/// Concrete `compute_only` syntax is represented as Compute mode after parsing;
/// the evaluator should still discharge fully reducible arithmetic directly.
#[test]
fn test_compute_only_alias_concrete_true_returns_verified() {
    let mut ctx = VerificationContext::new();
    let obligation = crate::vc::ProofObligation::new(
        "compute_only_arith".to_string(),
        "2 + 3 == 5".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "compute_only alias should verify concrete arithmetic",
    );
}

/// Compute mode can unfold concrete recursive spec-function body axioms when
/// every recursive branch selected by concrete conditionals stays within fuel.
#[test]
fn test_compute_mode_recursive_spec_function_verifies_with_bounded_unfolding() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.set_function_context(crate::vc::FunctionContext {
        name: "fib_compute".to_string(),
        params: vec![(
            "n".to_string(),
            crate::ir::TrustVcType::from_str("u64").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("u64").unwrap(),
        is_recursive: true,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });
    ctx.obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_fib_compute",
            "fib_compute(n) == { if n <= 1 { n } else { fib_compute(n - 1) + fib_compute(n - 2) } }",
        )
        .with_bound_vars(vec!["n".to_string()])
        .with_trigger_patterns(vec![vec!["fib_compute(n)".to_string()]]),
    );

    let obligation = crate::vc::ProofObligation::new(
        "compute_recursive_fib".to_string(),
        "fib_compute(6) == 8".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Compute mode should verify concrete recursive fib within bounded unfolding",
    );
}

/// Memoized compute can evaluate Verus-shaped `nat` recursion without
/// materializing the exponential `fib(n-1) + fib(n-2)` call tree.
#[test]
fn test_compute_mode_recursive_spec_fib_26_verifies_with_memoization() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::Nat);
    ctx.set_function_context(crate::vc::FunctionContext {
        name: "fib_compute".to_string(),
        params: vec![("n".to_string(), crate::ir::TrustVcType::Nat)],
        return_type: crate::ir::TrustVcType::Nat,
        is_recursive: true,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });
    ctx.obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_fib_compute",
            "fib_compute(n) == { if n == 0 { 0 } else if n == 1 { 1 } else { fib_compute((n - 1) as nat) + fib_compute((n - 2) as nat) } }",
        )
        .with_bound_vars(vec!["n".to_string()])
        .with_trigger_patterns(vec![vec!["fib_compute(n)".to_string()]]),
    );

    let obligation = crate::vc::ProofObligation::new(
        "compute_recursive_fib_26".to_string(),
        "fib_compute(26) == 121393".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Compute mode should verify fib(26) through memoized recursive evaluation",
    );
}

/// The same memoized compute path must still reject wrong concrete results.
#[test]
fn test_compute_mode_recursive_spec_fib_26_wrong_result_is_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::Nat);
    ctx.set_function_context(crate::vc::FunctionContext {
        name: "fib_compute".to_string(),
        params: vec![("n".to_string(), crate::ir::TrustVcType::Nat)],
        return_type: crate::ir::TrustVcType::Nat,
        is_recursive: true,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });
    ctx.obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_fib_compute",
            "fib_compute(n) == { if n == 0 { 0 } else if n == 1 { 1 } else { fib_compute((n - 1) as nat) + fib_compute((n - 2) as nat) } }",
        )
        .with_bound_vars(vec!["n".to_string()])
        .with_trigger_patterns(vec![vec!["fib_compute(n)".to_string()]]),
    );

    let obligation = crate::vc::ProofObligation::new(
        "compute_recursive_fib_26_wrong".to_string(),
        "fib_compute(26) == 121394".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Compute mode should counterexample an incorrect fib(26) value",
    );
}

/// Recursive compute remains fail-closed: once bounded unfolding is exhausted,
/// compute returns Unknown instead of falling back to SMT for the residual call.
#[test]
fn test_compute_mode_recursive_spec_function_fuel_exhaustion_returns_unknown() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.set_function_context(crate::vc::FunctionContext {
        name: "countdown_compute".to_string(),
        params: vec![(
            "n".to_string(),
            crate::ir::TrustVcType::from_str("u64").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("u64").unwrap(),
        is_recursive: true,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });
    ctx.obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_countdown_compute",
            "countdown_compute(n) == { if n == 0 { 0 } else { countdown_compute(n - 1) } }",
        )
        .with_bound_vars(vec!["n".to_string()])
        .with_trigger_patterns(vec![vec!["countdown_compute(n)".to_string()]]),
    );

    let obligation = crate::vc::ProofObligation::new(
        "compute_recursive_countdown_exhausted".to_string(),
        "countdown_compute(33) == 0".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_unknown(
        &result,
        "Compute mode should fail closed when recursive unfolding fuel is exhausted",
    );
}

/// Compute mode: symbolic arithmetic with let-binding assumptions verifies.
/// Equivalent to `let a = 2; let b = 3; assert_by_compute!(a + b == 5)`.
/// Assumptions discharge both variables, substitution reduces to `2 + 3 == 5`.
/// Part of #2454.
#[test]
fn test_compute_mode_symbolic_with_let_bindings_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("let_a", "a == 2"));
    ctx.push_obligation(ProofObligation::assume("let_b", "b == 3"));

    let obligation = crate::vc::ProofObligation::new(
        "compute_let_bindings".to_string(),
        "a + b == 5".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Compute mode: a+b==5 with a==2,b==3 should verify");
}

/// Compute mode: chained equality substitution verifies.
/// Equivalent to `let y = 3; assume!(x == y + 2); assert_by_compute!(x == 5)`.
/// y→3 propagates into x's binding: x→y+2→3+2→5. Part of #2454.
#[test]
fn test_compute_mode_chained_equality_substitution_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("let_y", "y == 3"));
    ctx.push_obligation(ProofObligation::assume("x_eq", "x == y + 2"));

    let obligation = crate::vc::ProofObligation::new(
        "compute_chained".to_string(),
        "x == 5".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Compute mode: x==5 with y==3,x==y+2 should verify via chained substitution",
    );
}

/// Compute mode: symbolic with false result returns Counterexample.
/// Assumptions make the expression concrete but false: a==2,b==3 but a+b==6.
/// Part of #2454.
#[test]
fn test_compute_mode_symbolic_false_returns_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("let_a", "a == 2"));
    ctx.push_obligation(ProofObligation::assume("let_b", "b == 3"));

    let obligation = crate::vc::ProofObligation::new(
        "compute_sym_false".to_string(),
        "a + b == 6".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Compute mode: a+b==6 with a==2,b==3 should return Counterexample",
    );
}

/// Compute mode: block-local let bindings with shadowing reduce to false.
/// Mirrors the upstream assert_by_compute `lets_bad` shape with a local
/// arithmetic helper instead of a spec function call. This prevents compute
/// mode from silently treating both shadowed `x` bindings as one value.
#[test]
fn test_compute_mode_block_let_shadowing_false_returns_counterexample() {
    let mut ctx = VerificationContext::new();
    let obligation = crate::vc::ProofObligation::new(
        "compute_lets_bad_shadowing".to_string(),
        "{ let x: i32 = 4; let r1: i32 = x + 1; let x: i32 = 5; let r2: i32 = x + 1; r1 == r2 }"
            .to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Compute mode: lets_bad-style shadowing should return Counterexample",
    );
}

/// Compute mode: unresolved variable still returns Unknown (fail-closed).
/// Assumption binds a but not b. Part of #2454.
#[test]
fn test_compute_mode_partial_binding_returns_unknown() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("let_a", "a == 2"));

    let obligation = crate::vc::ProofObligation::new(
        "compute_partial".to_string(),
        "a + b == 5".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_unknown(
        &result,
        "Compute mode with unresolved b should return Unknown",
    );
}

/// Compute mode: non-equality assumptions are silently ignored (fail-closed).
/// Only `var == expr` bindings are extracted; range assumptions like `x > 0`
/// are skipped. Part of #2454.
#[test]
fn test_compute_mode_non_equality_assumption_ignored() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("range", "x > 0"));

    let obligation = crate::vc::ProofObligation::new(
        "compute_non_eq".to_string(),
        "x > 0".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_unknown(
        &result,
        "Compute mode with non-equality assumption should return Unknown",
    );
}

/// Regression: a Compute assertion that evaluates to true must NOT short-circuit
/// the entire verification — subsequent failing assertions must still be checked.
/// Before the fix, `return VerifyResult::Verified` on Compute(true) skipped all
/// remaining assertions. Part of #2405.
#[test]
fn test_compute_true_does_not_skip_later_failing_assertion() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));

    let compute = crate::vc::ProofObligation::new(
        "compute_pass".to_string(),
        "2 + 3 == 5".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(compute);
    ctx.push_obligation(ProofObligation::assert("failing_after_compute", "x < 0"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "A passing Compute assertion must not skip later failing assertions",
    );
}
