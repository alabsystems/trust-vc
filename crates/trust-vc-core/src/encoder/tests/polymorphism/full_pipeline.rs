// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Full pipeline integration tests: AYEncoder::verify() with VerificationContext.
//!
//! These tests simulate the exact obligations that proc macros produce,
//! exercising prepare_context → verify_typed → setup_from_prepared → broadcast
//! encoding with polymorphic types. If the encoder-level tests above pass
//! but these fail, the gap is in the string-based obligation pipeline.

use super::*;

/// Full pipeline: `identity<T>(y) == y` via AYEncoder::verify().
///
/// Simulates what `#[trust_vc::spec] fn identity<T>(x: T) -> T { x }` and
/// `#[trust_vc::proof] fn test() { let y: i32 = 5; assert!(identity(y) == y); }`
/// produce through the proc-macro pipeline:
///   1. Variable x: TypeParam("T") (spec function's formal param)
///   2. Variable y: Int{32} (proof function's local)
///   3. FunctionContext for identity with TypeParam params
///   4. BroadcastAssume body axiom: "identity(x) == x"
///   5. Assume y == 5
///   6. Assert identity(y) == y
#[test]
fn test_polymorphic_identity_full_pipeline_verify() {
    use crate::encoder::AYEncoder;
    use crate::ir::TrustVcType;
    use crate::vc::{FunctionContext, ProofObligation, VerificationContext};

    let mut ctx = VerificationContext::new();

    // Spec function's formal parameter: x: TypeParam("T")
    ctx.declare_var_typed("x", TrustVcType::TypeParam("T".to_string()));
    // Proof function's local: y: i32
    ctx.declare_var_typed("y", TrustVcType::Int { width: 32 });

    // Function context: identity<T>(x: T) -> T
    ctx.set_function_context(FunctionContext {
        name: "identity".to_string(),
        params: vec![("x".to_string(), TrustVcType::TypeParam("T".to_string()))],
        return_type: TrustVcType::TypeParam("T".to_string()),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Body axiom: forall x. identity(x) == x
    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_identity", "identity(x) == x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["identity(x)".to_string()]]),
    );

    // Assume y == 5
    ctx.push_obligation(crate::vc::ProofObligation::assume("y_val", "y == 5"));

    // Assert identity(y) == y
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "identity_y",
        "identity(y) == y",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "identity::<i32>(5) == 5 should verify through full pipeline",
    );
}

/// Full pipeline negative test: `identity<T>(y) == 6` should fail.
#[test]
fn test_polymorphic_identity_full_pipeline_fails_wrong_value() {
    use crate::encoder::AYEncoder;
    use crate::ir::TrustVcType;
    use crate::vc::{FunctionContext, ProofObligation, VerificationContext};

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::TypeParam("T".to_string()));
    ctx.declare_var_typed("y", TrustVcType::Int { width: 32 });

    ctx.set_function_context(FunctionContext {
        name: "identity".to_string(),
        params: vec![("x".to_string(), TrustVcType::TypeParam("T".to_string()))],
        return_type: TrustVcType::TypeParam("T".to_string()),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_identity", "identity(x) == x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["identity(x)".to_string()]]),
    );

    ctx.push_obligation(crate::vc::ProofObligation::assume("y_val", "y == 5"));
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "identity_wrong",
        "identity(y) == 6",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "identity::<i32>(5) == 6 should produce a counterexample",
    );
}

/// Full pipeline regression: proc-macro generic proofs can assert on a
/// literal-only polymorphic call without any concrete locals in scope.
///
/// This mirrors `assert!(spec_identity(5u64) == 5u64)` from the proc-macro
/// integration suite. Before #2658 Slice 3, the encoder inferred the
/// FnCall's compare type as raw `TypeParam("T")`, stayed in global Int mode
/// because only the formal `x: T` was declared, and then tried to box an
/// Int-sorted `5u64` into `Box_u64 : BV64 -> Poly`, producing a sort mismatch.
#[test]
fn test_polymorphic_identity_full_pipeline_literal_only_u64_verify() {
    use crate::encoder::AYEncoder;
    use crate::ir::TrustVcType;
    use crate::vc::{FunctionContext, ProofObligation, VerificationContext};

    let mut ctx = VerificationContext::new();

    ctx.declare_var_typed("x", TrustVcType::TypeParam("T".to_string()));
    ctx.set_function_context(FunctionContext {
        name: "identity".to_string(),
        params: vec![("x".to_string(), TrustVcType::TypeParam("T".to_string()))],
        return_type: TrustVcType::TypeParam("T".to_string()),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });
    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_identity", "identity(x) == x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["identity(x)".to_string()]]),
    );
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "identity_literal_u64",
        "identity(5u64) == 5u64",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "identity::<u64>(5u64) == 5u64 should verify without concrete locals",
    );
}

/// Literal-only negative case for the same proc-macro regression shape:
/// `identity(5u64) == 6u64` must fail even when no concrete locals are
/// declared in the verification context.
#[test]
fn test_polymorphic_identity_full_pipeline_literal_only_u64_wrong_value_fails() {
    use crate::encoder::AYEncoder;
    use crate::ir::TrustVcType;
    use crate::vc::{FunctionContext, ProofObligation, VerificationContext};

    let mut ctx = VerificationContext::new();

    ctx.declare_var_typed("x", TrustVcType::TypeParam("T".to_string()));
    ctx.set_function_context(FunctionContext {
        name: "identity".to_string(),
        params: vec![("x".to_string(), TrustVcType::TypeParam("T".to_string()))],
        return_type: TrustVcType::TypeParam("T".to_string()),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });
    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_identity", "identity(x) == x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["identity(x)".to_string()]]),
    );
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "identity_literal_u64_wrong",
        "identity(5u64) == 6u64",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "identity::<u64>(5u64) == 6u64 should produce a counterexample without concrete locals",
    );
}

/// Full pipeline: two spec functions — `identity<T>` and `double` — called from
/// one proof context. Validates that `declare_helper_function_typed` ensures ALL
/// called functions are available in TypeEnv, not just the last one (which
/// overwrites `function_context`). Regression test for #2431.
#[test]
fn test_multi_function_helper_typed_registry_verify() {
    use crate::encoder::AYEncoder;
    use crate::ir::TrustVcType;
    use crate::vc::{FunctionContext, ProofObligation, VerificationContext};

    let mut ctx = VerificationContext::new();

    // Spec function formal params for identity<T>
    ctx.declare_var_typed("x", TrustVcType::TypeParam("T".to_string()));
    // Concrete locals
    ctx.declare_var_typed("y", TrustVcType::Int { width: 32 });
    // Spec function formal params for double (monomorphic)
    ctx.declare_var_typed("n", TrustVcType::Int { width: 32 });

    // Register BOTH functions via typed helper registry (as spec expansion would).
    ctx.declare_helper_function_typed(
        "identity",
        TrustVcType::TypeParam("T".to_string()),
        vec![("x".to_string(), TrustVcType::TypeParam("T".to_string()))],
    );
    ctx.declare_helper_function_typed(
        "double",
        TrustVcType::Int { width: 32 },
        vec![("n".to_string(), TrustVcType::Int { width: 32 })],
    );

    // Last-called function_context (simulating spec expansion overwrite).
    // Only "double" survives in function_context — "identity" is ONLY in
    // helper_functions_typed. This is the scenario #2431 fixes.
    ctx.set_function_context(FunctionContext {
        name: "double".to_string(),
        params: vec![("n".to_string(), TrustVcType::Int { width: 32 })],
        return_type: TrustVcType::Int { width: 32 },
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Body axioms for both functions.
    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_identity", "identity(x) == x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["identity(x)".to_string()]]),
    );
    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_double", "double(n) == n + n")
            .with_bound_vars(vec!["n".to_string()])
            .with_trigger_patterns(vec![vec!["double(n)".to_string()]]),
    );

    ctx.push_obligation(crate::vc::ProofObligation::assume("y_val", "y == 5"));
    // Assert uses BOTH functions: identity(y) from helper_functions_typed,
    // double(y) from function_context. Both must resolve in TypeEnv.
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "combined",
        "identity(y) == y",
    ));
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "double_check",
        "double(y) == 10",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Multi-function proof (identity + double) should verify",
    );
}

/// Full pipeline: two type params — `first<A,B>(x, flag) == x`.
///
/// Simulates `#[trust_vc::spec] fn first<A, B>(a: A, b: B) -> A { a }`
/// with a call `first(x, flag)` where x: i32, flag: bool.
/// Validates multi-type-param binding inference through the full pipeline.
#[test]
fn test_polymorphic_two_params_full_pipeline_verify() {
    use crate::encoder::AYEncoder;
    use crate::ir::TrustVcType;
    use crate::vc::{FunctionContext, ProofObligation, VerificationContext};

    let mut ctx = VerificationContext::new();

    // Spec function's formal params
    ctx.declare_var_typed("a", TrustVcType::TypeParam("A".to_string()));
    ctx.declare_var_typed("b", TrustVcType::TypeParam("B".to_string()));
    // Proof function's locals
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("flag", TrustVcType::Bool);

    ctx.set_function_context(FunctionContext {
        name: "first".to_string(),
        params: vec![
            ("a".to_string(), TrustVcType::TypeParam("A".to_string())),
            ("b".to_string(), TrustVcType::TypeParam("B".to_string())),
        ],
        return_type: TrustVcType::TypeParam("A".to_string()),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_first", "first(a, b) == a")
            .with_bound_vars(vec!["a".to_string(), "b".to_string()])
            .with_trigger_patterns(vec![vec!["first(a, b)".to_string()]]),
    );

    ctx.push_obligation(crate::vc::ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "first_eq",
        "first(x, flag) == x",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "first::<i32, bool>(42, flag) == 42 should verify through full pipeline",
    );
}
