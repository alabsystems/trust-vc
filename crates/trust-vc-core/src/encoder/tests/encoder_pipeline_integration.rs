// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for encoder pipeline paths: datatype encoding,
//! fuel encoding (recursive function termination), and ground pool
//! registration/flush through the full VerificationPipeline.
//!
//! These tests exercise the encoder end-to-end through `AYEncoder::verify()`
//! and `VerificationPipeline`, covering integration points that unit tests
//! for individual modules (datatype.rs, fuel.rs, ground_pool.rs) do not reach.

use super::*;
use crate::ir::TrustVcType;
use crate::vc::{FunctionContext, ProofObligation};
use crate::verification_bridge::VerificationPipeline;

// ---------------------------------------------------------------------------
// Helpers: register datatype function signatures in VerificationContext so
// that prepare_context() can lower string conditions referencing tester,
// constructor, and selector functions.
// ---------------------------------------------------------------------------

/// Registers the Option<u64> tester and constructor function signatures
/// into the VerificationContext's helper function registry so that
/// `prepare_context()` can resolve them during obligation lowering.
fn register_option_u64_datatype_fns(ctx: &mut VerificationContext) {
    let option_ty = TrustVcType::parse_or_opaque("Option<u64>");
    let u64_ty = TrustVcType::Uint { width: 64 };

    // Testers: is_Option_u64_Some(opt) -> bool, is_Option_u64_None(opt) -> bool
    ctx.declare_helper_function_typed(
        "is_Option_u64_Some",
        TrustVcType::Bool,
        vec![("__self".to_string(), option_ty.clone())],
    );
    ctx.declare_helper_function_typed(
        "is_Option_u64_None",
        TrustVcType::Bool,
        vec![("__self".to_string(), option_ty.clone())],
    );

    // Constructor: Option_u64_Some(val) -> Option<u64>
    ctx.declare_helper_function_typed(
        "Option_u64_Some",
        option_ty.clone(),
        vec![("__val".to_string(), u64_ty.clone())],
    );

    // Selector: Option_u64_Some_0(opt) -> u64
    ctx.declare_helper_function_typed(
        "Option_u64_Some_0",
        u64_ty,
        vec![("__self".to_string(), option_ty)],
    );
}

/// Registers the Result<u64, bool> tester function signatures.
fn register_result_u64_bool_datatype_fns(ctx: &mut VerificationContext) {
    let result_ty = TrustVcType::parse_or_opaque("Result<u64, bool>");

    ctx.declare_helper_function_typed(
        "is_Result_u64_bool_Ok",
        TrustVcType::Bool,
        vec![("__self".to_string(), result_ty.clone())],
    );
    ctx.declare_helper_function_typed(
        "is_Result_u64_bool_Err",
        TrustVcType::Bool,
        vec![("__self".to_string(), result_ty)],
    );
}

/// Registers the Option<i32> tester function signatures.
fn register_option_i32_datatype_fns(ctx: &mut VerificationContext) {
    let option_ty = TrustVcType::parse_or_opaque("Option<i32>");

    ctx.declare_helper_function_typed(
        "is_Option_i32_Some",
        TrustVcType::Bool,
        vec![("__self".to_string(), option_ty.clone())],
    );
    ctx.declare_helper_function_typed(
        "is_Option_i32_None",
        TrustVcType::Bool,
        vec![("__self".to_string(), option_ty)],
    );
}

// ---------------------------------------------------------------------------
// 1. Datatype encoding: struct/enum -> ay algebraic datatypes via pipeline
// ---------------------------------------------------------------------------

/// End-to-end: Option<u64> datatype variable declared through
/// VerificationContext, with an assertion about the tester function.
///
/// Exercises: register_builtin_datatypes -> declare_variant_encoding ->
/// assert_datatype_axioms -> tester symbol lookup via verify().
///
/// The assertion `is_Option_u64_Some(opt) || is_Option_u64_None(opt)` is
/// tautological by the exhaustive axiom. If datatype registration or axiom
/// emission is broken, this fails with Unknown or Counterexample.
#[test]
fn test_pipeline_datatype_option_exhaustive_tautology_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opt", TrustVcType::parse_or_opaque("Option<u64>"));
    register_option_u64_datatype_fns(&mut ctx);

    // Native datatype exhaustiveness makes this tautological. `is_some()`/
    // `is_none()` lower to the native testers `is-Option_u64_Some`/
    // `is-Option_u64_None` (renamed from the legacy `is_` UF symbols by the
    // native-datatype migration).
    ctx.push_obligation(ProofObligation::assert(
        "exhaustive",
        "opt.is_some() || opt.is_none()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Option<u64> exhaustive tautology should verify through full pipeline",
    );
}

/// End-to-end: Result<u64, bool> with disjointness axiom through pipeline.
///
/// Exercises: multi-variant datatype registration with different field types,
/// tester disjointness axiom. Asserts that is_Ok(res) implies !is_Err(res).
#[test]
fn test_pipeline_datatype_result_disjointness_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res", TrustVcType::parse_or_opaque("Result<u64, bool>"));
    register_result_u64_bool_datatype_fns(&mut ctx);

    // Disjointness: (res is Ok) => !(res is Err). The `is`-variant tests lower to
    // the native testers `is-Result_u64_bool_Ok`/`is-Result_u64_bool_Err`.
    ctx.push_obligation(ProofObligation::assume("is_ok", "res is Ok"));
    ctx.push_obligation(ProofObligation::assert("not_err", "!(res is Err)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Result<u64, bool> disjointness should verify: is_Ok => !is_Err",
    );
}

/// End-to-end: Option<u64> constructor + tester roundtrip through
/// VerificationPipeline.
///
/// Exercises: constructor function lookup, tester function lookup,
/// the tester-constructor axiom (is_Some(Some(v)) == true).
///
/// Uses VerificationPipeline (not AYEncoder::verify) to exercise the
/// bridge path.
#[test]
fn test_pipeline_datatype_option_constructor_tester_via_verification_pipeline() {
    let mut pipeline = VerificationPipeline::new();
    pipeline
        .context_mut()
        .declare_var_typed("v", TrustVcType::parse_or_opaque("u64"));
    pipeline
        .context_mut()
        .declare_var_typed("opt", TrustVcType::parse_or_opaque("Option<u64>"));
    register_option_u64_datatype_fns(pipeline.context_mut());

    // Assume opt == Some(v)
    pipeline.add_obligation(ProofObligation::assume(
        "opt_is_some_v",
        "opt == Option_u64_Some(v)",
    ));

    // Assert the native tester recognizes it as Some. `opt.is_some()` lowers to
    // the native tester `is-Option_u64_Some(opt)` (renamed from the legacy `is_`
    // UF symbol by the native-datatype migration).
    pipeline.add_obligation(ProofObligation::assert("is_some", "opt.is_some()"));

    let result = pipeline.verify();
    expect_verified(
        &result,
        "Option<u64> constructor+tester roundtrip should verify via VerificationPipeline",
    );
}

/// End-to-end: datatype symbols used only inside an obligation expression.
///
/// Regression coverage for obligations that mention Option constructors and
/// testers without any declared `Option<_>` variable in the verification
/// context. Setup must still register the datatype UF symbols before encoding.
#[test]
fn test_pipeline_datatype_expression_only_option_tester_verifies() {
    let mut ctx = VerificationContext::new();

    ctx.push_obligation(ProofObligation::assert(
        "expr_only_option_tester",
        "{ let opt: Option<u32> = if true { Some(42u32) } else { None::<u32> }; opt.is_some() }",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Option<u32> used only inside an obligation expression should auto-register",
    );
}

/// End-to-end: Result constructors produced by Option lowering are registered
/// even when neither Option nor Result appears as a declared variable.
#[test]
fn test_pipeline_datatype_expression_only_result_constructor_verifies() {
    let mut ctx = VerificationContext::new();

    ctx.push_obligation(ProofObligation::assert(
        "expr_only_result_constructor",
        "{ let opt: Option<u32> = Some(42u32); opt.ok_or_else(|| 0u32) } == Ok::<u32, u32>(42u32)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Result<u32, u32> produced inside an obligation expression should auto-register",
    );
}

// ---------------------------------------------------------------------------
// 2. Fuel encoding: recursive function termination via ay fuel axioms
// ---------------------------------------------------------------------------

/// End-to-end: factorial base case through full pipeline.
///
/// Exercises: fuel.rs encode_fuel_axioms -> direct defining axiom emission ->
/// E-matching instantiation (1 round for base case).
///
/// fact(0) == 1 is the base case of the recursive definition and requires
/// exactly one E-matching round to unfold.
#[test]
fn test_pipeline_fuel_factorial_base_case_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", TrustVcType::parse_or_opaque("i32"));

    ctx.set_function_context(FunctionContext {
        name: "fact".to_string(),
        params: vec![("n".to_string(), TrustVcType::from_str("i32").unwrap())],
        return_type: TrustVcType::from_str("i32").unwrap(),
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

    // Base case: fact(0) == 1, requires 1 E-matching round
    ctx.push_obligation(ProofObligation::assert("fact_0", "fact(0) == 1"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fact(0) == 1 should verify (base case, 1 E-matching round)",
    );
}

/// End-to-end: factorial with small concrete input through pipeline.
///
/// Exercises: fuel.rs encode_fuel_axioms -> direct defining axiom ->
/// multi-round E-matching chaining (fact(5) needs 5 unfoldings).
///
/// fact(5) = 5*4*3*2*1 = 120. With MAX_EMATCHING_ROUNDS = 8, 5 unfoldings
/// are within reach.
#[test]
fn test_pipeline_fuel_factorial_small_concrete_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", TrustVcType::parse_or_opaque("i32"));

    ctx.set_function_context(FunctionContext {
        name: "fact".to_string(),
        params: vec![("n".to_string(), TrustVcType::from_str("i32").unwrap())],
        return_type: TrustVcType::from_str("i32").unwrap(),
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

    // fact(5) == 120: needs 5 E-matching rounds (within limit of 8)
    ctx.push_obligation(ProofObligation::assert("fact_5", "fact(5) == 120"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fact(5) == 120 should verify (5 E-matching rounds, within fuel limit)",
    );
}

/// End-to-end: Fibonacci through pipeline with multi-recursive body axiom.
///
/// Exercises: fuel encoding with a function body that contains TWO recursive
/// calls (fib(n-1) + fib(n-2)), testing that E-matching chains correctly
/// through both branches of the recursion tree.
///
/// fib(0)=0, fib(1)=1, fib(5)=5 needs: fib(5)=fib(4)+fib(3),
/// fib(4)=fib(3)+fib(2), etc. The tree flattens to ~5 distinct calls.
#[test]
fn test_pipeline_fuel_fibonacci_concrete_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", TrustVcType::parse_or_opaque("i32"));

    ctx.set_function_context(FunctionContext {
        name: "fib".to_string(),
        params: vec![("n".to_string(), TrustVcType::from_str("i32").unwrap())],
        return_type: TrustVcType::from_str("i32").unwrap(),
        is_recursive: true,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_fib",
            "fib(n) == { if n == 0 { 0 } else { if n == 1 { 1 } else { fib(n - 1) + fib(n - 2) } } }",
        )
        .with_bound_vars(vec!["n".to_string()])
        .with_trigger_patterns(vec![vec!["fib(n)".to_string()]]),
    );

    // fib(5) == 5: exercises multi-recursive unfolding
    ctx.push_obligation(ProofObligation::assert("fib_5", "fib(5) == 5"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fib(5) == 5 should verify with multi-recursive E-matching chaining",
    );
}

// ---------------------------------------------------------------------------
// 3. Ground pool: registration and flush through the verify pipeline
// ---------------------------------------------------------------------------

/// End-to-end: ground pool flush integrates with broadcast axiom instantiation
/// through the full verification pipeline.
///
/// Exercises: ground_pool.register -> register_axiom -> flush_ground_axioms_to_fixpoint
/// through AYEncoder::verify(). The broadcast axiom `forall j: a.index(j) >= 0`
/// is instantiated via ground pool seeding when `a.index(0)` appears in the goal.
///
/// Without ground pool flush, the quantified broadcast has no ground trigger
/// terms and the solver returns Unknown.
#[test]
fn test_pipeline_ground_pool_broadcast_instantiation_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("j", TrustVcType::parse_or_opaque("u64"));

    ctx.push_obligation(ProofObligation::assume("len_bound", "a.len() > 0"));

    // Broadcast: all elements are non-negative
    ctx.obligations.push(
        ProofObligation::broadcast_assume("all_nonneg", "a.index(j) >= 0")
            .with_bound_vars(vec!["j".to_string()])
            .with_trigger_patterns(vec![vec!["a.index(j)".to_string()]]),
    );

    // Assert element 0 is non-negative (ground pool + E-matching)
    ctx.push_obligation(ProofObligation::assert("elem_0_nonneg", "a.index(0) >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ground pool flush should instantiate broadcast for a.index(0) >= 0",
    );
}

/// End-to-end: ground pool with spec function body axiom and ground term reuse.
///
/// Exercises the interaction between fuel encoding (which registers body
/// axioms with the ground pool) and flush_ground_axioms_to_fixpoint (which
/// instantiates them for concrete call sites).
///
/// The spec function `double(n) == n + n` is defined as a body axiom.
/// The ground pool should register the axiom, and when `double(5)` appears
/// in the assertion, flush should instantiate `double(5) == 5 + 5 == 10`.
#[test]
fn test_pipeline_ground_pool_fuel_body_axiom_flush_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", TrustVcType::parse_or_opaque("i32"));

    ctx.set_function_context(FunctionContext {
        name: "double".to_string(),
        params: vec![("n".to_string(), TrustVcType::from_str("i32").unwrap())],
        return_type: TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Body axiom: double(n) == n + n
    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_double", "double(n) == n + n")
            .with_bound_vars(vec!["n".to_string()])
            .with_trigger_patterns(vec![vec!["double(n)".to_string()]]),
    );

    // Assert double(5) == 10
    ctx.push_obligation(ProofObligation::assert("double_5", "double(5) == 10"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ground pool should flush body axiom for double(5) == 10",
    );
}

/// End-to-end: VerificationPipeline with both datatype and fuel encoding
/// exercised simultaneously.
///
/// Exercises the interaction between datatype registration (Option<i32>)
/// and spec function body axiom (abs(n)), verifying that both encoder
/// subsystems coexist correctly in a single pipeline run.
#[test]
fn test_pipeline_combined_datatype_and_fuel_coexist() {
    let mut pipeline = VerificationPipeline::new();
    pipeline
        .context_mut()
        .declare_var_typed("n", TrustVcType::parse_or_opaque("i32"));
    pipeline
        .context_mut()
        .declare_var_typed("opt", TrustVcType::parse_or_opaque("Option<i32>"));
    register_option_i32_datatype_fns(pipeline.context_mut());

    pipeline
        .context_mut()
        .set_function_context(FunctionContext {
            name: "abs".to_string(),
            params: vec![("n".to_string(), TrustVcType::from_str("i32").unwrap())],
            return_type: TrustVcType::from_str("i32").unwrap(),
            is_recursive: false,
            mode: crate::mode::FunctionMode::Spec,
            trait_bounds: vec![],
        });

    // Body axiom: abs(n) == if n >= 0 { n } else { 0 - n }
    pipeline.context_mut().obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_abs",
            "abs(n) == { if n >= 0 { n } else { 0 - n } }",
        )
        .with_bound_vars(vec!["n".to_string()])
        .with_trigger_patterns(vec![vec!["abs(n)".to_string()]]),
    );

    // abs(5) == 5 exercises the fuel/body axiom path
    pipeline.add_obligation(ProofObligation::assert("abs_positive", "abs(5) == 5"));

    // Option exhaustive tautology exercises the datatype path. `is_some()`/
    // `is_none()` lower to the native testers `is-Option_i32_Some`/
    // `is-Option_i32_None`.
    pipeline.add_obligation(ProofObligation::assert(
        "opt_exhaustive",
        "opt.is_some() || opt.is_none()",
    ));

    let result = pipeline.verify();
    expect_verified(
        &result,
        "combined datatype + fuel should verify through VerificationPipeline",
    );
}
