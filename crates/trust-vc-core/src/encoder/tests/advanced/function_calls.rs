//! Function registration, application, and multi-segment path tests.
//!
//! Tests: recursive function declaration, zero-arity constants, distinct
//! arguments, multi-segment path resolution, and error paths.
//!
//! Issues: #1539, #1552
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// Function registration and application tests (Issues #1539, #1552)
// ========================================================================

/// Test that recursive functions are encoded as uninterpreted functions
/// with proper arity, not as constants. Verifies fix for issue #1539.
///
/// The bug: `register_function_context` used `declare_const` which made
/// `f(1)` and `f(2)` identical (same constant), losing all argument info.
/// The fix: use `declare_fun` so `f(1)` and `f(2)` are distinct terms.
#[test]
fn test_recursive_function_declared_as_uninterpreted_function() {
    use crate::vc::FunctionContext;

    let mut encoder = AYEncoder::new();

    let func_ctx = FunctionContext {
        name: "factorial".to_string(),
        params: vec![(
            "n".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: true,
        mode: crate::mode::FunctionMode::Exec,
        trait_bounds: vec![],
    };

    // Should succeed — declares factorial as an uninterpreted function
    let result = encoder.register_function_context(&func_ctx);
    assert!(result.is_ok(), "Failed to register function: {:?}", result);

    // The function should be in the functions map, NOT in variables
    assert!(
        encoder.fn_ctx.functions.contains_key("factorial"),
        "Recursive function should be registered as FuncDecl"
    );
    assert!(
        !encoder.variables.contains_key("factorial"),
        "N-arity function should NOT be in variables (that was the bug)"
    );
}

/// Test that zero-arity recursive functions are declared as constants.
#[test]
fn test_zero_arity_function_declared_as_constant() {
    use crate::vc::FunctionContext;

    let mut encoder = AYEncoder::new();

    let func_ctx = FunctionContext {
        name: "get_value".to_string(),
        params: vec![],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Exec,
        trait_bounds: vec![],
    };

    let result = encoder.register_function_context(&func_ctx);
    assert!(result.is_ok(), "Failed to register function: {:?}", result);

    // Zero-arity: should be a constant in variables map
    assert!(
        encoder.variables.contains_key("get_value"),
        "Zero-arity function should be in variables"
    );
}

#[test]
fn test_zero_arity_seq_empty_constructor_length_is_zero() {
    use crate::vc::FunctionContext;

    let mut encoder = AYEncoder::new();
    let func_ctx = FunctionContext {
        name: format!(
            "{}trust_vc_types_Seq_i32_empty",
            crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX
        ),
        params: vec![],
        return_type: crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Int {
            width: 32,
        })),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    };

    encoder
        .register_function_context(&func_ctx)
        .expect("collection constructor registration should succeed");

    let len_term = *encoder
        .collection_lengths
        .get(&func_ctx.name)
        .expect("Seq::empty constructor should seed collection length metadata");
    // Route A models spec-collection lengths as unbounded non-negative `Int`,
    // so build the comparison constant in the length term's own sort (`Int`
    // here) rather than a fixed-width bitvector. The behaviour under test —
    // the empty constructor length is fixed at zero — is unchanged.
    let zero = match encoder.solver.term_sort(len_term) {
        ay_dpll::api::Sort::Int => encoder.solver.int_const(0),
        ay_dpll::api::Sort::BitVec(bv) => encoder
            .solver
            .try_bv_const(0, bv.width)
            .expect("zero bitvector should build"),
        other => panic!("unexpected length sort {other:?}"),
    };
    let len_eq_zero = encoder
        .solver
        .try_eq(len_term, zero)
        .expect("empty constructor length equality should build");
    let len_not_zero = encoder
        .solver
        .try_not(len_eq_zero)
        .expect("negated empty constructor length equality should build");
    encoder
        .solver
        .try_assert_term(len_not_zero)
        .expect("negated empty constructor length equality should assert");

    let result = check_sat_with_bv_watchdog(&mut encoder);
    assert!(
        result.is_unsat(),
        "Seq::empty constructor length must be fixed at zero"
    );
}

/// `setup_from_prepared` must preserve zero-arity function contexts as encoder
/// constants so later typed obligation encoding can resolve `helper()`.
#[test]
fn test_setup_from_prepared_registers_zero_arity_function_constant() {
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.set_function_context(crate::vc::FunctionContext {
        name: "get_value".to_string(),
        params: vec![],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    let prepared = crate::prepared_context::prepare_context(&ctx)
        .expect("prepare_context should preserve zero-arity function context");
    let slices =
        crate::encoder::verification::VerificationSlices::new(&prepared, &[], &[], &[], &[], &[]);
    let encoder = AYEncoder::setup_from_prepared(&slices, false, None)
        .expect("setup_from_prepared should register zero-arity function contexts");

    assert!(
        encoder.variables.contains_key("get_value"),
        "zero-arity function context should be registered as a constant during setup"
    );
    assert!(
        encoder.fn_ctx.return_types.contains_key("get_value"),
        "zero-arity function context should populate the return-type table during setup"
    );
}

/// Test that function application produces distinct terms for different arguments.
///
/// This is the core soundness property: f(1) != f(2) must be satisfiable
/// (since f is uninterpreted, the solver can assign different values).
#[test]
fn test_function_application_distinct_arguments() {
    use crate::vc::FunctionContext;

    let mut encoder = AYEncoder::new();

    // Declare parameter variable
    encoder.solver.declare_const("n", Sort::bitvec(32));

    let func_ctx = FunctionContext {
        name: "f".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: true,
        mode: crate::mode::FunctionMode::Exec,
        trait_bounds: vec![],
    };

    encoder.register_function_context(&func_ctx).unwrap();

    // Create f(1) and f(2)
    let func_decl = encoder.fn_ctx.functions.get("f").unwrap().clone();
    let one = encoder.solver.try_bv_const(1, 32).unwrap();
    let two = encoder.solver.try_bv_const(2, 32).unwrap();
    let f_one = encoder.solver.try_apply(&func_decl, &[one]).unwrap();
    let f_two = encoder.solver.try_apply(&func_decl, &[two]).unwrap();

    // Assert f(1) != f(2) — should be SAT for uninterpreted function
    let eq = encoder.solver.try_eq(f_one, f_two).unwrap();
    let neq = encoder.solver.try_not(eq).unwrap();
    encoder.solver.try_assert_term(neq).unwrap();

    // Use the production-style watchdog so the test stays compatible with
    // non-Send solver internals while preserving BV timeout coverage.
    let result = check_sat_with_bv_watchdog(&mut encoder);
    assert!(
        result.is_sat(),
        "f(1) != f(2) should be satisfiable for uninterpreted function"
    );
}

// ========================================================================
// Multi-segment function call tests (Issue #1552)
// ========================================================================

#[test]
fn test_multi_segment_function_call_full_path() {
    // Register a function as "math::double" and call it as math::double(x)
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "math::double".to_string(),
        params: vec![(
            "n".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Exec,
        trait_bounds: vec![],
    });
    // math::double is uninterpreted, so f(x) == f(x) is trivially true
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "reflexive",
        "math::double(x) == math::double(x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "math::double(x) == math::double(x) should verify");
}

#[test]
fn test_multi_segment_function_call_qualified_name_mismatch_errors() {
    // Calling Math::double when only "double" is registered should error
    // (no implicit last-segment fallback). Before #2169 this silently
    // defaulted the return type to Bool; now it correctly reports
    // a TypeInference error for the unregistered qualified path.
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "double".to_string(),
        params: vec![(
            "n".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Exec,
        trait_bounds: vec![],
    });
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "reflexive",
        "Math::double(x) == Math::double(x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "Math::double(x) with only 'double' registered should error",
    );
}

#[test]
fn test_multi_segment_function_call_unregistered_error() {
    // Calling an unregistered multi-segment function should give an error
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "call_unknown",
        "unknown::func(x) == 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "unknown::func(x) should produce an error when not registered",
    );
}

// ========================================================================
// Opaque return type rejection (#2248 Finding 3, #1926)
// ========================================================================

/// Top-level unknown return type (e.g., Vec<i32>) must be rejected.
/// Strict from_str rejects unknown types at parse time; the
/// contains_opaque guard is defense-in-depth for lenient parsing.
#[test]
fn test_register_function_context_rejects_opaque_return_type() {
    use crate::vc::FunctionContext;

    let mut encoder = AYEncoder::new();
    let func_ctx = FunctionContext {
        name: "get_name".to_string(),
        params: vec![(
            "id".to_string(),
            crate::ir::TrustVcType::from_str("u64").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::Opaque("Vec<i32>".to_string()),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Exec,
        trait_bounds: vec![],
    };

    let result = encoder.register_function_context(&func_ctx);
    assert!(
        result.is_err(),
        "Unknown return type 'Vec<i32>' should be rejected, got: {:?}",
        result
    );
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("Unknown type") || err_msg.contains("Unsupported return type"),
        "Error should mention unknown/unsupported type, got: {}",
        err_msg
    );
}

/// SOUNDNESS (#1926): Nested unknown type in return type (e.g., Seq<Vec<i32>>)
/// must be rejected. Strict from_str rejects at parse time (inner `Vec<i32>`
/// fails). The contains_opaque guard provides defense-in-depth.
#[test]
fn test_register_function_context_rejects_nested_opaque_return_type() {
    use crate::vc::FunctionContext;

    let mut encoder = AYEncoder::new();
    let func_ctx = FunctionContext {
        name: "get_items".to_string(),
        params: vec![],
        return_type: crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Opaque(
            "Vec<i32>".to_string(),
        ))),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Exec,
        trait_bounds: vec![],
    };

    let result = encoder.register_function_context(&func_ctx);
    assert!(
        result.is_err(),
        "Nested unknown return type Seq<Vec<i32>> must be rejected, got: {:?}",
        result
    );
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("Unknown type") || err_msg.contains("Unsupported return type"),
        "Error should mention unknown/unsupported type, got: {}",
        err_msg
    );
}
