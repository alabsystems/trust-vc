// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ir::TrustVcType;
use crate::mode::FunctionMode;

#[test]
fn test_function_context_creation() {
    // Test creating a FunctionContext with all fields
    let func_ctx = FunctionContext {
        name: "factorial".to_string(),
        params: vec![("n".to_string(), TrustVcType::from_str("u64").unwrap())],
        return_type: TrustVcType::from_str("u64").unwrap(),
        is_recursive: true,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    };

    assert_eq!(func_ctx.name, "factorial");
    assert_eq!(func_ctx.params.len(), 1);
    assert_eq!(func_ctx.params[0].0, "n");
    assert_eq!(func_ctx.params[0].1, TrustVcType::from_str("u64").unwrap());
    assert_eq!(func_ctx.return_type, TrustVcType::from_str("u64").unwrap());
    assert!(func_ctx.is_recursive);
}

#[test]
fn test_function_context_clone() {
    // Test that FunctionContext implements Clone correctly
    let func_ctx = FunctionContext {
        name: "fibonacci".to_string(),
        params: vec![
            ("n".to_string(), TrustVcType::from_str("u32").unwrap()),
            (
                "cache".to_string(),
                TrustVcType::Opaque("HashMap<u32, u32>".to_string()),
            ),
        ],
        return_type: TrustVcType::from_str("u32").unwrap(),
        is_recursive: true,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    };

    let cloned = func_ctx.clone();
    assert_eq!(cloned.name, func_ctx.name);
    assert_eq!(cloned.params.len(), func_ctx.params.len());
    assert_eq!(cloned.params[0].0, func_ctx.params[0].0);
    assert_eq!(cloned.params[1].1, func_ctx.params[1].1);
    assert_eq!(cloned.return_type, func_ctx.return_type);
    assert_eq!(cloned.is_recursive, func_ctx.is_recursive);
    assert_eq!(cloned.mode, func_ctx.mode);
}

#[test]
fn test_set_function_context() {
    // Test setting function context in VerificationContext
    let mut ctx = VerificationContext::new();

    // Initially no function context
    assert!(ctx.function_context.is_none());

    // Create and set a function context
    let func_ctx = FunctionContext {
        name: "sum".to_string(),
        params: vec![
            ("a".to_string(), TrustVcType::from_str("i32").unwrap()),
            ("b".to_string(), TrustVcType::from_str("i32").unwrap()),
        ],
        return_type: TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    };

    ctx.set_function_context(func_ctx.clone());

    // Verify it was set correctly
    assert!(ctx.function_context.is_some());
    let stored = ctx
        .function_context
        .as_ref()
        .expect("function_context was just set");
    assert_eq!(stored.name, "sum");
    assert_eq!(stored.params.len(), 2);
    assert_eq!(stored.return_type, TrustVcType::from_str("i32").unwrap());
    assert!(!stored.is_recursive);
}

#[test]
fn test_set_function_context_exec_enables_mode_overflow_checks() {
    let mut ctx = VerificationContext::new();
    assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Allow);
    assert!(!ctx.check_overflow());

    ctx.set_function_context(FunctionContext {
        name: "exec_add".to_string(),
        params: vec![("x".to_string(), TrustVcType::from_str("u8").unwrap())],
        return_type: TrustVcType::from_str("u8").unwrap(),
        is_recursive: false,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    });

    assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Error);
    assert!(ctx.check_overflow());
}

#[test]
fn test_set_function_context_proof_keeps_allow_overflow_behavior() {
    let mut ctx = VerificationContext::new();
    ctx.set_function_context(FunctionContext {
        name: "lemma".to_string(),
        params: vec![("x".to_string(), TrustVcType::from_str("u8").unwrap())],
        return_type: TrustVcType::Opaque("()".to_string()),
        is_recursive: false,
        mode: FunctionMode::Proof,
        trait_bounds: vec![],
    });

    assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Allow);
    assert!(!ctx.check_overflow());
}

#[test]
fn test_set_function_context_preserves_explicit_overflow_override() {
    let mut ctx = VerificationContext::new();
    ctx.set_overflow_behavior(OverflowBehavior::Truncate);

    ctx.set_function_context(FunctionContext {
        name: "exec_add".to_string(),
        params: vec![("x".to_string(), TrustVcType::from_str("u8").unwrap())],
        return_type: TrustVcType::from_str("u8").unwrap(),
        is_recursive: false,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    });

    assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Truncate);
    assert!(!ctx.check_overflow());
    assert_eq!(ctx.div0_behavior(), Div0Behavior::Error);
    assert_eq!(ctx.bitshift_behavior(), BitshiftBehavior::Error);
}

#[test]
fn test_set_function_context_updates_auto_derived_behavior_on_mode_change() {
    let mut ctx = VerificationContext::new();

    ctx.set_function_context(FunctionContext {
        name: "exec_add".to_string(),
        params: vec![("x".to_string(), TrustVcType::from_str("u8").unwrap())],
        return_type: TrustVcType::from_str("u8").unwrap(),
        is_recursive: false,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    });
    assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Error);

    ctx.set_function_context(FunctionContext {
        name: "spec_add".to_string(),
        params: vec![("x".to_string(), TrustVcType::from_str("u8").unwrap())],
        return_type: TrustVcType::from_str("u8").unwrap(),
        is_recursive: false,
        mode: FunctionMode::Spec,
        trait_bounds: vec![],
    });

    assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Allow);
    assert!(!ctx.check_overflow());
}

#[test]
fn test_set_overflow_behavior_after_exec_context_keeps_mode_derived_other_checks() {
    let mut ctx = VerificationContext::new();
    ctx.set_function_context(FunctionContext {
        name: "exec_add".to_string(),
        params: vec![("x".to_string(), TrustVcType::from_str("u8").unwrap())],
        return_type: TrustVcType::from_str("u8").unwrap(),
        is_recursive: false,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    });

    ctx.set_overflow_behavior(OverflowBehavior::Truncate);

    assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Truncate);
    assert_eq!(ctx.div0_behavior(), Div0Behavior::Error);
    assert_eq!(ctx.bitshift_behavior(), BitshiftBehavior::Error);
}

#[test]
fn test_explicit_overflow_override_respects_spec_mode_regardless_of_order() {
    let mut before_context = VerificationContext::new();
    before_context.set_overflow_behavior(OverflowBehavior::Error);
    before_context.set_function_context(FunctionContext {
        name: "lemma".to_string(),
        params: vec![("x".to_string(), TrustVcType::from_str("u8").unwrap())],
        return_type: TrustVcType::Opaque("()".to_string()),
        is_recursive: false,
        mode: FunctionMode::Spec,
        trait_bounds: vec![],
    });

    let mut after_context = VerificationContext::new();
    after_context.set_function_context(FunctionContext {
        name: "lemma".to_string(),
        params: vec![("x".to_string(), TrustVcType::from_str("u8").unwrap())],
        return_type: TrustVcType::Opaque("()".to_string()),
        is_recursive: false,
        mode: FunctionMode::Spec,
        trait_bounds: vec![],
    });
    after_context.set_overflow_behavior(OverflowBehavior::Error);

    for ctx in [before_context, after_context] {
        assert_eq!(ctx.overflow_behavior(), OverflowBehavior::Error);
        assert_eq!(ctx.div0_behavior(), Div0Behavior::Allow);
        assert_eq!(ctx.bitshift_behavior(), BitshiftBehavior::Allow);
    }
}

#[test]
fn test_function_context_with_verification() {
    // Test that function context works with full verification workflow
    let mut ctx = VerificationContext::new();

    // Set up a recursive function context
    let func_ctx = FunctionContext {
        name: "count_down".to_string(),
        params: vec![("n".to_string(), TrustVcType::from_str("u64").unwrap())],
        return_type: TrustVcType::Opaque("()".to_string()),
        is_recursive: true,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    };
    ctx.set_function_context(func_ctx);

    // Add relevant variables and obligations
    ctx.declare_var_typed("n", TrustVcType::Uint { width: 64 });
    ctx.add_measure_nonneg("n");
    ctx.add_measure_decreases("n", "n", "n - 1");

    // Verify context is properly set up
    assert!(ctx.function_context.is_some());
    assert_eq!(ctx.variables.len(), 1);
    assert_eq!(ctx.obligations.len(), 2);

    // Check that the function context correctly identifies recursion
    assert!(
        ctx.function_context
            .as_ref()
            .expect("function_context was set")
            .is_recursive
    );
}

#[test]
fn test_function_context_non_recursive() {
    // Test non-recursive function context
    let func_ctx = FunctionContext {
        name: "add".to_string(),
        params: vec![
            ("x".to_string(), TrustVcType::from_str("i32").unwrap()),
            ("y".to_string(), TrustVcType::from_str("i32").unwrap()),
        ],
        return_type: TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    };

    assert!(!func_ctx.is_recursive);
    assert_eq!(func_ctx.params.len(), 2);
}

#[test]
fn test_function_context_no_params() {
    // Test function with no parameters
    let func_ctx = FunctionContext {
        name: "get_constant".to_string(),
        params: vec![],
        return_type: TrustVcType::from_str("u32").unwrap(),
        is_recursive: false,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    };

    assert_eq!(func_ctx.params.len(), 0);
    assert_eq!(func_ctx.return_type, TrustVcType::from_str("u32").unwrap());
}

#[test]
fn test_function_context_complex_types() {
    // Test function with complex parameter types
    let func_ctx = FunctionContext {
        name: "process_data".to_string(),
        params: vec![
            (
                "data".to_string(),
                TrustVcType::Opaque("Vec<u8>".to_string()),
            ),
            (
                "config".to_string(),
                TrustVcType::Opaque("Config".to_string()),
            ),
            (
                "callback".to_string(),
                TrustVcType::Opaque("fn(u8) -> bool".to_string()),
            ),
        ],
        return_type: TrustVcType::Opaque("Result<Vec<u8>, Error>".to_string()),
        is_recursive: false,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    };

    assert_eq!(func_ctx.params.len(), 3);
    assert_eq!(
        func_ctx.params[2].1,
        TrustVcType::Opaque("fn(u8) -> bool".to_string())
    );
    assert_eq!(
        func_ctx.return_type,
        TrustVcType::Opaque("Result<Vec<u8>, Error>".to_string())
    );
}

#[test]
fn test_function_context_update() {
    // Test updating function context
    let mut ctx = VerificationContext::new();

    // Set initial context
    let func_ctx1 = FunctionContext {
        name: "func1".to_string(),
        params: vec![("a".to_string(), TrustVcType::from_str("i32").unwrap())],
        return_type: TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    };
    ctx.set_function_context(func_ctx1);

    assert_eq!(
        ctx.function_context
            .as_ref()
            .expect("function_context was set")
            .name,
        "func1"
    );

    // Update with new context
    let func_ctx2 = FunctionContext {
        name: "func2".to_string(),
        params: vec![("b".to_string(), TrustVcType::from_str("u64").unwrap())],
        return_type: TrustVcType::from_str("u64").unwrap(),
        is_recursive: true,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    };
    ctx.set_function_context(func_ctx2);

    // Verify update worked
    assert_eq!(
        ctx.function_context
            .as_ref()
            .expect("function_context was set")
            .name,
        "func2"
    );
    assert!(
        ctx.function_context
            .as_ref()
            .expect("function_context was set")
            .is_recursive
    );
}

#[test]
fn test_function_context_debug() {
    // Test that Debug trait works for FunctionContext
    let func_ctx = FunctionContext {
        name: "debug_test".to_string(),
        params: vec![("x".to_string(), TrustVcType::from_str("i32").unwrap())],
        return_type: TrustVcType::Opaque("()".to_string()),
        is_recursive: false,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    };

    let debug_str = format!("{:?}", func_ctx);
    assert!(debug_str.contains("debug_test"));
    assert!(debug_str.contains("is_recursive: false"));
}

#[test]
fn test_function_context_with_requires_ensures() {
    // Test that function context works with requires/ensures obligations
    let mut ctx = VerificationContext::new();

    let func_ctx = FunctionContext {
        name: "divide".to_string(),
        params: vec![
            (
                "numerator".to_string(),
                TrustVcType::from_str("i32").unwrap(),
            ),
            (
                "denominator".to_string(),
                TrustVcType::from_str("i32").unwrap(),
            ),
        ],
        return_type: TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    };
    ctx.set_function_context(func_ctx);

    // Add typical requires/ensures for a divide function
    ctx.declare_var_typed("numerator", TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("denominator", TrustVcType::Int { width: 32 });
    // Using push_obligation for requires (precondition)
    ctx.push_obligation(ProofObligation::assume(
        "denominator_nonzero",
        "denominator != 0",
    ));
    // Using push_obligation for ensures (postcondition check)
    ctx.push_obligation(ProofObligation::assert(
        "result_bounded",
        "result <= numerator",
    ));

    // Verify proper setup
    assert!(ctx.function_context.is_some());
    assert_eq!(
        ctx.function_context
            .as_ref()
            .expect("function_context was set")
            .name,
        "divide"
    );
    assert_eq!(ctx.obligations.len(), 2);

    // Check obligation types (assume maps to Assume, assert maps to Assert)
    let assume_count = ctx
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assume))
        .count();
    let assert_count = ctx
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assert))
        .count();
    assert_eq!(assume_count, 1);
    assert_eq!(assert_count, 1);
}

#[test]
fn test_function_context_edge_cases() {
    // Test edge cases: empty name, special characters in types
    let func_ctx = FunctionContext {
        name: "".to_string(), // Empty function name
        params: vec![
            (
                "_".to_string(),
                TrustVcType::Opaque("Option<Vec<u8>>".to_string()),
            ), // Underscore param
            ("".to_string(), TrustVcType::Opaque("()".to_string())), // Empty param name
        ],
        return_type: TrustVcType::Opaque("Result<(), &'static str>".to_string()), // Lifetime in return type
        is_recursive: false,
        mode: FunctionMode::Exec,
        trait_bounds: vec![],
    };

    // Should handle these without panicking
    assert_eq!(func_ctx.name, "");
    assert_eq!(func_ctx.params.len(), 2);
    assert_eq!(func_ctx.params[0].0, "_");
    assert_eq!(func_ctx.params[1].0, "");

    // Test setting in context
    let mut ctx = VerificationContext::new();
    ctx.set_function_context(func_ctx.clone());
    assert!(ctx.function_context.is_some());
}

#[test]
fn test_function_context_proof_mode() {
    // Test creating a FunctionContext with Proof mode
    let func_ctx = FunctionContext {
        name: "lemma_sum_positive".to_string(),
        params: vec![("n".to_string(), TrustVcType::from_str("u64").unwrap())],
        return_type: TrustVcType::Opaque("()".to_string()),
        is_recursive: true,
        mode: FunctionMode::Proof,
        trait_bounds: vec![],
    };

    assert_eq!(func_ctx.mode, FunctionMode::Proof);
    assert!(func_ctx.mode.can_call(FunctionMode::Spec));
    assert!(!func_ctx.mode.can_call(FunctionMode::Exec));
}

#[test]
fn test_function_context_spec_mode() {
    // Test creating a FunctionContext with Spec mode
    let func_ctx = FunctionContext {
        name: "spec_sum".to_string(),
        params: vec![("s".to_string(), TrustVcType::from_str("Seq<i32>").unwrap())],
        return_type: TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: FunctionMode::Spec,
        trait_bounds: vec![],
    };

    assert_eq!(func_ctx.mode, FunctionMode::Spec);
    assert!(func_ctx.mode.can_call(FunctionMode::Spec));
    assert!(!func_ctx.mode.can_call(FunctionMode::Proof));
    assert!(!func_ctx.mode.can_call(FunctionMode::Exec));
}
