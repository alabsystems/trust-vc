//! Regression tests for local binding scope restore after nested encoding.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Consolidation: #2609 — centralized binding_scope helpers. These tests verify
//! that the shared save/restore mechanism correctly restores outer bindings
//! after nested encoding (success and error paths).

use super::*;

use crate::ir::{CompareOp, TrustVcExpr, TrustVcType};
use ay_dpll::api::Solver;

struct ScopeTestEnv {
    solver: Solver,
    variables: std::collections::HashMap<String, Term>,
    collection_lengths: std::collections::HashMap<String, Term>,
    var_types: std::collections::HashMap<String, TrustVcType>,
    functions: std::collections::HashMap<String, ay_dpll::api::FuncDecl>,
}

impl ScopeTestEnv {
    fn new() -> Self {
        ScopeTestEnv {
            solver: Solver::try_new(ay_dpll::api::Logic::All).unwrap(),
            variables: std::collections::HashMap::new(),
            collection_lengths: std::collections::HashMap::new(),
            var_types: std::collections::HashMap::new(),
            functions: std::collections::HashMap::new(),
        }
    }

    fn parser(&mut self) -> AstExpressionParser<'_> {
        AstExpressionParser::new(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.functions,
        )
    }
}

/// Outer local binding survives a let-binding encode that shadows the same name.
///
/// Regression: before #2609, manual save/restore in ite_let.rs could miss
/// restoring local_var_types on early-return error paths.
#[test]
fn test_let_binding_restores_outer_local() {
    let mut env = ScopeTestEnv::new();
    let mut parser = env.parser();

    // Seed an outer local binding for "x"
    let outer_sort = ay_dpll::api::Sort::Int;
    let outer_term = parser.solver.declare_const("outer_x", outer_sort);
    let outer_ty = TrustVcType::Int { width: 32 };
    parser.local_vars.insert("x".to_string(), outer_term);
    parser
        .local_var_types
        .insert("x".to_string(), outer_ty.clone());

    // Encode a let expression: let x = 42 in x + 1
    let let_expr = TrustVcExpr::Let {
        name: "x".to_string(),
        ty: TrustVcType::Int { width: 32 },
        value: Box::new(TrustVcExpr::IntLit {
            value: 42,
            ty: TrustVcType::Int { width: 32 },
        }),
        body: Box::new(TrustVcExpr::Arith {
            op: crate::ir::ArithOp::Add,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 1,
                ty: TrustVcType::Int { width: 32 },
            }),
            ty: TrustVcType::Int { width: 32 },
        }),
    };

    let result = parser.encode_trust_vc_expr(&let_expr);
    assert!(
        result.is_ok(),
        "let encoding should succeed: {:?}",
        result.err()
    );

    // Verify the outer binding is restored
    assert_eq!(
        parser.local_vars.get("x"),
        Some(&outer_term),
        "#2609: outer local_vars binding must survive let-binding scope"
    );
    assert_eq!(
        parser.local_var_types.get("x"),
        Some(&outer_ty),
        "#2609: outer local_var_types binding must survive let-binding scope"
    );
}

/// Outer local binding is restored even when the nested let-body encode fails.
///
/// This exercises the `Err` path of `with_local_bindings`: the closure returns
/// an encode error after the shadowing binding is installed, so the helper must
/// still restore both local maps before the error escapes.
#[test]
fn test_let_binding_restores_outer_local_on_error() {
    let mut env = ScopeTestEnv::new();
    let mut parser = env.parser();

    // Seed an outer local binding for "x"
    let outer_sort = ay_dpll::api::Sort::Int;
    let outer_term = parser.solver.declare_const("outer_x_err", outer_sort);
    let outer_ty = TrustVcType::Int { width: 32 };
    parser.local_vars.insert("x".to_string(), outer_term);
    parser
        .local_var_types
        .insert("x".to_string(), outer_ty.clone());

    // Encode a let expression whose body references an undefined variable.
    // The nested body encode must error after the temporary binding is installed.
    let let_expr = TrustVcExpr::Let {
        name: "x".to_string(),
        ty: TrustVcType::Int { width: 32 },
        value: Box::new(TrustVcExpr::IntLit {
            value: 42,
            ty: TrustVcType::Int { width: 32 },
        }),
        body: Box::new(TrustVcExpr::Var {
            name: "missing".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }),
    };

    let err = parser
        .encode_trust_vc_expr(&let_expr)
        .expect_err("undefined variable in let body must error");
    assert!(
        err.to_string().contains("undefined variable"),
        "expected undefined-variable error, got: {err}"
    );

    // Verify the outer binding is restored after the error path.
    assert_eq!(
        parser.local_vars.get("x"),
        Some(&outer_term),
        "#2625: outer local_vars binding must survive let-binding error path"
    );
    assert_eq!(
        parser.local_var_types.get("x"),
        Some(&outer_ty),
        "#2625: outer local_var_types binding must survive let-binding error path"
    );
}

/// Outer local binding survives a choose expression that shadows the same name.
///
/// choose(|x: u32| x > 0) introduces "x" in scope for the condition encode.
/// After the choose returns, the outer "x" must be restored.
#[test]
fn test_choose_restores_outer_local() {
    let mut env = ScopeTestEnv::new();
    let mut parser = env.parser();

    // Seed an outer local binding for "x"
    let outer_sort = ay_dpll::api::Sort::Int;
    let outer_term = parser.solver.declare_const("outer_x", outer_sort);
    let outer_ty = TrustVcType::Uint { width: 32 };
    parser.local_vars.insert("x".to_string(), outer_term);
    parser
        .local_var_types
        .insert("x".to_string(), outer_ty.clone());

    // Set up choose registry
    let mut choose_registry = std::collections::HashMap::new();
    parser.choose_registry = Some(&mut choose_registry);

    let choose_expr = TrustVcExpr::Choose {
        var_name: "x".to_string(),
        var_ty: TrustVcType::Uint { width: 32 },
        condition: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Uint { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Uint { width: 32 },
            }),
        }),
        key: "scope_test_choose".to_string(),
        also_assert: None,
    };

    let result = parser.encode_trust_vc_expr(&choose_expr);
    assert!(
        result.is_ok(),
        "choose encoding should succeed: {:?}",
        result.err()
    );

    // Verify the outer binding is restored
    assert_eq!(
        parser.local_vars.get("x"),
        Some(&outer_term),
        "#2609: outer local_vars binding must survive choose scope"
    );
    assert_eq!(
        parser.local_var_types.get("x"),
        Some(&outer_ty),
        "#2609: outer local_var_types binding must survive choose scope"
    );
}

/// local_vars entry is correctly removed (not restored) when the outer scope
/// had no binding for that name.
///
/// This tests the None-branch of restore: if "x" was NOT in local_vars before
/// the nested encode, it must be removed afterward, not left dangling.
#[test]
fn test_let_binding_removes_fresh_local_after_scope() {
    let mut env = ScopeTestEnv::new();
    let mut parser = env.parser();

    // No outer binding for "x" — local_vars does NOT contain "x"
    assert!(!parser.local_vars.contains_key("x"));

    let let_expr = TrustVcExpr::Let {
        name: "x".to_string(),
        ty: TrustVcType::Int { width: 32 },
        value: Box::new(TrustVcExpr::IntLit {
            value: 99,
            ty: TrustVcType::Int { width: 32 },
        }),
        body: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }),
    };

    let result = parser.encode_trust_vc_expr(&let_expr);
    assert!(
        result.is_ok(),
        "let encoding should succeed: {:?}",
        result.err()
    );

    // "x" must NOT be in local_vars after let scope exits
    assert!(
        !parser.local_vars.contains_key("x"),
        "#2609: fresh local binding must be removed after let scope, not left dangling"
    );
    assert!(
        !parser.local_var_types.contains_key("x"),
        "#2609: fresh local_var_types must be removed after let scope"
    );
}
