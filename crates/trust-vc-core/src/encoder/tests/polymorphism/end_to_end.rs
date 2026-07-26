// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end polymorphic call-site Box/Unbox tests (#2053 Slice 6).

use super::*;

/// End-to-end: `identity::<i32>(5) == 5` verifies through the typed pipeline.
///
/// Exercises the full Box/Unbox wrapping chain:
///   1. Register generic `identity<T>(x: T) -> T`
///   2. Encoder infers T → i32 from argument type
///   3. Box_i32(y) wraps concrete arg into Poly
///   4. identity(Box_i32(y)) applies the Poly→Poly function
///   5. Unbox_i32(...) projects back to BV32
///   6. Roundtrip axiom proves Unbox(Box(y)) == y
///   7. Body axiom proves identity(p) == p for all Poly p
///   8. Together: Unbox_i32(identity(Box_i32(y))) == y → verified
#[test]
fn test_polymorphic_identity_i32_verifies_end_to_end() {
    use crate::encoder::AYEncoder;
    use crate::ir::{TrustVcExpr, TrustVcType};
    use crate::vc::FunctionContext;

    let mut encoder = AYEncoder::new();

    // Register identity<T>(x: T) -> T as a polymorphic function.
    let func_ctx = FunctionContext {
        name: "identity".to_string(),
        params: vec![("x".to_string(), TrustVcType::TypeParam("T".to_string()))],
        return_type: TrustVcType::TypeParam("T".to_string()),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    };
    encoder
        .register_function_context(&func_ctx)
        .expect("register identity should succeed");

    // Declare y : i32
    encoder
        .declare_variable(&crate::vc::VariableDecl {
            bounded_len: false,
            name: "y".to_string(),
            ty: TrustVcType::Int { width: 32 },
        })
        .expect("declare y");

    // Assume y == 5
    let assume_expr = TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Eq,
        left: Box::new(TrustVcExpr::Var {
            name: "y".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 5,
            ty: TrustVcType::Int { width: 32 },
        }),
    };
    let assume_term = encoder
        .encode_condition_typed(&assume_expr)
        .expect("encode assume y == 5");
    encoder.solver.try_assert_term(assume_term).unwrap();

    // Add body axiom: forall x:Poly. identity(x) == x
    // (This is what the BroadcastAssume pipeline would add for a spec function)
    let poly_sort = Sort::Uninterpreted("Poly".to_string());
    let x_bound = encoder.solver.fresh_var("__x", poly_sort);
    let id_decl = encoder.fn_ctx.functions["identity"].clone();
    let id_x = encoder.solver.try_apply(&id_decl, &[x_bound]).unwrap();
    let eq = encoder.solver.try_eq(id_x, x_bound).unwrap();
    let body_axiom = encoder
        .solver
        .try_forall_with_triggers(&[x_bound], eq, &[&[id_x]])
        .unwrap();
    encoder.solver.try_assert_term(body_axiom).unwrap();

    // Encode assertion: identity(y) == y
    // This should trigger Box/Unbox wrapping: Unbox_i32(identity(Box_i32(y))) == y
    let assert_expr = TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Eq,
        left: Box::new(TrustVcExpr::FnCall {
            name: "identity".to_string(),
            args: vec![TrustVcExpr::Var {
                name: "y".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }],
            return_ty: TrustVcType::TypeParam("T".to_string()),
        }),
        right: Box::new(TrustVcExpr::Var {
            name: "y".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }),
    };
    let assert_term = encoder
        .encode_condition_typed(&assert_expr)
        .expect("encode identity(y) == y");

    // Negate and check: should be unsat (verified)
    let neg = encoder.solver.try_not(assert_term).unwrap();
    encoder.solver.try_assert_term(neg).unwrap();
    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "identity::<i32>(5) == 5 should verify through Box/Unbox, got: {:?}",
        result
    );
}

/// End-to-end: `identity::<i32>(5) == 6` fails verification (counterexample).
#[test]
fn test_polymorphic_identity_i32_wrong_value_fails() {
    use crate::encoder::AYEncoder;
    use crate::ir::{TrustVcExpr, TrustVcType};
    use crate::vc::FunctionContext;

    let mut encoder = AYEncoder::new();

    let func_ctx = FunctionContext {
        name: "identity".to_string(),
        params: vec![("x".to_string(), TrustVcType::TypeParam("T".to_string()))],
        return_type: TrustVcType::TypeParam("T".to_string()),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    };
    encoder
        .register_function_context(&func_ctx)
        .expect("register identity");

    encoder
        .declare_variable(&crate::vc::VariableDecl {
            bounded_len: false,
            name: "y".to_string(),
            ty: TrustVcType::Int { width: 32 },
        })
        .expect("declare y");

    // Assume y == 5
    let assume_expr = TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Eq,
        left: Box::new(TrustVcExpr::Var {
            name: "y".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 5,
            ty: TrustVcType::Int { width: 32 },
        }),
    };
    let assume_term = encoder
        .encode_condition_typed(&assume_expr)
        .expect("encode assume");
    encoder.solver.try_assert_term(assume_term).unwrap();

    // Body axiom
    let poly_sort = Sort::Uninterpreted("Poly".to_string());
    let x_bound = encoder.solver.fresh_var("__x", poly_sort);
    let id_decl = encoder.fn_ctx.functions["identity"].clone();
    let id_x = encoder.solver.try_apply(&id_decl, &[x_bound]).unwrap();
    let eq = encoder.solver.try_eq(id_x, x_bound).unwrap();
    let body_axiom = encoder
        .solver
        .try_forall_with_triggers(&[x_bound], eq, &[&[id_x]])
        .unwrap();
    encoder.solver.try_assert_term(body_axiom).unwrap();

    // Assert identity(y) == 6 — should FAIL
    let assert_expr = TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Eq,
        left: Box::new(TrustVcExpr::FnCall {
            name: "identity".to_string(),
            args: vec![TrustVcExpr::Var {
                name: "y".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }],
            return_ty: TrustVcType::TypeParam("T".to_string()),
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 6,
            ty: TrustVcType::Int { width: 32 },
        }),
    };
    let assert_term = encoder
        .encode_condition_typed(&assert_expr)
        .expect("encode identity(y) == 6");
    let neg = encoder.solver.try_not(assert_term).unwrap();
    encoder.solver.try_assert_term(neg).unwrap();
    let result = encoder.solver.check_sat();
    assert!(
        result.is_sat(),
        "identity::<i32>(5) == 6 should fail verification with SAT counterexample, got: {:?}",
        result
    );
}

/// Two-type-param function: swap<A, B>(a, b) returns b.
/// Verifies that multiple type parameter bindings work correctly.
#[test]
fn test_polymorphic_two_type_params_swap_first_verifies() {
    use crate::encoder::AYEncoder;
    use crate::ir::{TrustVcExpr, TrustVcType};
    use crate::vc::FunctionContext;

    let mut encoder = AYEncoder::new();

    // Register first<A, B>(a: A, b: B) -> A
    let func_ctx = FunctionContext {
        name: "first".to_string(),
        params: vec![
            ("a".to_string(), TrustVcType::TypeParam("A".to_string())),
            ("b".to_string(), TrustVcType::TypeParam("B".to_string())),
        ],
        return_type: TrustVcType::TypeParam("A".to_string()),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    };
    encoder
        .register_function_context(&func_ctx)
        .expect("register first");

    // Declare x: i32, flag: bool
    encoder
        .declare_variable(&crate::vc::VariableDecl {
            bounded_len: false,
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        })
        .expect("declare x");
    encoder
        .declare_variable(&crate::vc::VariableDecl {
            bounded_len: false,
            name: "flag".to_string(),
            ty: TrustVcType::Bool,
        })
        .expect("declare flag");

    // Assume x == 42
    let assume_expr = TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Eq,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 42,
            ty: TrustVcType::Int { width: 32 },
        }),
    };
    let assume_term = encoder
        .encode_condition_typed(&assume_expr)
        .expect("encode assume");
    encoder.solver.try_assert_term(assume_term).unwrap();

    // Body axiom: forall a:Poly, b:Poly. first(a, b) == a
    let poly_sort = Sort::Uninterpreted("Poly".to_string());
    let a_bound = encoder.solver.fresh_var("__a", poly_sort.clone());
    let b_bound = encoder.solver.fresh_var("__b", poly_sort);
    let first_decl = encoder.fn_ctx.functions["first"].clone();
    let first_ab = encoder
        .solver
        .try_apply(&first_decl, &[a_bound, b_bound])
        .unwrap();
    let eq = encoder.solver.try_eq(first_ab, a_bound).unwrap();
    let body_axiom = encoder
        .solver
        .try_forall_with_triggers(&[a_bound, b_bound], eq, &[&[first_ab]])
        .unwrap();
    encoder.solver.try_assert_term(body_axiom).unwrap();

    // Assert first(x, flag) == x
    let assert_expr = TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Eq,
        left: Box::new(TrustVcExpr::FnCall {
            name: "first".to_string(),
            args: vec![
                TrustVcExpr::Var {
                    name: "x".to_string(),
                    ty: TrustVcType::Int { width: 32 },
                },
                TrustVcExpr::Var {
                    name: "flag".to_string(),
                    ty: TrustVcType::Bool,
                },
            ],
            return_ty: TrustVcType::TypeParam("A".to_string()),
        }),
        right: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }),
    };
    let assert_term = encoder
        .encode_condition_typed(&assert_expr)
        .expect("encode first(x, flag) == x");
    let neg = encoder.solver.try_not(assert_term).unwrap();
    encoder.solver.try_assert_term(neg).unwrap();
    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "first::<i32, bool>(42, flag) == 42 should verify, got: {:?}",
        result
    );
}
