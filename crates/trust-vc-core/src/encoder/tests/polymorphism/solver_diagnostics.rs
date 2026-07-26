// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Solver-level E-matching and diagnostic tests for polymorphic encoding.
//!
//! Tests isolate ay E-matching from the TrustVcExpr encoding pipeline.

use super::*;

/// Pure solver-level test: identity function with Box/Unbox chain.
///
/// Single-hop E-matching test: body axiom fires on f(p) to give f(p)==p.
/// If this fails, ay E-matching is fundamentally broken.
#[test]
fn test_single_hop_ematching_body_axiom() {
    let mut solver = test_solver();
    let poly_sort = Sort::Uninterpreted("Poly".to_string());

    // Declare f: Poly → Poly
    let f = solver
        .try_declare_fun(
            "f_single",
            std::slice::from_ref(&poly_sort),
            poly_sort.clone(),
        )
        .unwrap();

    // Body axiom: forall x:Poly. {f(x)} f(x) == x
    let x = solver.fresh_var("__x", poly_sort.clone());
    let fx = solver.try_apply(&f, &[x]).unwrap();
    let eq = solver.try_eq(fx, x).unwrap();
    let axiom = solver.try_forall_with_triggers(&[x], eq, &[&[fx]]).unwrap();
    solver.try_assert_term(axiom).unwrap();

    // Declare p: Poly
    let p = solver.declare_const("p_test", poly_sort);

    // Assert NOT(f(p) == p) — should be unsat
    let fp = solver.try_apply(&f, &[p]).unwrap();
    let eq2 = solver.try_eq(fp, p).unwrap();
    let neg = solver.try_not(eq2).unwrap();
    solver.try_assert_term(neg).unwrap();
    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "single-hop E-matching body axiom should fire, got: {:?}",
        result
    );
}

/// Congruence test: body axiom gives f(a)==a, then g(f(a))==g(a) by congruence.
#[test]
fn test_congruence_after_body_axiom() {
    let mut solver = test_solver();
    let poly_sort = Sort::Uninterpreted("Poly".to_string());

    let f = solver
        .try_declare_fun(
            "f_cong",
            std::slice::from_ref(&poly_sort),
            poly_sort.clone(),
        )
        .unwrap();
    let g = solver
        .try_declare_fun(
            "g_cong",
            std::slice::from_ref(&poly_sort),
            poly_sort.clone(),
        )
        .unwrap();

    // Body axiom: forall x:Poly. {f(x)} f(x) == x
    let x = solver.fresh_var("__x", poly_sort.clone());
    let fx = solver.try_apply(&f, &[x]).unwrap();
    let eq = solver.try_eq(fx, x).unwrap();
    let axiom = solver.try_forall_with_triggers(&[x], eq, &[&[fx]]).unwrap();
    solver.try_assert_term(axiom).unwrap();

    let a = solver.declare_const("a_cong", poly_sort);
    let fa = solver.try_apply(&f, &[a]).unwrap();
    let g_fa = solver.try_apply(&g, &[fa]).unwrap();
    let g_a = solver.try_apply(&g, &[a]).unwrap();

    // Assert NOT(g(f(a)) == g(a)) — should be unsat by congruence
    let eq2 = solver.try_eq(g_fa, g_a).unwrap();
    let neg = solver.try_not(eq2).unwrap();
    solver.try_assert_term(neg).unwrap();
    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "congruence after body axiom should give g(f(a))==g(a), got: {:?}",
        result
    );
}

/// Two-hop E-matching test: body axiom + roundtrip chain.
/// If single-hop passes but this fails, ay doesn't propagate triggers
/// from instantiation results to other quantifiers.
#[test]
fn test_two_hop_ematching_body_plus_roundtrip() {
    let mut solver = test_solver();
    let poly_sort = Sort::Uninterpreted("Poly".to_string());
    let bv32 = Sort::bitvec(32);

    // Declare UFs
    let id_fn = solver
        .try_declare_fun(
            "id_2hop",
            std::slice::from_ref(&poly_sort),
            poly_sort.clone(),
        )
        .unwrap();
    let box_fn = solver
        .try_declare_fun("Box_2hop", std::slice::from_ref(&bv32), poly_sort.clone())
        .unwrap();
    let unbox_fn = solver
        .try_declare_fun("Unbox_2hop", &[poly_sort], bv32.clone())
        .unwrap();

    // QUANTIFIED body axiom (as in real encoding): forall x:Poly. {id(x)} id(x)==x
    let x = solver.fresh_var("__x", Sort::Uninterpreted("Poly".to_string()));
    let id_x = solver.try_apply(&id_fn, &[x]).unwrap();
    let body_eq = solver.try_eq(id_x, x).unwrap();
    let body_axiom = solver
        .try_forall_with_triggers(&[x], body_eq, &[&[id_x]])
        .unwrap();
    solver.try_assert_term(body_axiom).unwrap();

    let a = solver.declare_const("a_2hop", Sort::bitvec(32));
    let box_a = solver.try_apply(&box_fn, &[a]).unwrap();
    let id_box_a = solver.try_apply(&id_fn, &[box_a]).unwrap();
    let result_term = solver.try_apply(&unbox_fn, &[id_box_a]).unwrap();
    let unbox_box_a = solver.try_apply(&unbox_fn, &[box_a]).unwrap();

    // Ground roundtrip: Unbox(Box(a)) == a
    let ground_rt = solver.try_eq(unbox_box_a, a).unwrap();
    solver.try_assert_term(ground_rt).unwrap();

    // Congruence hint implication retained for ay 6c423022:
    // id(Box(a)) == Box(a) -> Unbox(id(Box(a))) == Unbox(Box(a)).
    // Removing this assertion makes the current solver return SAT here.
    let premise = solver.try_eq(id_box_a, box_a).unwrap();
    let conclusion = solver.try_eq(result_term, unbox_box_a).unwrap();
    let hint = solver.try_implies(premise, conclusion).unwrap();
    solver.try_assert_term(hint).unwrap();

    // Assert NOT(result == a) — should be Unsat
    let eq_full = solver.try_eq(result_term, a).unwrap();
    let neg_full = solver.try_not(eq_full).unwrap();
    solver.try_assert_term(neg_full).unwrap();
    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "body axiom + roundtrip + congruence hint should prove Unbox(id(Box(a)))==a, got: {:?}",
        result
    );
}

/// Models the full committed call-site workaround:
/// quantified body axiom + ground roundtrip + congruence hint.
/// If this passes but the end-to-end test fails, the issue is in the
/// encoding pipeline rather than the raw solver chain.
#[test]
fn test_identity_box_unbox_chain_pure_solver() {
    let mut solver = test_solver();
    let mut ctx = PolyContext::new();
    let i32_ty = TrustVcType::Int { width: 32 };
    let poly_sort = Sort::Uninterpreted("Poly".to_string());

    // Declare identity : Poly → Poly
    let id_fn = solver
        .try_declare_fun(
            "identity",
            std::slice::from_ref(&poly_sort),
            poly_sort.clone(),
        )
        .unwrap();

    // Body axiom: forall x:Poly. {identity(x)} identity(x) == x
    let x_poly = solver.fresh_var("__x", poly_sort);
    let id_x = solver.try_apply(&id_fn, &[x_poly]).unwrap();
    let body_eq = solver.try_eq(id_x, x_poly).unwrap();
    let body_axiom = solver
        .try_forall_with_triggers(&[x_poly], body_eq, &[&[id_x]])
        .unwrap();
    solver.try_assert_term(body_axiom).unwrap();

    // Declare Box_i32, Unbox_i32, roundtrip axiom
    let (box_fn, unbox_fn) = ctx.ensure_box_unbox(&mut solver, &i32_ty).unwrap();

    // Declare y : BV32
    let y = solver.declare_const("y", Sort::bitvec(32));

    // Assume y == 5
    let five = solver.try_bv_const(5i64, 32).unwrap();
    let y_eq_5 = solver.try_eq(y, five).unwrap();
    solver.try_assert_term(y_eq_5).unwrap();

    // Build: Unbox_i32(identity(Box_i32(y)))
    let boxed_y = solver.try_apply(&box_fn, &[y]).unwrap();
    let id_boxed_y = solver.try_apply(&id_fn, &[boxed_y]).unwrap();
    let unboxed = solver.try_apply(&unbox_fn, &[id_boxed_y]).unwrap();
    let unbox_boxed_y = solver.try_apply(&unbox_fn, &[boxed_y]).unwrap();

    // Ground roundtrip: Unbox(Box(y)) == y
    let ground_rt = solver.try_eq(unbox_boxed_y, y).unwrap();
    solver.try_assert_term(ground_rt).unwrap();

    // Congruence hint implication retained for ay 6c423022:
    // identity(Box(y)) == Box(y) -> Unbox(identity(Box(y))) == Unbox(Box(y)).
    let premise = solver.try_eq(id_boxed_y, boxed_y).unwrap();
    let conclusion = solver.try_eq(unboxed, unbox_boxed_y).unwrap();
    let hint = solver.try_implies(premise, conclusion).unwrap();
    solver.try_assert_term(hint).unwrap();

    // Assert NOT(unboxed == y) — should be unsat
    let eq = solver.try_eq(unboxed, y).unwrap();
    let neg = solver.try_not(eq).unwrap();
    solver.try_assert_term(neg).unwrap();
    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "pure solver identity+Box/Unbox chain should verify, got: {:?}",
        result
    );
}

// ==========================================================================
// Diagnostic: isolate encode_fn_call from encode_compare (#2053 Slice 6)
// ==========================================================================

/// Diagnostic: encode FnCall and Var separately through the pipeline, then
/// manually build equality and negate. If this passes but the full end-to-end
/// fails, the bug is in encode_compare's handling of the terms.
#[test]
fn test_polymorphic_identity_separate_encode_manual_eq() {
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
        .expect("encode assume y == 5");
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

    // Encode JUST the FnCall through the pipeline (not the full Compare)
    let fn_call_expr = TrustVcExpr::FnCall {
        name: "identity".to_string(),
        args: vec![TrustVcExpr::Var {
            name: "y".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }],
        return_ty: TrustVcType::TypeParam("T".to_string()),
    };
    let fn_call_term = encoder
        .encode_condition_typed(&fn_call_expr)
        .expect("encode identity(y) as FnCall");

    // Verify Box_i32 was created by the encoding
    assert!(
        encoder
            .box_fn_for_type(&TrustVcType::Int { width: 32 })
            .is_some(),
        "Box_i32 should have been created during FnCall encoding"
    );

    // Encode the variable separately
    let var_expr = TrustVcExpr::Var {
        name: "y".to_string(),
        ty: TrustVcType::Int { width: 32 },
    };
    let var_term = encoder.encode_condition_typed(&var_expr).expect("encode y");

    // Manually build equality and negate
    let eq = encoder.solver.try_eq(fn_call_term, var_term).unwrap();
    let neg = encoder.solver.try_not(eq).unwrap();
    encoder.solver.try_assert_term(neg).unwrap();
    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "separate-encode identity(y) == y should verify (unsat), got: {:?}",
        result
    );
}

/// Diagnostic: use AYEncoder's solver but build the chain entirely manually
/// (like the pure solver test). If this passes, the solver instance is fine
/// and the issue is in how the pipeline encodes things.
#[test]
fn test_polymorphic_identity_ayencoder_solver_manual_chain() {
    use crate::encoder::AYEncoder;
    use crate::ir::TrustVcType;
    use crate::vc::FunctionContext;

    let mut encoder = AYEncoder::new();
    let mut ctx = PolyContext::new();
    let i32_ty = TrustVcType::Int { width: 32 };

    // Register identity to set up the UF declaration
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

    let id_decl = encoder.fn_ctx.functions["identity"].clone();

    // Body axiom on the encoder's solver
    let poly_sort = Sort::Uninterpreted("Poly".to_string());
    let x_bound = encoder.solver.fresh_var("__x", poly_sort);
    let id_x = encoder.solver.try_apply(&id_decl, &[x_bound]).unwrap();
    let eq = encoder.solver.try_eq(id_x, x_bound).unwrap();
    let body_axiom = encoder
        .solver
        .try_forall_with_triggers(&[x_bound], eq, &[&[id_x]])
        .unwrap();
    encoder.solver.try_assert_term(body_axiom).unwrap();

    // Box/Unbox on the encoder's solver
    let (box_fn, unbox_fn) = ctx.ensure_box_unbox(&mut encoder.solver, &i32_ty).unwrap();

    // Declare y on the encoder's solver
    let y = encoder.solver.declare_const("__diag_y", Sort::bitvec(32));
    let five = encoder.solver.try_bv_const(5i64, 32).unwrap();
    let y_eq_5 = encoder.solver.try_eq(y, five).unwrap();
    encoder.solver.try_assert_term(y_eq_5).unwrap();

    // Manually build: Unbox_i32(identity(Box_i32(y)))
    let boxed_y = encoder.solver.try_apply(&box_fn, &[y]).unwrap();
    let id_boxed_y = encoder.solver.try_apply(&id_decl, &[boxed_y]).unwrap();
    let unboxed = encoder.solver.try_apply(&unbox_fn, &[id_boxed_y]).unwrap();

    // Ground roundtrip: Unbox_i32(Box_i32(y)) == y
    let unbox_box_y = encoder.solver.try_apply(&unbox_fn, &[boxed_y]).unwrap();
    let ground_rt = encoder.solver.try_eq(unbox_box_y, y).unwrap();
    encoder.solver.try_assert_term(ground_rt).unwrap();

    // Congruence hint retained from the production encode_fn_call path.
    // Without this bridge, ay 6c423022 leaves the manual Poly roundtrip chain
    // satisfiable.
    let premise = encoder.solver.try_eq(id_boxed_y, boxed_y).unwrap();
    let conclusion = encoder.solver.try_eq(unboxed, unbox_box_y).unwrap();
    let hint = encoder.solver.try_implies(premise, conclusion).unwrap();
    encoder.solver.try_assert_term(hint).unwrap();

    // Assert NOT(unboxed == y)
    let eq = encoder.solver.try_eq(unboxed, y).unwrap();
    let neg = encoder.solver.try_not(eq).unwrap();
    encoder.solver.try_assert_term(neg).unwrap();
    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "manual chain on AYEncoder solver should verify, got: {:?}",
        result
    );
}
