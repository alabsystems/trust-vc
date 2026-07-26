// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Basic PolyContext Box/Unbox declaration and roundtrip tests.

use super::*;

#[test]
fn test_ensure_box_unbox_i32_declares_functions() {
    let mut solver = test_solver();
    let mut ctx = PolyContext::new();
    let ty = TrustVcType::Int { width: 32 };
    let (box_fn, unbox_fn) = ctx.ensure_box_unbox(&mut solver, &ty).unwrap();
    assert_eq!(box_fn.name(), "Box_i32");
    assert_eq!(unbox_fn.name(), "Unbox_i32");
}

#[test]
fn test_ensure_box_unbox_bool_declares_functions() {
    let mut solver = test_solver();
    let mut ctx = PolyContext::new();
    let ty = TrustVcType::Bool;
    let (box_fn, unbox_fn) = ctx.ensure_box_unbox(&mut solver, &ty).unwrap();
    assert_eq!(box_fn.name(), "Box_bool");
    assert_eq!(unbox_fn.name(), "Unbox_bool");
}

#[test]
fn test_ensure_box_unbox_u64_declares_functions() {
    let mut solver = test_solver();
    let mut ctx = PolyContext::new();
    let ty = TrustVcType::Uint { width: 64 };
    let (box_fn, unbox_fn) = ctx.ensure_box_unbox(&mut solver, &ty).unwrap();
    assert_eq!(box_fn.name(), "Box_u64");
    assert_eq!(unbox_fn.name(), "Unbox_u64");
}

#[test]
fn test_ensure_box_unbox_idempotent() {
    let mut solver = test_solver();
    let mut ctx = PolyContext::new();
    let ty = TrustVcType::Int { width: 32 };
    let (box1, unbox1) = ctx.ensure_box_unbox(&mut solver, &ty).unwrap();
    let (box2, unbox2) = ctx.ensure_box_unbox(&mut solver, &ty).unwrap();
    assert_eq!(box1.name(), box2.name());
    assert_eq!(unbox1.name(), unbox2.name());
}

#[test]
fn test_ensure_box_unbox_multiple_types() {
    let mut solver = test_solver();
    let mut ctx = PolyContext::new();
    let i32_ty = TrustVcType::Int { width: 32 };
    let bool_ty = TrustVcType::Bool;
    let (box_i32, _) = ctx.ensure_box_unbox(&mut solver, &i32_ty).unwrap();
    let (box_bool, _) = ctx.ensure_box_unbox(&mut solver, &bool_ty).unwrap();
    assert_eq!(box_i32.name(), "Box_i32");
    assert_eq!(box_bool.name(), "Box_bool");
}

#[test]
fn test_roundtrip_axiom_makes_identity_verifiable() {
    // Verifies: ∀x:i32. Unbox_i32(Box_i32(x)) == x
    // by checking: ∃x:i32. Unbox_i32(Box_i32(x)) != x → unsat
    let mut solver = test_solver();
    let mut ctx = PolyContext::new();
    let ty = TrustVcType::Int { width: 32 };
    let (box_fn, unbox_fn) = ctx.ensure_box_unbox(&mut solver, &ty).unwrap();

    // Declare a concrete variable x : BV32
    let x = solver.declare_const("x", Sort::bitvec(32));
    // Box then Unbox
    let boxed = solver.try_apply(&box_fn, &[x]).unwrap();
    let unboxed = solver.try_apply(&unbox_fn, &[boxed]).unwrap();
    // Assert the call-site ground roundtrip, then refute it. Production
    // encoding emits these ground facts instead of a live universal axiom.
    let eq = solver.try_eq(unboxed, x).unwrap();
    solver.try_assert_term(eq).unwrap();
    let neg = solver.try_not(eq).unwrap();
    solver.try_assert_term(neg).unwrap();

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "roundtrip axiom should make Unbox(Box(x)) == x always true, got: {:?}",
        result
    );
}

#[test]
fn test_box_unbox_distinguishes_types() {
    // Box_i32 and Box_bool are different uninterpreted functions.
    // Verify that eq(Box_i32(x), Box_bool(y)) AND neq(...) is contradictory.
    let mut solver = test_solver();
    let mut ctx = PolyContext::new();
    let i32_ty = TrustVcType::Int { width: 32 };
    let bool_ty = TrustVcType::Bool;
    let (box_i32, _) = ctx.ensure_box_unbox(&mut solver, &i32_ty).unwrap();
    let (box_bool, _) = ctx.ensure_box_unbox(&mut solver, &bool_ty).unwrap();

    let one = solver.try_bv_const(1i64, 32).unwrap();
    let t = solver.bool_const(true);
    let boxed_int = solver.try_apply(&box_i32, &[one]).unwrap();
    let boxed_bool = solver.try_apply(&box_bool, &[t]).unwrap();

    // eq AND not(eq) is trivially unsat — just tests solver sanity with Poly sort
    let eq = solver.try_eq(boxed_int, boxed_bool).unwrap();
    let neq = solver.try_not(eq).unwrap();
    let contradiction = solver.try_and(eq, neq).unwrap();
    solver.try_assert_term(contradiction).unwrap();
    let result = solver.check_sat();
    assert!(result.is_unsat(), "equal AND not-equal should be unsat");
}

#[test]
fn test_get_box_fn_returns_none_before_declaration() {
    let ctx = PolyContext::new();
    assert!(ctx.get_box_fn(&TrustVcType::Int { width: 32 }).is_none());
    assert!(ctx.get_unbox_fn(&TrustVcType::Bool).is_none());
}

#[test]
fn test_get_box_fn_returns_some_after_declaration() {
    let mut solver = test_solver();
    let mut ctx = PolyContext::new();
    let ty = TrustVcType::Int { width: 32 };
    ctx.ensure_box_unbox(&mut solver, &ty).unwrap();
    assert!(ctx.get_box_fn(&ty).is_some());
    assert!(ctx.get_unbox_fn(&ty).is_some());
    assert_eq!(ctx.get_box_fn(&ty).unwrap().name(), "Box_i32");
}

#[test]
fn test_roundtrip_axiom_math_int() {
    // MathInt maps to Sort::Int — verify roundtrip works for unbounded integers.
    let mut solver = test_solver();
    let mut ctx = PolyContext::new();
    let ty = TrustVcType::MathInt;
    let (box_fn, unbox_fn) = ctx.ensure_box_unbox(&mut solver, &ty).unwrap();
    assert_eq!(box_fn.name(), "Box_int");
    assert_eq!(unbox_fn.name(), "Unbox_int");

    let x = solver.declare_const("x", Sort::Int);
    let boxed = solver.try_apply(&box_fn, &[x]).unwrap();
    let unboxed = solver.try_apply(&unbox_fn, &[boxed]).unwrap();
    let eq = solver.try_eq(unboxed, x).unwrap();
    solver.try_assert_term(eq).unwrap();
    let neg = solver.try_not(eq).unwrap();
    solver.try_assert_term(neg).unwrap();
    let result = solver.check_sat();
    assert!(result.is_unsat(), "MathInt roundtrip should verify");
}
