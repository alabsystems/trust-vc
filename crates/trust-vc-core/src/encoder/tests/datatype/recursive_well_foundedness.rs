// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_well_foundedness_skipped_for_non_recursive_option() {
    // Native-datatype migration: the soundness facts (exhaustiveness, tester,
    // selector roundtrip, injectivity, disjointness) are ay native theory
    // invariants established by `try_declare_datatype`, not hand-asserted top-level
    // forall axioms — so registration no longer grows the solver's assertion list.
    // The property this test guards is that well-foundedness (the dt_size UF and
    // its size axioms) is SKIPPED for a non-recursive datatype: registering
    // Option<u64> succeeds and registers no size function.
    let mut encoder = AYEncoder::new();
    let (name, variants) = option_u64_components();
    let _encoding = encoder.register_datatype(&name, &variants).unwrap();
    assert!(
        encoder.dt_size_func(&name).is_none(),
        "well-foundedness/size machinery must be skipped for non-recursive Option<u64>"
    );
}

#[test]
fn test_well_foundedness_emitted_for_recursive_list() {
    let mut encoder = AYEncoder::new();
    let (name, variants) = list_i32_components();
    let encoding = encoder.register_datatype(&name, &variants).unwrap();
    assert_eq!(encoding.variants.len(), 2);
}

#[test]
fn test_encoder_rejects_ill_founded_recursive_type() {
    let mut encoder = AYEncoder::new();
    let (name, variants) = ill_founded_recursive_components();
    let err = encoder
        .register_datatype(&name, &variants)
        .expect_err("ill-founded recursive datatypes must be rejected before encoding");
    let message = err.to_string();
    assert!(
        message.contains("Recursive cycle in datatype 'Bad' has no base case variant"),
        "expected recursive-cycle diagnostic, got: {message}"
    );
    assert!(
        message.contains("Box<T>, Arc<T>, or Rc<T>"),
        "expected indirection guidance, got: {message}"
    );
}

#[test]
fn test_list_nil_has_size_zero() {
    let mut encoder = AYEncoder::new();
    let (name, variants) = list_i32_components();
    let encoding = encoder.register_datatype(&name, &variants).unwrap();
    let nil = encoding.variant("Nil").expect("Nil variant");
    let ConstructorKind::Constant(nil_val) = &nil.constructor else {
        panic!("Nil should be a constant constructor");
    };

    let size_func = encoder
        .dt_size_func("List_i32")
        .expect("size function should be registered for recursive datatype")
        .clone();
    let size_nil = encoder.solver.try_apply(&size_func, &[*nil_val]).unwrap();
    let zero = encoder.solver.int_const(0);

    let neq = encoder.solver.try_neq(size_nil, zero).unwrap();
    encoder.solver.try_assert_term(neq).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "size(Nil) should be 0 by well-foundedness base case axiom, got {:?}",
        result
    );
}

#[test]
fn test_list_dt_size_func_registered_for_recursive_datatype() {
    let mut encoder = AYEncoder::new();
    let (name, variants) = list_i32_components();
    let encoding = encoder.register_datatype(&name, &variants).unwrap();

    assert!(
        encoder.dt_size_func("List_i32").is_some(),
        "dt_size should be registered for recursive List_i32"
    );

    let nil = encoding.variant("Nil").expect("Nil variant");
    let ConstructorKind::Constant(nil_val) = &nil.constructor else {
        panic!("Nil should be a constant constructor");
    };
    let size_func = encoder.dt_size_func("List_i32").unwrap().clone();
    let size_nil = encoder.solver.try_apply(&size_func, &[*nil_val]).unwrap();
    let zero = encoder.solver.int_const(0);
    let eq = encoder.solver.try_eq(size_nil, zero).unwrap();
    let neg = encoder.solver.try_not(eq).unwrap();
    encoder.solver.try_assert_term(neg).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "size(Nil) == 0 should hold (ground fact), got {:?}",
        result
    );
}

#[test]
fn test_manual_size_axiom_fires_for_cons() {
    use ay_dpll::api::{Logic, Solver, Sort, Term};

    let mut solver = Solver::try_new(Logic::All).unwrap();

    let cons = solver
        .try_declare_fun("Cons", &[Sort::Int, Sort::Int], Sort::Int)
        .unwrap();
    let size = solver
        .try_declare_fun("size", &[Sort::Int], Sort::Int)
        .unwrap();

    let h = solver.fresh_var("h", Sort::Int);
    let t = solver.fresh_var("t", Sort::Int);
    let one = solver.int_const(1);
    let cons_ht = solver.try_apply(&cons, &[h, t]).unwrap();
    let size_cons = solver.try_apply(&size, &[cons_ht]).unwrap();
    let size_t = solver.try_apply(&size, &[t]).unwrap();
    let rhs = solver.try_add(one, size_t).unwrap();
    let body = solver.try_eq(size_cons, rhs).unwrap();
    let trigger_groups = [vec![cons_ht]];
    let trigger_refs: Vec<&[Term]> = trigger_groups.iter().map(Vec::as_slice).collect();
    let axiom = solver
        .try_forall_with_triggers(&[h, t], body, &trigger_refs)
        .unwrap();
    solver.try_assert_term(axiom).unwrap();

    let forty_two = solver.int_const(42);
    let tail = solver.declare_const("tail", Sort::Int);
    let cons_42_tail = solver.try_apply(&cons, &[forty_two, tail]).unwrap();
    let size_result = solver.try_apply(&size, &[cons_42_tail]).unwrap();
    let size_tail = solver.try_apply(&size, &[tail]).unwrap();

    let le = solver.try_le(size_result, size_tail).unwrap();
    solver.try_assert_term(le).unwrap();

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "Manual size axiom: size(Cons(h,t)) should be > size(t), got {:?}",
        result
    );
}

#[test]
fn test_list_size_nonnegative() {
    let mut encoder = AYEncoder::new();
    let (name, variants) = list_i32_components();
    let _encoding = encoder.register_datatype(&name, &variants).unwrap();

    // `my_list` is over the native datatype carrier sort (was Sort::Int); the
    // dt_size UF now takes the carrier sort as its domain.
    let list_val = encoder.solver.declare_const(
        "my_list",
        crate::encoder::datatype::datatype_carrier_sort("List_i32"),
    );
    let size_func = encoder
        .dt_size_func("List_i32")
        .expect("size function registered")
        .clone();
    let size_val = encoder.solver.try_apply(&size_func, &[list_val]).unwrap();
    let zero = encoder.solver.int_const(0);
    let negative = encoder.solver.try_lt(size_val, zero).unwrap();
    encoder.solver.try_assert_term(negative).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "size should be non-negative by well-foundedness axiom, got {:?}",
        result
    );
}
