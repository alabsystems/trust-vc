// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// INTENT CHANGE (native-datatype migration): this module previously asserted
// that `register_datatype` declares hand-rolled UF symbols over `Sort::Int` and
// hand-asserts the soundness axioms (tester, selector roundtrip, injectivity,
// exhaustiveness, disjointness) in `datatype_axioms.rs`. Those hand-asserted
// quantified axioms are GONE — `register_datatype` now declares the datatype
// natively via `Solver::try_declare_datatype`, and the soundness facts are ay's
// own native datatype theory invariants over the carrier sort
// `Sort::Uninterpreted(name)` (the term-level form of `Sort::Datatype`).
//
// This rewrite preserves every behavioral property the old module covered —
// selector roundtrip, exhaustiveness, variant disjointness, injectivity,
// cross-variant constructor-image disjointness — but now asserts they hold via
// the NATIVE theory (UNSAT-to-negate over carrier-sorted terms), and asserts the
// registration exposes native symbol names/sorts (constructor names, the native
// `is-{constructor}` tester name, carrier-sorted selectors). It is NOT a
// weakening: the same theorems are checked, against the native theory rather than
// against hand-asserted UF axioms.

use super::*;
use crate::encoder::datatype::{datatype_carrier_sort, tester_symbol_name};

#[test]
fn test_register_datatype_option_declares_native_symbols() {
    let mut encoder = AYEncoder::new();
    let (name, variants) = option_u64_components();
    let encoding = encoder.register_datatype(&name, &variants).unwrap();

    assert_eq!(encoding.name, "Option<u64>");
    assert_eq!(encoding.symbol_prefix, "Option_u64");
    assert_eq!(encoding.variants.len(), 2);

    let none = encoding.variant("None").expect("None variant should exist");
    assert_eq!(none.constructor_name, "Option_u64_None");
    assert!(matches!(&none.constructor, ConstructorKind::Constant(_)));
    // Native tester name uses the ay `is-{constructor}` (hyphen) convention so the
    // applied tester term carries the symbol ay's native datatype theory and the
    // mbqi tester-completion recognizers key on.
    assert_eq!(none.tester.name(), "is-Option_u64_None");
    assert_eq!(none.tester.name(), tester_symbol_name(&name, "None"));
    // Tester domain is the native datatype carrier sort, not the legacy Sort::Int.
    assert_eq!(none.tester.domain(), &[datatype_carrier_sort(&name)]);

    let some = encoding.variant("Some").expect("Some variant should exist");
    assert_eq!(some.constructor_name, "Option_u64_Some");
    let ConstructorKind::Function(some_ctor) = &some.constructor else {
        panic!("Some constructor should be a function");
    };
    // Constructor returns the native carrier sort.
    assert_eq!(some_ctor.range(), &datatype_carrier_sort(&name));
    assert_eq!(some.tester.name(), "is-Option_u64_Some");
    assert_eq!(some.selectors.len(), 1);
    assert_eq!(some.selectors[0].name(), "Option_u64_Some_0");
    // Selector takes the carrier sort and returns the field sort (u64 -> BV64).
    assert_eq!(some.selectors[0].domain(), &[datatype_carrier_sort(&name)]);
    assert_eq!(some.selectors[0].range(), &ay_dpll::api::Sort::bitvec(64));
}

#[test]
fn test_native_selector_roundtrip_is_unsat_to_negate() {
    let mut encoder = AYEncoder::new();
    let (name, variants) = option_u64_components();
    let encoding = encoder.register_datatype(&name, &variants).unwrap();
    let some = encoding.variant("Some").expect("Some variant should exist");
    let ConstructorKind::Function(some_ctor) = &some.constructor else {
        panic!("Some constructor should be a function");
    };

    let forty_two = encoder.solver.try_bv_const(42, 64).unwrap();
    let some_42 = encoder.solver.try_apply(some_ctor, &[forty_two]).unwrap();
    let selected = encoder
        .solver
        .try_apply(&some.selectors[0], &[some_42])
        .unwrap();
    let eq = encoder.solver.try_eq(selected, forty_two).unwrap();
    let not_eq = encoder.solver.try_not(eq).unwrap();
    encoder.solver.try_assert_term(not_eq).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "native selector roundtrip should make negation unsat, got {:?}",
        result
    );
}

#[test]
fn test_native_exhaustive_theory_covers_symbolic_value() {
    let mut encoder = AYEncoder::new();
    let (name, variants) = option_u64_components();
    let encoding = encoder.register_datatype(&name, &variants).unwrap();
    let none = encoding.variant("None").expect("None variant should exist");
    let some = encoding.variant("Some").expect("Some variant should exist");

    // Symbolic datatype value over the native carrier sort (was Sort::Int).
    let value = encoder
        .solver
        .declare_const("opt", datatype_carrier_sort(&name));
    let is_none = encoder.solver.try_apply(&none.tester, &[value]).unwrap();
    let is_some = encoder.solver.try_apply(&some.tester, &[value]).unwrap();
    let covered = encoder.solver.try_or(is_none, is_some).unwrap();
    let uncovered = encoder.solver.try_not(covered).unwrap();
    encoder.solver.try_assert_term(uncovered).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "native exhaustiveness should rule out uncovered datatype values, got {:?}",
        result
    );
}

#[test]
fn test_native_disjoint_theory_rejects_dual_testers() {
    let mut encoder = AYEncoder::new();
    let (name, variants) = option_u64_components();
    let encoding = encoder.register_datatype(&name, &variants).unwrap();
    let none = encoding.variant("None").expect("None variant should exist");
    let some = encoding.variant("Some").expect("Some variant should exist");

    let value = encoder
        .solver
        .declare_const("opt", datatype_carrier_sort(&name));
    let is_none = encoder.solver.try_apply(&none.tester, &[value]).unwrap();
    let is_some = encoder.solver.try_apply(&some.tester, &[value]).unwrap();
    let both = encoder.solver.try_and(is_none, is_some).unwrap();
    encoder.solver.try_assert_term(both).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "native disjointness should forbid simultaneous variant testers, got {:?}",
        result
    );
}

#[test]
fn test_native_injectivity_theory_forces_equal_payloads() {
    let mut encoder = AYEncoder::new();
    let (name, variants) = option_u64_components();
    let encoding = encoder.register_datatype(&name, &variants).unwrap();
    let some = encoding.variant("Some").expect("Some variant should exist");
    let ConstructorKind::Function(some_ctor) = &some.constructor else {
        panic!("Some constructor should be a function");
    };

    let left = encoder
        .solver
        .declare_const("left", ay_dpll::api::Sort::bitvec(64));
    let right = encoder
        .solver
        .declare_const("right", ay_dpll::api::Sort::bitvec(64));
    let left_value = encoder.solver.try_apply(some_ctor, &[left]).unwrap();
    let right_value = encoder.solver.try_apply(some_ctor, &[right]).unwrap();
    let same_ctor = encoder.solver.try_eq(left_value, right_value).unwrap();
    let same_payload = encoder.solver.try_eq(left, right).unwrap();
    let different_payload = encoder.solver.try_not(same_payload).unwrap();
    let contradiction = encoder
        .solver
        .try_and(same_ctor, different_payload)
        .unwrap();
    encoder.solver.try_assert_term(contradiction).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "native injectivity should make equal constructor terms imply equal payloads, got {:?}",
        result
    );
}

#[test]
fn test_native_result_variant_image_disjointness_makes_ok_and_err_distinct() {
    let mut encoder = AYEncoder::new();
    let (name, variants) = result_u64_bool_components();
    let encoding = encoder.register_datatype(&name, &variants).unwrap();
    let ok = encoding.variant("Ok").expect("Ok variant should exist");
    let err = encoding.variant("Err").expect("Err variant should exist");
    let ConstructorKind::Function(ok_ctor) = &ok.constructor else {
        panic!("Ok constructor should be a function");
    };
    let ConstructorKind::Function(err_ctor) = &err.constructor else {
        panic!("Err constructor should be a function");
    };

    let forty_two = encoder.solver.try_bv_const(42, 64).unwrap();
    let true_term = encoder.solver.bool_const(true);
    let ok_value = encoder.solver.try_apply(ok_ctor, &[forty_two]).unwrap();
    let err_value = encoder.solver.try_apply(err_ctor, &[true_term]).unwrap();
    let eq = encoder.solver.try_eq(ok_value, err_value).unwrap();
    encoder.solver.try_assert_term(eq).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "native theory: Ok(_) and Err(_) should be disjoint constructor images, got {:?}",
        result
    );
}
