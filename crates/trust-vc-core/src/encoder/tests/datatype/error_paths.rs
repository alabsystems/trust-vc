// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_register_datatype_is_idempotent_and_does_not_add_duplicate_axioms() {
    // Native-datatype migration: the soundness facts (exhaustiveness, tester,
    // selector roundtrip, injectivity, disjointness) are now ay native datatype
    // theory invariants established by `try_declare_datatype` — NOT hand-asserted
    // top-level forall axioms — so registration adds no top-level assertions, and
    // there is no per-datatype forall count to compare. Idempotence is therefore
    // asserted natively: the first registration records the datatype in the
    // registry, and the second reuses that cache (returning the identical encoding)
    // without re-declaring symbols or adding assertions.
    let mut encoder = AYEncoder::new();
    let (name, variants) = option_u64_components();

    assert!(
        encoder.datatype_encoding(&name).is_none(),
        "precondition: datatype not yet registered"
    );

    let before = encoder.solver.assertions().len();
    let first = encoder.register_datatype(&name, &variants).unwrap();
    let after_first = encoder.solver.assertions().len();

    // Native registration adds no top-level forall axioms.
    assert_eq!(
        after_first, before,
        "native registration must not hand-assert top-level axioms"
    );
    assert!(
        encoder.datatype_encoding(&name).is_some(),
        "first registration should record the datatype natively in the registry"
    );

    let second = encoder.register_datatype(&name, &variants).unwrap();
    let after_second = encoder.solver.assertions().len();

    // Idempotent: the second registration reuses the cached encoding and adds
    // nothing (no duplicate symbol declarations, no extra assertions).
    assert_eq!(
        after_first, after_second,
        "second registration should reuse cache and add no axioms"
    );
    assert_eq!(first.name, second.name);
    assert_eq!(first.variants.len(), second.variants.len());
}

#[test]
fn test_register_datatype_empty_variants_returns_error() {
    let mut encoder = AYEncoder::new();
    let result = encoder.register_datatype("Empty", &[]);
    assert!(result.is_err(), "empty variants should error");
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("at least one variant"),
        "error should mention variant requirement, got: {err_msg}"
    );
}

#[test]
fn test_sanitize_symbol_strips_special_characters() {
    use crate::encoder::datatype::{selector_symbol_name, tester_symbol_name, variant_symbol_name};

    let name = variant_symbol_name("Option<u64>", "Some");
    assert_eq!(name, "Option_u64_Some");

    let tester = tester_symbol_name("Option<u64>", "None");
    assert_eq!(tester, "is-Option_u64_None");

    let selector = selector_symbol_name("Result<u64, bool>", "Ok", "value", 0);
    assert_eq!(selector, "Result_u64_bool_Ok_value");

    let selector_idx = selector_symbol_name("Result<u64, bool>", "Ok", "", 0);
    assert_eq!(selector_idx, "Result_u64_bool_Ok_Datatype");

    let selector_tuple = selector_symbol_name("Option<u64>", "Some", "0", 0);
    assert_eq!(selector_tuple, "Option_u64_Some_0");
}

#[test]
fn test_constructor_image_disjointness_some_vs_none_is_unsat() {
    let mut encoder = AYEncoder::new();
    let (name, variants) = option_u64_components();
    let encoding = encoder.register_datatype(&name, &variants).unwrap();
    let some = encoding.variant("Some").expect("Some variant should exist");
    let none = encoding.variant("None").expect("None variant should exist");
    let ConstructorKind::Function(some_ctor) = &some.constructor else {
        panic!("Some should be a function constructor");
    };
    let ConstructorKind::Constant(none_val) = &none.constructor else {
        panic!("None should be a constant constructor");
    };

    let x = encoder
        .solver
        .declare_const("x", ay_dpll::api::Sort::bitvec(64));
    let some_x = encoder.solver.try_apply(some_ctor, &[x]).unwrap();
    let eq = encoder.solver.try_eq(some_x, *none_val).unwrap();
    encoder.solver.try_assert_term(eq).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "Some(x) should never equal None by constructor-image disjointness, got {:?}",
        result
    );
}
