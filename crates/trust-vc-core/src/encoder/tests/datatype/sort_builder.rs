// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// P0 unit tests for the pure `datatype_sort_for` builder: maps a
// `TrustVcType::Datatype` to ay's native `DatatypeSort` descriptor. These tests
// exercise the builder in isolation (no solver registration), confirming
// constructor/field names and recursively-resolved field sorts.

use super::*;
use crate::encoder::datatype::{
    datatype_carrier_sort, datatype_sort_for, selector_symbol_name, variant_symbol_name,
};
use ay_dpll::api::Sort;

#[test]
fn test_datatype_sort_for_option_u64_constructors_and_fields() {
    let (name, variants) = option_u64_components();
    let dt = datatype_sort_for(&name, &variants);

    assert_eq!(dt.name, "Option<u64>");
    assert_eq!(dt.constructors.len(), 2);

    let none = &dt.constructors[0];
    assert_eq!(none.name, variant_symbol_name(&name, "None"));
    assert_eq!(none.name, "Option_u64_None");
    assert!(none.fields.is_empty(), "None is nullary");

    let some = &dt.constructors[1];
    assert_eq!(some.name, variant_symbol_name(&name, "Some"));
    assert_eq!(some.name, "Option_u64_Some");
    assert_eq!(some.fields.len(), 1);
    assert_eq!(
        some.fields[0].name,
        selector_symbol_name(&name, "Some", "0", 0)
    );
    // u64 payload -> 64-bit bitvector field sort.
    assert_eq!(some.fields[0].sort, Sort::bitvec(64));
}

#[test]
fn test_datatype_sort_for_result_u64_bool_field_sorts() {
    let (name, variants) = result_u64_bool_components();
    let dt = datatype_sort_for(&name, &variants);

    assert_eq!(dt.constructors.len(), 2);
    let ok = dt
        .constructors
        .iter()
        .find(|c| c.name == variant_symbol_name(&name, "Ok"))
        .expect("Ok constructor present");
    assert_eq!(ok.fields.len(), 1);
    assert_eq!(ok.fields[0].sort, Sort::bitvec(64));

    let err = dt
        .constructors
        .iter()
        .find(|c| c.name == variant_symbol_name(&name, "Err"))
        .expect("Err constructor present");
    assert_eq!(err.fields.len(), 1);
    assert_eq!(err.fields[0].sort, Sort::Bool);
}

#[test]
fn test_datatype_sort_for_recursive_field_uses_carrier_sort() {
    let (name, variants) = list_i32_components();
    let dt = datatype_sort_for(&name, &variants);

    let cons = dt
        .constructors
        .iter()
        .find(|c| c.name == variant_symbol_name(&name, "Cons"))
        .expect("Cons constructor present");
    assert_eq!(cons.fields.len(), 2);
    // head: i32 -> 32-bit bitvector.
    assert_eq!(cons.fields[0].sort, Sort::bitvec(32));
    // tail: RecursiveRef("List_i32") -> the datatype's own native carrier sort,
    // NOT the legacy shared Sort::Int.
    assert_eq!(cons.fields[1].sort, datatype_carrier_sort(&name));
    assert_eq!(cons.fields[1].sort, Sort::Uninterpreted("List_i32".into()));

    let nil = dt
        .constructors
        .iter()
        .find(|c| c.name == variant_symbol_name(&name, "Nil"))
        .expect("Nil constructor present");
    assert!(nil.fields.is_empty());
}

#[test]
fn test_datatype_sort_for_branching_recursion_all_carrier() {
    let (name, variants) = tree_i32_components();
    let dt = datatype_sort_for(&name, &variants);

    let branch = dt
        .constructors
        .iter()
        .find(|c| c.name == variant_symbol_name(&name, "Branch"))
        .expect("Branch constructor present");
    assert_eq!(branch.fields.len(), 2);
    for field in &branch.fields {
        assert_eq!(field.sort, datatype_carrier_sort(&name));
    }
}

/// Native theory engages through the encoder's real term path: `register_datatype`
/// declares constructor/selector/tester `FuncDecl`s over the native carrier sort,
/// and applying the tester FuncDecl to a constructor term (the `encode_fn_call`
/// path) satisfies ay's native tester-evaluation axiom — `is-Some(Some(5))` holds
/// (negation UNSAT) without any hand-asserted tester axiom.
#[test]
fn test_native_funcdecl_tester_roundtrip_unsat_to_negate() {
    let mut encoder = AYEncoder::new();
    let (name, variants) = option_u64_components();
    let encoding = encoder.register_datatype(&name, &variants).unwrap();
    let some = encoding.variant("Some").unwrap();
    let crate::encoder::datatype::ConstructorKind::Function(some_ctor) = &some.constructor else {
        panic!("Some constructor should be a function");
    };
    let some_ctor = some_ctor.clone();
    let tester = some.tester.clone();
    let five = encoder.solver.try_bv_const(5, 64).unwrap();
    let some5 = encoder.solver.try_apply(&some_ctor, &[five]).unwrap();
    let is_some = encoder.solver.try_apply(&tester, &[some5]).unwrap();
    let not_is_some = encoder.solver.try_not(is_some).unwrap();
    encoder.solver.try_assert_term(not_is_some).unwrap();
    assert!(
        encoder.solver.check_sat().is_unsat(),
        "native theory: is-Some(Some(5)) must hold (negation UNSAT)"
    );
}

/// Symbolic-value exhaustiveness — the core completeness gain. A datatype-sorted
/// constant `opt` with NO constructor in scope still satisfies the native
/// exhaustiveness invariant: `is-None(opt) || is-Some(opt)` is valid, so its
/// negation is UNSAT. Under the legacy UF-over-Int encoding this required a
/// hand-asserted exhaustiveness forall that the skipped-quantifier soundness gate
/// degraded to Unknown for symbolic values.
#[test]
fn test_native_funcdecl_symbolic_exhaustiveness_unsat_to_negate() {
    let mut encoder = AYEncoder::new();
    let (name, variants) = option_u64_components();
    let encoding = encoder.register_datatype(&name, &variants).unwrap();
    let none = encoding.variant("None").unwrap();
    let some = encoding.variant("Some").unwrap();
    let opt = encoder
        .solver
        .declare_const("opt", datatype_carrier_sort(&name));
    let is_none = encoder.solver.try_apply(&none.tester, &[opt]).unwrap();
    let is_some = encoder.solver.try_apply(&some.tester, &[opt]).unwrap();
    let cov = encoder.solver.try_or(is_none, is_some).unwrap();
    let uncov = encoder.solver.try_not(cov).unwrap();
    encoder.solver.try_assert_term(uncov).unwrap();
    assert!(
        encoder.solver.check_sat().is_unsat(),
        "native theory: symbolic exhaustiveness must rule out an uncovered value"
    );
}
/// Real-path completeness: a symbolic `opt: Option<u32>` (no constructor in
/// scope) in a `match` obligation discharges via native datatype theory. The
/// exhaustive `match opt { Some(x) => true, None => true }` is a tautology and
/// VERIFIES end-to-end through `AYEncoder::verify` — the symbolic-datatype-value
/// case the migration targets (legacy UF-over-Int degraded such obligations to
/// Unknown via the skipped-quantifier soundness gate).
#[test]
fn test_symbolic_match_tautology_verifies_end_to_end() {
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.declare_var_typed(
        "opt",
        crate::ir::TrustVcType::parse_or_opaque("Option<u32>"),
    );
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "match_taut",
        "match opt { Some(x) => true, None => true }",
    ));
    let result = crate::encoder::AYEncoder::verify(&ctx);
    crate::encoder::tests::result_oracles::expect_verified(
        &result,
        "symbolic-datatype match tautology should verify natively",
    );
}
