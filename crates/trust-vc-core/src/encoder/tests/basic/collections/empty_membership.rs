//! Regression tests for empty collection membership constraints (#2530).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Without const_array(false) constraints on empty Set/Map arrays, the
//! underlying SMT array is unconstrained and `select(empty_set, x)` can
//! return true, causing false counterexamples.

use super::*;

use crate::vc::FunctionContext;

fn register_empty_set_i32(encoder: &mut AYEncoder) -> String {
    let name = format!(
        "{}trust_vc_types_Set_i32_empty",
        crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX
    );
    let func_ctx = FunctionContext {
        name: name.clone(),
        params: vec![],
        return_type: crate::ir::TrustVcType::Set(Box::new(crate::ir::TrustVcType::Int {
            width: 32,
        })),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    };
    encoder
        .register_function_context(&func_ctx)
        .expect("empty Set constructor registration should succeed");
    name
}

fn register_empty_map_i32_bool(encoder: &mut AYEncoder) -> String {
    let name = format!(
        "{}trust_vc_types_Map_i32_bool_empty",
        crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX
    );
    let func_ctx = FunctionContext {
        name: name.clone(),
        params: vec![],
        return_type: crate::ir::TrustVcType::Map(
            Box::new(crate::ir::TrustVcType::Int { width: 32 }),
            Box::new(crate::ir::TrustVcType::Bool),
        ),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    };
    encoder
        .register_function_context(&func_ctx)
        .expect("empty Map constructor registration should succeed");
    name
}

/// DISCRIMINATING: `Set::empty().contains(x)` must always be false.
///
/// Without the const_array(false) fix, the SMT array for the empty set
/// is unconstrained, so `select(empty_set, 42)` can be true → UNSAT
/// when we negate it, causing false verification via vacuous truth.
/// With the fix, `select(empty_set, 42) == false` is forced → SAT when
/// we assert `select(empty_set, 42) == false`.
#[test]
fn test_empty_set_contains_is_always_false() {
    let mut encoder = AYEncoder::new();
    let name = register_empty_set_i32(&mut encoder);

    let set_term = *encoder
        .variables
        .get(&name)
        .expect("empty Set should be registered as a constant");

    // select(empty_set, 42) should be false
    let idx = encoder.solver.try_bv_const(42, 32).unwrap();
    let selected = encoder.solver.try_select(set_term, idx).unwrap();

    // Assert select(empty_set, 42) == true — should be UNSAT
    encoder.solver.try_assert_term(selected).unwrap();

    let result = check_sat_with_bv_watchdog(&mut encoder);
    assert!(
        result.is_unsat(),
        "select(Set::empty(), 42) must be false — empty set membership \
         is unconstrained without const_array fix (#2530)"
    );
}

/// DISCRIMINATING: `Map::empty().contains_key(k)` must always be false.
///
/// The domain array for empty Map must be all-false so that
/// `select(dom, k) == true` is UNSAT for any k.
#[test]
fn test_empty_map_contains_key_is_always_false() {
    let mut encoder = AYEncoder::new();
    let name = register_empty_map_i32_bool(&mut encoder);

    let dom_name = format!("{name}_dom");
    let dom_term = *encoder
        .variables
        .get(&dom_name)
        .expect("empty Map should register a domain array");

    // select(empty_map_dom, 7) should be false
    let key = encoder.solver.try_bv_const(7, 32).unwrap();
    let selected = encoder.solver.try_select(dom_term, key).unwrap();

    // Assert select(dom, 7) == true — should be UNSAT
    encoder.solver.try_assert_term(selected).unwrap();

    let result = check_sat_with_bv_watchdog(&mut encoder);
    assert!(
        result.is_unsat(),
        "select(Map::empty().dom(), 7) must be false — empty map domain \
         is unconstrained without const_array fix (#2530)"
    );
}

/// CORRECTNESS: empty set's const_array(false) constraint is consistent
/// with insert via store(set, elem, true).
///
/// After constraining the empty set to const_array(false), inserting an
/// element with store(set, 5, true) should yield select(result, 5) == true.
/// This validates that const_array(false) + store produces a correct
/// membership result.
#[test]
fn test_empty_set_insert_membership_consistent() {
    let mut encoder = AYEncoder::new();
    let name = register_empty_set_i32(&mut encoder);

    let set_term = *encoder
        .variables
        .get(&name)
        .expect("empty Set should be registered as a constant");

    // store(empty_set, 5, true) = insert(5)
    let idx = encoder.solver.try_bv_const(5, 32).unwrap();
    let true_val = encoder.solver.bool_const(true);
    let after_insert = encoder.solver.try_store(set_term, idx, true_val).unwrap();

    // select(after_insert, 5) should be true
    let membership = encoder.solver.try_select(after_insert, idx).unwrap();
    let not_member = encoder.solver.try_not(membership).unwrap();
    // Assert NOT member — should be UNSAT (member must be true after insert)
    encoder.solver.try_assert_term(not_member).unwrap();

    let result = check_sat_with_bv_watchdog(&mut encoder);
    assert!(
        result.is_unsat(),
        "store(Set::empty(), 5, true) must have select(result, 5) == true — \
         const_array(false) must be consistent with store/select"
    );
}
