//! Direct encoder-level tests for collection coercion and bounds checking.
//!
//! These tests construct `AstExpressionParser` directly and call encoder
//! methods without invoking the solver pipeline. This eliminates ay-dpll
//! timeout risk from quantified BV formulas while testing the same
//! encoding correctness properties.
//!
//! Split from `collections.rs` for file size compliance. Fixes #1972.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::encoder::diagnostics::EncodingApproximation;

// ========================================================================
// Int-to-BV store coercion — direct encoder tests (#1936, #1972)
// ========================================================================

/// REGRESSION (#1936): coerce_value_for_store_in_int_mode converts Sort::Int
/// to BV32 for Seq<i32> store operations in quantifier bodies.
///
/// Direct encoder test — validates the coercion method without invoking
/// the solver, eliminating the 169s+ timeout risk from the original
/// solver-pipeline version. Fixes #1972.
#[test]
fn test_seq_update_value_coercion_int_to_bv32_direct() {
    use ay_dpll::api::{ArraySort, Sort};
    let pw = crate::ir::pointer_width();
    let mut solver = Solver::try_new(Logic::All).unwrap();

    let seq_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(pw),
        element_sort: Sort::bitvec(32),
    }));
    let seq_term = solver.fresh_var("s", seq_sort);
    let len_term = solver.try_bv_const(3, pw).unwrap();

    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::from([(
        "s".to_string(),
        crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
    )]);
    let mut collection_lengths = std::collections::HashMap::from([("s".to_string(), len_term)]);
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Simulate int_mode (inside quantifier body)
    parser.quantifier_depth = 1;

    // Sort::Int value (literal 0 from quantifier arithmetic)
    let int_value = parser.solver.int_const(0);

    let result = parser.coerce_value_for_store_in_int_mode(int_value, seq_term, Some("s"));
    assert!(
        result.is_ok(),
        "Int→BV32 value coercion should succeed (#1936): {:?}",
        result.err()
    );

    let coerced = result.unwrap();
    assert!(
        parser.term_widths.contains_key(&coerced),
        "coerced value must be registered in term_widths"
    );
    let (width, is_signed) = parser.term_widths[&coerced];
    assert_eq!(width, 32, "coerced value should be BV32 for Seq<i32>");
    assert!(is_signed, "i32 element should be signed");
    assert_eq!(
        parser
            .diagnostics
            .count(EncodingApproximation::IntBvCoercion),
        1,
        "should record one Int→BV coercion"
    );
}

/// REGRESSION (#1936): coerce_value_for_store_in_int_mode converts Sort::Int
/// to BV32 for Seq::push store path.
///
/// Direct encoder test — replaces the 101s exists-quantifier solver test.
/// Fixes #1972.
#[test]
fn test_seq_push_value_coercion_int_to_bv32_direct() {
    use ay_dpll::api::{ArraySort, Sort};
    let pw = crate::ir::pointer_width();
    let mut solver = Solver::try_new(Logic::All).unwrap();

    let seq_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(pw),
        element_sort: Sort::bitvec(32),
    }));
    let seq_term = solver.fresh_var("s", seq_sort);
    let len_term = solver.try_bv_const(2, pw).unwrap();

    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::from([(
        "s".to_string(),
        crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
    )]);
    let mut collection_lengths = std::collections::HashMap::from([("s".to_string(), len_term)]);
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    parser.quantifier_depth = 1;

    // Sort::Int value 42 (from quantifier-bound arithmetic)
    let int_value = parser.solver.int_const(42);

    let result = parser.coerce_value_for_store_in_int_mode(int_value, seq_term, Some("s"));
    assert!(
        result.is_ok(),
        "Int→BV32 push value coercion should succeed (#1936): {:?}",
        result.err()
    );
    let coerced = result.unwrap();
    let (width, _) = parser.term_widths[&coerced];
    assert_eq!(width, 32, "push value should be coerced to BV32");
}

/// REGRESSION (#1936): BV-typed values must not be re-coerced via int2bv.
///
/// When `x` is already BV32 (from outer scope), coerce_value_for_store_in_int_mode
/// should return it unchanged (through the BV width match path, not the Int→BV path).
/// Direct encoder test — replaces solver-pipeline version. Fixes #1972.
#[test]
fn test_seq_update_bv_value_passthrough_in_int_mode_direct() {
    use ay_dpll::api::{ArraySort, Sort};
    let pw = crate::ir::pointer_width();
    let mut solver = Solver::try_new(Logic::All).unwrap();

    let seq_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(pw),
        element_sort: Sort::bitvec(32),
    }));
    let seq_term = solver.fresh_var("s", seq_sort);
    let len_term = solver.try_bv_const(3, pw).unwrap();

    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::from([(
        "s".to_string(),
        crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
    )]);
    let mut collection_lengths = std::collections::HashMap::from([("s".to_string(), len_term)]);
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    parser.quantifier_depth = 1;

    // BV32 value from outer scope (not Sort::Int)
    let bv_value = parser.solver.try_bv_const(99, 32).unwrap();
    parser.term_widths.insert(bv_value, (32, true));

    let result = parser.coerce_value_for_store_in_int_mode(bv_value, seq_term, Some("s"));
    assert!(
        result.is_ok(),
        "BV32 value passthrough should succeed (#1936): {:?}",
        result.err()
    );
    let coerced = result.unwrap();
    assert_eq!(
        coerced, bv_value,
        "BV32 value with matching width should pass through unchanged"
    );
    assert_eq!(
        parser
            .diagnostics
            .count(EncodingApproximation::IntBvCoercion),
        0,
        "no Int→BV coercion should occur for already-BV values"
    );
}

// ========================================================================
// Map/Set key Int-to-BV coercion — direct encoder tests (#1953, #1972)
// ========================================================================

/// REGRESSION (#1953): coerce_key_for_store_in_int_mode converts Sort::Int
/// to BV32 for Map<u32, i64> key in quantifier bodies.
///
/// Direct encoder test — replaces solver-pipeline version. Fixes #1972.
#[test]
fn test_map_key_coercion_int_to_bv32_direct() {
    use ay_dpll::api::{ArraySort, Sort};
    let mut solver = Solver::try_new(Logic::All).unwrap();

    // Map<u32, i64> = Array(BV32, BV64)
    let map_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(32),
        element_sort: Sort::bitvec(64),
    }));
    let map_term = solver.fresh_var("m", map_sort);

    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::from([(
        "m".to_string(),
        crate::ir::TrustVcType::Map(
            Box::new(crate::ir::TrustVcType::Uint { width: 32 }),
            Box::new(crate::ir::TrustVcType::Int { width: 64 }),
        ),
    )]);
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    parser.quantifier_depth = 1;

    // Sort::Int key (quantifier-bound variable)
    let int_key = parser.solver.int_const(1);

    let result = parser.coerce_key_for_store_in_int_mode(int_key, map_term, Some("m"));
    assert!(
        result.is_ok(),
        "Int→BV32 map key coercion should succeed (#1953): {:?}",
        result.err()
    );
    let coerced = result.unwrap();
    assert!(
        parser.term_widths.contains_key(&coerced),
        "coerced key must be registered in term_widths"
    );
    let (width, is_signed) = parser.term_widths[&coerced];
    assert_eq!(width, 32, "Map<u32, i64> key should be coerced to BV32");
    assert!(!is_signed, "u32 key should be unsigned");
    assert_eq!(
        parser
            .diagnostics
            .count(EncodingApproximation::IntBvCoercion),
        1,
        "should record one Int→BV coercion for map key"
    );
}

/// REGRESSION (#1953): coerce_key_for_store_in_int_mode converts Sort::Int
/// to BV32 for Map insert (try_store) path.
///
/// Direct encoder test — replaces solver-pipeline test that never compiled.
/// Fixes #1972.
#[test]
fn test_map_insert_key_coercion_int_to_bv32_direct() {
    use ay_dpll::api::{ArraySort, Sort};
    let mut solver = Solver::try_new(Logic::All).unwrap();

    let map_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(32),
        element_sort: Sort::bitvec(64),
    }));
    let map_term = solver.fresh_var("m", map_sort);

    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::from([(
        "m".to_string(),
        crate::ir::TrustVcType::Map(
            Box::new(crate::ir::TrustVcType::Uint { width: 32 }),
            Box::new(crate::ir::TrustVcType::Int { width: 64 }),
        ),
    )]);
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    parser.quantifier_depth = 1;

    // Sort::Int key for insert
    let int_key = parser.solver.int_const(5);

    let result = parser.coerce_key_for_store_in_int_mode(int_key, map_term, Some("m"));
    assert!(
        result.is_ok(),
        "Int→BV32 map insert key coercion should succeed (#1953): {:?}",
        result.err()
    );
    let coerced = result.unwrap();
    let (width, _) = parser.term_widths[&coerced];
    assert_eq!(width, 32, "insert key should be coerced to BV32");
}

/// REGRESSION (#1953): coerce_key_for_store_in_int_mode converts Sort::Int
/// to BV32 for Set<i32> key in quantifier bodies.
///
/// Direct encoder test — replaces solver-pipeline test that returned Unknown
/// due to ay-dpll quantifier BV limitations. Fixes #1972.
#[test]
fn test_set_key_coercion_int_to_bv32_direct() {
    use ay_dpll::api::{ArraySort, Sort};
    let mut solver = Solver::try_new(Logic::All).unwrap();

    // Set<i32> = Array(BV32, Bool)
    let set_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(32),
        element_sort: Sort::Bool,
    }));
    let set_term = solver.fresh_var("s", set_sort);

    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::from([(
        "s".to_string(),
        crate::ir::TrustVcType::Set(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
    )]);
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    parser.quantifier_depth = 1;

    // Sort::Int key (quantifier-bound variable)
    let int_key = parser.solver.int_const(5);

    let result = parser.coerce_key_for_store_in_int_mode(int_key, set_term, Some("s"));
    assert!(
        result.is_ok(),
        "Int→BV32 set key coercion should succeed (#1953): {:?}",
        result.err()
    );
    let coerced = result.unwrap();
    assert!(
        parser.term_widths.contains_key(&coerced),
        "coerced set key must be registered in term_widths"
    );
    let (width, is_signed) = parser.term_widths[&coerced];
    assert_eq!(width, 32, "Set<i32> key should be coerced to BV32");
    assert!(is_signed, "i32 key should be signed");
    assert_eq!(
        parser
            .diagnostics
            .count(EncodingApproximation::IntBvCoercion),
        1,
        "should record one Int→BV coercion for set key"
    );
}

// ========================================================================
// Bounds check targeting in quantifier bodies (#2231 Finding 1)
// ========================================================================

/// DISCRIMINATING: constant index in quantifier body must be bounds-checked.
///
/// Before #2231 fix, `add_seq_index_bounds_check` skipped ALL bounds checks
/// when `quantifier_depth > 0`, including constant indices like `s.index(42)`.
/// This was a soundness gap: the skip was only correct for bound-variable
/// indices where the user's quantifier guard handles OOB.
///
/// After the fix, only bound-variable indices are skipped. Constant and free
/// indices generate Int-mode bounds checks (0 <= idx < bv2int(len)).
#[test]
fn test_constant_index_bounds_checked_in_quantifier_body() {
    use ay_dpll::api::{ArraySort, Sort};
    let pw = crate::ir::pointer_width();
    let mut solver = Solver::try_new(Logic::All).unwrap();

    // Set up a Seq "s" with length 2
    let seq_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(pw),
        element_sort: Sort::bitvec(32),
    }));
    let seq_term = solver.fresh_var("s", seq_sort);
    let len_term = solver.try_bv_const(2, pw).unwrap();

    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::from([("s".to_string(), len_term)]);
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Simulate being inside a non-Skolemized quantifier (exists)
    parser.quantifier_depth = 1;

    // Constant index 42 as Sort::Int (int_mode)
    let idx = parser.solver.int_const(42);

    let result = parser.add_seq_index_bounds_check(seq_term, Some("s"), idx, "index");
    assert!(
        result.is_ok(),
        "int-mode bounds check should not error: {:?}",
        result.err()
    );
    assert_eq!(
        parser.overflow_checks.len(),
        1,
        "constant index 42 in quantifier body must generate bounds check (#2231)"
    );
}

/// DISCRIMINATING: bound-variable index in quantifier body must skip bounds check.
///
/// This is the correct-behavior counterpart to the test above. When the index
/// IS a quantifier-bound variable, the bounds check is correctly skipped
/// because the user's quantifier guard (e.g., `!(i < len) || ...`) handles OOB.
#[test]
fn test_bound_var_index_skips_bounds_check_in_quantifier_body() {
    use ay_dpll::api::{ArraySort, Sort};
    let pw = crate::ir::pointer_width();
    let mut solver = Solver::try_new(Logic::All).unwrap();

    let seq_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(pw),
        element_sort: Sort::bitvec(32),
    }));
    let seq_term = solver.fresh_var("s", seq_sort);
    let len_term = solver.try_bv_const(2, pw).unwrap();

    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::from([("s".to_string(), len_term)]);
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Simulate being inside a quantifier
    parser.quantifier_depth = 1;
    let bound_var = parser.solver.fresh_var("i", Sort::Int);

    // Register as a quantifier-bound term
    use crate::encoder::quantifier_scope::QuantifierScope;
    let mut scope = QuantifierScope::default();
    scope.add_bound_term(bound_var);
    parser.quantifier_scopes.push(scope);

    let result = parser.add_seq_index_bounds_check(seq_term, Some("s"), bound_var, "index");
    assert!(
        result.is_ok(),
        "bound var bounds check should not error: {:?}",
        result.err()
    );
    assert_eq!(
        parser.overflow_checks.len(),
        0,
        "bound-variable index must skip bounds check (user guard handles OOB)"
    );
}
