//! Measure collection-path tests for decreases inference.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;
use crate::context_management::with_clean_thread_locals;
use crate::decreases_runtime::is_valid_measure_component;

fn compact(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

#[test]
fn test_is_valid_measure_component() {
    assert!(is_valid_measure_component("n"));
    assert!(is_valid_measure_component("count"));
    assert!(is_valid_measure_component("_x"));
    assert!(is_valid_measure_component("x.len"));
    assert!(is_valid_measure_component("n - 1"));
    assert!(!is_valid_measure_component(""));
    assert!(!is_valid_measure_component("5"));
    assert!(!is_valid_measure_component("123"));
    assert!(!is_valid_measure_component("++"));
}

#[test]
fn test_decreases_skips_empty_measure() {
    // Empty measure is invalid — graceful skip, no obligations added (#1955).
    with_clean_thread_locals(|| {
        collect_decreases_measure("".to_string(), None);
        let ctx = get_context();
        let has_obligations = ctx.as_ref().is_some_and(|c| !c.obligations.is_empty());
        assert!(
            !has_obligations,
            "empty measure should produce no obligations"
        );
    });
}

#[test]
fn test_decreases_skips_numeric_literal() {
    // Numeric literal is invalid — graceful skip (#1955).
    with_clean_thread_locals(|| {
        collect_decreases_measure("5".to_string(), None);
        let ctx = get_context();
        let has_obligations = ctx.as_ref().is_some_and(|c| !c.obligations.is_empty());
        assert!(
            !has_obligations,
            "numeric literal should produce no obligations"
        );
    });
}

#[test]
fn test_decreases_skips_empty_tuple_components() {
    // Empty tuple is invalid — graceful skip (#1955).
    with_clean_thread_locals(|| {
        collect_decreases_measure("(, )".to_string(), None);
        let ctx = get_context();
        let has_obligations = ctx.as_ref().is_some_and(|c| !c.obligations.is_empty());
        assert!(
            !has_obligations,
            "empty tuple should produce no obligations"
        );
    });
}

#[test]
fn test_decreases_skips_numeric_tuple_component() {
    // Numeric tuple component is invalid — graceful skip (#1955).
    with_clean_thread_locals(|| {
        collect_decreases_measure("(n, 5)".to_string(), None);
        let ctx = get_context();
        let has_obligations = ctx.as_ref().is_some_and(|c| !c.obligations.is_empty());
        assert!(
            !has_obligations,
            "numeric tuple component should produce no obligations"
        );
    });
}

#[test]
fn test_decreases_accepts_valid_tuple_measure() {
    with_clean_thread_locals(|| {
        collect_decreases_measure("(m, n)".to_string(), None);
        let ctx = get_context();
        assert!(ctx.is_some());
    });
}

#[test]
fn test_decreases_preserves_nested_comma_tuple_component() {
    with_clean_thread_locals(|| {
        collect_decreases_measure("(f(a, b), c)".to_string(), None);

        let ctx = get_context().expect("nested-comma tuple should initialize a context");
        let nonneg_conditions: Vec<String> = ctx
            .obligations
            .iter()
            .filter(|o| matches!(o.kind, crate::vc::ObligationKind::MeasureNonNegative))
            .map(|o| compact(&o.condition))
            .collect();

        assert_eq!(
            nonneg_conditions.len(),
            2,
            "nested-comma tuple should split into two components, got {:?}",
            nonneg_conditions
        );
        assert!(
            nonneg_conditions.contains(&"f(a,b)>=0".to_string()),
            "first component should preserve nested comma, got {:?}",
            nonneg_conditions
        );
        assert!(
            nonneg_conditions.contains(&"c>=0".to_string()),
            "second component should remain intact, got {:?}",
            nonneg_conditions
        );
    });
}

#[test]
fn test_decreases_parenthesized_nested_comma_as_single_measure() {
    with_clean_thread_locals(|| {
        collect_decreases_measure("(f(a, b))".to_string(), None);

        let ctx = get_context().expect("parenthesized singleton should initialize a context");
        let nonneg_conditions: Vec<String> = ctx
            .obligations
            .iter()
            .filter(|o| matches!(o.kind, crate::vc::ObligationKind::MeasureNonNegative))
            .map(|o| compact(&o.condition))
            .collect();

        assert_eq!(
            nonneg_conditions,
            vec!["(f(a,b))>=0".to_string()],
            "parenthesized singleton should stay a single measure, got {:?}",
            nonneg_conditions
        );
    });
}

#[test]
fn test_decreases_preserves_struct_literal_tuple_component() {
    with_clean_thread_locals(|| {
        collect_decreases_measure("(f(Foo { x: a, y: b }), c)".to_string(), None);

        let ctx = get_context().expect("struct-literal tuple should initialize a context");
        let nonneg_conditions: Vec<String> = ctx
            .obligations
            .iter()
            .filter(|o| matches!(o.kind, crate::vc::ObligationKind::MeasureNonNegative))
            .map(|o| compact(&o.condition))
            .collect();

        assert_eq!(
            nonneg_conditions.len(),
            2,
            "struct-literal tuple should split into two components, got {:?}",
            nonneg_conditions
        );
        assert!(
            nonneg_conditions.contains(&"f(Foo{x:a,y:b})>=0".to_string()),
            "first component should preserve struct literal commas, got {:?}",
            nonneg_conditions
        );
        assert!(
            nonneg_conditions.contains(&"c>=0".to_string()),
            "second component should remain intact, got {:?}",
            nonneg_conditions
        );
    });
}

#[test]
fn test_loop_decreases_preserves_struct_literal_tuple_component() {
    with_clean_thread_locals(|| {
        collect_variable("a".to_string(), "u64".to_string());
        collect_variable("b".to_string(), "u64".to_string());
        collect_variable("c".to_string(), "u64".to_string());
        collect_loop_decreases_measure(
            "(f(Foo { x: a, y: b }), c)".to_string(),
            Some("test_loop_struct_literal".to_string()),
        );

        let ctx = get_context().expect("struct-literal loop tuple should initialize a context");
        let nonneg_conditions: Vec<String> = ctx
            .obligations
            .iter()
            .filter(|o| matches!(o.kind, crate::vc::ObligationKind::MeasureNonNegative))
            .map(|o| compact(&o.condition))
            .collect();
        assert_eq!(
            nonneg_conditions.len(),
            2,
            "loop tuple should split into two nonneg obligations, got {:?}",
            nonneg_conditions
        );
        assert!(
            nonneg_conditions.contains(&"f(Foo{x:a,y:b})>=0".to_string()),
            "loop tuple should preserve struct literal commas, got {:?}",
            nonneg_conditions
        );
        assert!(
            nonneg_conditions.contains(&"c>=0".to_string()),
            "loop tuple should keep the second component intact, got {:?}",
            nonneg_conditions
        );

        let lex_obligation = ctx
            .obligations
            .iter()
            .find(|o| matches!(o.kind, crate::vc::ObligationKind::MeasureDecreases))
            .expect("loop tuple should generate a lexicographic decreases obligation");
        let lex_condition = compact(&lex_obligation.condition);
        assert!(
            lex_condition.contains("f(Foo{x:a,y:b})<"),
            "lex obligation should preserve the first component, got {}",
            lex_condition
        );
        assert!(
            lex_condition.contains("c<c_entry"),
            "lex obligation should include the second component, got {}",
            lex_condition
        );
    });
}

#[test]
fn test_loop_decreases_parenthesized_nested_comma_as_single_measure() {
    with_clean_thread_locals(|| {
        collect_variable("a".to_string(), "u64".to_string());
        collect_variable("b".to_string(), "u64".to_string());
        collect_loop_decreases_measure(
            "(f(a, b))".to_string(),
            Some("test_loop_parenthesized_singleton".to_string()),
        );

        let ctx = get_context().expect("parenthesized singleton loop should initialize a context");
        let nonneg_conditions: Vec<String> = ctx
            .obligations
            .iter()
            .filter(|o| matches!(o.kind, crate::vc::ObligationKind::MeasureNonNegative))
            .map(|o| compact(&o.condition))
            .collect();
        assert_eq!(
            nonneg_conditions,
            vec!["(f(a,b))>=0".to_string()],
            "loop decreases should keep the parenthesized singleton intact, got {:?}",
            nonneg_conditions
        );

        let lex_obligation = ctx
            .obligations
            .iter()
            .find(|o| matches!(o.kind, crate::vc::ObligationKind::MeasureDecreases))
            .expect("single loop measure should generate a decreases obligation");
        let lex_condition = compact(&lex_obligation.condition);
        assert!(
            lex_condition.contains("(f(a,b))<"),
            "single loop decreases should preserve the parenthesized expression, got {}",
            lex_condition
        );
        assert!(
            !lex_condition.contains("||"),
            "single loop decreases should not synthesize lexicographic disjunctions, got {}",
            lex_condition
        );
    });
}

#[test]
fn test_decreases_preserves_shift_operator_tuple_component() {
    with_clean_thread_locals(|| {
        collect_decreases_measure("(n >> 1, c)".to_string(), None);

        let ctx = get_context().expect("shift-operator tuple should initialize a context");
        let nonneg_conditions: Vec<String> = ctx
            .obligations
            .iter()
            .filter(|o| matches!(o.kind, crate::vc::ObligationKind::MeasureNonNegative))
            .map(|o| compact(&o.condition))
            .collect();

        assert_eq!(
            nonneg_conditions.len(),
            2,
            "shift-operator tuple should split into two components, got {:?}",
            nonneg_conditions
        );
        assert!(
            nonneg_conditions.contains(&"n>>1>=0".to_string()),
            "first component should preserve the shift expression, got {:?}",
            nonneg_conditions
        );
        assert!(
            nonneg_conditions.contains(&"c>=0".to_string()),
            "second component should remain intact, got {:?}",
            nonneg_conditions
        );
    });
}

#[test]
fn test_loop_decreases_preserves_shift_operator_tuple_component() {
    with_clean_thread_locals(|| {
        collect_variable("n".to_string(), "u64".to_string());
        collect_variable("c".to_string(), "u64".to_string());
        collect_loop_decreases_measure(
            "(n >> 1, c)".to_string(),
            Some("test_loop_shift_tuple".to_string()),
        );

        let ctx = get_context().expect("shift-operator loop tuple should initialize a context");
        let nonneg_conditions: Vec<String> = ctx
            .obligations
            .iter()
            .filter(|o| matches!(o.kind, crate::vc::ObligationKind::MeasureNonNegative))
            .map(|o| compact(&o.condition))
            .collect();
        assert_eq!(
            nonneg_conditions.len(),
            2,
            "loop shift tuple should split into two nonneg obligations, got {:?}",
            nonneg_conditions
        );
        assert!(
            nonneg_conditions.contains(&"n>>1>=0".to_string()),
            "loop tuple should preserve the shift expression, got {:?}",
            nonneg_conditions
        );
        assert!(
            nonneg_conditions.contains(&"c>=0".to_string()),
            "loop tuple should keep the second component intact, got {:?}",
            nonneg_conditions
        );

        let lex_obligation = ctx
            .obligations
            .iter()
            .find(|o| matches!(o.kind, crate::vc::ObligationKind::MeasureDecreases))
            .expect("loop shift tuple should generate a lexicographic decreases obligation");
        let lex_condition = compact(&lex_obligation.condition);
        assert!(
            lex_condition.contains("n>>1<"),
            "lex obligation should preserve the shift expression, got {}",
            lex_condition
        );
        assert!(
            lex_condition.contains("c<c_entry"),
            "lex obligation should include the second component, got {}",
            lex_condition
        );
    });
}
