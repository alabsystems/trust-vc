//! Runtime value and let-binding tests for obligation collection.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::context_management::{get_context, with_clean_thread_locals};
use crate::vc::ObligationKind;

// -- collect_let_binding_runtime_value_from_ref: integer + unsupported types --

#[test]
fn runtime_value_from_ref_captures_integer_types() {
    with_clean_thread_locals(|| {
        let val_i32: i32 = -42;
        collect_let_binding_runtime_value_from_ref("v_i32", &val_i32);

        let context = get_context().expect("integer capture should initialize context");
        let binding = context
            .obligations
            .iter()
            .find(|o| o.name == "let_binding_runtime_v_i32");
        assert!(
            binding.is_some(),
            "i32 runtime capture should create a binding"
        );
        let cond = &binding.unwrap().condition;
        assert!(
            cond.contains("v_i32") && cond.contains("42"),
            "i32 runtime capture should reference the variable and value, got: {}",
            cond
        );
    });

    with_clean_thread_locals(|| {
        let val_u64: u64 = 999_999;
        collect_let_binding_runtime_value_from_ref("v_u64", &val_u64);

        let context2 = get_context().expect("u64 capture should initialize context");
        let binding2 = context2
            .obligations
            .iter()
            .find(|o| o.name == "let_binding_runtime_v_u64");
        assert!(
            binding2.is_some(),
            "u64 runtime capture should create a binding"
        );
        assert!(
            binding2.unwrap().condition.contains("999999"),
            "u64 runtime capture should contain 999999"
        );
    });
}

#[test]
fn runtime_value_from_ref_ignores_unsupported_types() {
    with_clean_thread_locals(|| {
        let val_str: String = "hello".to_string();
        collect_let_binding_runtime_value_from_ref("v_str", &val_str);

        // String type is unsupported — should be silently ignored
        let has_binding = get_context()
            .map(|c| c.obligations.iter().any(|o| o.name.contains("v_str")))
            .unwrap_or(false);
        assert!(
            !has_binding,
            "unsupported types should be silently ignored by runtime value capture"
        );
    });
}

// -- collect_let_binding: symbolic let-binding assumption --

#[test]
fn collect_let_binding_creates_named_assume_obligation() {
    with_clean_thread_locals(|| {
        collect_let_binding("y".to_string(), "5 * 5".to_string());

        let context = get_context().expect("let binding should initialize context");
        let binding = context
            .obligations
            .iter()
            .find(|o| o.name == "let_binding_y");
        assert!(
            binding.is_some(),
            "collect_let_binding must create a let_binding_<var> obligation"
        );
        let ob = binding.unwrap();
        assert_eq!(ob.kind, ObligationKind::Assume);
        assert!(
            ob.condition.contains("y") && ob.condition.contains("5 * 5"),
            "collect_let_binding condition should reference both variable and expression, got: {}",
            ob.condition
        );
    });
}

// -- collect_let_binding_runtime_value: i64 decimal literal --

#[test]
fn collect_let_binding_runtime_value_records_i64_literal() {
    with_clean_thread_locals(|| {
        collect_let_binding_runtime_value("counter".to_string(), 42_i64);

        let context = get_context().expect("runtime value should initialize context");
        let binding = context
            .obligations
            .iter()
            .find(|o| o.name == "let_binding_runtime_counter");
        assert!(
            binding.is_some(),
            "collect_let_binding_runtime_value must create a let_binding_runtime_<var> obligation"
        );
        let ob = binding.unwrap();
        assert_eq!(ob.kind, ObligationKind::Assume);
        assert!(
            ob.condition.contains("42"),
            "i64 runtime capture must preserve the exact decimal literal, got: {}",
            ob.condition
        );
        assert!(
            ob.condition.contains("counter"),
            "condition should reference the variable name, got: {}",
            ob.condition
        );
    });
}

// -- collect_let_binding_runtime_value_i128: wide i128 literal --

#[test]
fn collect_let_binding_runtime_value_i128_preserves_large_value() {
    with_clean_thread_locals(|| {
        // Value larger than i64::MAX to ensure the wide path is required
        let large: i128 = i64::MAX as i128 + 1;
        collect_let_binding_runtime_value_i128("big_i128".to_string(), large);

        let context = get_context().expect("i128 runtime capture should initialize context");
        let binding = context
            .obligations
            .iter()
            .find(|o| o.name == "let_binding_runtime_big_i128");
        assert!(
            binding.is_some(),
            "collect_let_binding_runtime_value_i128 must create a runtime obligation"
        );
        let ob = binding.unwrap();
        assert_eq!(ob.kind, ObligationKind::Assume);
        assert!(
            ob.condition.contains("9223372036854775808"),
            "i128 path must preserve values larger than i64::MAX without truncation, got: {}",
            ob.condition
        );
    });
}

// -- collect_let_binding_runtime_value_u128: wide u128 literal --

#[test]
fn collect_let_binding_runtime_value_u128_preserves_large_value() {
    with_clean_thread_locals(|| {
        // Value larger than i128::MAX to ensure we need the unsigned path
        let large: u128 = i128::MAX as u128 + 1;
        collect_let_binding_runtime_value_u128("big_u128".to_string(), large);

        let context = get_context().expect("u128 runtime capture should initialize context");
        let binding = context
            .obligations
            .iter()
            .find(|o| o.name == "let_binding_runtime_big_u128");
        assert!(
            binding.is_some(),
            "collect_let_binding_runtime_value_u128 must create a runtime obligation"
        );
        let ob = binding.unwrap();
        assert_eq!(ob.kind, ObligationKind::Assume);
        assert!(
            ob.condition
                .contains("170141183460469231731687303715884105728"),
            "u128 path must preserve values larger than i128::MAX without signed wrapping, got: {}",
            ob.condition
        );
    });
}
