//! Tests for emit_runtime_value_capture.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// --- emit_runtime_value_capture tests ---

#[test]
fn test_emit_runtime_capture_i32() {
    let result = emit_runtime_value_capture("x", "i32");
    assert!(result.is_some(), "i32 should produce a capture");
    let tokens = result.unwrap().to_string();
    assert!(
        tokens.contains("collect_let_binding_runtime_value"),
        "Should call i64 variant"
    );
    assert!(tokens.contains("as i64"), "Should cast to i64");
}

#[test]
fn test_emit_runtime_capture_u64() {
    let result = emit_runtime_value_capture("n", "u64");
    assert!(result.is_some(), "u64 should produce a capture");
    let tokens = result.unwrap().to_string();
    assert!(
        tokens.contains("collect_let_binding_runtime_value_i128"),
        "Should call i128 variant for u64"
    );
    assert!(tokens.contains("as i128"), "Should cast to i128");
}

#[test]
fn test_emit_runtime_capture_u128() {
    let result = emit_runtime_value_capture("big", "u128");
    assert!(result.is_some(), "u128 should produce a capture");
    let tokens = result.unwrap().to_string();
    assert!(
        tokens.contains("collect_let_binding_runtime_value_u128"),
        "Should call u128 variant"
    );
}

/// Regression test: u128 values above i128::MAX must produce the correct
/// positive decimal in the obligation condition string (#1696, fix: #1556).
///
/// Before commit 159c96d, u128 was grouped with the i128 cast arm.
/// `u128::MAX as i128` wraps to -1, producing the wrong condition string.
/// The fix passes u128 through a dedicated collector without any cast.
#[test]
fn test_u128_above_i128_max_produces_correct_condition() {
    use crate::context_management::{take_context, with_clean_thread_locals};
    use crate::obligation_collection::collect_let_binding_runtime_value_u128;
    use crate::vc::ObligationKind;

    with_clean_thread_locals(|| {
        let large_value: u128 = u128::MAX; // 340282366920938463463374607431768211455
        collect_let_binding_runtime_value_u128("big".to_string(), large_value);

        let ctx = take_context().expect("obligation should have created a context");
        let assumptions: Vec<_> = ctx
            .obligations
            .iter()
            .filter(|o| matches!(o.kind, ObligationKind::Assume))
            .collect();

        assert_eq!(
            assumptions.len(),
            1,
            "should have exactly one assumption from u128 capture"
        );

        let condition = &assumptions[0].condition;
        let expected_decimal = u128::MAX.to_string();
        assert!(
            condition.contains(&expected_decimal),
            "condition must contain the correct positive decimal for u128::MAX ({}), got: {}",
            expected_decimal,
            condition
        );
        // Must NOT contain a negative value (which would happen with the old i128 cast)
        assert!(
            !condition.contains('-'),
            "condition must not contain negative values (i128 wrapping bug), got: {}",
            condition
        );
    });
}

/// Bool runtime capture must use string "true"/"false" via collect_let_binding,
/// not integer 1/0 via collect_let_binding_runtime_value. The integer path
/// produces a Bool vs Int sort mismatch in the ay encoder. Fixes #2558.
#[test]
fn test_emit_runtime_capture_bool() {
    let result = emit_runtime_value_capture("flag", "bool");
    assert!(result.is_some(), "bool should produce a capture");
    let tokens = result.unwrap().to_string();
    assert!(
        tokens.contains("collect_let_binding"),
        "Bool should use string-based collect_let_binding"
    );
    assert!(
        !tokens.contains("collect_let_binding_runtime_value"),
        "Bool must NOT use integer-based runtime value capture (#2558)"
    );
    assert!(
        tokens.contains("true"),
        "Bool capture should encode true as string"
    );
    assert!(
        tokens.contains("false"),
        "Bool capture should encode false as string"
    );
}

#[test]
fn test_emit_runtime_capture_str_none() {
    let result = emit_runtime_value_capture("s", "str");
    assert!(result.is_none(), "str should not produce a capture");
}

#[test]
fn test_emit_runtime_capture_f64_none() {
    let result = emit_runtime_value_capture("f", "f64");
    assert!(result.is_none(), "f64 should not produce a capture");
}

#[test]
fn test_emit_runtime_capture_unknown_type_none() {
    let result = emit_runtime_value_capture("v", "Vec<i32>");
    assert!(
        result.is_none(),
        "Unknown types should not produce a capture"
    );
}
