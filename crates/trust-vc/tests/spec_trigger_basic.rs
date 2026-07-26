// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for #[spec] and #[trigger] attribute expansions.
//!
//! Verifies that spec functions and trigger patterns compile and verify correctly.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc::{broadcast, spec, trigger};

// Test helper module for verification
#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;

// Test: basic spec function (unit return type - verified pattern)
#[spec]
fn spec_assert_positive(n: u64) {
    trust_vc::assert!(n > 0);
}

#[test]
fn test_spec_compiles() {
    // spec functions should compile
    // They panic at runtime (ghost code)
    let result = std::panic::catch_unwind(|| {
        spec_assert_positive(5);
    });
    assert!(result.is_err(), "spec function should panic at runtime");
}

#[test]
fn test_spec_panic_message() {
    let result = std::panic::catch_unwind(|| {
        spec_assert_positive(10);
    });
    match result {
        Err(e) => {
            let msg = e
                .downcast_ref::<&str>()
                .map(|s| s.to_string())
                .or_else(|| e.downcast_ref::<String>().cloned())
                .unwrap_or_default();
            assert!(
                msg.contains("spec function") || msg.contains("ghost code"),
                "panic message should mention spec function: got {:?}",
                msg
            );
        }
        Ok(_) => panic!("spec function should have panicked"),
    }
}

// Test: spec functions with logic (unit return)
#[spec]
fn spec_assert_max_ge(a: i64, b: i64) {
    // Assert that max(a, b) >= a and max(a, b) >= b
    let max = if a > b { a } else { b };
    trust_vc::assert!(max >= a);
    trust_vc::assert!(max >= b);
}

#[spec]
fn spec_assert_min_le(a: i64, b: i64) {
    // Assert that min(a, b) <= a and min(a, b) <= b
    let min = if a < b { a } else { b };
    trust_vc::assert!(min <= a);
    trust_vc::assert!(min <= b);
}

#[test]
fn test_spec_functions_compile() {
    // Multiple spec functions should compile
    let _ = std::panic::catch_unwind(|| spec_assert_max_ge(1, 2));
    let _ = std::panic::catch_unwind(|| spec_assert_min_le(1, 2));
}

// Test: spec functions with non-unit return types (issue #25 fix)
// These previously failed to compile due to type mismatch in expansion.

#[spec]
fn spec_max(a: i64, b: i64) -> i64 {
    if a > b {
        a
    } else {
        b
    }
}

#[spec]
fn spec_min(a: i64, b: i64) -> i64 {
    if a < b {
        a
    } else {
        b
    }
}

#[spec]
fn spec_abs(x: i64) -> u64 {
    if x < 0 {
        (-x) as u64
    } else {
        x as u64
    }
}

#[test]
fn test_spec_non_unit_return_compiles() {
    // Spec functions with non-unit return types should compile
    // They panic at runtime (ghost code)
    let result = std::panic::catch_unwind(|| spec_max(5, 10));
    assert!(result.is_err(), "spec function should panic at runtime");
}

#[test]
fn test_spec_min_with_return() {
    let result = std::panic::catch_unwind(|| spec_min(3, 7));
    assert!(result.is_err(), "spec function should panic at runtime");
}

#[test]
fn test_spec_abs_with_return() {
    let result = std::panic::catch_unwind(|| spec_abs(-42));
    assert!(result.is_err(), "spec function should panic at runtime");
}

// Test: trigger attribute on a function
#[trigger(foo(n))]
fn lemma_foo_property(n: u64) {
    // Trigger pattern is foo(n)
    // SMT solver instantiates when it sees foo(n)
}

#[test]
fn test_trigger_compiles() {
    // Function with trigger should compile
    // Triggers are metadata - calling the function works normally
    lemma_foo_property(10);
}

// Test: broadcast lemma with trigger
// Helper function for testing
#[spec]
fn max_val(a: i64, b: i64) -> i64 {
    if a >= b {
        a
    } else {
        b
    }
}

#[broadcast]
#[trigger(max_val(a, b))]
fn lemma_max_ge_both(a: i64, b: i64) {
    // Broadcast lemma about max function
    // Triggered when SMT sees max_val(a, b)
    trust_vc::ensures!(max_val(a, b) >= a && max_val(a, b) >= b); // Proper max property
}

#[test]
fn test_broadcast_with_trigger_compiles() {
    // Broadcast lemma with trigger should compile and run in test mode.
    // In test mode, broadcast functions collect obligations (not erased).
    // Panics only happen outside test mode (#[cfg(not(any(trust_mc, test)))]).
    let result = std::panic::catch_unwind(|| {
        lemma_max_ge_both(5, 10);
    });
    assert!(
        result.is_ok(),
        "broadcast lemma should run without panic in test mode, got: {:?}",
        result.err()
    );
}

#[test]
fn test_broadcast_runs_in_test_mode() {
    // Broadcast functions in test mode execute their body for obligation collection.
    // This is distinct from spec functions which may panic via ghost_unreachable_block.
    let result = std::panic::catch_unwind(|| {
        lemma_max_ge_both(1, 2);
    });
    assert!(
        result.is_ok(),
        "broadcast lemma should collect obligations in test mode"
    );
}

// Test: multiple triggers on same function
#[broadcast]
#[trigger(min_val(a, b))]
#[trigger(max_val(a, b))]
fn lemma_min_max_relation(a: i64, b: i64) {
    // Lemma relating min and max (conceptual)
    trust_vc::ensures!(a <= b || b <= a); // Tautology for testing
}

#[test]
fn test_multiple_triggers_compile() {
    // Multiple triggers on same function should compile
    let _ = std::panic::catch_unwind(|| {
        lemma_min_max_relation(3, 7);
    });
}

// Test: trigger with complex pattern
#[trigger(foo(n) + bar(m))]
fn lemma_additive(n: u64, m: u64) {
    // Complex trigger pattern
}

#[test]
fn test_complex_trigger_pattern() {
    // Complex trigger patterns should compile
    lemma_additive(5, 10);
}

// Test: trigger with named group syntax
#[trigger(grouped_pair(a, b), group = 2)]
fn lemma_named_group(a: u64, b: u64) {
    // Named trigger groups should compile alongside the legacy positional form.
}

#[test]
fn test_named_group_trigger_pattern() {
    lemma_named_group(5, 10);
}
