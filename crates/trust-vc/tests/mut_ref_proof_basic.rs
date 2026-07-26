// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integration tests for `&mut` parameter proof verification.
//!
//! The mut-ref MVP rewrites `*x` reads on `&mut` parameters into SSA-style
//! shadow values and instruments direct stores. These tests verify end-to-end
//! that the shadow-variable chain feeds the ay verification pipeline correctly.
//!
//! Design: `designs/2026-03-18-2411-mut-ref-proof-mvp.md`
//! Issue: #2426 (acceptance criterion 1: simple &mut parameter pre/post reasoning)

use trust_vc::{assume, proof};
use trust_vc_core::VerifyResult;
mod common;

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy)]
    struct Counter {
        count: i32,
        max: i32,
    }

    #[derive(Clone, Copy)]
    struct OuterCounter {
        inner: Counter,
        limit: i32,
    }

    /// Single `&mut i32` parameter with increment and ensures postcondition.
    #[test]
    fn test_mut_ref_increment_ensures() {
        #[proof]
        fn lemma_increment(x: &mut i32) {
            assume!(*x >= 0);
            assume!(*x < 1000);
            *x = *x + 1;
            trust_vc::ensures!(*x == old!(*x) + 1);
        }

        let mut val = 42;
        lemma_increment(&mut val);
        assert_eq!(val, 43, "runtime store should advance the value");
    }

    /// Two independent `&mut` parameters — each gets independent shadow tracking.
    #[test]
    fn test_mut_ref_two_params() {
        #[proof]
        fn lemma_two_params(a: &mut i32, b: &mut i32) {
            assume!(*a >= 0);
            assume!(*a < 500);
            assume!(*b >= 0);
            assume!(*b < 500);
            *a = *a + 1;
            *b = *b + 2;
            trust_vc::assert!(*a > 0);
            trust_vc::ensures!(*b == old!(*b) + 2);
        }

        let mut x = 10;
        let mut y = 20;
        lemma_two_params(&mut x, &mut y);
        assert_eq!(x, 11);
        assert_eq!(y, 22);
    }

    /// Multiple sequential stores advance the shadow version correctly.
    #[test]
    fn test_mut_ref_double_store() {
        #[proof]
        fn lemma_double_bump(x: &mut i32) {
            assume!(*x >= 0);
            assume!(*x < 100);
            *x = *x + 1;
            *x = *x + 1;
            trust_vc::ensures!(*x == old!(*x) + 2);
        }

        let mut val = 5;
        lemma_double_bump(&mut val);
        assert_eq!(val, 7);
    }

    /// Requires uses the entry value of *x (before any stores).
    #[test]
    fn test_mut_ref_requires_entry_value() {
        #[proof]
        fn lemma_bounded_update(x: &mut i32) {
            trust_vc::requires!(*x >= 0);
            trust_vc::requires!(*x < 1000);
            *x = *x + 1;
            trust_vc::assert!(*x > 0);
        }

        let mut val = 50;
        lemma_bounded_update(&mut val);
        assert_eq!(val, 51);
    }

    /// `old!(*x)` works inside `trust_vc::assert!()` — per design MVP Goal.
    #[test]
    fn test_mut_ref_old_inside_assert() {
        #[proof]
        fn lemma_old_in_assert(x: &mut i32) {
            assume!(*x >= 0);
            assume!(*x < 1000);
            *x = *x + 1;
            trust_vc::assert!(*x > old!(*x));
            trust_vc::assert!(*x == old!(*x) + 1);
            trust_vc::ensures!(*x == old!(*x) + 1);
        }

        let mut val = 42;
        lemma_old_in_assert(&mut val);
        assert_eq!(val, 43);
    }

    /// Mixed &mut and value parameters — value params are unaffected by the
    /// mut-ref transform.
    #[test]
    fn test_mut_ref_mixed_params() {
        #[proof]
        fn lemma_add_offset(x: &mut i32, offset: i32) {
            assume!(*x >= 0);
            assume!(*x < 500);
            assume!(offset > 0);
            assume!(offset < 500);
            *x = *x + offset;
            trust_vc::ensures!(*x == old!(*x) + offset);
        }

        let mut val = 10;
        lemma_add_offset(&mut val, 5);
        assert_eq!(val, 15);
    }

    /// Field-level updates preserve untouched fields automatically via
    /// per-place entry shadows.
    #[test]
    fn test_mut_ref_field_update_frame_condition() {
        #[proof]
        fn lemma_update_count(counter: &mut Counter) {
            assume!(counter.count >= 0);
            assume!(counter.count < counter.max);
            counter.count = counter.count + 1;
            trust_vc::assert!(counter.count <= counter.max);
            trust_vc::ensures!(counter.count == old!(counter.count) + 1);
            trust_vc::ensures!(counter.max == old!(counter.max));
        }

        let mut counter = Counter { count: 2, max: 5 };
        lemma_update_count(&mut counter);
        assert_eq!(counter.count, 3);
        assert_eq!(counter.max, 5);
    }

    /// Nested field-place updates on symbolic structs use leaf-place shadows.
    #[test]
    fn test_mut_ref_nested_field_update() {
        #[proof]
        fn lemma_update_nested(counter: &mut OuterCounter) {
            assume!(counter.inner.count >= 0);
            assume!(counter.inner.count < counter.inner.max);
            counter.inner.count = counter.inner.count + 1;
            trust_vc::ensures!(counter.limit == old!(counter.limit));
            trust_vc::ensures!(counter.inner.count == old!(counter.inner.count) + 1);
            trust_vc::ensures!(counter.inner.max == old!(counter.inner.max));
        }

        let mut counter = OuterCounter {
            inner: Counter { count: 1, max: 4 },
            limit: 10,
        };
        lemma_update_nested(&mut counter);
        assert_eq!(counter.inner.count, 2);
        assert_eq!(counter.inner.max, 4);
        assert_eq!(counter.limit, 10);
    }

    /// Invalid ensures should fail verification (negative test).
    /// The postcondition claims *x == old!(*x) but the body changes *x.
    #[test]
    #[should_panic(expected = "Proof verification")]
    fn test_mut_ref_invalid_ensures_fails() {
        #[proof]
        fn lemma_wrong_ensures(x: &mut i32) {
            assume!(*x >= 0);
            assume!(*x < 1000);
            *x = *x + 1;
            // Wrong: *x changed, so *x != old!(*x)
            trust_vc::ensures!(*x == old!(*x));
        }

        let mut val = 10;
        lemma_wrong_ensures(&mut val);
    }

    #[test]
    fn test_mut_ref_counterexample_uses_source_place_names() {
        let result = common::verify_and_get_result(|| {
            #[proof]
            fn lemma_wrong_nested(counter: &mut OuterCounter) {
                assume!(counter.inner.count >= 0);
                assume!(counter.inner.count < counter.inner.max);
                counter.inner.count = counter.inner.count + 1;
                trust_vc::ensures!(counter.inner.count == old!(counter.inner.count) + 2);
            }

            let mut counter = OuterCounter {
                inner: Counter { count: 1, max: 4 },
                limit: 10,
            };
            lemma_wrong_nested(&mut counter);
        });

        match result {
            VerifyResult::Counterexample {
                model: Some(model), ..
            } => {
                assert!(
                    model.contains("counter.inner.count@1"),
                    "counterexample should show the dotted mut-ref place, got: {model}"
                );
                assert!(
                    !model.contains("__trust_vc_mutref_counter_inner_count_1"),
                    "counterexample should hide the raw mut-ref helper name, got: {model}"
                );
            }
            VerifyResult::Unknown { reason, .. } => {
                assert!(
                    !reason.contains("__trust_vc_mutref_counter_inner_count_1"),
                    "unknown reason should not leak the raw mut-ref helper name, got: {reason}"
                );
            }
            other => panic!("expected Counterexample with model, got {other:?}"),
        }
    }
}
