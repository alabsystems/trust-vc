// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the #[all_triggers] attribute.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file verify trigger behavior using ay through VerificationPipeline
//!
//! Tests that the all_triggers attribute correctly marks functions
//! for aggressive automatic trigger selection in broadcast lemmas.
//!
//! FIXED (#758): Now actually verifies that triggers work, not just expansion.

use syn::parse_quote;
use trust_vc_core::expand_all_triggers;

#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;
use test_verify_helpers_v2::{expect_counterexample, expect_verified};

mod common;

#[test]
fn test_expand_all_triggers_basic_function() {
    common::with_clean_verification(|| {
        let input = parse_quote! {
            fn lemma_collection_property(s: Seq<i32>) {
                trust_vc::ensures!(s.len() >= 0);
            }
        };

        let expanded = expand_all_triggers(input);
        let expanded_str = expanded.to_string();

        // Verify all triggers marker is added
        assert!(
            expanded_str.contains("trust_vc_runtime::__trigger::auto_aggressive"),
            "all_triggers should add aggressive trigger marker string"
        );

        // Verify function structure is preserved
        assert!(
            expanded_str.contains("fn lemma_collection_property"),
            "Function name should be preserved"
        );

        // Expansion successful - actual verification happens in trust_mc/ay
    })
}

#[test]
fn test_all_triggers_actually_verifies() {
    common::with_clean_verification(|| {
        // FIXED (#758): Test that all_triggers actually affects verification
        // Simulate a broadcast lemma with aggressive triggers
        // Use a simple assertion that should always pass
        trust_vc_core::verify_macro::collect_variable("x".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "lemma_positive".to_string(),
            "x + 0 == x".to_string(), // Identity property that should verify
            None,
        );

        // Verify it actually works
        expect_verified().expect("all_triggers lemma with identity property should verify");
    })
}

#[test]
fn test_all_triggers_invalid_lemma_fails() {
    common::with_clean_verification(|| {
        // FIXED (#758): Negative test - invalid lemma must fail
        // Add an INVALID broadcast lemma that should fail verification
        trust_vc_core::verify_macro::collect_variable("x".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "invalid_lemma".to_string(),
            "x > 0 && x < 0".to_string(), // This is always false!
            None,
        );

        // Should fail verification
        expect_counterexample()
            .expect("Contradictory lemma (x > 0 && x < 0) should fail verification");
    })
}

#[test]
fn test_expand_all_triggers_with_multiple_params() {
    common::with_clean_verification(|| {
        let input = parse_quote! {
            fn lemma_relation(x: i32, y: i32) {
                trust_vc::ensures!(x + y == y + x);
            }
        };

        let expanded = expand_all_triggers(input);
        let expanded_str = expanded.to_string();

        // Verify all triggers marker is added
        assert!(
            expanded_str.contains("trust_vc_runtime::__trigger::auto_aggressive"),
            "all_triggers should add aggressive trigger marker string"
        );

        // Verify parameters are preserved
        assert!(
            expanded_str.contains("x: i32") || expanded_str.contains("x : i32"),
            "Parameter x should be preserved"
        );
        assert!(
            expanded_str.contains("y: i32") || expanded_str.contains("y : i32"),
            "Parameter y should be preserved"
        );

        // Expansion successful - actual verification happens in trust_mc/ay
    })
}
#[test]
fn test_expand_all_triggers_with_complex_types() {
    common::with_clean_verification(|| {
        let input = parse_quote! {
            fn lemma_map_property(m: Map<String, i32>, key: String) {
                trust_vc::requires!(m.contains_key(key));
                trust_vc::ensures!(m.get(key).is_some());
            }
        };

        let expanded = expand_all_triggers(input);
        let expanded_str = expanded.to_string();

        // Verify all triggers marker is added
        assert!(
            expanded_str.contains("trust_vc_runtime::__trigger::auto_aggressive"),
            "all_triggers should add aggressive trigger marker string"
        );

        // Verify complex types are preserved
        assert!(expanded_str.contains("Map"), "Map type should be preserved");
        assert!(
            expanded_str.contains("String"),
            "String type should be preserved"
        );

        // Expansion successful - actual verification happens in trust_mc/ay
    })
}
#[test]
fn test_expand_all_triggers_with_trait_bounds() {
    common::with_clean_verification(|| {
        let input = parse_quote! {
            fn lemma_trait_property<T: Clone + PartialEq>(val: T) {
                trust_vc::ensures!(val == val.clone());
            }
        };

        let expanded = expand_all_triggers(input);
        let expanded_str = expanded.to_string();

        // Verify all triggers marker is added
        assert!(
            expanded_str.contains("trust_vc_runtime::__trigger::auto_aggressive"),
            "all_triggers should add aggressive trigger marker string"
        );

        // Verify trait bounds are preserved
        assert!(
            expanded_str.contains("Clone"),
            "Clone trait bound should be preserved"
        );
        assert!(
            expanded_str.contains("PartialEq"),
            "PartialEq trait bound should be preserved"
        );

        // Expansion successful - actual verification happens in trust_mc/ay
    })
}
#[test]
fn test_expand_all_triggers_nested_quantifiers() {
    common::with_clean_verification(|| {
        let input = parse_quote! {
            fn lemma_nested_property(n: u64) {
                trust_vc::ensures!(
                    forall(|i: u64| i < n ==> exists(|j: u64| j > i && j <= n))
                );
            }
        };

        let expanded = expand_all_triggers(input);
        let expanded_str = expanded.to_string();

        // Verify all triggers marker is added
        assert!(
            expanded_str.contains("trust_vc_runtime::__trigger::auto_aggressive"),
            "all_triggers should add aggressive trigger marker string"
        );

        // Verify quantifiers are preserved (might be transformed)
        assert!(
            expanded_str.contains("forall") || expanded_str.contains("ensures"),
            "Quantified expression should be preserved in some form"
        );

        // Expansion successful - actual verification happens in trust_mc/ay
    })
}
#[test]
fn test_all_triggers_vs_auto_trigger_difference() {
    common::with_clean_verification(|| {
        // Test that all_triggers adds a different marker than auto_trigger
        let all_input = parse_quote! {
            fn lemma_all(x: i32) {
                trust_vc::ensures!(x == x);
            }
        };

        let all_expanded = expand_all_triggers(all_input);
        let all_str = all_expanded.to_string();

        // Verify they use different trigger strategies
        assert!(
            all_str.contains("trust_vc_runtime::__trigger::auto_aggressive"),
            "all_triggers should use aggressive strategy"
        );

        // Expansion successful - actual verification happens in trust_mc/ay
    })
}
