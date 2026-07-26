// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test to verify assert_by! condition extraction works correctly.
//!
//! Issue #753: assert_by! originally lost condition information.
//! Issue #845: let bindings in proof blocks are now inlined via substitution.

use trust_vc::assert_by;

mod common;

#[test]
fn test_assert_by_preserves_simple_condition() {
    common::with_clean_verification(|| {
        // Simple condition without proof block
        assert_by!(5 > 3);

        // Check what was collected
        let obligations = get_collected_obligations();

        // The condition "5 > 3" should be preserved
        assert!(
            obligations.iter().any(|o| o.condition().contains("5 > 3")),
            "Condition '5 > 3' not found in obligations: {:?}",
            obligations
        );
    })
}

#[test]
fn test_assert_by_with_proof_block_substitutes_let() {
    common::with_clean_verification(|| {
        // assert_by! with proof block and final condition
        // Fix #845: let bindings are now inlined into the final expression
        assert_by! {
            let _proof = 2 + 2;
            _proof == 4
        };

        let obligations = get_collected_obligations();

        for obligation in &obligations {
            println!("Collected obligation: {}", obligation.condition());
        }

        // After fix #845, _proof is substituted: (2 + 2) == 4
        let has_substituted_condition = obligations
            .iter()
            .any(|o| o.condition().contains("(2 + 2) == 4"));

        // The let statement should NOT appear in the condition
        let has_let_statement = obligations
            .iter()
            .any(|o| o.condition().contains("let _proof"));

        assert!(
            has_substituted_condition,
            "Fix #845: let bindings should be inlined into the condition. \
             Expected '(2 + 2) == 4' in obligations: {:?}",
            obligations
                .iter()
                .map(|o| o.condition())
                .collect::<Vec<_>>()
        );
        assert!(
            !has_let_statement,
            "Fix #845: let statements should not leak into conditions"
        );
    })
}

#[test]
fn test_assert_by_complex_block_substitutes_chained_lets() {
    common::with_clean_verification(|| {
        // Complex block with multiple chained let statements
        assert_by! {
            let a = 1;
            let b = 2;
            let c = a + b;
            c == 3
        };

        let obligations = get_collected_obligations();

        println!("Obligations for complex block:");
        for obligation in &obligations {
            println!("  - {}", obligation.condition());
        }

        // After fix #845: c = (a) + (b), a = 1, b = 2
        // Let substitution wraps values in parens: ((1) + (2)) == 3
        let has_substituted = obligations.iter().any(|o| {
            (o.condition().contains("1 + 2") || o.condition().contains("(1) + (2)"))
                && o.condition().contains("== 3")
                && !o.condition().contains("let")
        });

        // No let statements should leak
        let has_let = obligations
            .iter()
            .any(|o| o.condition().contains("let a") || o.condition().contains("let b"));

        assert!(
            has_substituted,
            "Fix #845: chained let bindings should be fully inlined. \
             Expected condition with '1 + 2' and '== 3' (no let), got: {:?}",
            obligations
                .iter()
                .map(|o| o.condition())
                .collect::<Vec<_>>()
        );
        assert!(
            !has_let,
            "Fix #845: let statements should not appear in conditions"
        );
    })
}

// Helper to get collected obligations for inspection
fn get_collected_obligations() -> Vec<trust_vc_core::vc::ProofObligation> {
    // Use the public API instead of accessing private VERIFICATION_CONTEXT
    trust_vc_core::verify_macro::get_context()
        .map(|ctx| ctx.obligations().to_vec())
        .unwrap_or_default()
}
