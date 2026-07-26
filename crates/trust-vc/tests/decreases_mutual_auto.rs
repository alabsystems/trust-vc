// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for automatic mutual recursion detection via SCC analysis (#2054).
//!
//! Unlike `decreases_mutual_basic.rs` which uses explicit `mutual_with(...)`,
//! these tests verify that `#[decreases]` automatically discovers mutual
//! recursion partners through crate-local call graph SCC computation.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline.

use trust_vc::decreases;
use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;

mod common;

// -- Automatic mutual recursion pair: is_even / is_odd --
// No `mutual_with(...)` — SCC analysis should detect the cycle automatically.

#[decreases(n)]
fn is_even_auto(n: u64) -> bool {
    if n == 0 {
        true
    } else {
        is_odd_auto(n - 1)
    }
}

#[decreases(n)]
fn is_odd_auto(n: u64) -> bool {
    if n == 0 {
        false
    } else {
        is_even_auto(n - 1)
    }
}

#[test]
fn test_auto_mutual_recursion_compiles_and_executes() {
    common::with_clean_verification(|| {
        assert!(is_even_auto(0));
        assert!(!is_odd_auto(0));
        assert!(!is_even_auto(1));
        assert!(is_odd_auto(1));
        assert!(is_even_auto(4));
        assert!(is_odd_auto(5));
        assert!(!is_even_auto(7));
        assert!(!is_odd_auto(8));
    })
}

#[test]
fn test_auto_mutual_recursion_collects_decrease_obligations() {
    common::with_clean_verification(|| {
        // Call is_even_auto to trigger obligation collection in test mode.
        // Without SCC analysis, the call to is_odd_auto(n-1) would NOT generate
        // a MeasureDecreases obligation because there's no mutual_with(...).
        let _ = is_even_auto(3);

        let pipeline = VerificationPipeline::collect_from_macros();
        let obligations = pipeline.context().obligations();

        let decrease_obligations: Vec<_> = obligations
            .iter()
            .filter(|o| o.kind() == ObligationKind::MeasureDecreases)
            .collect();

        assert!(
            !decrease_obligations.is_empty(),
            "automatic SCC mutual recursion should generate MeasureDecreases obligations \
             without explicit mutual_with(...), got: {:?}",
            obligations
                .iter()
                .map(|o| (o.name(), o.kind()))
                .collect::<Vec<_>>()
        );
    })
}
