// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression tests for qualified-path recursive calls in `#[decreases]`.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline.

use trust_vc::decreases;
use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;

mod common;

#[decreases(n)]
fn countdown_self(n: u64) -> u64 {
    if n == 0 {
        0
    } else {
        self::countdown_self(n - 1)
    }
}

#[decreases(n, mutual_with(odd_q))]
fn even_q(n: u64) -> bool {
    if n == 0 {
        true
    } else {
        self::odd_q(n - 1)
    }
}

#[decreases(n, mutual_with(even_q))]
fn odd_q(n: u64) -> bool {
    if n == 0 {
        false
    } else {
        self::even_q(n - 1)
    }
}

fn collect_decrease_obligations() -> Vec<String> {
    VerificationPipeline::collect_from_macros()
        .context()
        .obligations()
        .iter()
        .filter(|o| o.kind() == ObligationKind::MeasureDecreases)
        .map(|o| o.name().to_string())
        .collect()
}

#[test]
fn test_self_qualified_self_recursion_collects_decrease_obligations() {
    common::with_clean_verification(|| {
        let _ = countdown_self(3);

        let obligations = collect_decrease_obligations();
        assert!(
            !obligations.is_empty(),
            "self-qualified self recursion should collect MeasureDecreases obligations, got: {:?}",
            obligations
        );
    });
}

#[test]
fn test_self_qualified_mutual_recursion_collects_decrease_obligations() {
    common::with_clean_verification(|| {
        let _ = even_q(3);

        let obligations = collect_decrease_obligations();
        assert!(
            !obligations.is_empty(),
            "self-qualified mutual recursion should collect MeasureDecreases obligations, got: {:?}",
            obligations
        );
    });
}
