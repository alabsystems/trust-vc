// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Extern spec coverage for u32 bit-manipulation methods.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests exercise the extern_spec bridge import path for bit-method contracts.
//! Per design (#2450), tests inspect imported obligations — they do NOT
//! prove downstream semantic properties (that requires #2451).

trust_vc::extern_spec! {
    impl u32 {
        #[ensures(result <= 32)]
        fn count_ones(self) -> u32;

        #[ensures(result <= 32)]
        fn leading_zeros(self) -> u32;

        #[ensures(result <= 32)]
        fn trailing_zeros(self) -> u32;
    }
}

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;

#[test]
fn test_count_ones_imports_ensures_as_assume() {
    common::with_clean_verification(|| {
        let _ = trust_vc_core::verify_extern_call!("u32::count_ones", 5_u32.count_ones());

        let pipeline = VerificationPipeline::collect_from_macros();
        let obligations = pipeline.context().obligations();

        let ensures = obligations
            .iter()
            .find(|o| o.name().contains("count_ones") && o.name().contains("ensures"))
            .expect("should import an ensures obligation for u32::count_ones");

        assert_eq!(
            ensures.kind(),
            ObligationKind::Assume,
            "ensures should be imported as Assume (caller trusts postcondition)"
        );
        // The macro rewrites `result` to a generated variable name, but the
        // bound `<= 32` is preserved from the original contract text.
        assert!(
            ensures.condition().contains("<= 32"),
            "ensures condition should contain the '<= 32' bound, got: {}",
            ensures.condition()
        );
    })
}

#[test]
fn test_leading_zeros_imports_ensures_as_assume() {
    common::with_clean_verification(|| {
        let _ = trust_vc_core::verify_extern_call!("u32::leading_zeros", 0_u32.leading_zeros());

        let pipeline = VerificationPipeline::collect_from_macros();
        let obligations = pipeline.context().obligations();

        let ensures = obligations
            .iter()
            .find(|o| o.name().contains("leading_zeros") && o.name().contains("ensures"))
            .expect("should import an ensures obligation for u32::leading_zeros");

        assert_eq!(ensures.kind(), ObligationKind::Assume);
        assert!(
            ensures.condition().contains("<= 32"),
            "ensures condition should contain the '<= 32' bound, got: {}",
            ensures.condition()
        );
    })
}

#[test]
fn test_trailing_zeros_imports_ensures_as_assume() {
    common::with_clean_verification(|| {
        let _ = trust_vc_core::verify_extern_call!("u32::trailing_zeros", 0_u32.trailing_zeros());

        let pipeline = VerificationPipeline::collect_from_macros();
        let obligations = pipeline.context().obligations();

        let ensures = obligations
            .iter()
            .find(|o| o.name().contains("trailing_zeros") && o.name().contains("ensures"))
            .expect("should import an ensures obligation for u32::trailing_zeros");

        assert_eq!(ensures.kind(), ObligationKind::Assume);
        assert!(
            ensures.condition().contains("<= 32"),
            "ensures condition should contain the '<= 32' bound, got: {}",
            ensures.condition()
        );
    })
}

#[test]
fn test_plain_call_without_verify_extern_call_imports_no_obligations() {
    common::with_clean_verification(|| {
        // Plain call without verify_extern_call! should NOT import obligations
        let _ = 5_u32.count_ones();

        let pipeline = VerificationPipeline::collect_from_macros();
        let obligations = pipeline.context().obligations();

        assert!(
            obligations.is_empty(),
            "plain call without verify_extern_call! should not import obligations, got: {:?}",
            obligations.iter().map(|o| o.name()).collect::<Vec<_>>()
        );
    })
}

#[test]
fn test_verify_extern_call_fails_loudly_on_lexical_path_mismatch() {
    common::with_clean_verification(|| {
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = trust_vc_core::verify_extern_call!(
                "core::primitive::u32::count_ones",
                5_u32.count_ones()
            );
        }))
        .expect_err("lexical mismatch should panic instead of silently dropping contracts");

        let message = if let Some(message) = panic.downcast_ref::<String>() {
            message.clone()
        } else if let Some(message) = panic.downcast_ref::<&str>() {
            message.to_string()
        } else {
            "unknown panic".to_string()
        };

        assert!(
            message.contains("current package rooted at"),
            "panic should explain the searched package boundary, got: {message}"
        );
        assert!(
            message.contains("dependency crates are not searched"),
            "panic should explain the unsupported dependency-crate boundary, got: {message}"
        );
    })
}
