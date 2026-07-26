// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Semantic verification coverage for extern_spec call-site bindings.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline.

trust_vc::extern_spec! {
    impl u32 {
        #[ensures(result <= 32)]
        fn count_ones(self) -> u32;

        #[requires(shift == 0)]
        #[ensures(result == self)]
        fn rotate_left(self, shift: u32) -> u32;
    }
}

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

#[test]
fn test_verify_extern_call_rewrites_receiver_and_argument_placeholders() {
    common::with_clean_verification(|| {
        let zero_amount = 0_u32;
        let _ =
            trust_vc_core::verify_extern_call!("u32::rotate_left", 5_u32.rotate_left(zero_amount));

        let pipeline = VerificationPipeline::collect_from_macros();
        let requires = pipeline
            .context()
            .obligations()
            .iter()
            .find(|obligation| obligation.name().contains("u32::rotate_left_requires"))
            .expect("rotate_left requires obligation should be imported");
        assert_eq!(requires.kind(), ObligationKind::Assert);
        assert!(
            requires.condition().contains("zero_amount"),
            "argument placeholder should rewrite to the call-site local, got: {}",
            requires.condition()
        );
        assert!(
            !requires.condition().contains("shift == 0"),
            "raw parameter name should not survive substitution, got: {}",
            requires.condition()
        );

        let ensures = pipeline
            .context()
            .obligations()
            .iter()
            .find(|obligation| obligation.name().contains("u32::rotate_left_ensures"))
            .expect("rotate_left ensures obligation should be imported");
        assert_eq!(ensures.kind(), ObligationKind::Assume);
        assert!(
            ensures.condition().contains("5_u32"),
            "receiver placeholder should rewrite to the concrete call-site receiver, got: {}",
            ensures.condition()
        );
        assert!(
            !ensures.condition().contains("result == self"),
            "raw receiver/result placeholders should not survive substitution, got: {}",
            ensures.condition()
        );
    })
}

#[test]
fn test_register_extern_spec_from_manifest_scope_for_call_proves_count_ones_bound() {
    common::with_clean_verification(|| {
        trust_vc_core::register_extern_spec_from_manifest_scope_for_call(
            file!(),
            env!("CARGO_MANIFEST_DIR"),
            "u32::count_ones",
            "input.count_ones()",
            Some("count"),
        )
        .expect("count_ones extern spec should register with call bindings");

        let mut pipeline = VerificationPipeline::collect_from_macros();
        pipeline.context_mut().declare_var_parsed("count", "u32");
        pipeline
            .context_mut()
            .push_assert("count_bound", "count <= 32");

        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "count_ones ensures(result <= 32) should prove the call-result bound, got: {result:?}"
        );
    })
}

#[test]
fn test_register_extern_spec_from_manifest_scope_for_call_proves_rotate_left_identity() {
    common::with_clean_verification(|| {
        trust_vc_core::register_extern_spec_from_manifest_scope_for_call(
            file!(),
            env!("CARGO_MANIFEST_DIR"),
            "u32::rotate_left",
            "input.rotate_left(zero_amount)",
            Some("rotated"),
        )
        .expect("rotate_left extern spec should register with call bindings");

        let mut pipeline = VerificationPipeline::collect_from_macros();
        pipeline.context_mut().declare_var_parsed("input", "u32");
        pipeline
            .context_mut()
            .declare_var_parsed("zero_amount", "u32");
        pipeline.context_mut().declare_var_parsed("rotated", "u32");
        pipeline
            .context_mut()
            .push_assume("zero_shift", "zero_amount == 0");
        pipeline
            .context_mut()
            .push_assert("rotation_identity", "rotated == input");

        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "rotate_left ensures(result == self) with shift == 0 should prove identity, got: {result:?}"
        );
    })
}
