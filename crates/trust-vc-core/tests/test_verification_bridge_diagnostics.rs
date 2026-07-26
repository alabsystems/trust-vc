// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Public API regression tests for `VerificationPipeline` diagnostics and
//! clear/reset behavior.

mod common;

use trust_vc_core::ir::TrustVcType;
use trust_vc_core::vc::ProofObligation;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod alpha {
    ::trust_vc_core::inventory::submit! {
        ::trust_vc_core::BroadcastFnGroupDef {
            function: "lemma_shared_diagnostics",
            group: "alpha",
        }
    }
}

mod beta {
    ::trust_vc_core::inventory::submit! {
        ::trust_vc_core::BroadcastFnGroupDef {
            function: "lemma_shared_diagnostics",
            group: "beta",
        }
    }
}

#[test]
fn test_pipeline_diagnostic_display_summarizes_public_state() {
    let mut pipeline = VerificationPipeline::new();
    pipeline
        .context_mut()
        .declare_var_typed("x", TrustVcType::Int { width: 32 });
    pipeline.add_obligation(ProofObligation::assert("check_positive", "x > 0"));
    pipeline.add_obligation(ProofObligation::assume("given_x", "x == 5"));

    let diagnostic = pipeline.diagnose();

    assert_eq!(diagnostic.num_obligations(), 2);
    assert_eq!(diagnostic.num_variables(), 1);
    assert!(diagnostic.has_assertions());
    assert!(diagnostic.has_assumptions());
    assert_eq!(
        diagnostic.to_string(),
        "Pipeline: 2 obligations, 1 variables, assertions=true, assumptions=true"
    );

    pipeline.clear();

    let cleared = pipeline.diagnose();
    assert_eq!(cleared.num_obligations(), 0);
    assert_eq!(cleared.num_variables(), 0);
    assert!(!cleared.has_assertions());
    assert!(!cleared.has_assumptions());
    assert_eq!(
        cleared.to_string(),
        "Pipeline: 0 obligations, 0 variables, assertions=false, assumptions=false"
    );
}

#[test]
fn test_pipeline_clear_discards_collection_error_from_public_api() {
    common::with_clean_verification(|| {
        verify_macro::set_proof_mode(true);
        trust_vc_core::register_broadcast_use_or_group("alpha");
        verify_macro::set_proof_mode(false);

        let mut pipeline = VerificationPipeline::collect_from_macros();
        let result_before_clear = pipeline.verify();
        assert!(
            matches!(result_before_clear, VerifyResult::Error { ref message }
                if message.contains(
                    "function `lemma_shared_diagnostics` has conflicting broadcast_group registrations: alpha, beta"
                )),
            "conflicting named-group manifest entries must surface as collection errors, got: {result_before_clear:?}"
        );

        pipeline.clear();

        let diagnostic = pipeline.diagnose();
        assert_eq!(diagnostic.num_obligations(), 0);
        assert_eq!(diagnostic.num_variables(), 0);
        assert!(!diagnostic.has_assertions());
        assert!(!diagnostic.has_assumptions());

        let result_after_clear = pipeline.verify();
        assert!(
            matches!(result_after_clear, VerifyResult::Error { ref message }
                if message.contains("empty context")),
            "clear() must discard the prior collection error so verify() falls back to the empty-context error, got: {result_after_clear:?}"
        );
    });
}
