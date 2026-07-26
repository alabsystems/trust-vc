// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Manifest validation regressions for named-group broadcast imports.

mod common;

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod alpha {
    ::trust_vc_core::inventory::submit! {
        ::trust_vc_core::BroadcastFnGroupDef {
            function: "lemma_shared",
            group: "alpha",
        }
    }
}

mod beta {
    ::trust_vc_core::inventory::submit! {
        ::trust_vc_core::BroadcastFnGroupDef {
            function: "lemma_shared",
            group: "beta",
        }
    }
}

#[test]
fn test_conflicting_broadcast_group_registrations_fail_closed() {
    let result = common::with_clean_verification(|| {
        verify_macro::set_proof_mode(true);
        trust_vc::broadcast_use!(alpha);
        verify_macro::set_proof_mode(false);
        VerificationPipeline::collect_from_macros().verify()
    });

    assert!(
        matches!(result, VerifyResult::Error { ref message } if message.contains("function `lemma_shared` has conflicting broadcast_group registrations: alpha, beta")),
        "conflicting broadcast_group registrations must surface as VerifyResult::Error, got: {result:?}"
    );
}
