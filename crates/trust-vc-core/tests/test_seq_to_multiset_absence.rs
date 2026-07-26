//! Regression for Seq-derived Multiset absent-element projection behavior.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

use trust_vc_core::vc::{ProofObligation, VerificationContext};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

fn verify_context(context: VerificationContext) -> VerifyResult {
    common::with_clean_verification(|| {
        let mut pipeline = VerificationPipeline::new();
        pipeline.replace_context(context);
        pipeline.verify()
    })
}

#[test]
fn test_seq_to_multiset_rejects_element_proved_absent() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "s",
        trust_vc_core::ir::TrustVcType::parse_or_opaque("Seq<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("absent", "!s.contains(9)"));
    ctx.push_obligation(ProofObligation::assert(
        "to_multiset_contains_absent",
        "s.to_multiset().contains(9)",
    ));

    let result = verify_context(ctx);
    match result {
        VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. } => {}
        VerifyResult::Verified => {
            panic!("s.to_multiset() must not contain an element proved absent from the source");
        }
        VerifyResult::Error { message } => {
            // Under native-seq, ToMultiset is not yet supported and produces an
            // encoder error. This is the expected fail-closed behavior (#2680).
            if cfg!(feature = "native-seq") && message.contains("not yet supported with native-seq")
            {
                return;
            }
            panic!(
                "s.to_multiset() absent-element regression should fail closed without encoder errors, got: {message}"
            );
        }
        other => {
            panic!("unexpected verification result for absent-element regression: {other:?}");
        }
    }
}
