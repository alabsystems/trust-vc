// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![deny(unused_must_use)]

use trust_vc_core::ir::TrustVcType;
use trust_vc_core::mode::FunctionMode;
use trust_vc_core::vc::FunctionContext;
use trust_vc_core::vc::{ProofObligation, VerificationContext};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify::{Proof, Verifier};
use trust_vc_core::VerificationReportOptions;

fn main() {
    Proof::new("proof");
    Verifier::verify(&Proof::new("proof").with_assertion("true"));

    VerificationContext::new();
    VerificationContext::new().with_overflow_checks();

    ProofObligation::assert("assertion", "true");
    ProofObligation::assert("assertion", "true").with_location("file.rs:1:1");

    VerificationPipeline::new();
    VerificationPipeline::new().diagnose();

    let report = VerificationContext::new().verify_with_report(VerificationReportOptions::new());
    report.result();
    report.steps();

    FunctionContext::new("lemma", vec![], TrustVcType::Bool, FunctionMode::Spec);
    FunctionContext::new("lemma", vec![], TrustVcType::Bool, FunctionMode::Spec)
        .with_recursive(true);
}
