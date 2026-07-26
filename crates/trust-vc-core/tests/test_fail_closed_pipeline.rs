//! Full-pipeline fail-closed regressions for graceful-skip collection paths.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro::{
    collect_obligation, collect_old_value, collect_variable_from_ref,
};
use trust_vc_core::VerifyResult;

#[test]
fn test_collect_variable_from_ref_missing_ref_fails_closed_in_pipeline() {
    common::with_clean_verification(|| {
        collect_variable_from_ref("target_var".to_string(), "source_var".to_string());
        collect_obligation(
            ObligationKind::Assert,
            "uses_missing_target".to_string(),
            "target_var > 0".to_string(),
            None,
        );

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Error { message } => assert!(
                message.contains("target_var"),
                "pipeline should report the unresolved target_var after graceful skip, got: {message}"
            ),
            other => panic!(
                "missing ref type should fail closed through the pipeline, got: {:?}",
                other
            ),
        }
    });
}

#[test]
fn test_collect_old_value_missing_var_fails_closed_in_pipeline() {
    common::with_clean_verification(|| {
        collect_old_value("x".to_string());
        collect_obligation(
            ObligationKind::Assert,
            "uses_missing_old_value".to_string(),
            "__trust_vc_old_x > 0".to_string(),
            None,
        );

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Error { message } => assert!(
                message.contains("__trust_vc_old_x"),
                "pipeline should report the unresolved old snapshot after graceful skip, got: {message}"
            ),
            other => panic!(
                "missing old snapshot should fail closed through the pipeline, got: {:?}",
                other
            ),
        }
    });
}
