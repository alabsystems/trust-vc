//! Typed verification validation-boundary regressions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::encoder::types::VerifyResult;
use crate::encoder::AYEncoder;
use crate::ir::TrustVcType;
use crate::prepared_context::prepare_context;
use crate::vc::{ProofObligation, VerificationContext};

#[test]
fn test_verify_typed_reports_all_opaque_variables_in_unknown_reason() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Opaque("Vec<i32>".to_string()));
    ctx.declare_var_typed("y", TrustVcType::Opaque("Widget".to_string()));
    ctx.push_obligation(ProofObligation::assert("trivial_assert", "true"));

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
    let result = AYEncoder::verify_typed(&prepared);

    match result {
        VerifyResult::Unknown { reason, .. } => {
            assert!(
                reason.contains("'x' (type: Vec<i32>)"),
                "unknown reason should include the first opaque variable: {reason}"
            );
            assert!(
                reason.contains("'y' (type: Widget)"),
                "unknown reason should include the second opaque variable: {reason}"
            );
        }
        other => panic!("expected Unknown for opaque variables, got: {other:?}"),
    }
}
