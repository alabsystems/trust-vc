//! Result mapping: tla_check::CheckResult → trust_vc VerifyResult.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::{UnknownCategory, VerifyResult};
use tla_check::CheckResult;

/// Convert a ty model checking result to a trust_vc verification result.
///
/// Maps all 7 known `CheckResult` variants plus a wildcard for future
/// variants (`CheckResult` is `#[non_exhaustive]`).
pub(crate) fn check_result_to_verify_result(result: CheckResult) -> VerifyResult {
    match result {
        CheckResult::Success(_stats) => VerifyResult::Verified,
        CheckResult::InvariantViolation {
            invariant, trace, ..
        } => VerifyResult::Counterexample {
            obligation_name: invariant,
            model: Some(format!("{} state(s) in trace", trace.states.len())),
            bindings: Vec::new(),
        },
        CheckResult::PropertyViolation {
            property, trace, ..
        } => VerifyResult::Counterexample {
            obligation_name: property,
            model: Some(format!("{} state(s) in trace", trace.states.len())),
            bindings: Vec::new(),
        },
        CheckResult::LivenessViolation {
            property,
            prefix,
            cycle,
            ..
        } => VerifyResult::Counterexample {
            obligation_name: property,
            model: Some(format!(
                "liveness: {} prefix state(s), {} cycle state(s)",
                prefix.states.len(),
                cycle.states.len()
            )),
            bindings: Vec::new(),
        },
        CheckResult::Deadlock { trace, .. } => VerifyResult::Counterexample {
            obligation_name: "deadlock_freedom".into(),
            model: Some(format!("{} state(s) in trace", trace.states.len())),
            bindings: Vec::new(),
        },
        CheckResult::Error { error, .. } => VerifyResult::Error {
            message: format!("ty check error: {error}"),
        },
        CheckResult::LimitReached { limit_type, .. } => VerifyResult::unknown(
            format!("ty state space limit: {limit_type:?}"),
            Some(UnknownCategory::SolverUnknown),
        ),
        _ => VerifyResult::unknown(
            "ty returned unrecognized CheckResult variant",
            Some(UnknownCategory::Other),
        ),
    }
}
