//! Vacuous-truth precheck for contradictory assumptions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::encoder::diagnostics::EncodingDiagnostics;
use crate::encoder::types::VerifyResult;
use crate::encoder::AYEncoder;
use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};
use crate::verification_report;

use super::unknown_category::UnknownCategory;
use super::VerificationSlices;

type VacuousCheckOutput = (
    Result<ay_dpll::api::SolveDetails, ay_dpll::api::SolverError>,
    EncodingDiagnostics,
    usize,
    Vec<String>,
);

fn obligation_uses_int_mode(obligation: &PreparedObligation) -> bool {
    obligation
        .solver_mode
        .is_some_and(|mode| mode == crate::vc::SolverMode::NonlinearArith)
        || matches!(
            obligation.kind,
            crate::vc::ObligationKind::MeasureNonNegative
                | crate::vc::ObligationKind::MeasureDecreases
        )
}

fn run_vacuous_precheck(
    ctx: &PreparedVerificationContext,
    assumptions: &[&PreparedObligation],
    broadcast_assumptions: &[&PreparedObligation],
    use_int_for_measures: bool,
) -> Result<VacuousCheckOutput, crate::error::TrustVcError> {
    let slices = VerificationSlices::new(ctx, assumptions, broadcast_assumptions, &[], &[], &[]);
    let mut sat_encoder = AYEncoder::setup_from_prepared(&slices, use_int_for_measures, None)?;
    let details = super::solve::try_check_sat_with_details(&mut sat_encoder.solver);
    let term_bytes = sat_encoder.solver.instance_term_bytes();
    let used_assumptions = match &details {
        Ok(details) if details.result.result().is_unsat() => {
            #[cfg(feature = "named-assertions")]
            {
                match sat_encoder.solver.try_get_unsat_core() {
                    Ok(core) => sat_encoder.state.used_assumptions_from_core(&core),
                    Err(error) => {
                        tracing::debug!(
                            error = ?error,
                            "failed to extract UNSAT core for vacuous truth precheck"
                        );
                        Vec::new()
                    }
                }
            }
            #[cfg(not(feature = "named-assertions"))]
            {
                Vec::new()
            }
        }
        _ => Vec::new(),
    };
    Ok((
        details,
        sat_encoder.state.diagnostics.clone(),
        term_bytes,
        used_assumptions,
    ))
}

pub(super) fn demoted_context_result(
    target: &str,
    diagnostics: &EncodingDiagnostics,
) -> VerifyResult {
    VerifyResult::unknown(
        diagnostics.demotion_reason(target),
        Some(UnknownCategory::EncodingDemotion),
    )
}

/// Returns a terminal verification result when contradictory assumptions make
/// the context vacuous; otherwise `None` so the normal assertion path proceeds.
pub(super) fn check_vacuous_truth(
    ctx: &PreparedVerificationContext,
    assumptions: &[&PreparedObligation],
    broadcast_assumptions: &[&PreparedObligation],
    vacuous_precheck_diagnostics: &mut EncodingDiagnostics,
) -> Option<VerifyResult> {
    // If assumptions are contradictory, every assertion is trivially proved
    // (solver returns Unsat for any negated assertion under impossible
    // assumptions). One extra solver call catches the false positive up front.
    //
    // Wrapped in catch_unwind because assumption encoding can trigger ay-dpll
    // sort mismatches (for example quantified Seq expressions). The normal
    // assertion path catches these via verify_single_assertion_typed; the
    // precheck should skip rather than rewrap them here.
    if assumptions.is_empty() && broadcast_assumptions.is_empty() {
        return None;
    }

    let run_int_mode = ctx.obligations.iter().any(obligation_uses_int_mode);

    for use_int_for_measures in [false, true] {
        if use_int_for_measures && !run_int_mode {
            continue;
        }

        let vacuous_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            run_vacuous_precheck(
                ctx,
                assumptions,
                broadcast_assumptions,
                use_int_for_measures,
            )
        }));

        if let Ok(Ok((details_result, diagnostics, term_bytes, used_assumptions))) = vacuous_result
        {
            vacuous_precheck_diagnostics.merge(&diagnostics);
            if let Ok(details) = details_result {
                tracing::debug!(
                    result = ?details.result.result(),
                    verification_level = %details.verification_level,
                    unknown_reason = ?details.unknown_reason,
                    model_validated = details.verification.sat_model_validated,
                    conflicts = details.statistics.conflicts,
                    decisions = details.statistics.decisions,
                    propagations = details.statistics.propagations,
                    restarts = details.statistics.restarts,
                    learned_clauses = details.statistics.learned_clauses,
                    deleted_clauses = details.statistics.deleted_clauses,
                    theory_conflicts = details.statistics.theory_conflicts,
                    theory_propagations = details.statistics.theory_propagations,
                    num_vars = details.statistics.num_vars,
                    num_clauses = details.statistics.num_clauses,
                    num_assertions = details.statistics.num_assertions,
                    term_bytes,
                    use_int_for_measures,
                    "vacuous truth check solver stats"
                );
                verification_report::record_solve_details(&details, Some(term_bytes));
                if details.result.result().is_unsat() {
                    verification_report::record_used_assumptions(&used_assumptions);
                    if vacuous_precheck_diagnostics.has_demoting() {
                        return Some(demoted_context_result(
                            "vacuous truth precheck",
                            vacuous_precheck_diagnostics,
                        ));
                    }
                    return Some(VerifyResult::unknown(
                        "Assumptions are contradictory — all assertions would be vacuously \
                         true. Check requires/assume annotations for conflicting constraints."
                            .to_string(),
                        Some(UnknownCategory::VacuousTruth),
                    ));
                }
            }
        }
    }

    // Sat, Unknown, encoder error, or panic: proceed with normal verification.
    // Panics and setup errors will surface with better context per assertion.
    None
}

#[cfg(test)]
#[path = "vacuous_proof_tests.rs"]
mod proof_tests;
