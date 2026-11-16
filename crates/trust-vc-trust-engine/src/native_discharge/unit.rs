// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! One obligation, one verification unit, one verdict.
//!
//! # One assertion per unit
//!
//! A unit carries the body relation and the function's `requires` as
//! ASSUMPTIONS, and exactly ONE assertion: the obligation being decided. That is
//! not a simplification, it is what makes attribution honest. `verify_with_report`
//! answers for the whole context, and a certificate binds to the solver query it
//! refuted; with two assertions in one unit, a counterexample for the other one
//! would be reported against this obligation. Everything that would add a second
//! assertion — a body `Inst::Assert`, a call-site precondition — declines in the
//! body lane instead.
//!
//! # Machine width, and what a verified `ensures` does NOT claim
//!
//! CORRECTED after adversarial review. The paragraph that stood here argued that
//! deciding a clause's `+` at the machine width was honest because the
//! no-overflow claim is a separate arithmetic-safety row. It is not: a
//! `wrapping_add` body lowers to the same plain `BinOp` this lane accepts (a
//! CHECKED add lowers to `Inst::Overflow`, which the body lane declines), so for
//! a wrapping body no panic-freedom row can ever fail and a mathematically FALSE
//! `ensures result == x + 1` was certified at `x = u32::MAX`. The clause means
//! mathematical arithmetic — the parser types every leaf `Sort::Int` and the
//! fleet lowers `Formula::Add` to ay's `int_add` — so a mathematical arithmetic
//! node over machine operands now DECLINES in the formula decoder, and no clause
//! reaches this unit at a width.
//!
//! What remains at a width is the BODY relation, where machine arithmetic is
//! EXACT rather than approximate: a plain `BinOp` denotes the wrapping machine
//! operation. The unit is verified under exec arithmetic
//! (`TrustVerificationUnit::with_exec_arithmetic`), which makes division and
//! shift partiality checked failures; it does NOT make overflow one, since
//! MEASURED `obligation_carries_spec_arithmetic` disables overflow checking for
//! `Ensures` obligations. Every outcome over fixed-width body arithmetic carries
//! a `MachineArithmetic` premise naming the operation, and that premise is
//! disclosure of the width decision, not a claim that the operation cannot
//! overflow.

use super::body::BodyRelation;
use super::Decline;
use crate::{
    TrustExpr, TrustObligation, TrustObligationKind, TrustOutcome, TrustProofPolicy, TrustVariable,
    TrustVcNativeTrustIrDischargeStatus, TrustVcTrustEngine, TrustVerificationMode,
    TrustVerificationRequest, TrustVerificationUnit, TrustVerifier,
};

/// What one unit produced.
pub(crate) struct UnitOutcome {
    pub(crate) status: TrustVcNativeTrustIrDischargeStatus,
    pub(crate) message: String,
    /// The kernel-checked Alethe proof, when the engine produced one.
    pub(crate) proof: Option<ProducedProof>,
}

/// A proof artifact this run produced.
pub(crate) struct ProducedProof {
    pub(crate) alethe: String,
    pub(crate) kernel_verified: bool,
    pub(crate) strict_verified: bool,
    pub(crate) cast_observation:
        Option<Result<crate::native_scalar_cast::UnitCastObservation, String>>,
}

/// The unit id (and its single assertion's id) for one obligation.
pub(crate) fn assertion_id(unit_id: &str) -> String {
    format!("{unit_id}#assert")
}

/// Assemble and run the unit for one obligation.
pub(crate) fn decide(
    unit_id: &str,
    relation: &BodyRelation,
    assumptions: &[(String, TrustExpr)],
    assertion: TrustExpr,
    observe_casts: bool,
) -> Result<UnitOutcome, Decline> {
    let mut unit = TrustVerificationUnit::new(unit_id).with_exec_arithmetic();
    for (name, sort) in &relation.variables {
        unit = unit.with_variable(TrustVariable::new(name.clone(), sort.clone()));
    }
    for (id, predicate) in assumptions {
        unit = unit.with_obligation(TrustObligation::assume_typed(
            id.clone(),
            // A body fact is DERIVED from the program, not an axiom taken on
            // faith; the kind says so rather than borrowing `Axiom`.
            TrustObligationKind::Other("body_relation".to_string()),
            predicate.clone(),
        ));
    }
    let assertion_id = assertion_id(unit_id);
    unit = unit.with_obligation(TrustObligation::ensures_typed(
        assertion_id.clone(),
        assertion,
    ));

    let request = TrustVerificationRequest::new(unit_id)
        .with_units(vec![unit])
        .for_full_verification()
        .with_proof_policy(proof_policy());

    let engine = TrustVcTrustEngine::new();
    let mut cast_observation = None;
    let verification = if observe_casts {
        engine
            .verify_with_scalar_cast_capture(&request)
            .map(|observed| {
                let (report, mut captures) = observed.into_parts();
                cast_observation = Some(match captures.pop() {
                    Some(Ok(encoding)) if captures.is_empty() => {
                        crate::native_scalar_cast::bounded_json(&request).map(|_| {
                            crate::native_scalar_cast::UnitCastObservation {
                                request: request.clone(),
                                encoding,
                            }
                        })
                    }
                    Some(Err(reason)) => Err(reason),
                    _ => Err("cast capture did not match the one native unit".into()),
                });
                report
            })
    } else {
        TrustVerifier::verify(&engine, &request)
    };
    let report = match verification {
        Ok(report) => report,
        // The engine refuses rather than answers: a unit it cannot lower, or a
        // proof policy it cannot satisfy. Either way nothing was proved, and
        // the reason is the engine's own.
        Err(error) => {
            return Ok(UnitOutcome {
                status: TrustVcNativeTrustIrDischargeStatus::Unknown {
                    reason: error.to_string(),
                    category: "EngineRefusal".to_string(),
                },
                message: format!("trust-vc's engine did not answer: {error}"),
                proof: None,
            })
        }
    };

    let Some(unit_report) = report.units().first() else {
        return Err(Decline::new(
            "trust-vc's engine returned no unit report for a request with one unit",
        ));
    };

    let proof = unit_report
        .proof_artifacts()
        .iter()
        // The certificate must be the refutation of THIS assertion's own
        // negated goal. The engine already enforces that before attaching, so a
        // mismatch here means the two layers disagree — take none rather than
        // the first.
        .find(|artifact| {
            artifact
                .assertion_obligation_ids()
                .iter()
                .any(|id| id == &assertion_id)
        })
        .map(|artifact| ProducedProof {
            alethe: artifact.payload().to_string(),
            kernel_verified: artifact.kernel_verified(),
            strict_verified: artifact.strict_verified(),
            cast_observation: cast_observation.take(),
        });

    Ok(match unit_report.outcome() {
        TrustOutcome::Verified => UnitOutcome {
            status: TrustVcNativeTrustIrDischargeStatus::Verified,
            message: format!("discharged by trust-vc/ay as `{unit_id}`"),
            proof,
        },
        TrustOutcome::Refuted {
            obligation_id,
            bindings,
            ..
        } if obligation_id == &assertion_id => UnitOutcome {
            status: TrustVcNativeTrustIrDischargeStatus::Counterexample {
                bindings: bindings.clone(),
            },
            message: format!("refuted by trust-vc/ay with a model for `{unit_id}`"),
            proof: None,
        },
        // A refutation whose label is NOT this unit's assertion is a model-less
        // non-proof for this obligation: the engine folds `NotProved` into
        // `Refuted` with a synthesized label, and attributing someone else's
        // counterexample to this row would be a false accusation.
        TrustOutcome::Refuted { obligation_id, .. } => UnitOutcome {
            status: TrustVcNativeTrustIrDischargeStatus::NotProved,
            message: format!("not proved ({obligation_id})"),
            proof: None,
        },
        TrustOutcome::Unknown { reason, category } => UnitOutcome {
            status: TrustVcNativeTrustIrDischargeStatus::Unknown {
                reason: reason.clone(),
                category: category.clone(),
            },
            message: format!("trust-vc/ay could neither prove nor refute `{unit_id}`: {reason}"),
            proof: None,
        },
        TrustOutcome::Error { message } => UnitOutcome {
            status: TrustVcNativeTrustIrDischargeStatus::Unknown {
                reason: message.clone(),
                category: "EngineError".to_string(),
            },
            message: format!("trust-vc's engine errored on `{unit_id}`: {message}"),
            proof: None,
        },
        // `TrustOutcome` is `#[non_exhaustive]`, so this arm is unreachable in
        // THIS crate and required for any consumer compiled against a newer
        // one. An outcome this build does not know is not a proof.
        #[allow(unreachable_patterns)]
        other => UnitOutcome {
            status: TrustVcNativeTrustIrDischargeStatus::Unknown {
                reason: format!("unrecognized engine outcome: {other:?}"),
                category: "UnrecognizedOutcome".to_string(),
            },
            message: "trust-vc's engine returned an outcome this build does not model".to_string(),
            proof: None,
        },
    })
}

/// The proof policy the discharge lane runs under.
///
/// With `proof-certificates` the bar is RELEASE ADMISSIBILITY: a proven unit
/// that cannot produce a kernel-checked, strictly-accepted artifact is refused
/// by the engine and surfaces here as `Unknown`, never as a discharge. That is
/// also what keeps an ay certification-funnel refusal — a computed UNSAT the
/// solver declines to publish — out of the `Discharged` verdict.
///
/// Without the feature there is no artifact to require, so the lane reports the
/// solver's verdict and produces no certificate. A consumer that needs a
/// certificate sees an empty `produced_certificates`, which is the honest
/// signal; it must not read the verdict alone as certified.
const fn proof_policy() -> TrustProofPolicy {
    #[cfg(feature = "proof-certificates")]
    {
        TrustProofPolicy::RequireReleaseAdmissibleCertificate
    }
    #[cfg(not(feature = "proof-certificates"))]
    {
        TrustProofPolicy::EvidenceOnly
    }
}

/// Full verification is the only mode this lane uses: every obligation it
/// carries is a typed expression, never a source string.
const _: TrustVerificationMode = TrustVerificationMode::Full;
