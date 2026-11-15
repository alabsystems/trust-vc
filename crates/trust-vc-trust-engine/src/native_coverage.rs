// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Release-grade COVERAGE of an imported native TrustIr certificate, derived
//! by this consumer from evidence it re-checks itself.
//!
//! # The rule
//!
//! Coverage is a verdict the consumer derives, never a row a producer writes.
//! trust-ir-build's [`coverage_establishment_report`] is the authority, called
//! with [`CoverageInputs::default`] — no attestation, no solved bundles, no
//! replayer — so only BASIS K can establish anything: this process replayed
//! exactly the certificate in the Clean kernel against the claim re-derived
//! from its obligation, and the replayed claim is of a family whose
//! quantification is written down (`ContractGroundDecision`, a universally
//! closed claim, is `Unbounded`; every other family is undetermined).
//!
//! A certificate `C` is release-grade for coverage only when ALL of:
//!
//! 1. the bundle already passed `validate_upstream_bundle` and `C` its
//!    identity checks (the caller's side of the rule);
//! 2. the report is checked ([`CoverageEstablishmentReport::is_checked`]);
//! 3. `C`'s OWN verdict ([`CoverageEstablishmentReport::for_certificate`] of
//!    `C.lineage_ref()`) is `Established { bound: Unbounded, basis }` with a
//!    `KernelReplayedClaim` basis naming `C` itself;
//! 4. the report records no refusal ANYWHERE
//!    ([`CoverageEstablishmentReport::refusals`]): a refusal means a producer
//!    stated something false (an in-module `assurance` row claiming more than
//!    its certificate's derived bound, a module without wire identity), and
//!    it is fatal for every certificate of the bundle. An UNDETERMINED
//!    verdict elsewhere does not block `C`;
//! 5. `C`'s obligation states exactly ONE SMT-LIB formula text
//!    ([`formula_text_defect`]): schema `smtlib2`, whose payload IS SMT-LIB
//!    source that trust-ir's own SMT-LIB2 reader reads as one well-sorted
//!    quantifier-free `Bool` term over the clause's own bindings
//!    (`trust_ir::spec_surface::check_linked_invariant`, the reader trust-ir's
//!    spec linker holds a typed carrier to), with no `smtlib` rendering or one
//!    equal to the payload byte for byte, and no sort but `Bool`. trust-ir's
//!    contract grounder reads `ProofFormula::smtlib_text` through the same
//!    SMT-LIB2 reader (the schema, rendering, source and sort clauses, a
//!    clause name that is a theory symbol and a lone `and` / `or`), and its
//!    bundle validator refuses a bundle that breaks them before this rule
//!    runs. This consumer keeps no byte rules of its own: what counts as
//!    SMT-LIB source is trust-ir's reader's answer, and it checks every
//!    clause itself rather than trusting upstream to: a certificate of any
//!    other obligation is UNDETERMINED, never admitted.
//!
//! Basis R (a verified solver result cited by a sealed attestation) is per
//! OBLIGATION and vouches for no certificate, so it never admits one: this
//! module never supplies an attestation, and a certificate verdict cannot
//! carry a solver result (`CoverageBasis` has no such variant). The in-module
//! `ProofCertificate::assurance` row is never read as coverage here.

use std::collections::BTreeMap;

use serde::Serialize;
use trust_ir::proof::{
    ClauseSort, CoverageBound, KernelClaimFamily, ProofCertificateRef, ProofFormula,
};
use trust_ir::request::NativeVerificationBundle;
use trust_ir::spec_surface::{check_linked_invariant, linked_var_env};
use trust_ir::{ProofId, ProofObligation};
use trust_ir_build::{
    coverage_establishment_report, CertificateCoverage, CoverageBasis, CoverageEstablishmentReport,
    CoverageInputs, CoverageUndeterminedReason, ValidationError,
};

use crate::TrustVcNativeTrustIrCertificateRejection;

/// How a certificate's release-grade coverage was ESTABLISHED.
///
/// Serialized into the certificate's release admission and bound into the
/// fingerprint of every proof artifact built from it. Never decoded: a
/// serialized basis is a record of a judgement made against a bundle, not
/// evidence (see [`crate::TrustVcNativeTrustIrCertificateAdmission`]).
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "basis", rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeCoverageBasis {
    /// Basis K: this process replayed exactly this certificate in the Clean
    /// kernel (`NativeVerificationBundle::kernel_replayed_certificates`)
    /// against the claim re-derived from its obligation, and the claim's
    /// family establishes `Unbounded`.
    KernelReplayedClaim {
        /// The certificate's obligation (its `ProofCertificateRef`).
        obligation_id: u32,
        /// The certificate's prover label (its `ProofCertificateRef`).
        prover: String,
        /// The certificate's evidence digest (its `ProofCertificateRef`).
        evidence_digest: String,
        /// The classified family of the replayed claim.
        family: TrustVcNativeKernelClaimFamily,
    },
}

/// The classified family of a kernel-replayed claim (trust-ir's
/// `KernelClaimFamily`), as far as this build classifies it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeKernelClaimFamily {
    /// The contract path: a closed ground decision, or the `∀ x : Nat`
    /// nonnegativity tautology bound to an unsigned IR place — universally
    /// closed, so `Unbounded` relative to the obligation's formula.
    ContractGroundDecision,
}

/// This build's reading of an upstream family, or `None` for one it does not
/// know. trust-ir's enum is `#[non_exhaustive]`: a family added upstream
/// arrives here as `None`, which [`judge_certificate`] refuses to admit.
const fn kernel_claim_family(family: KernelClaimFamily) -> Option<TrustVcNativeKernelClaimFamily> {
    match family {
        KernelClaimFamily::ContractGroundDecision => {
            Some(TrustVcNativeKernelClaimFamily::ContractGroundDecision)
        }
        _ => None,
    }
}

/// One certificate's coverage judgement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CoverageJudgement {
    /// `Some` exactly when coverage is ESTABLISHED as `Unbounded` for this
    /// certificate; then `rejections` is empty.
    pub(crate) basis: Option<TrustVcNativeCoverageBasis>,
    /// Why coverage is not release-grade; never empty when `basis` is `None`.
    pub(crate) rejections: Vec<TrustVcNativeTrustIrCertificateRejection>,
    /// trust-ir-build's own words for a rejection (its refusals, or the
    /// undetermined reason), for a report reader. Never read back.
    pub(crate) detail: Option<String>,
}

impl CoverageJudgement {
    fn rejected(
        rejection: TrustVcNativeTrustIrCertificateRejection,
        detail: impl Into<String>,
    ) -> Self {
        Self {
            basis: None,
            rejections: vec![rejection],
            detail: Some(detail.into()),
        }
    }
}

/// trust-ir-build's coverage establishment over ONE bundle, run once per
/// bundle by [`crate::TrustVcTrustEngine::consume_native_trust_ir_bundle`].
pub(crate) struct CoverageJudge {
    report: CoverageEstablishmentReport,
    /// Rule 5, per obligation id of the module: `None` when the obligation
    /// states exactly one SMT-LIB formula text, else why it does not.
    formula_defects: BTreeMap<ProofId, Option<String>>,
}

impl CoverageJudge {
    /// Derive coverage for `bundle` from basis K alone. The caller has
    /// already refused a module without wire identity; the report refuses
    /// one too (by name, unchecked), so neither path can panic hashing it.
    pub(crate) fn for_bundle(bundle: &NativeVerificationBundle) -> Self {
        Self {
            report: coverage_establishment_report(bundle, CoverageInputs::default()),
            formula_defects: formula_defects(&bundle.module.proof_obligations),
        }
    }

    /// The judgement for the certificate whose lineage reference is
    /// `certificate` (rules 2–5 of the module doc).
    pub(crate) fn judge(&self, certificate: &ProofCertificateRef) -> CoverageJudgement {
        let formula_defect = match self.formula_defects.get(&certificate.obligation) {
            Some(defect) => defect.clone(),
            None => Some("the module states no obligation with the certificate's id".to_string()),
        };
        judge_certificate(
            certificate,
            self.report.is_checked(),
            formula_defect.as_deref(),
            self.report.for_certificate(certificate),
            self.report.refusals(),
        )
    }
}

/// The one schema whose payload IS an SMT-LIB text (trust-ir's
/// `ProofFormula::smtlib2`). Every other schema's payload is opaque here.
const SMTLIB2_SCHEMA: &str = "smtlib2";

/// Rule 5: why `formula` does NOT state exactly one SMT-LIB formula text —
/// the only kind of text a kernel replay of its obligation grounds — or `None`
/// when it does. Byte equality between payload and rendering, no
/// normalization: a rewriter here would be trusted code between the
/// obligation and the claim.
fn formula_text_defect(formula: Option<&ProofFormula>) -> Option<String> {
    let Some(formula) = formula else {
        return Some("the obligation states no formula".to_string());
    };
    if formula.schema != SMTLIB2_SCHEMA {
        return Some(format!(
            "the obligation's formula is in schema `{}`, whose payload is opaque to this \
             consumer: no SMT-LIB text a replay grounds is shown to be it",
            formula.schema
        ));
    }
    // The clause's own bindings are the environment, built by trust-ir's own
    // `linked_var_env` from each binding's surface type: a name bound twice
    // is ambiguous at every use, and a name no term can denote (not a simple
    // symbol, primed, a theory symbol) or a sort outside the surface is left
    // out, so a use of it is refused as undeclared, never guessed.
    let types: Vec<(&str, String)> = formula
        .bindings
        .iter()
        .map(|(name, binding)| (name.as_str(), surface_type(&binding.sort)))
        .collect();
    let env = linked_var_env(types.iter().map(|(name, ty)| (*name, ty.as_str())));
    if let Err(detail) = check_linked_invariant(&formula.payload, &env) {
        return Some(format!(
            "the obligation's smtlib2 payload is not SMT-LIB source trust-ir reads as one \
             Bool term over the clause's own bindings: {detail}"
        ));
    }
    if formula
        .smtlib
        .as_deref()
        .is_some_and(|rendering| rendering != formula.payload)
    {
        return Some(
            "the obligation's smtlib2 payload and its smtlib rendering are two different \
             SMT-LIB texts"
                .to_string(),
        );
    }
    if let Some(sort) = formula.sort.as_deref().filter(|sort| *sort != "Bool") {
        return Some(format!(
            "the obligation's formula has sort `{sort}`, so it is no SMT-LIB predicate"
        ));
    }
    None
}

/// A binding's sort spelled as a variable type of trust-ir's Linked spec
/// surface (`parse_spec_var_sort`: `Bool`, `Int`, `BitVec(<w>)`), or empty
/// for a sort the surface has no type for, which `linked_var_env` then leaves
/// out of the environment. Every variant is decided here: no wildcard.
fn surface_type(sort: &ClauseSort) -> String {
    match sort {
        ClauseSort::Bool => "Bool".to_string(),
        ClauseSort::Int => "Int".to_string(),
        ClauseSort::BitVec(width) => format!("BitVec({width})"),
        ClauseSort::Array(..)
        | ClauseSort::Float { .. }
        | ClauseSort::RoundingMode
        | ClauseSort::Datatype { .. } => String::new(),
    }
}

/// Rule 5 for every obligation of a module, by id. An id the module states
/// twice is a defect whatever either formula says: the certificate would
/// name two obligations.
fn formula_defects(obligations: &[ProofObligation]) -> BTreeMap<ProofId, Option<String>> {
    let mut defects = BTreeMap::new();
    for obligation in obligations {
        let defect = formula_text_defect(obligation.formula.as_ref());
        defects
            .entry(obligation.id)
            .and_modify(|seen: &mut Option<String>| {
                *seen = Some("the module states the certificate's obligation id twice".to_string());
            })
            .or_insert(defect);
    }
    defects
}

/// Rules 2–5 over what the report and the obligation say, as a pure function
/// of them so every arm is testable without forging a report.
fn judge_certificate(
    certificate: &ProofCertificateRef,
    checked: bool,
    formula_defect: Option<&str>,
    verdict: CertificateCoverage,
    refusals: &[ValidationError],
) -> CoverageJudgement {
    use TrustVcNativeTrustIrCertificateRejection as Rejection;

    // Rule 4: a refusal anywhere is fatal for the whole bundle.
    if !refusals.is_empty() {
        return CoverageJudgement::rejected(
            Rejection::CertificateCoverageRefused,
            refusals
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("; "),
        );
    }
    // Rule 2: nothing is derived from an unchecked report.
    if !checked {
        return CoverageJudgement::rejected(
            Rejection::CertificateCoverageUndetermined,
            "coverage establishment report is UNCHECKED: the bundle did not validate for it",
        );
    }
    // Rule 5, ahead of rule 3 so the detail names the formula: a replayed
    // claim is the obligation's only when the obligation states ONE text.
    if let Some(defect) = formula_defect {
        return CoverageJudgement::rejected(
            Rejection::CertificateCoverageUndetermined,
            format!(
                "{defect}; a kernel-replayed claim is not shown to be the obligation's formula"
            ),
        );
    }
    // Rule 3: this certificate's own verdict.
    match verdict {
        CertificateCoverage::Established { bound, basis } => {
            let (basis_certificate, family) = match &basis {
                CoverageBasis::KernelReplayedClaim {
                    certificate: basis_certificate,
                    family,
                } => (basis_certificate, *family),
                // `CoverageBasis` is `#[non_exhaustive]`: a basis this build
                // does not know establishes nothing here.
                _ => {
                    return CoverageJudgement::rejected(
                        Rejection::CertificateCoverageUndetermined,
                        format!("established on a basis this build does not know: {basis:?}"),
                    );
                }
            };
            if basis_certificate != certificate {
                return CoverageJudgement::rejected(
                    Rejection::CertificateCoverageBasisNotThisCertificate,
                    format!(
                        "the kernel-replayed basis names certificate {}/{}, not this one",
                        basis_certificate.obligation.index(),
                        basis_certificate.prover
                    ),
                );
            }
            let Some(family) = kernel_claim_family(family) else {
                return CoverageJudgement::rejected(
                    Rejection::CertificateCoverageUndetermined,
                    format!(
                        "kernel-replayed claim family {family:?} is not classified by this build"
                    ),
                );
            };
            match bound {
                CoverageBound::Unbounded => CoverageJudgement {
                    basis: Some(TrustVcNativeCoverageBasis::KernelReplayedClaim {
                        obligation_id: certificate.obligation.index(),
                        prover: certificate.prover.clone(),
                        evidence_digest: certificate.evidence_digest.to_string(),
                        family,
                    }),
                    rejections: Vec::new(),
                    detail: None,
                },
                // `CoverageBound` is `#[non_exhaustive]`; only `Unbounded` is
                // release grade, whatever else it grows.
                other => CoverageJudgement::rejected(
                    Rejection::CertificateCoverageBounded,
                    format!("established {other:?}, not Unbounded"),
                ),
            }
        }
        CertificateCoverage::Undetermined {
            reason: CoverageUndeterminedReason::NotTheReplayedCertificate,
        } => CoverageJudgement::rejected(
            Rejection::CertificateCoverageBasisNotThisCertificate,
            "a SIBLING certificate on the same obligation was kernel-replayed, not this one",
        ),
        CertificateCoverage::Undetermined { reason } => CoverageJudgement::rejected(
            Rejection::CertificateCoverageUndetermined,
            format!("{reason:?}"),
        ),
        // Unreachable with `refusals` empty (a refused verdict is also a
        // refusal of the report); fail closed on it anyway.
        CertificateCoverage::Refused(error) => {
            CoverageJudgement::rejected(Rejection::CertificateCoverageRefused, error.to_string())
        }
    }
}

#[cfg(test)]
mod tests;
