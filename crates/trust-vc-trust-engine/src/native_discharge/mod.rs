// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The DISCHARGE lane: trust-vc proving a trust-ir module's obligations itself.
//!
//! Import and merge check certificates somebody else produced. This lane is the
//! other direction — `TrustVcVerificationMode::DischargeProofObligations` hands
//! trust-vc a trust-ir function and a list of proof obligations and asks it to
//! decide them with its own encoder and the ay solver.
//!
//! # What it answers, and what it refuses
//!
//! The lane is deliberately NARROW and FAIL-CLOSED. Every trust-ir construct,
//! type and formula node it does not model produces a
//! [`TrustVcNativeTrustIrDischargeStatus::Declined`] naming that construct. An
//! unmodelled shape must never become a silent `Verified`: a false `Verified` on
//! this lane is a false `check-pass` in the compiler that consumes it.
//!
//! # Unified compilation and callee bodies
//!
//! Trust compiles whole programs, so a callee's body is legitimately visible to
//! its caller and using it definitionally is the SUPERIOR default — except for
//! `external_body`/`external`, which must be opaque in every mode. The trust-ir
//! this crate pins (0.14.0, binary VERSION 40) carries NO opacity marker:
//! `FuncAttrs` is `readonly`/`readnone`/`inlinehint`/`cold`/`params` and
//! `Linkage` is an ABI fact, not a trust boundary. A body-less function
//! (`blocks.is_empty()`) is not that marker either — an `external_body` function
//! may well have a placeholder body, and such a body often lowers to
//! `Unreachable`, which inlines as `assume(false)` and proves every caller
//! postcondition.
//!
//! So at this pin `Definitional` is not merely off by policy, it is
//! UNAVAILABLE: this lane uses the callee's CONTRACT only, and records that as a
//! [`TrustVcNativeTrustIrPremiseKind::CalleeContract`] premise on the outcome.
//! A `FuncAttrs.body_opacity` bit exists in a trust-ir v42 DRAFT; when that is
//! pinned here, definitional bodies become expressible for callees the producer
//! has positively marked non-opaque, and only for those.

mod body;
mod formula;
mod ty;
mod unit;

use super::native_trust_ir_bundle::{
    RequestReportInputs, TrustVcNativeTrustIrDischargeOutcome, TrustVcNativeTrustIrDischargeStatus,
    TrustVcNativeTrustIrPremise, TrustVcNativeTrustIrPremiseKind,
    TrustVcNativeTrustIrProducedCertificate,
};
use crate::{TrustExpr, TrustSort};
use body::BodyRelation;
use std::collections::BTreeMap;
use trust_ir::inst::Inst;
use trust_ir::request::TrustVcNativeEvidenceBundle;
use trust_ir::{FuncId, ObligationKind, ObligationSite, ProofId};
use ty::TypeDecoder;

/// What the unit declares for one wire name.
///
/// `emit` is NOT always the wire name: a callee's contract is lowered in a scope
/// that maps the callee's own parameter names onto the CALLER's argument
/// variables, so the clause is rebound rather than textually substituted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ScopeEntry {
    pub(crate) emit: String,
    pub(crate) sort: TrustSort,
}

impl ScopeEntry {
    pub(crate) fn new(emit: String, sort: TrustSort) -> Self {
        Self { emit, sort }
    }
}

/// Wire name -> what the unit declares for it.
pub(crate) type Scope = BTreeMap<String, ScopeEntry>;

/// The name the MIR return place carries on the wire.
///
/// MEASURED: `trust_types::spec_parse::map_var_name` rewrites the clause word
/// `result` to `_0`, so this is what a producer-emitted `ensures` names.
pub(crate) const RESULT_VAR: &str = "_0";

/// A refusal to model something, carrying the reason a consumer will read.
///
/// Every decline names the construct it refused. "Unsupported" with no name is
/// how a fail-closed lane quietly becomes an unfalsifiable one: nobody can tell
/// whether the gap is a missing feature or a missing case.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Decline {
    reason: String,
}

impl Decline {
    pub(crate) fn new(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
        }
    }

    pub(crate) fn reason(&self) -> &str {
        &self.reason
    }

    pub(crate) fn into_reason(self) -> String {
        self.reason
    }
}

impl std::fmt::Display for Decline {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.reason)
    }
}

/// Everything one discharge request contributed.
#[derive(Debug, Default)]
pub(crate) struct DischargeReport {
    /// One entry per requested obligation.
    pub(crate) outcomes: Vec<TrustVcNativeTrustIrDischargeOutcome>,
    /// Set when the request was refused BEFORE any obligation was lowered.
    /// Forces `DischargeNotAnswerable` — "never reached the lowering" — which is
    /// strictly worse than any per-obligation decline.
    pub(crate) request_refusal: Option<String>,
    pub(crate) produced_certificates: Vec<TrustVcNativeTrustIrProducedCertificate>,
    pub(crate) produced_evidence_bundle: Option<TrustVcNativeEvidenceBundle>,
}

impl DischargeReport {
    /// Refuse the whole request, recording the reason on every obligation so the
    /// wire report says WHY and not merely that nothing happened.
    fn refuse_request(inputs: &RequestReportInputs<'_>, reason: impl Into<String>) -> Self {
        let reason = reason.into();
        Self {
            outcomes: inputs
                .request
                .obligations
                .iter()
                .map(|obligation| {
                    TrustVcNativeTrustIrDischargeOutcome::declined(
                        inputs,
                        *obligation,
                        reason.clone(),
                    )
                })
                .collect(),
            request_refusal: Some(reason),
            produced_certificates: Vec::new(),
            produced_evidence_bundle: None,
        }
    }
}

/// Decide every obligation of one `DischargeProofObligations` request.
pub(crate) fn discharge_request(inputs: RequestReportInputs<'_>) -> DischargeReport {
    let request = inputs.request;

    if request.obligations.is_empty() {
        return DischargeReport {
            request_refusal: Some("discharge request names no obligations".to_string()),
            ..DischargeReport::default()
        };
    }

    // `TrustVcNativeRequest.function` is the function the obligations are
    // discharged AGAINST. Without it there is no body to lower and no scope for
    // the formulas' free variables, so there is nothing to be right about.
    let Some(function_id) = request.function else {
        return DischargeReport::refuse_request(
            &inputs,
            "discharge request carries no `function`: nothing names the body to lower",
        );
    };

    let Some(function) = inputs.module.function_by_id(function_id) else {
        return DischargeReport::refuse_request(
            &inputs,
            format!(
                "discharge request names function {} which is not in the module",
                function_id.index()
            ),
        );
    };

    let types = TypeDecoder::from_module(inputs.module);
    let mut relation = match body::lower_body(inputs.module, function, function_id, types) {
        Ok(relation) => relation,
        // A body this lane cannot model is a REQUEST-level refusal: it is not
        // about any one obligation, and every obligation of the function is
        // equally unanswerable.
        Err(decline) => return DischargeReport::refuse_request(&inputs, decline.into_reason()),
    };

    // The function's own `requires` rows are ASSUMED at the definition site.
    //
    // `site.is_none()` is the def-site test (a contract row minted by
    // `add_obligation` carries no site; a per-check VC carries one). A
    // Precondition row that is a CALL-SITE VC must never be assumed — that is
    // the `assume(P) |- P` false accept — and the body lane refuses the call
    // outright rather than relying on this filter alone (since round 6 it
    // refuses on a callee `Precondition` at ANY site, so a sited row can no
    // longer slip past the guard by leaving the collection it scans).
    //
    // A def-site `requires` is lowered in a scope that EXCLUDES the return place
    // (`_0`). A precondition constrains the INPUTS; a row whose formula names
    // the output would, if assumed, pin `_0` to a value the program never
    // computes and prove any postcondition about it — the same `assume(P) |- P`
    // shape, one level down. The producer is not trusted to have rejected
    // `result` in a `requires`: the scope makes the name unresolvable, so such a
    // row refuses the request instead.
    //
    // ROUND 6, THE CLASS: this filter has the SAME SHAPE as the callee-side one
    // that was fail-open (`function && site && kind`), and it is nonetheless
    // safe — for a reason that is about DIRECTION, not about the filter. A row
    // this selection drops REMOVES an assumption, which makes the unit strictly
    // STRONGER, so a drop can only over-reject; the dangerous move here would be
    // ADDING a row, and it adds only `site.is_none()` preconditions, which is
    // exactly what a `requires` means. The callee-side filter runs the other
    // way: a row IT dropped removed a GUARD, so the same shape was fail-open
    // there and had to be inverted. The full enumeration of every point where a
    // producer claim can influence a verdict is at
    // `body::Builder::callee_contract_facts`.
    //
    // NO STATUS GATE HERE, deliberately — and this is the contrast with the
    // callee-contract status gate in `body::Builder::lower_call` (round 5). A
    // def-site `requires` is not a claim the producer proved; it is the
    // obligation this function imposes on its CALLERS, and every call site owes
    // a separate discharge of it. Its `ProofStatus` therefore records whether
    // the CALL SITES established it, which says nothing about whether assuming
    // it here is sound: assuming your own precondition at your own definition
    // site is what a `requires` MEANS. A callee's `ensures` is the opposite — a
    // fact imported INTO this proof — so there the status is load-bearing.
    let mut assumptions = relation.assumptions.clone();
    let precondition_scope: Scope = relation
        .scope
        .iter()
        .filter(|(name, _)| name.as_str() != RESULT_VAR)
        .map(|(name, entry)| (name.clone(), entry.clone()))
        .collect();
    for obligation in inputs.module.proof_obligations.iter().filter(|obligation| {
        obligation.function == Some(function_id)
            && obligation.site.is_none()
            && matches!(obligation.kind, ObligationKind::Precondition)
    }) {
        // ROUND 8, THE SECOND MINOR — THE TWO `ObligationSite` READINGS,
        // RECONCILED.
        //
        // `body::Builder::callee_contract_facts` refuses to conclude anything
        // from `site`, while this selection reads `site.is_none()`. The reading
        // applied at BOTH seams is upstream's own: `None` means "no position
        // recorded" and is NEVER a witness. It is not used as one here either —
        // the ADMITTING condition is `function == Some(f) && kind ==
        // Precondition`, which is the producer's own definition of a `requires`,
        // and `site.is_none()` only NARROWS that set. A narrowing can drop a row
        // (strictly stronger unit, see the round-6 note above); it can never add
        // one.
        //
        // The shape that would make the difference bite is a row scoped to `f`
        // that some call declares is ITS callee's precondition —
        // `ProofContext.establishes` is upstream's per-call-site "callee
        // preconditions the caller must establish", so such a row would be two
        // incompatible claims about whose it is, and assuming it here would be
        // the `assume(P) |- P` false accept with no site to give it away.
        //
        // A guard for it was WRITTEN and then DELETED, because it could not be
        // given a discriminating test: `trust_ir_build::validate_module` — the
        // P1 input gate — already refuses the shape, and the refusal is NOT one
        // of the carried-past verdicts. MEASURED (round 8): attaching
        // `establishes: [2]` for an obligation owned by `fn#0` to a call naming
        // `fn#1` answers "bb0: proof context establishes obligation #2 owned by
        // fn#0, but the call names callee fn#1 — scope mismatch (B5.1)", and a
        // `proof_context` on a non-call instruction answers "bb0: a proof
        // context (B5) is attached to a non-call instruction". Round 8's own
        // rule is that a guard with no discriminating test is either untested or
        // unjustified; this one was the latter. The upstream refusal is pinned
        // instead, in
        // `a_requires_that_a_call_lists_as_someone_elses_precondition_is_refused_upstream`,
        // so a relaxation there becomes a failing test here rather than a silent
        // widening.
        match lower_predicate(inputs.module, obligation.id, &precondition_scope) {
            Ok(predicate) => {
                assumptions.push((
                    format!("{}_requires_{}", function.name, obligation.id.index()),
                    predicate,
                ));
                // DISCLOSED, not silent. An `Inst::Assume` is published as a
                // `BodyAssume` premise because "an assume IS the producer
                // speaking"; a def-site `requires` is the same producer content,
                // assumed with no status gate and no satisfiability check of its
                // own, and until round 7 it was folded in with no premise at all.
                relation.premises.push(TrustVcNativeTrustIrPremise::new(
                    TrustVcNativeTrustIrPremiseKind::DefSiteRequires,
                    format!(
                        "precondition {} of `{}` is ASSUMED at its definition site, as a \
                             `requires` means; its producer `ProofStatus` ({}) is deliberately \
                             not read, and every call site owes a separate discharge of it",
                        obligation.id.index(),
                        function.name,
                        obligation.status
                    ),
                ));
            }
            // A `requires` this lane cannot read is not droppable: dropping an
            // assumption makes the unit STRONGER, so a proof under it would
            // claim more than the program promises. Refuse the request.
            Err(decline) => {
                return DischargeReport::refuse_request(
                    &inputs,
                    format!(
                        "precondition {} of `{}` could not be lowered, and dropping a `requires` \
                         would strengthen every obligation of this function: {} (a def-site \
                         `requires` is lowered WITHOUT the return place `{RESULT_VAR}` in scope: \
                         a precondition constrains the inputs, and assuming one that names the \
                         output would pin the result)",
                        obligation.id.index(),
                        function.name,
                        decline.reason()
                    ),
                )
            }
        }
    }

    let unit = UnitInputs {
        relation: &relation,
        assumptions: &assumptions,
        function_name: &function.name,
    };

    let mut report = DischargeReport::default();
    for obligation_id in &request.obligations {
        let (outcome, produced) = discharge_obligation(&inputs, function_id, &unit, *obligation_id);
        report.outcomes.push(outcome);
        report.produced_certificates.extend(produced);
    }
    report.produced_evidence_bundle =
        super::native_trust_ir_bundle::produced_evidence_bundle(&inputs, &report);
    report
}

/// Everything shared by every obligation of one request.
struct UnitInputs<'a> {
    relation: &'a BodyRelation,
    /// The body relation's assumptions plus the function's own `requires`.
    assumptions: &'a [(String, TrustExpr)],
    function_name: &'a str,
}

/// One obligation: assembled into a unit and decided, or declined.
fn discharge_obligation(
    inputs: &RequestReportInputs<'_>,
    function_id: FuncId,
    unit: &UnitInputs<'_>,
    obligation_id: ProofId,
) -> (
    TrustVcNativeTrustIrDischargeOutcome,
    Option<TrustVcNativeTrustIrProducedCertificate>,
) {
    let assertion = match assertion_for(inputs, function_id, unit, obligation_id) {
        Ok(assertion) => assertion,
        Err(decline) => {
            return (
                TrustVcNativeTrustIrDischargeOutcome::declined(
                    inputs,
                    obligation_id,
                    decline.into_reason(),
                ),
                None,
            )
        }
    };

    let unit_id = unit_id_for(inputs, obligation_id, unit.function_name);
    let decided = match unit::decide(&unit_id, unit.relation, unit.assumptions, assertion) {
        Ok(decided) => decided,
        Err(decline) => {
            return (
                TrustVcNativeTrustIrDischargeOutcome::declined(
                    inputs,
                    obligation_id,
                    decline.into_reason(),
                ),
                None,
            )
        }
    };

    let verified = matches!(
        decided.status,
        TrustVcNativeTrustIrDischargeStatus::Verified
    );
    let outcome = TrustVcNativeTrustIrDischargeOutcome::new(
        inputs,
        obligation_id,
        decided.status,
        unit.relation.premises.clone(),
        decided.message,
    );
    // A certificate is minted ONLY for a verified obligation, and only from an
    // artifact the engine bound to this unit's own assertion.
    let certificate = decided.proof.filter(|_| verified).map(|proof| {
        TrustVcNativeTrustIrProducedCertificate::new(
            inputs,
            obligation_id,
            &unit_id,
            proof.alethe,
            proof.kernel_verified,
            proof.strict_verified,
        )
    });
    (outcome, certificate)
}

/// The stable identity a unit (and its certificate) is keyed on.
///
/// The public `vc:<def_path>:<kind>:<i>` identity when the bundle carries one —
/// that is what the compiler and the corpus harness join on — and otherwise a
/// spelling that cannot be confused with it.
fn unit_id_for(
    inputs: &RequestReportInputs<'_>,
    obligation_id: ProofId,
    function_name: &str,
) -> String {
    inputs
        .obligations
        .get(&obligation_id)
        .and_then(|obligation| obligation.source.as_ref())
        .and_then(|source| source.public.as_ref())
        .map(|public| public.obligation_id.clone())
        .unwrap_or_else(|| {
            format!(
                "trust-ir:{function_name}:obligation:{}",
                obligation_id.index()
            )
        })
}

/// The single assertion a unit for this obligation must discharge.
fn assertion_for(
    inputs: &RequestReportInputs<'_>,
    function_id: FuncId,
    unit: &UnitInputs<'_>,
    obligation_id: ProofId,
) -> Result<TrustExpr, Decline> {
    let obligation = inputs
        .obligations
        .get(&obligation_id)
        .copied()
        .ok_or_else(|| {
            Decline::new(format!(
                "obligation {} is not in the module",
                obligation_id.index()
            ))
        })?;

    // `ProofObligation.function` scopes an obligation to a function, and this
    // lane requires it POSITIVELY. An obligation naming a different function is
    // obviously not this request's to decide; one naming NO function is not
    // either — `function` is an `Option`, and an unowned row decided against
    // whichever body the request happens to name would be attributed to that
    // body, certificate and evidence row included. Ownership is a fact the
    // producer states or the lane declines.
    match obligation.function {
        Some(owner) if owner == function_id => {}
        Some(owner) => {
            return Err(Decline::new(format!(
                "obligation {} belongs to function {}, not the requested function {}",
                obligation_id.index(),
                owner.index(),
                function_id.index()
            )))
        }
        None => {
            return Err(Decline::new(format!(
                "obligation {} names no owning function, so nothing binds it to the requested \
                 function {}; deciding an unowned row against this body would attribute the \
                 proof to a function the producer never named",
                obligation_id.index(),
                function_id.index()
            )))
        }
    }

    // THE REQUESTED ROW'S SITE. trust-ir refuses a discharge request that cites
    // an obligation not sited in the requested function, so every row this
    // lane is asked about carries a site. The lane decides a `Postcondition`
    // over every path to a return, so it binds that verdict to the row only
    // when the site names where the check is generated: the function's ONE
    // `Return` terminator. A site anywhere else is a per-check VC whose
    // condition is generated at its own instruction, and a function with
    // several returns would need the verdict split per return; both decline.
    // An unsited row is a def-site row, as before.
    if let Some(site) = obligation.site {
        if !matches!(obligation.kind, ObligationKind::Postcondition)
            || !site_is_the_only_return(inputs.module, function_id, site)
        {
            return Err(Decline::new(format!(
                "obligation {} is anchored at an instruction site (block {}, instruction {}) \
                 that is not the one `Return` of function {}; this slice decides a \
                 postcondition at its return only, and a per-check VC must be bound to the \
                 condition generated AT its own instruction",
                obligation_id.index(),
                site.block.index(),
                site.inst_index,
                function_id.index()
            )));
        }
    }

    match obligation.kind {
        ObligationKind::Postcondition => {}
        ObligationKind::Precondition => {
            return Err(Decline::new(format!(
                "obligation {} is a def-site precondition: a `requires` is ASSUMED at the \
                 definition site, never proved there",
                obligation_id.index()
            )))
        }
        ref other => {
            return Err(Decline::new(format!(
                "obligation {} has kind `{other:?}`, which this slice does not decide",
                obligation_id.index()
            )))
        }
    }

    let _ = unit;
    lower_predicate(inputs.module, obligation_id, &unit.relation.scope)
}

/// Whether `site` names the one `Return` terminator of function `function_id`:
/// the site's function is that function, it has exactly one `Return` in all
/// its blocks, and the site's block and instruction index are that `Return`'s.
fn site_is_the_only_return(
    module: &trust_ir::Module,
    function_id: FuncId,
    site: ObligationSite,
) -> bool {
    if site.function != function_id {
        return false;
    }
    let Some(function) = module.function_by_id(function_id) else {
        return false;
    };
    let mut returns = function.blocks.iter().flat_map(|block| {
        block
            .body
            .iter()
            .enumerate()
            .filter(|(_, node)| matches!(node.inst, Inst::Return { .. }))
            .map(move |(index, _)| (block.id, index))
    });
    let (Some((block, index)), None) = (returns.next(), returns.next()) else {
        return false;
    };
    site.block == block && usize::try_from(site.inst_index).is_ok_and(|site| site == index)
}

/// Decode one obligation's `trust-types.Formula@1` predicate against a scope.
fn lower_predicate(
    module: &trust_ir::Module,
    obligation_id: ProofId,
    scope: &Scope,
) -> Result<TrustExpr, Decline> {
    let obligation = module
        .proof_obligations
        .iter()
        .find(|obligation| obligation.id == obligation_id)
        .ok_or_else(|| {
            Decline::new(format!(
                "obligation {} is not in the module",
                obligation_id.index()
            ))
        })?;
    let formula = obligation.formula.as_ref().ok_or_else(|| {
        Decline::new(format!(
            "obligation {} carries no formula, so there is no predicate to decide",
            obligation_id.index()
        ))
    })?;
    let node = formula::decode_predicate(formula)?;
    formula::FormulaDecoder::new(scope).lower_predicate(&node)
}
