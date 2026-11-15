//! Driver-independent lowering: a fully-typed function model → verdict.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module is the **seam** between a typed front end and trust-vc's existing
//! back end. It takes a [`DriverFn`] — a function with *already resolved* types,
//! preconditions, a symbolic return value, and postconditions — and turns it into
//! a [`VerificationContext`], then runs the real `trust_vc_core` encoder + ay
//! solver via [`VerificationContext::verify`].
//!
//! The key property: a [`DriverFn`] carries [`TrustVcType`]s directly, so this
//! lowering performs **no name resolution, no type inference, and no
//! re-parsing**. That is exactly the information the `syn` front end lacks and
//! must approximate; here the rustc-driver front end (`driver.rs`) supplies it
//! from `TyCtxt`/THIR, and lowering becomes total.
//!
//! Verification is encoded in the standard Hoare style:
//! `assume(requires) ∧ assume(result == body) ⊢ assert(ensures)`. Preconditions
//! and the body relation become assumptions; each postcondition becomes a checked
//! assertion. A false postcondition is *refuted* (the backend returns a
//! counterexample), which is what makes the seam sound rather than a rubber stamp.

use trust_vc_core::ir::{ArithOp, CompareOp, LogicOp, TrustVcExpr, TrustVcType};
use trust_vc_core::vc::{TypedProofObligation, VariableDecl, VerificationContext};
use trust_vc_core::VerifyResult;

/// A typed binding — a parameter or the function's return value.
///
/// The `ty` is a fully-resolved [`TrustVcType`]; in the driver path it comes from
/// `TyCtxt`/THIR, so there is no ambiguity for lowering to resolve.
#[derive(Debug, Clone)]
pub struct Binding {
    /// SMT-level variable name (parameter name, or the synthetic result name).
    pub name: String,
    /// Resolved trust-vc type.
    pub ty: TrustVcType,
}

impl Binding {
    /// Creates a typed binding.
    pub fn new(name: impl Into<String>, ty: TrustVcType) -> Self {
        Self {
            name: name.into(),
            ty,
        }
    }

    /// The binding as a [`TrustVcExpr::Var`] reference.
    #[must_use]
    pub fn as_var(&self) -> TrustVcExpr {
        TrustVcExpr::Var {
            name: self.name.clone(),
            ty: self.ty.clone(),
        }
    }
}

/// A single verification target produced by lowering one rustc function body.
///
/// This is the **only** type the (toolchain-pinned) rustc-driver layer needs to
/// produce; everything downstream is stable, driver-independent code. Because the
/// fields are plain typed IR, a `DriverFn` can also be built directly in tests
/// (see this crate's `tests/`), which is how the seam is exercised on stable.
#[derive(Debug, Clone)]
pub struct DriverFn {
    /// Function name, used to label obligations.
    pub name: String,
    /// Typed parameters.
    pub params: Vec<Binding>,
    /// The return binding (its name is referenced by `ensures` as `result`).
    pub result: Binding,
    /// Preconditions (`requires`), assumed at body entry.
    pub requires: Vec<TrustVcExpr>,
    /// The symbolic return value, encoded as `assume(result == body_value)`.
    /// `None` models an abstract/opaque body (postconditions then hold only if
    /// implied by the preconditions alone).
    pub body_value: Option<TrustVcExpr>,
    /// Postconditions (`ensures`), each checked as a separate assertion.
    pub ensures: Vec<TrustVcExpr>,
}

/// The verdict for a [`DriverFn`], mapped from [`VerifyResult`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// Every postcondition is implied by the preconditions and the body.
    Verified,
    /// At least one postcondition was refuted by a concrete counterexample.
    Refuted,
    /// The backend could neither prove nor refute (solver incompleteness).
    Unknown,
    /// The context could not be encoded/checked.
    Error(String),
}

impl DriverFn {
    /// Builds the [`VerificationContext`] for this function without running it.
    ///
    /// Useful for inspection/tests and for callers that want to add additional
    /// obligations before verifying.
    pub fn to_context(&self) -> VerificationContext {
        let mut variables: Vec<VariableDecl> = self
            .params
            .iter()
            .map(|p| VariableDecl::new(p.name.clone(), p.ty.clone()))
            .collect();
        variables.push(VariableDecl::new(
            self.result.name.clone(),
            self.result.ty.clone(),
        ));

        let mut obligations: Vec<TypedProofObligation> = Vec::new();

        for (i, req) in self.requires.iter().enumerate() {
            obligations.push(TypedProofObligation::requires(
                format!("{}_requires_{i}", self.name),
                req.clone(),
            ));
        }

        if let Some(body) = &self.body_value {
            let body_eq = TrustVcExpr::Compare {
                op: CompareOp::Eq,
                left: Box::new(self.result.as_var()),
                right: Box::new(body.clone()),
            };
            obligations.push(TypedProofObligation::assume(
                format!("{}_body", self.name),
                body_eq,
            ));
        }

        for (i, ens) in self.ensures.iter().enumerate() {
            obligations.push(TypedProofObligation::ensures(
                format!("{}_ensures_{i}", self.name),
                ens.clone(),
            ));
        }

        VerificationContext::from_typed_parts(variables, obligations)
    }

    /// Lowers and verifies this function, returning both the coarse [`Outcome`]
    /// and the raw [`VerifyResult`] (which carries counterexample bindings).
    pub fn verify(&self) -> (Outcome, VerifyResult) {
        let result = self.to_context().verify();
        let outcome = outcome_from(&result);
        (outcome, result)
    }

    /// Lowers and verifies this function under **exec** arithmetic semantics:
    /// fixed-width overflow/underflow, division-by-zero, and shift-bounds are
    /// asserted (Verus's `OverflowBehavior::Error` for exec code), so a body that
    /// can overflow fails closed rather than proving a too-strong postcondition.
    ///
    /// This is the verdict the rustc-driver front end uses for exec functions
    /// (`driver.rs`): the THIR walker must not silently drop the implicit
    /// no-overflow obligation that Verus's exec semantics impose. Spec/proof
    /// bodies (unbounded `int`/`nat`) must continue to use [`Self::verify`].
    pub fn verify_exec(&self) -> (Outcome, VerifyResult) {
        let mut ctx = self.to_context();
        ctx.enable_overflow_checks();
        let result = ctx.verify();
        let outcome = outcome_from(&result);
        (outcome, result)
    }
}

/// Maps a backend [`VerifyResult`] into the coarse [`Outcome`]. `VerifyResult`
/// is `#[non_exhaustive]`, so any future variant is treated fail-closed as a
/// non-proof rather than silently accepted.
///
/// Public so the rustc-driver oracle-diff harness can map a syn-path
/// `VerifyResult` into the same coarse verdict it compares the driver against.
pub fn outcome_from(result: &VerifyResult) -> Outcome {
    match result {
        VerifyResult::Verified => Outcome::Verified,
        VerifyResult::Counterexample { .. } => Outcome::Refuted,
        // A model-less non-proof is a verification FAILURE, not an inconclusive
        // outcome. `Outcome` has no finer distinction than `Refuted`, and
        // `Refuted` here means "did not verify" for the coarse driver verdict —
        // reporting `Unknown` would understate a definite failure.
        VerifyResult::NotProved { .. } => Outcome::Refuted,
        VerifyResult::Unknown { .. } => Outcome::Unknown,
        VerifyResult::Error { message } => Outcome::Error(message.clone()),
        _ => Outcome::Unknown,
    }
}

// ---------------------------------------------------------------------------
// Certified verification (feature = "certificates").
//
// This is the capability that makes trust-vc a *better* Verus rather than an
// equal one: Verus trusts Z3's yes/no answer as an unaudited oracle, whereas
// every trust-vc "Verified" can carry an ay UNSAT proof (rendered as Alethe
// text) that the small, independent `trust-vc-kernel` re-checks. We surface that
// certificate at the front-end seam so both the in-Trust and standalone paths
// can return checkable proofs — leveraging ay's owned, certificate-emitting
// solver, not just its yes/no verdict.
// ---------------------------------------------------------------------------

/// An independently-checkable proof certificate from a verified [`DriverFn`].
///
/// Produced from ay's UNSAT proof artifact and re-checked by `trust-vc-kernel`
/// (`kernel_verified`). Available with the `certificates` feature.
///
/// It is the certificate of ONE obligation, [`Self::refuted_obligation`]: the
/// last one the solver refuted for this function. Every flag is a claim about
/// that obligation's query. A function with several obligations has a
/// certificate per obligation in its verification report's steps, and this one
/// says nothing about the others.
#[cfg(feature = "certificates")]
#[derive(Debug, Clone)]
pub struct Certificate {
    /// The obligation whose negated goal this certificate refutes.
    pub refuted_obligation: String,
    /// True if `trust-vc-kernel` independently re-checked the ay UNSAT proof as
    /// a refutation of [`Self::refuted_obligation`]'s own query (premises bound
    /// to it; theory lemmas taken as given and checked by ay's strict checker).
    pub kernel_verified: bool,
    /// True if ay's strict proof checker accepted the proof and its premises
    /// are [`Self::refuted_obligation`]'s own query.
    pub strict_verified: bool,
    /// True if the proof uses only clean-supported (non-`trust`) rules.
    pub clean_supported: bool,
    /// Rendered Alethe (SMT-LIB-compatible) proof text.
    pub alethe: String,
    /// Count of trusted (unjustified) steps remaining in the proof.
    pub trust_count: u32,
    /// Count of holes (gaps) in the proof.
    pub hole_count: u32,
}

/// A verification verdict paired with its proof certificate, when one was
/// produced (a proof is emitted for proven results that took the
/// proof-generating solver path).
#[cfg(feature = "certificates")]
#[derive(Debug, Clone)]
pub struct CertifiedOutcome {
    /// The coarse verdict.
    pub outcome: Outcome,
    /// The kernel-checkable certificate, if the backend produced one.
    pub certificate: Option<Certificate>,
}

#[cfg(feature = "certificates")]
impl DriverFn {
    /// Verify and, for a proven result, return an independently-checkable proof
    /// certificate: an ay UNSAT proof re-checked by `trust-vc-kernel`.
    ///
    /// This is the front-end-seam realization of trust-vc's soundness edge over
    /// Verus (whose Z3 backend yields no checkable artifact). The certificate
    /// can be carried into Trust's `trust_ir::ProofCertificate` lineage.
    pub fn verify_certified(&self) -> CertifiedOutcome {
        let report = self
            .to_context()
            .verify_with_report(trust_vc_core::VerificationReportOptions::new());
        let outcome = outcome_from(report.result());
        let certificate = report.proof().map(|p| Certificate {
            refuted_obligation: p.refuted_obligation().to_string(),
            kernel_verified: p.kernel_verified(),
            strict_verified: p.strict_verified(),
            clean_supported: p.clean_supported(),
            alethe: p.alethe().to_string(),
            trust_count: p.trust_count(),
            hole_count: p.hole_count(),
        });
        CertifiedOutcome {
            outcome,
            certificate,
        }
    }
}

/// A compact, portable attestation of an independently-checked proof.
///
/// A `ProofReceipt` summarizes a [`Certificate`] into a small, deterministic
/// record — the kernel-verification flag plus the proof's size and a content
/// hash of its Alethe text — suitable for carrying in a `trust_ir` lineage,
/// logging, or cheap equality/replay checks without shipping the full proof.
/// Verus's black-box Z3 backend produces no checkable proof artifact at all, so
/// it has nothing analogous: this receipt is a concrete token of the soundness
/// edge (every trust-vc "Verified" can attest an independently re-checked proof).
#[cfg(feature = "certificates")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofReceipt {
    /// True iff `trust-vc-kernel` independently re-checked the ay UNSAT proof.
    pub kernel_verified: bool,
    /// True iff ay's strict proof checker accepted the proof.
    pub strict_verified: bool,
    /// Length (bytes) of the rendered Alethe proof text.
    pub alethe_len: usize,
    /// Stable content hash of the Alethe proof text (deterministic per proof).
    pub alethe_hash: u64,
}

#[cfg(feature = "certificates")]
impl Certificate {
    /// Distill this certificate into a portable [`ProofReceipt`].
    #[must_use]
    pub fn receipt(&self) -> ProofReceipt {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.alethe.hash(&mut hasher);
        ProofReceipt {
            kernel_verified: self.kernel_verified,
            strict_verified: self.strict_verified,
            alethe_len: self.alethe.len(),
            alethe_hash: hasher.finish(),
        }
    }
}

// ---------------------------------------------------------------------------
// Typed-IR builders.
//
// These are the primitives the rustc-driver THIR walker emits and that tests use
// to construct `DriverFn`s. They keep call sites readable and centralize the (few)
// shapes the first increment supports: integer literals/vars, +/*, comparisons,
// and boolean conjunction.
// ---------------------------------------------------------------------------

/// `uN` unsigned integer type of the given bit width.
#[must_use]
pub fn uint(width: u32) -> TrustVcType {
    TrustVcType::Uint { width }
}

/// `iN` signed integer type of the given bit width.
#[must_use]
pub fn int(width: u32) -> TrustVcType {
    TrustVcType::Int { width }
}

/// A typed variable reference.
#[must_use]
pub fn var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}

/// A typed integer literal.
#[must_use]
pub fn lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty }
}

/// `left + right` at the given (result) type.
#[must_use]
pub fn add(left: TrustVcExpr, right: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(left),
        right: Box::new(right),
        ty,
    }
}

/// `left * right` at the given (result) type.
#[must_use]
pub fn mul(left: TrustVcExpr, right: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op: ArithOp::Mul,
        left: Box::new(left),
        right: Box::new(right),
        ty,
    }
}

/// A comparison `left <op> right`.
#[must_use]
pub fn cmp(op: CompareOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}

/// `left && right`.
#[must_use]
pub fn and(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(left),
        right: Box::new(right),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Pure (no-solver) structural tests: lowering shape is deterministic.

    fn sample() -> DriverFn {
        // fn add_bounds(x: u32, y: u32) -> u32 requires x < 100, y < 100
        //   { x + y } ensures result < 200
        DriverFn {
            name: "add_bounds".into(),
            params: vec![Binding::new("x", uint(32)), Binding::new("y", uint(32))],
            result: Binding::new("result", uint(32)),
            requires: vec![
                cmp(CompareOp::Lt, var("x", uint(32)), lit(100, uint(32))),
                cmp(CompareOp::Lt, var("y", uint(32)), lit(100, uint(32))),
            ],
            body_value: Some(add(var("x", uint(32)), var("y", uint(32)), uint(32))),
            ensures: vec![cmp(
                CompareOp::Lt,
                var("result", uint(32)),
                lit(200, uint(32)),
            )],
        }
    }

    #[test]
    fn lowers_params_result_and_obligations() {
        let ctx = sample().to_context();
        // 2 params + result.
        assert_eq!(ctx.variables().len(), 3);
        // 2 requires (assume) + 1 body (assume) + 1 ensures (assert) = 4.
        assert_eq!(ctx.obligations().len(), 4);
        // The ensures obligation is the only assertion.
        assert!(ctx.has_assertions());
        assert!(ctx.has_assumptions());
    }

    #[test]
    fn binding_as_var_roundtrips() {
        let b = Binding::new("z", uint(64));
        match b.as_var() {
            TrustVcExpr::Var { name, ty } => {
                assert_eq!(name, "z");
                assert_eq!(ty, uint(64));
            }
            other => panic!("expected Var, got {other:?}"),
        }
    }
}
