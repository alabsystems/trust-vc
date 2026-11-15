// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! trust-ir body lane v0: in-process, ADVISORY discharge of `Assert` sites in
//! one `trust_ir::Function`.
//!
//! # What is decided
//!
//! For each obligation scoped to or sited in the function, exactly this:
//! "the `Inst::Assert` at `obligation.site` never fails, for any input that
//! satisfies every `Inst::Assume` executed before it". The obligation's
//! `ProofFormula` payload, its status, `module.proof_certificates`, and every
//! `ProofAnnotation` are never read as facts; the report records that they
//! were present and ignored. An obligation that names a temporal property
//! (`ProofObligation::spec`) is refused: an `Assert`-site answer cannot back
//! that attribution.
//!
//! Earlier `Assert`s are deliberately NOT assumed at a later site. That is
//! sound but incomplete: a site that only holds because an earlier assert
//! would have panicked first is refuted, and such a refutation is labelled
//! [`TrustIrBodyVerdict::RefutedIgnoringPriorAsserts`] after concrete replay.
//!
//! # What is admitted
//!
//! An acyclic chain of blocks joined by unconditional `Br` (each non-entry
//! block has exactly one predecessor), ending in one `Return`, over 8- to
//! 64-bit integers and `Bool`, with `Const`, wrapping `BinOp`
//! `Add`/`Sub`/`Mul`, scalar Bool `BAnd`/`BOr`/`BXor`, `Overflow`, `ICmp`,
//! `Copy`, complete nonempty scalar tuples (`MakeAggregate`), the legacy static checked-op pack (`Undef`
//! tuple + `InsertField`), `ExtractField`, `Assume` and `Assert`.
//! Everything else is refused with a reason naming the block, index and
//! instruction; that includes every tensor operation, type and constant, and a
//! module carrying a weight blob table (`Module.blobs`) is refused whole. See
//! `check.rs` and `lower.rs`.
//!
//! # Which semantics a verdict is about: the `Undef` havoc reading
//!
//! Complete `MakeAggregate` tuples execute as written under the pinned
//! interpreter, retain declaration order and exact lane types, and introduce
//! no havoc. Their readable fields use the same scalar aliases as the legacy
//! pack. Aggregate parameters, returns, copies and non-scalar lanes remain
//! outside this fragment.
//!
//! The legacy checked-op fixtures seed their tuple with `Inst::Undef`, and executing
//! a tuple `Undef` is UNDEFINED BEHAVIOUR under the shared reference
//! interpreter (`scalar_poison`: a
//! scalar `Undef` binds poison, a non-scalar one is UB, aggregate poison being
//! unmodelled). Read literally, then, NO input ever
//! reaches an `Assert` that sits behind that pack: every such claim would be
//! vacuously true and this lane would decide nothing about that legacy shape.
//!
//! v0 therefore decides the HAVOC reading: an admitted `Undef` denotes a fresh
//! unconstrained value. That is the over-approximation trust-ir's own
//! `ProofAnnotation::FreshSymbolicHavoc` doc sanctions
//! (`proof/annotations.rs:168-178`), and v0 takes it UNIFORMLY rather than on
//! the annotation's say-so — the annotation is inert here, like every other
//! producer claim. The doc's condition, that nothing may narrow the fresh
//! value, is kept STRUCTURALLY: a field no `InsertField` wrote cannot be read
//! (`check.rs`), and an aggregate cannot be used where a scalar is required,
//! so no havoc value reaches a solver term, a `Br` argument, a `Return`, or
//! the replay. Every readable field aliases a concrete SSA value.
//!
//! Because no havoc value is readable, the particular value the replay picks
//! is unobservable: the execution trace is the same for EVERY instantiation.
//! So a refutation refutes the whole havoc family, not one member of it, and a
//! discharge holds across all of it. `tests/trust_ir_body_oracle.rs` measures
//! that by replaying each variant under a second, deliberately different
//! seeding and requiring identical outcomes on every input.
//!
//! The two readings differ only in that the pinned one additionally halts at
//! the `Undef`, so the havoc reading has strictly MORE reaching inputs. A
//! discharge under it therefore implies the pinned claim as well. A REFUTATION
//! does not: its witness is a genuine counterexample under the havoc reading,
//! while under the pinned reading execution traps before the site. Nothing is
//! hidden — [`TrustIrBodyReport::havoc_seeds`] lists every admitted `Undef`,
//! [`TrustIrBodyObligationReport::reading`] says which semantics that
//! obligation was decided under, every [`TrustIrBodyWitness`] carries the same
//! tag so a witness cannot be read without it, and the tag is part of a
//! certificate's binding string, hence of its `unit_id`.
//!
//! # Authority
//!
//! There is no independent re-check that the solver query is the site's
//! meaning, so a discharge is [`TrustIrBodyAuthority::Advisory`] with
//! [`LoweringWitness::None`], and nothing here converts into
//! [`crate::TrustOutcome`]. What IS checked concretely, through trust-ir's own
//! reference interpreter, ON THE BODY UNDER THE OBLIGATION'S DECLARED READING
//! (havoc-instantiated where a seed precedes the site, the module as written
//! otherwise): every refutation witness fails the site, and every discharge
//! has a witness input that reaches it, so no discharge rests on a premise set
//! that is unsatisfiable UNDER THAT READING. Under the pinned reading a
//! havoc-seeded body has no reaching input at all; that is a property of the
//! `Undef`, is disclosed rather than repaired, and is pinned by
//! `tests/trust_ir_body_discharge.rs`.
//!
//! # How a native TrustIr request reaches this lane
//!
//! Two entries, one implementation:
//!
//! * directly, [`TrustVcTrustEngine::discharge_trust_ir_function`], with an
//!   in-memory module and a `FuncId`;
//! * through a native `DischargeProofObligations` request —
//!   [`TrustVcTrustEngine::discharge_native_trust_ir_request`] checks the
//!   request's shape (it must name a function, carry no certificates, and cite
//!   only obligations scoped to or sited in that function), calls this lane,
//!   and maps each cited obligation's verdict onto
//!   [`crate::TrustVcNativeTrustIrDischargeAnswer`]. The answer is carried as
//!   ADVISORY in its own required, single-valued types, never enters the
//!   certificate-admission channel, and its request verdict can never satisfy
//!   `TrustVcNativeTrustIrVerdict::is_ok`.
//!
//! These are in-process advisory entries. Serialized bundles consumed by
//! [`TrustVcTrustEngine::consume_native_trust_ir_bundle`] instead route
//! validated discharge requests to the distinct [`crate::native_discharge`]
//! implementation, with its own verdicts and certificates. Extending this
//! body fragment changes neither that route nor production proof authority.

mod binding;
mod check;
mod lower;
mod replay;

use std::collections::BTreeSet;

use thiserror::Error;
use trust_ir::{
    BlockId, FuncId, Function, Inst, Module, ObligationKind, ObligationSite, ProofId,
    ProofObligation, ProofStatus, Ty, ValueId,
};
use trust_vc_core::{VerificationReport, VerificationReportOptions, VerifyResult};

pub(crate) use binding::wire_identity_gap;
pub use binding::{
    trust_ir_body_semantic_digest, TrustIrBodyBinding, TrustIrBodyCertificate,
    TRUST_IR_BODY_BINDING_SCHEMA, TRUST_IR_BODY_TRUST_IR_PIN,
};

use crate::{TrustProofPolicy, TrustVcTrustEngine};
use check::{CheckedBody, StepKind};
use replay::{Outcome, Variant};

/// Schema of [`TrustIrBodyReport`].
pub const TRUST_IR_BODY_LANE_SCHEMA: &str = "trust-vc.trust-ir-body.v0";

/// Label carried by every entry of [`TrustIrBodyReport::unobligated_asserts`].
pub const UNOBLIGATED_ASSERT_LABEL: &str = "unobligated assert, not examined";

/// The disclosure every [`BodyReading::HavocInstantiatedUndef`] verdict carries
/// by construction; see the module doc.
pub const HAVOC_INSTANTIATION_NOTE: &str =
    "decided with Inst::Undef read as a fresh unconstrained \
     value; the pinned trust-ir interpreter calls executing Undef undefined behaviour, so under \
     that reading no input reaches this site at all";

/// Which semantics a verdict is about.
///
/// The lane can only decide a body it can also execute, and a body containing
/// `Inst::Undef` is not executable under the pinned reference interpreter. See
/// the module doc for why the havoc reading is admitted and what keeps it an
/// over-approximation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BodyReading {
    /// The module as written; the pinned interpreter executes it unchanged.
    PinnedInterpreter,
    /// An `Inst::Undef` is executed on the way to the site, and is read as a
    /// fresh unconstrained value. See [`HAVOC_INSTANTIATION_NOTE`].
    HavocInstantiatedUndef,
}

impl BodyReading {
    /// `true` when the verdict is NOT about the module as the pinned
    /// interpreter reads it.
    pub const fn is_havoc_instantiated(self) -> bool {
        matches!(self, Self::HavocInstantiatedUndef)
    }
}

/// One admitted `Inst::Undef`, disclosed on [`TrustIrBodyReport::havoc_seeds`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HavocSeedPosition {
    pub block: BlockId,
    pub inst_index: u32,
    /// The seeded type, rendered (always a tuple of admitted scalars).
    pub ty: String,
}

/// Options for [`TrustVcTrustEngine::discharge_trust_ir_function`].
///
/// Only `EvidenceOnly` and `AttachReplayableCertificates` are accepted: an
/// advisory lane cannot promise the admission the `Require*` policies ask for.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct TrustIrBodyOptions {
    pub proof_policy: TrustProofPolicy,
}

/// Structural misuse of the lane (as opposed to a body it declines).
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum TrustIrBodyError {
    #[error("trust-ir function #{} is not in the module", .0.index())]
    FunctionMissing(FuncId),
    #[error("trust-ir function #{} is declared more than once", .0.index())]
    FunctionDuplicated(FuncId),
    #[error("trust-ir proof obligation #{} is declared more than once", .0.index())]
    DuplicateProofId(ProofId),
    #[error("proof policy {0:?} is not available on the advisory trust-ir body lane")]
    UnsupportedPolicy(TrustProofPolicy),
    /// The function carries a construct trust-ir's canonical binary writer
    /// cannot encode (an instruction ahead of its wire tag, e.g. `MemCopy` /
    /// `MemSet` at trust-ir `0.14.0@4f09dab8`). Its semantic digest does not
    /// exist, so no verdict could be bound to it and none is made.
    #[error(
        "trust-ir function #{} has no wire identity ({construct} at {location}), so no \
         verdict can be bound to it",
        function.index()
    )]
    NoWireIdentity {
        function: FuncId,
        location: String,
        construct: String,
    },
}

/// Authority of every verdict of this lane. A single variant on purpose.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrustIrBodyAuthority {
    Advisory,
}

/// Evidence that the lowering matches trust-ir semantics. None exists yet.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoweringWitness {
    None,
}

/// Inputs the lane saw and deliberately did not use as facts.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct IgnoredInputs {
    /// Some reported obligation carried a status other than `Pending`.
    pub statuses: bool,
    /// The module carried proof certificates.
    pub certificates: bool,
    /// Some reported obligation carried a formula payload.
    pub formulas: bool,
    /// The function or one of its nodes carried proof annotations.
    pub annotations: bool,
    /// The function summary carried `requires` clauses.
    pub summary_requires: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AssertPosition {
    pub block: BlockId,
    pub inst_index: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrustIrScalar {
    Int { ty: Ty, value: i128 },
    Bool(bool),
}

/// Concrete entry-parameter values, replayed through trust-ir's interpreter.
///
/// `reading` says which body the replay ran on, so a witness handed on alone
/// still carries the disclosure: under
/// [`BodyReading::HavocInstantiatedUndef`] the replayed body is not the module
/// as the pinned interpreter reads it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustIrBodyWitness {
    pub params: Vec<(ValueId, TrustIrScalar)>,
    pub reading: BodyReading,
}

/// Why an obligation (or the whole function) was not answered.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrustIrBodyRefusal {
    ControlFlow {
        block: BlockId,
        inst_index: Option<u32>,
        detail: String,
    },
    UnsupportedInstruction {
        block: BlockId,
        inst_index: u32,
        inst: &'static str,
        detail: String,
    },
    UnsupportedType {
        block: Option<BlockId>,
        inst_index: Option<u32>,
        ty: String,
    },
    IllTyped {
        block: BlockId,
        inst_index: u32,
        detail: String,
    },
    /// SSA redefinition, use before definition, function-type mismatch,
    /// missing function type, duplicate block.
    Malformed {
        detail: String,
    },
    /// The module carries a table v0 does not model, named by its trust-ir
    /// path: today only a non-empty `Module.blobs`, the weight blob table of
    /// trust-ir wire v70. Refused for the whole module, before any body is
    /// read.
    UnsupportedModuleTable {
        table: &'static str,
        detail: String,
    },
    FunctionScopeMissing,
    SiteMissing,
    SiteFunctionMismatch {
        site_function: FuncId,
    },
    SiteBlockMissing {
        block: BlockId,
    },
    SiteIndexOutOfRange {
        block: BlockId,
        inst_index: u32,
    },
    SiteNotAssert {
        found: &'static str,
    },
    UnsupportedObligationKind(String),
    /// The obligation names a temporal property it would discharge
    /// (`ProofObligation::spec`, trust-ir wire v46): machine `machine`,
    /// property `temporal`.
    ///
    /// This lane decides one `Assert` site; a discharge here says nothing
    /// about a named temporal property, so answering would let a downstream
    /// reader attribute that property as proved. trust-ir's validator admits
    /// `spec` only on `TemporalSafety`/`Liveness`, which `admitted_kind`
    /// already refuses, so reaching this refusal means an unvalidated module
    /// put `spec` on a panic-class obligation. Refused, never answered.
    TemporalPropertyAttributed {
        machine: String,
        temporal: String,
    },
    /// The `Assume`s before the site are unsatisfiable: any claim would hold
    /// vacuously, so none is made.
    VacuousPremises,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrustIrBodyVerdict {
    /// The site holds under its premises, per the solver; the premises are
    /// witnessed satisfiable by interpreter replay. No independent re-check
    /// of the lowering exists, so this is ADVISORY.
    DischargedAdvisory {
        premise_witness: TrustIrBodyWitness,
        certificate: Option<Box<TrustIrBodyCertificate>>,
        certificate_note: Option<String>,
    },
    /// Replayed: the witness passes every earlier `Assume` and `Assert` and
    /// fails the site.
    Refuted {
        witness: TrustIrBodyWitness,
    },
    /// Replayed: the witness fails the site, but an earlier (non-assumed)
    /// `Assert` fails first.
    RefutedIgnoringPriorAsserts {
        witness: TrustIrBodyWitness,
    },
    Unknown {
        reason: String,
        category: String,
    },
    NotAnswerable(TrustIrBodyRefusal),
}

impl TrustIrBodyVerdict {
    /// Deliberately the only positive predicate: there is no `is_verified`,
    /// and no conversion into `TrustOutcome`.
    pub const fn is_discharged_advisory(&self) -> bool {
        matches!(self, Self::DischargedAdvisory { .. })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TrustIrBodyObligationReport {
    pub proof_id: ProofId,
    pub kind: ObligationKind,
    pub site: Option<ObligationSite>,
    /// `Assert`s strictly before the site in chain order; none is assumed.
    pub prior_asserts_not_assumed: usize,
    /// Which semantics this obligation's verdict is about. Always
    /// [`BodyReading::PinnedInterpreter`] when the lane reached no decision.
    pub reading: BodyReading,
    pub verdict: TrustIrBodyVerdict,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TrustIrBodyReport {
    pub schema: &'static str,
    pub authority: TrustIrBodyAuthority,
    pub lowering_witness: LoweringWitness,
    pub function: FuncId,
    /// Provisional binding digest (see [`trust_ir_body_semantic_digest`]).
    pub semantic_digest: String,
    /// Set when the body is outside v0; every obligation is then
    /// `NotAnswerable` with this reason.
    pub function_refusal: Option<TrustIrBodyRefusal>,
    /// Every obligation scoped to or sited in the function, in `ProofId` order.
    pub obligations: Vec<TrustIrBodyObligationReport>,
    /// `Assert`s no obligation cites; see [`UNOBLIGATED_ASSERT_LABEL`].
    pub unobligated_asserts: Vec<AssertPosition>,
    /// Every admitted `Inst::Undef`, in chain order. Non-empty means some
    /// verdict in this report is about a havoc-instantiated body rather than
    /// about the module as the pinned interpreter reads it; see
    /// [`HAVOC_INSTANTIATION_NOTE`] and the module doc. Empty when the body
    /// was refused.
    pub havoc_seeds: Vec<HavocSeedPosition>,
    pub ignored_inputs: IgnoredInputs,
}

impl TrustIrBodyReport {
    pub fn obligation(&self, proof_id: ProofId) -> Option<&TrustIrBodyObligationReport> {
        self.obligations
            .iter()
            .find(|report| report.proof_id == proof_id)
    }
}

impl TrustVcTrustEngine {
    /// Discharge the `Assert` sites of one trust-ir function, ADVISORY and
    /// in-process only.
    ///
    /// For a native `DischargeProofObligations` request, call
    /// [`Self::discharge_native_trust_ir_request`] instead: it applies the
    /// request-shape gates and returns the answer in the wire report's own
    /// advisory types. The serialized bundle route uses the distinct
    /// `native_discharge` implementation, not this advisory entry.
    pub fn discharge_trust_ir_function(
        &self,
        module: &Module,
        function: FuncId,
        options: &TrustIrBodyOptions,
    ) -> Result<TrustIrBodyReport, TrustIrBodyError> {
        if options.proof_policy.requires_replayable_artifact() {
            return Err(TrustIrBodyError::UnsupportedPolicy(options.proof_policy));
        }
        let semantic_digest = trust_ir_body_semantic_digest(module, function)?;
        let target = module
            .functions
            .iter()
            .find(|candidate| candidate.id == function)
            .ok_or(TrustIrBodyError::FunctionMissing(function))?;
        let mut seen = BTreeSet::new();
        for obligation in &module.proof_obligations {
            if !seen.insert(obligation.id) {
                return Err(TrustIrBodyError::DuplicateProofId(obligation.id));
            }
        }

        let checked = check::check_function(module, target);
        let function_refusal = checked.as_ref().err().cloned();

        let mut scoped = module
            .proof_obligations
            .iter()
            .filter(|obligation| {
                obligation.function == Some(function)
                    || obligation.site.map(|site| site.function) == Some(function)
            })
            .collect::<Vec<_>>();
        scoped.sort_by_key(|obligation| obligation.id);

        let ignored_inputs = IgnoredInputs {
            statuses: scoped
                .iter()
                .any(|obligation| obligation.status != ProofStatus::Pending),
            certificates: !module.proof_certificates.is_empty(),
            formulas: scoped.iter().any(|obligation| obligation.formula.is_some()),
            annotations: !target.proofs.is_empty()
                || target.instructions().any(|node| !node.proofs.is_empty()),
            summary_requires: target
                .summary
                .as_ref()
                .is_some_and(|summary| !summary.requires.is_empty()),
        };

        let unobligated_asserts = unobligated_asserts(target, &scoped);
        let context = SiteContext {
            module,
            function: target,
            semantic_digest: &semantic_digest,
            policy: options.proof_policy,
        };
        let obligations = scoped
            .iter()
            .map(|obligation| context.answer(checked.as_ref(), obligation))
            .collect();

        let havoc_seeds = checked
            .as_ref()
            .map(|body| {
                body.havoc_seeds
                    .iter()
                    .map(|seed| HavocSeedPosition {
                        block: seed.block,
                        inst_index: seed.inst_index,
                        ty: seed.ty.clone(),
                    })
                    .collect()
            })
            .unwrap_or_default();

        Ok(TrustIrBodyReport {
            schema: TRUST_IR_BODY_LANE_SCHEMA,
            authority: TrustIrBodyAuthority::Advisory,
            lowering_witness: LoweringWitness::None,
            function,
            semantic_digest,
            function_refusal,
            obligations,
            unobligated_asserts,
            havoc_seeds,
            ignored_inputs,
        })
    }
}

fn unobligated_asserts(function: &Function, scoped: &[&ProofObligation]) -> Vec<AssertPosition> {
    let cited = scoped
        .iter()
        .filter_map(|obligation| obligation.site)
        .filter(|site| site.function == function.id)
        .map(|site| (site.block, site.inst_index))
        .collect::<BTreeSet<_>>();
    let mut out = Vec::new();
    for block in &function.blocks {
        for (index, node) in block.body.iter().enumerate() {
            let inst_index = u32::try_from(index).unwrap_or(u32::MAX);
            if matches!(node.inst, Inst::Assert { .. }) && !cited.contains(&(block.id, inst_index))
            {
                out.push(AssertPosition {
                    block: block.id,
                    inst_index,
                });
            }
        }
    }
    out
}

const fn admitted_kind(kind: &ObligationKind) -> bool {
    matches!(
        kind,
        ObligationKind::ArithmeticSafety
            | ObligationKind::PanicFreedom
            | ObligationKind::BoundsCheck
    )
}

/// Per-obligation refusals, in the documented order.
fn obligation_refusal(
    function: &Function,
    obligation: &ProofObligation,
) -> Result<ObligationSite, TrustIrBodyRefusal> {
    // Every field is named, none is `..`-ed away: a field trust-ir appends to
    // `ProofObligation` must fail to compile HERE and be classified by hand —
    // read as a fact, refused, or ignored-and-disclosed — instead of being
    // silently dropped by the one function that decides what an obligation
    // asks this lane.
    let ProofObligation {
        // Identity only; the report carries it back.
        id: _,
        kind,
        // Producer claims, never read as facts (module doc; the report's
        // `ignored_inputs` records their presence).
        status: _,
        description: _,
        formula: _,
        // Provenance label; nothing here depends on it.
        source: _,
        function: scope,
        site,
        spec,
    } = obligation;
    let Some(scope) = *scope else {
        return Err(TrustIrBodyRefusal::FunctionScopeMissing);
    };
    let Some(site) = *site else {
        return Err(TrustIrBodyRefusal::SiteMissing);
    };
    if site.function != scope || site.function != function.id {
        return Err(TrustIrBodyRefusal::SiteFunctionMismatch {
            site_function: site.function,
        });
    }
    let Some(block) = function.blocks.iter().find(|block| block.id == site.block) else {
        return Err(TrustIrBodyRefusal::SiteBlockMissing { block: site.block });
    };
    let Some(node) = block.body.get(site.inst_index as usize) else {
        return Err(TrustIrBodyRefusal::SiteIndexOutOfRange {
            block: site.block,
            inst_index: site.inst_index,
        });
    };
    if !matches!(node.inst, Inst::Assert { .. }) {
        return Err(TrustIrBodyRefusal::SiteNotAssert {
            found: check::inst_name(&node.inst),
        });
    }
    if !admitted_kind(kind) {
        return Err(TrustIrBodyRefusal::UnsupportedObligationKind(format!(
            "{kind:?}"
        )));
    }
    if let Some(spec) = spec {
        return Err(TrustIrBodyRefusal::TemporalPropertyAttributed {
            machine: spec.machine.clone(),
            temporal: spec.temporal.clone(),
        });
    }
    Ok(site)
}

enum PremiseProbe {
    Vacuous,
    Witnessed(TrustIrBodyWitness),
    Unknown { reason: String, category: String },
}

fn unknown(reason: impl Into<String>, category: impl Into<String>) -> TrustIrBodyVerdict {
    TrustIrBodyVerdict::Unknown {
        reason: reason.into(),
        category: category.into(),
    }
}

/// A solved query together with the names its certificate would bind.
/// The name fields are read only by the `proof-certificates` build.
#[cfg_attr(not(feature = "proof-certificates"), allow(dead_code))]
struct Solved {
    report: VerificationReport,
    assertion_name: String,
    assumption_names: Vec<String>,
}

fn verify(query: lower::Query) -> Solved {
    let assertion_name = query.assertion_name.clone();
    let assumption_names = query.assumption_names.clone();
    let report = query
        .into_context()
        .verify_with_report(VerificationReportOptions::new());
    Solved {
        report,
        assertion_name,
        assumption_names,
    }
}

fn solver_unknown(result: &VerifyResult, what: &str) -> (String, String) {
    match result {
        VerifyResult::Unknown { reason, category } => (
            format!("{what}: {reason}"),
            format!("solver-unknown:{category:?}"),
        ),
        VerifyResult::NotProved { reason, category } => (
            format!("{what}: {reason}"),
            format!("solver-not-proved:{category:?}"),
        ),
        VerifyResult::Error { message } => {
            (format!("{what}: {message}"), "solver-error".to_string())
        }
        VerifyResult::Verified => (format!("{what}: verified"), "unexpected".to_string()),
        VerifyResult::Counterexample {
            obligation_name, ..
        } => (
            format!("{what}: counterexample for {obligation_name}"),
            "unexpected".to_string(),
        ),
        other => (
            format!("{what}: {other:?}"),
            "solver-unrecognized".to_string(),
        ),
    }
}

struct SiteContext<'a> {
    module: &'a Module,
    function: &'a Function,
    semantic_digest: &'a str,
    policy: TrustProofPolicy,
}

impl SiteContext<'_> {
    fn answer(
        &self,
        checked: Result<&CheckedBody, &TrustIrBodyRefusal>,
        obligation: &ProofObligation,
    ) -> TrustIrBodyObligationReport {
        let mut report = TrustIrBodyObligationReport {
            proof_id: obligation.id,
            kind: obligation.kind.clone(),
            site: obligation.site,
            prior_asserts_not_assumed: 0,
            reading: BodyReading::PinnedInterpreter,
            verdict: TrustIrBodyVerdict::NotAnswerable(TrustIrBodyRefusal::SiteMissing),
        };
        let body = match checked {
            Ok(body) => body,
            Err(refusal) => {
                report.verdict = TrustIrBodyVerdict::NotAnswerable(refusal.clone());
                return report;
            }
        };
        let site = match obligation_refusal(self.function, obligation) {
            Ok(site) => site,
            Err(refusal) => {
                report.verdict = TrustIrBodyVerdict::NotAnswerable(refusal);
                return report;
            }
        };
        let Some((position, cond)) = body.assert_at(site.block, site.inst_index) else {
            // The checker admitted the body and the node is an Assert, so it
            // was recorded; refuse rather than guess if that ever changes.
            report.verdict = unknown("checked body has no step for the sited Assert", "internal");
            return report;
        };
        report.prior_asserts_not_assumed = body
            .steps
            .iter()
            .filter(|step| step.position < position && matches!(step.kind, StepKind::Assert { .. }))
            .count();
        report.reading = if body.havoc_seeded_before(position) {
            BodyReading::HavocInstantiatedUndef
        } else {
            BodyReading::PinnedInterpreter
        };
        report.verdict = self.decide(body, obligation, site, position, cond, report.reading);
        report
    }

    fn decide(
        &self,
        body: &CheckedBody,
        obligation: &ProofObligation,
        site: ObligationSite,
        position: usize,
        cond: ValueId,
        reading: BodyReading,
    ) -> TrustIrBodyVerdict {
        let at = (site.block, site.inst_index);
        let solved = verify(lower::site_query(
            body,
            position,
            site.block,
            site.inst_index,
            cond,
        ));
        match solved.report.result() {
            VerifyResult::Counterexample { bindings, .. } => {
                let witness = match replay::witness_from_bindings(body, bindings, reading) {
                    Ok(witness) => witness,
                    Err(error) => return unknown(error, "model-unreadable"),
                };
                let site_run = replay::replay(
                    self.module,
                    self.function,
                    body,
                    at,
                    Variant::Site,
                    &witness,
                );
                let prior_run = replay::replay(
                    self.module,
                    self.function,
                    body,
                    at,
                    Variant::Prior,
                    &witness,
                );
                match (&site_run, &prior_run) {
                    (Outcome::Panic, Outcome::Reached) => TrustIrBodyVerdict::Refuted { witness },
                    (Outcome::Panic, Outcome::Panic) => {
                        TrustIrBodyVerdict::RefutedIgnoringPriorAsserts { witness }
                    }
                    _ => unknown(
                        format!(
                            "solver witness {witness:?} did not replay as a refutation: site variant {site_run:?}, prior-asserts variant {prior_run:?}"
                        ),
                        "model-replay-failed",
                    ),
                }
            }
            VerifyResult::Verified => match self.probe(body, position, at, reading) {
                PremiseProbe::Vacuous => {
                    TrustIrBodyVerdict::NotAnswerable(TrustIrBodyRefusal::VacuousPremises)
                }
                PremiseProbe::Unknown { reason, category } => unknown(reason, category),
                PremiseProbe::Witnessed(premise_witness) => {
                    let (certificate, certificate_note) =
                        self.certificate(obligation, site, &solved, reading);
                    TrustIrBodyVerdict::DischargedAdvisory {
                        premise_witness,
                        certificate: certificate.map(Box::new),
                        certificate_note,
                    }
                }
            },
            other => {
                let (reason, category) = solver_unknown(other, "site query");
                match self.probe(body, position, at, reading) {
                    PremiseProbe::Vacuous => {
                        TrustIrBodyVerdict::NotAnswerable(TrustIrBodyRefusal::VacuousPremises)
                    }
                    _ => unknown(reason, category),
                }
            }
        }
    }

    fn probe(
        &self,
        body: &CheckedBody,
        position: usize,
        at: (BlockId, u32),
        reading: BodyReading,
    ) -> PremiseProbe {
        let solved = verify(lower::premise_query(body, position, at.0, at.1));
        match solved.report.result() {
            VerifyResult::Verified => PremiseProbe::Vacuous,
            VerifyResult::Counterexample { bindings, .. } => {
                let witness = match replay::witness_from_bindings(body, bindings, reading) {
                    Ok(witness) => witness,
                    Err(error) => {
                        return PremiseProbe::Unknown {
                            reason: format!("premise probe: {error}"),
                            category: "premise-model-unreadable".to_string(),
                        }
                    }
                };
                match replay::replay(self.module, self.function, body, at, Variant::Pre, &witness) {
                    Outcome::Reached => PremiseProbe::Witnessed(witness),
                    other => PremiseProbe::Unknown {
                        reason: format!(
                            "premise witness {witness:?} did not reach the site under replay: {other:?}"
                        ),
                        category: "premise-replay-failed".to_string(),
                    },
                }
            }
            other => {
                let (reason, category) = solver_unknown(other, "premise probe");
                PremiseProbe::Unknown { reason, category }
            }
        }
    }

    fn binding(
        &self,
        obligation: &ProofObligation,
        site: ObligationSite,
        reading: BodyReading,
    ) -> TrustIrBodyBinding {
        TrustIrBodyBinding {
            schema: TRUST_IR_BODY_BINDING_SCHEMA,
            trust_ir: TRUST_IR_BODY_TRUST_IR_PIN,
            semantic_digest: self.semantic_digest.to_string(),
            function: self.function.id,
            site,
            proof_id: obligation.id,
            kind: format!("{:?}", obligation.kind),
            reading,
        }
    }

    #[cfg(feature = "proof-certificates")]
    fn certificate(
        &self,
        obligation: &ProofObligation,
        site: ObligationSite,
        solved: &Solved,
        reading: BodyReading,
    ) -> (Option<TrustIrBodyCertificate>, Option<String>) {
        if self.policy != TrustProofPolicy::AttachReplayableCertificates {
            return (
                None,
                Some(format!(
                    "certificate not requested (policy {:?})",
                    self.policy
                )),
            );
        }
        let binding = self.binding(obligation, site, reading);
        let unit_id = binding.canonical_string();
        match crate::TrustReplayableProofArtifact::from_verified_report(
            &unit_id,
            self.policy,
            &solved.report,
            std::slice::from_ref(&solved.assertion_name),
            &solved.assumption_names,
        ) {
            Ok(mut artifacts) if artifacts.len() == 1 => {
                let artifact = artifacts.remove(0);
                (
                    Some(TrustIrBodyCertificate {
                        binding,
                        artifact,
                        report_only: true,
                        lowering_witness: "none",
                    }),
                    None,
                )
            }
            Ok(artifacts) => (
                None,
                Some(format!(
                    "the verified site query yielded {} bindable Alethe certificates (exactly one required)",
                    artifacts.len()
                )),
            ),
            Err(error) => (None, Some(format!("certificate refused: {error}"))),
        }
    }

    #[cfg(not(feature = "proof-certificates"))]
    fn certificate(
        &self,
        obligation: &ProofObligation,
        site: ObligationSite,
        _solved: &Solved,
        reading: BodyReading,
    ) -> (Option<TrustIrBodyCertificate>, Option<String>) {
        let _ = self.binding(obligation, site, reading);
        let note = if self.policy == TrustProofPolicy::AttachReplayableCertificates {
            "trust-vc-trust-engine was built without the proof-certificates feature".to_string()
        } else {
            format!("certificate not requested (policy {:?})", self.policy)
        };
        (None, Some(note))
    }
}
