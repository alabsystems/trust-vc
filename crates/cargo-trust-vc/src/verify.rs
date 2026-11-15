// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Per-function verification wrapper with timing and certificate metadata.

mod dependency_specs;

#[cfg(test)]
#[path = "verify/source_location_tests.rs"]
mod source_location_tests;

use crate::scan::AnnotatedFunction;
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeSet, HashMap, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;
use trust_vc_core::{
    extract_verification_conditions_with_file_context, parse_file_allow_tracked,
    vc::{ObligationKind, VerificationContext},
    CounterexampleBinding, CrateSiblingView, StepResultKind, VerificationReport,
    VerificationReportOptions, VerifyResult,
};

/// Classification of a function's verification outcome.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum VerdictKind {
    Verified,
    Counterexample,
    Unknown,
    Error,
    Skipped,
    /// The scan SAW this `fn` item but computed no verdict for it, and says why.
    ///
    /// Distinct from [`VerdictKind::Skipped`], which is a recognized target the
    /// verifier deliberately declined (a bodyless trait declaration, a marker
    /// attribute with no contract). `NotAnalyzed` is the bucket for a function
    /// that never reached the verifier at all — an ordinary uncontracted helper,
    /// or a contract spelled in a way discovery could not recognize.
    ///
    /// It exists so the report's buckets SUM to the number of functions scanned.
    /// Before it, a function with an unrecognized contract spelling appeared in
    /// no bucket whatsoever: `"functions": []`, an all-zero summary and exit 0,
    /// indistinguishable from a clean verification of an empty file. It is not a
    /// failure — a crate full of uncontracted helpers must still exit 0 — but it
    /// is never silent.
    NotAnalyzed,
}

/// Step-level localization for the first non-verified proof obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct LocalizedFailure {
    pub label: String,
    pub phase: String,
    pub location: Option<String>,
    pub result: VerdictKind,
    pub duration_ms: u64,
    pub unknown_category: Option<String>,
    pub suggestion: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub used_assumptions: Vec<String>,
}

/// Result of verifying a single function.
#[derive(Debug, Clone)]
pub struct FunctionVerdict {
    pub function: AnnotatedFunction,
    pub result: VerdictKind,
    pub duration_ms: u64,
    pub detail: Option<String>,
    pub localized_failure: Option<LocalizedFailure>,
    pub bindings: Vec<CounterexampleBinding>,
}

/// Per-obligation certificate status.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ObligationStatus {
    Verified,
    /// The engine REFUTED this obligation: it found a model of its negation.
    Counterexample,
    /// The engine did NOT discharge this obligation and found NO MODEL — the
    /// certificate-layer mirror of [`VerifyResult::NotProved`].
    ///
    /// A verification FAILURE, but not a refutation. `trust-vc-core` keeps the
    /// two apart in the type system precisely so that no consumer narrates a
    /// counterexample that was never found (see `VerifyResult::NotProved`'s
    /// "Why a distinct variant"); this layer used to collapse them onto
    /// `Counterexample`, which made the certificate claim a refutation the
    /// solver never produced and let the corpus gate spend a NON-DECISION as
    /// the one failure upstream's `assert_one_fails` requires.
    NotProved,
    Unknown,
    Error,
    Skipped,
    Assumed,
    Uncaptured,
}

/// Verification output plus obligation metadata for certificate emission.
#[derive(Debug, Clone)]
pub struct FunctionVerification {
    pub verdict: FunctionVerdict,
    pub source_hash: Option<String>,
    pub obligations: Vec<ObligationVerification>,
    /// Non-fatal VERIFIER WARNINGS raised while extracting this function, in
    /// source order (Verus's `err.warnings`). A warning never changes a
    /// verdict; upstream's default `=> Ok(())` harness arm asserts there are
    /// none, so the corpus gate pins them per case.
    pub warnings: Vec<String>,
    /// The full verification report, retained when `--emit-hints` or similar
    /// flags need access to step-level detail for proven-fact extraction.
    pub report: Option<VerificationReport>,
    /// UNSAT proof in Alethe format, when `proof-certificates` feature is enabled
    /// and the result was Verified.
    #[cfg(feature = "proof-certificates")]
    pub proof_alethe: Option<String>,
    /// Whether the strict proof checker accepted the UNSAT proof.
    #[cfg(feature = "proof-certificates")]
    pub proof_strict_verified: Option<bool>,
}

/// One obligation entry inside a proof certificate.
#[derive(Debug, Clone)]
pub struct ObligationVerification {
    pub name: String,
    pub kind: String,
    pub location: Option<String>,
    /// The same position, STRUCTURED, when the engine recorded one.
    ///
    /// `location` is the rendering and stays the display channel. This is what
    /// a consumer that needs the LINE AS A NUMBER reads — the evidence gate's
    /// cross-check against upstream's `FAILS`-marked line is the one that
    /// matters, and re-deriving that number by splitting the rendering on
    /// colons is a parse that fails silently (a directory with a colon in its
    /// name reads as "no location" rather than as a bug).
    pub source_location: Option<trust_vc_core::SourceLocation>,
    pub condition_hash: String,
    pub status: ObligationStatus,
    pub unknown_category: Option<String>,
}

#[derive(Debug, Clone)]
struct StepStatus {
    condition: Option<String>,
    location: Option<String>,
    status: ObligationStatus,
    unknown_category: Option<String>,
}

fn captured_obligation_status(status: &ObligationStatus) -> bool {
    matches!(
        status,
        ObligationStatus::Verified
            | ObligationStatus::Counterexample
            | ObligationStatus::NotProved
            | ObligationStatus::Unknown
            | ObligationStatus::Error
    )
}

/// Asks the ENGINE whether this function's signature is rejected outright.
///
/// A file that cannot be read or parsed yields `None` — the normal pipeline
/// then reports that failure itself; this helper never invents one.
fn static_signature_rejection_for(func: &AnnotatedFunction) -> Option<String> {
    let source = fs::read_to_string(&func.file_path).ok()?;
    trust_vc_core::static_signature_rejection(&source, &func.name)
}

/// Returns true if the function has contracts extractable by vc_extraction
/// (requires/ensures/contract attributes or body assertions).
fn has_extractable_contracts(func: &AnnotatedFunction) -> bool {
    func.attributes
        .iter()
        .any(|attr| attr == "requires" || attr == "ensures" || attr == "contract")
}

/// Verifies a trait-impl CONFORMANCE obligation, addressed by name.
///
/// A function's verdict covers only its OWN obligations — it no longer inherits
/// a sibling impl's conformance verdict (ATTRIBUTION, see
/// the internal conformance-attribution design note). So this is the ONLY
/// channel through which a non-conforming impl is reported, and it must fail
/// closed: an obligation that cannot be built or addressed comes back
/// `Unknown`/`Error`, never `Verified`.
///
/// POINTER WIDTH is decided by the LIBRARY, not here. This lane used to install
/// only `install_pointer_width_for` — the pinned `global size_of usize`
/// directive, and otherwise nothing, leaving the host's 64-bit `usize` in force
/// — while the FUNCTION lane below routed through [`width_plan_for`] /
/// [`run_under_width_plan`]. Same file, two lanes, one of them blind to 32-bit:
/// an impl that violates its trait `ensures` at a 32-bit `usize` came back
/// `verified`. `trust_vc_core::verify_trait_conformance_obligation` now owns the
/// full plan (pinned / host / dual), so this call needs no guard of its own —
/// and must not install one, or it would pin a width the plan did not choose.
fn verify_conformance_obligation(
    func: &AnnotatedFunction,
) -> (
    VerdictKind,
    Option<String>,
    Vec<CounterexampleBinding>,
    ObligationStatus,
    Option<String>,
) {
    let Some(path) = func.file_path.to_str() else {
        return (
            VerdictKind::Error,
            Some(format!(
                "cannot verify trait conformance in non-UTF-8 path {}",
                func.file_path.display()
            )),
            Vec::new(),
            ObligationStatus::Error,
            None,
        );
    };
    match trust_vc_core::verify_trait_conformance_obligation(path, &func.name) {
        Ok(result) => {
            let (verdict, detail, bindings) = verdict_from_result(&result);
            let (status, unknown_category) = obligation_status_from_verify_result(&result);
            (verdict, detail, bindings, status, unknown_category)
        }
        Err(err) => (
            VerdictKind::Error,
            Some(err.to_string()),
            Vec::new(),
            ObligationStatus::Error,
            None,
        ),
    }
}

/// The certificate status of an obligation whose verdict IS one whole
/// `VerifyResult`.
///
/// [`verdict_from_result`] maps a model-less incompleteness onto
/// `VerdictKind::Counterexample`, because the gate's `counterexample`
/// expectation means "assert_fails" and not "a model exists". That is the right
/// answer for the FUNCTION verdict and the wrong one for the OBLIGATION status:
/// the certificate must say the solver found no model, or the corpus gate can
/// spend a non-decision as the one refutation `assert_one_fails` requires. So
/// this reads the result directly instead of the verdict it was folded into.
fn obligation_status_from_verify_result(
    result: &VerifyResult,
) -> (ObligationStatus, Option<String>) {
    let unknown_category = result
        .unknown_category()
        .map(|category| format!("{category:?}").to_ascii_lowercase());
    let status = match result {
        VerifyResult::Verified => ObligationStatus::Verified,
        VerifyResult::Counterexample { .. } => ObligationStatus::Counterexample,
        VerifyResult::NotProved { .. } => ObligationStatus::NotProved,
        VerifyResult::Unknown { .. } => ObligationStatus::Unknown,
        VerifyResult::Error { .. } => ObligationStatus::Error,
        _ => ObligationStatus::Uncaptured,
    };
    (status, unknown_category)
}

/// Reason reported for a bodyless trait method declaration. It is a SKIP, not a
/// pass: nothing about this item was proven, and the reader is pointed at the
/// obligations that do carry the weight.
const TRAIT_DECLARATION_SKIP_DETAIL: &str =
    "trait method declaration (no default body) — nothing to verify at the declaration; its \
     contract is discharged by the per-impl `trait impl conformance` obligations and assumed at \
     call sites";

/// The EXACT source line of `func`'s signature identifier, as the file scan
/// recorded it (`sig.ident.span().start().line`).
///
/// Every [`AnnotatedFunction`] that reaches a body-verifying path comes from
/// `scan::extract_from_items`, which stores that span line verbatim; the only
/// synthetic-`line` targets are trait-conformance obligations, and both
/// verifying entry points return those before they ever get here. So this is
/// real lexical provenance, and passing it lets the resolver name ONE item
/// instead of guessing among same-named ones.
///
/// This returns `Some` for every target the CLI has, because every target the
/// CLI has came from the scan. The `Option` is not hedging — it is the type that
/// makes [`find_target_function`] state a REQUIREMENT rather than an assumption:
/// a caller with no provenance must say so and take the fail-closed bare-name
/// gate. `trust_vc_core::verify_function_from_file`, the library entry a human's
/// bare name reaches, is exactly such a caller and still refuses an ambiguous
/// name. Collapsing this to a plain `usize` would let a future caller pass a
/// made-up line and silently get the wrong item.
fn provenance_line(func: &AnnotatedFunction) -> Option<usize> {
    Some(func.line)
}

/// Turn a scanned-but-unverified function into its report entry.
///
/// The verifier never runs here — there is nothing to run. What matters is that
/// the entry EXISTS, carrying the scan's reason, so the function is visible in
/// the report instead of being dropped between the scan and the summary.
pub fn not_analyzed_verdict(entry: &crate::scan::UnanalyzedFunction) -> FunctionVerdict {
    FunctionVerdict {
        function: AnnotatedFunction {
            file_path: entry.file_path.clone(),
            name: entry.name.clone(),
            line: entry.line,
            attributes: Vec::new(),
        },
        result: VerdictKind::NotAnalyzed,
        duration_ms: 0,
        detail: Some(entry.reason.clone()),
        localized_failure: None,
        bindings: Vec::new(),
    }
}

/// Verifies a single annotated function. Returns a verdict with timing.
pub fn verify_one(func: &AnnotatedFunction) -> FunctionVerdict {
    // SIGNATURE-level rejections come first here for the SAME reason they come
    // first in `verify_one_detailed`: Verus applies them at lowering, before
    // contract extraction and before the contract-free SKIP below. This is the
    // user-facing lane (`cargo trust-vc check`); without this consult it would
    // report `Skipped` for a construct the gate lane reports as an error, and
    // the two lanes would disagree about the same file.
    if let Some(detail) = static_signature_rejection_for(func) {
        return FunctionVerdict {
            function: func.clone(),
            result: VerdictKind::Error,
            duration_ms: 0,
            detail: Some(detail),
            localized_failure: None,
            bindings: Vec::new(),
        };
    }
    if crate::scan::is_trait_conformance_target(func) {
        let start = Instant::now();
        let (result, detail, bindings, _status, _unknown_category) =
            verify_conformance_obligation(func);
        return FunctionVerdict {
            function: func.clone(),
            result,
            duration_ms: u64::try_from(start.elapsed().as_millis()).unwrap_or(u64::MAX),
            detail,
            localized_failure: None,
            bindings,
        };
    }
    if crate::scan::is_trait_declaration_target(func) {
        return FunctionVerdict {
            function: func.clone(),
            result: VerdictKind::Skipped,
            duration_ms: 0,
            detail: Some(TRAIT_DECLARATION_SKIP_DETAIL.into()),
            localized_failure: None,
            bindings: Vec::new(),
        };
    }
    if !has_extractable_contracts(func) {
        return FunctionVerdict {
            function: func.clone(),
            result: VerdictKind::Skipped,
            duration_ms: 0,
            detail: Some(
                "no requires/ensures/contract attributes — full verification requires test mode"
                    .into(),
            ),
            localized_failure: None,
            bindings: Vec::new(),
        };
    }

    // `verify_result_for` holds the pointer-width guard across extraction AND
    // verification, and runs the unit at EVERY width its `WidthPlan` requires,
    // so this path agrees with `verify_one_detailed` and with the library's
    // `verify_function_from_file`.
    let start = Instant::now();
    let (result_kind, detail, cx_bindings) =
        match verify_result_for(&func.file_path, &func.name, provenance_line(func)) {
            Ok(result) => verdict_from_result(&result),
            Err(err) => (VerdictKind::Error, Some(err), Vec::new()),
        };

    FunctionVerdict {
        function: func.clone(),
        result: result_kind,
        duration_ms: u64::try_from(start.elapsed().as_millis()).unwrap_or(u64::MAX),
        detail,
        localized_failure: None,
        bindings: cx_bindings,
    }
}

/// Verifies a single annotated function and keeps obligation-level metadata.
pub fn verify_one_detailed(func: &AnnotatedFunction) -> FunctionVerification {
    // SIGNATURE-level rejections come first, exactly as Verus applies them at
    // lowering: before contract extraction, before the contract-free SKIP
    // below, and before any body work. The rule and its message live in the
    // engine (`trust_vc_core::static_signature_rejection`); this lane only
    // reports what the engine answered.
    if let Some(detail) = static_signature_rejection_for(func) {
        return FunctionVerification {
            verdict: FunctionVerdict {
                function: func.clone(),
                result: VerdictKind::Error,
                duration_ms: 0,
                detail: Some(detail),
                localized_failure: None,
                bindings: Vec::new(),
            },
            source_hash: source_hash(&func.file_path),
            warnings: Vec::new(),
            obligations: Vec::new(),
            report: None,
            #[cfg(feature = "proof-certificates")]
            proof_alethe: None,
            #[cfg(feature = "proof-certificates")]
            proof_strict_verified: None,
        };
    }
    if crate::scan::is_trait_conformance_target(func) {
        let start = Instant::now();
        let source_hash = source_hash(&func.file_path);
        // The status comes from the `VerifyResult` itself, NOT from the verdict
        // it was folded into: `verdict_from_result` deliberately reports a
        // model-less incompleteness as `Counterexample` (the gate's
        // "assert_fails" label), and reading the status off that verdict would
        // stamp a refutation the solver never produced.
        let (result, detail, bindings, status, unknown_category) =
            verify_conformance_obligation(func);
        return FunctionVerification {
            verdict: FunctionVerdict {
                function: func.clone(),
                result,
                duration_ms: u64::try_from(start.elapsed().as_millis()).unwrap_or(u64::MAX),
                detail,
                localized_failure: None,
                bindings,
            },
            source_hash,
            warnings: Vec::new(),
            // The obligation IS the target: one entry, carrying its verdict, so a
            // certificate can never claim a conformance obligation it did not check.
            obligations: vec![ObligationVerification {
                name: func.name.clone(),
                kind: "trait_conformance".to_string(),
                location: None,
                // A conformance obligation is raised from the trait and impl
                // DECLARATIONS by the encoder's own walk, not from a statement
                // the extractor visits, so there is no span to record.
                source_location: None,
                condition_hash: sha256_hex(&func.name),
                status,
                unknown_category,
            }],
            report: None,
            #[cfg(feature = "proof-certificates")]
            proof_alethe: None,
            #[cfg(feature = "proof-certificates")]
            proof_strict_verified: None,
        };
    }
    if crate::scan::is_trait_declaration_target(func) {
        return FunctionVerification {
            verdict: FunctionVerdict {
                function: func.clone(),
                result: VerdictKind::Skipped,
                duration_ms: 0,
                detail: Some(TRAIT_DECLARATION_SKIP_DETAIL.into()),
                localized_failure: None,
                bindings: Vec::new(),
            },
            source_hash: source_hash(&func.file_path),
            warnings: Vec::new(),
            obligations: Vec::new(),
            report: None,
            #[cfg(feature = "proof-certificates")]
            proof_alethe: None,
            #[cfg(feature = "proof-certificates")]
            proof_strict_verified: None,
        };
    }
    if !has_extractable_contracts(func) {
        return FunctionVerification {
            verdict: FunctionVerdict {
                function: func.clone(),
                result: VerdictKind::Skipped,
                duration_ms: 0,
                detail: Some(
                    "no requires/ensures/contract attributes — full verification requires test mode"
                        .into(),
                ),
                localized_failure: None,
                bindings: Vec::new(),
            },
            source_hash: source_hash(&func.file_path),
            warnings: Vec::new(),
            obligations: Vec::new(),
            report: None,
            #[cfg(feature = "proof-certificates")]
            proof_alethe: None,
            #[cfg(feature = "proof-certificates")]
            proof_strict_verified: None,
        };
    }

    let start = Instant::now();
    let source_hash = source_hash(&func.file_path);

    #[cfg(feature = "proof-certificates")]
    let mut proof_alethe: Option<String> = None;
    #[cfg(feature = "proof-certificates")]
    let mut proof_strict_verified: Option<bool> = None;

    let mut warnings: Vec<String> = Vec::new();
    let (result_kind, detail, localized_failure, cx_bindings, obligations, captured_report) =
        match load_context_and_report(&func.file_path, &func.name, provenance_line(func)) {
            Ok((ctx, report)) => {
                let obligations = collect_obligation_verifications(&ctx, &report);
                let localized_failure = localized_failure_from_report(&report);
                warnings = ctx.warnings().to_vec();
                let (kind, detail, bindings) = verdict_from_result(report.result());
                #[cfg(feature = "proof-certificates")]
                if let Some(proof) = report.proof() {
                    proof_alethe = Some(proof.alethe().to_string());
                    proof_strict_verified = Some(proof.strict_verified());
                }
                (
                    kind,
                    detail,
                    localized_failure,
                    bindings,
                    obligations,
                    Some(report),
                )
            }
            Err(err) => (
                VerdictKind::Error,
                Some(err),
                None,
                Vec::new(),
                Vec::new(),
                None,
            ),
        };

    FunctionVerification {
        verdict: FunctionVerdict {
            function: func.clone(),
            result: result_kind,
            duration_ms: u64::try_from(start.elapsed().as_millis()).unwrap_or(u64::MAX),
            detail,
            localized_failure,
            bindings: cx_bindings,
        },
        source_hash,
        warnings,
        obligations,
        report: captured_report,
        #[cfg(feature = "proof-certificates")]
        proof_alethe,
        #[cfg(feature = "proof-certificates")]
        proof_strict_verified,
    }
}

/// Reads `file_path` and, if it declares a `global size_of usize == N` directive
/// (Verus surface syntax for pinning the verification target's pointer width),
/// installs the corresponding thread-local width override and returns its guard.
///
/// The guard MUST be held across BOTH VC extraction and verification so that
/// width-dependent obligations (e.g. `usize` shift bounds) and their discharge
/// agree — mirroring `verify_function_from_file` (vc_extraction.rs). Returns
/// `None` when there is no valid directive, leaving the host width in effect
/// (so non-directive files are byte-identical in behavior). A malformed
/// directive installs no guard; the unstripped line then fails to parse
/// downstream, surfacing as an error (fail-closed).
///
/// TEST-ONLY since the conformance lane stopped calling it. It was the ONLY
/// width handling that lane had — a directive-or-nothing install with no
/// dual-width plan, which is what let a 32-bit-false conformance obligation
/// report `verified` on a 64-bit host. The plan now lives entirely in
/// `trust_vc_core::verify_trait_conformance_obligation`, so re-introducing a
/// production call here would pin a width the plan did not choose. The
/// directive-scan/guard-drop contract it asserts is still pinned by
/// `corpus_path_applies_pointer_width_directive`.
#[cfg(test)]
fn install_pointer_width_for(file_path: &Path) -> Option<trust_vc_core::ir::PointerWidthGuard> {
    let source = fs::read_to_string(file_path).ok()?;
    trust_vc_core::ir::scan_pointer_width_directive(&source)
        .ok()
        .flatten()
}

/// The pointer width(s) a unit must be verified at.
///
/// This mirrors, one for one, the dispatch that `trust_vc_core`'s
/// `verify_function_from_file` performs (`vc_extraction.rs`, #2778 dual-arch).
/// Before this existed the CLI ran exactly ONE width — the host's — so a
/// width-polymorphic unit that is true on a 64-bit `usize` and FALSE on a
/// 32-bit `usize` came back `verified` from `cargo trust-vc check` while the
/// library entry point reported a counterexample for the same bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WidthPlan {
    /// No `global size_of usize` directive and nothing width-dependent in the
    /// unit: verify once at the host width, with no override installed. This is
    /// byte-identical to the pre-dual-width behavior (one solve, no guard).
    Host,
    /// A `global size_of usize == N` directive pins the target architecture:
    /// verify exactly once, at that width.
    Pinned(u32),
    /// No directive, but the unit's proof depends on the pointer width. Rust
    /// permits both a 32-bit and a 64-bit `usize`, so the proof is sound only
    /// if it discharges at BOTH.
    Dual,
}

/// Decides the [`WidthPlan`] for `func` in `file_path`, whose (sibling-augmented)
/// AST is `ast`.
///
/// A pinned directive wins. Otherwise the decision is delegated, VERBATIM, to
/// the library's `trust_vc_core::ir::unit_is_pointer_width_polymorphic` — the
/// single implementation both entry points share. It used to be hand-copied
/// here, and the copy drifted: it lost the numeric-literal-suffix arm, so a unit
/// whose only `usize` was `4294967295usize` planned ONE host-width solve and
/// came back `verified` from the CLI while the library refuted it.
///
/// `ast` matters as much as `func`. The predicate needs the whole file because
/// `usize` reaches a unit through a type alias, a nested alias or a struct field
/// without ever appearing as a token inside the function. `load_ast` has already
/// merged the crate's sibling type definitions into `ast`, so those routes are
/// covered here too.
///
/// A malformed directive yields [`WidthPlan::Host`] deliberately: that is the
/// pre-existing fail-closed route, where the unstripped directive line survives
/// into the parse and surfaces as an error verdict rather than a proof.
fn width_plan_for(file_path: &Path, ast: &syn::File, func: &syn::ItemFn) -> WidthPlan {
    let pinned = fs::read_to_string(file_path)
        .ok()
        .and_then(|source| trust_vc_core::ir::scan_pointer_width_directive(&source).ok())
        .and_then(trust_vc_core::ir::pinned_width_from_guard);
    match pinned {
        Some(width) => WidthPlan::Pinned(width),
        None if trust_vc_core::ir::unit_is_pointer_width_polymorphic(Some(ast), func) => {
            WidthPlan::Dual
        }
        None => WidthPlan::Host,
    }
}

/// Runs `pass` once per pointer width required by `plan`, holding the matching
/// [`trust_vc_core::ir::PointerWidthGuard`] across the WHOLE pass (extraction
/// bakes usize/isize widths into the IR, and verification reads them back — the
/// two must agree).
///
/// For [`WidthPlan::Dual`] a `Verified` outcome requires BOTH widths to
/// discharge: the 32-bit pass runs first and, if it does not verify, its
/// outcome is returned as-is (fail-closed short circuit); only when 32-bit
/// verifies does the 64-bit pass decide. So this can only ever ADD rejections
/// relative to a single host-width run — it can never turn a non-verifying unit
/// into a verified one.
///
/// The surfaced outcome is the failing width's own, UNTAGGED. `trust-vc-core`
/// additionally suffixes the obligation name with `_32bit`/`_64bit`; the CLI
/// cannot do the same for the report path because `VerificationReport` is not
/// constructible outside its crate. Tagging is a reporting nicety, not a
/// soundness property, and is left as a follow-up.
fn run_under_width_plan<T>(
    plan: WidthPlan,
    mut pass: impl FnMut() -> Result<T, String>,
    is_verified: impl Fn(&T) -> bool,
) -> Result<T, String> {
    match plan {
        WidthPlan::Host => pass(),
        WidthPlan::Pinned(width) => {
            let _guard = trust_vc_core::ir::PointerWidthGuard::install(width);
            pass()
        }
        WidthPlan::Dual => {
            let at_32 = {
                let _guard = trust_vc_core::ir::PointerWidthGuard::install(32);
                pass()?
            };
            if !is_verified(&at_32) {
                return Ok(at_32);
            }
            let _guard = trust_vc_core::ir::PointerWidthGuard::install(64);
            pass()
        }
    }
}

fn load_context_and_report(
    file_path: &Path,
    func_name: &str,
    at_line: Option<usize>,
) -> Result<(VerificationContext, VerificationReport), String> {
    let (ast, siblings) = load_ast(file_path)?;
    let func = find_target_function(&ast, file_path, func_name, at_line)?;
    run_under_width_plan(
        width_plan_for(file_path, &ast, func),
        || {
            let ctx = context_from_func(&ast, &siblings, file_path, func)?;
            let report = ctx.verify_with_report(VerificationReportOptions::new());
            Ok((ctx, report))
        },
        |(_, report)| report.result().is_verified(),
    )
}

/// Verifies `func_name` in `file_path` under its [`WidthPlan`], returning the
/// raw [`VerifyResult`]. The result-only twin of [`load_context_and_report`];
/// both must route through [`run_under_width_plan`] or the CLI's two entry
/// points disagree with each other as well as with the library.
fn verify_result_for(
    file_path: &Path,
    func_name: &str,
    at_line: Option<usize>,
) -> Result<VerifyResult, String> {
    let (ast, siblings) = load_ast(file_path)?;
    let func = find_target_function(&ast, file_path, func_name, at_line)?;
    run_under_width_plan(
        width_plan_for(file_path, &ast, func),
        || Ok(context_from_func(&ast, &siblings, file_path, func)?.verify()),
        VerifyResult::is_verified,
    )
}

/// Reads, directive-strips, parses and sibling-augments `file_path`, and
/// returns with it what core must know about the copied items
/// ([`trust_vc_core::crate_sibling_view`]).
///
/// Parsing is pointer-width INDEPENDENT, so a dual-width verification parses
/// once and re-extracts per width; only extraction and verification sit inside
/// a [`trust_vc_core::ir::PointerWidthGuard`].
fn load_ast(file_path: &Path) -> Result<(syn::File, CrateSiblingView), String> {
    let source = fs::read_to_string(file_path).map_err(|err| err.to_string())?;
    // Strip the `global size_of usize == N` directive before parsing (it is not
    // valid Rust at item position); the width it declares is installed by the
    // caller's width guard. Offsets are preserved.
    let source = trust_vc_core::ir::strip_pointer_width_directives(&source);
    let mut ast = parse_file_allow_tracked(&source).map_err(|err| err.to_string())?;
    // The verifier resolves user datatypes (enums/structs/type aliases) from the
    // items of the single parsed file. A function in `sls.rs` that matches over
    // `crate::types::PbRel` therefore cannot lower its `PbRel::Ge` / `PbRel::Eq`
    // arms unless the `PbRel` definition is in scope. Bring the crate's other
    // source-file type definitions into the file AST so cross-file types resolve.
    // This only adds the REAL definitions the function legitimately references —
    // it enriches the type environment, never the proof obligation — and the
    // function's own file keeps precedence on name collisions.
    let siblings = augment_with_sibling_type_defs(file_path, &mut ast);
    Ok((ast, siblings))
}

/// Locates the requested function through trust-vc-core's SHARED resolver.
///
/// The CLI used to carry its own copy of this walk whose comment claimed to
/// match the core logic; it did not. The copy returned the FIRST source-order
/// match, so in a file with two same-named methods it verified one body and
/// contract and reported that verdict under the other's name — a false verify
/// when the first candidate happened to be the sound one. There is now exactly
/// one resolver, and an ambiguous name is REPORTED rather than silently
/// resolved: naming several functions at once has no single true verdict.
fn find_target_function<'a>(
    ast: &'a syn::File,
    file_path: &Path,
    func_name: &str,
    at_line: Option<usize>,
) -> Result<&'a syn::ItemFn, String> {
    // The failure strings live in trust-vc-core next to the resolver, so the CLI
    // and the library gate report the SAME reason for the SAME file. They had
    // already drifted: this arm reported ambiguity while `verify_function_from_file`
    // reported "not found" for the identical input.
    //
    // `at_line` is the caller's EXACT lexical provenance. The file scan records
    // each annotated function's ident line, so when it asks for a verdict it is
    // naming one item, not a name. Re-asking by bare name discarded that and
    // manufactured ambiguity: a file with `impl G for P` and `impl G for Q`
    // failed BOTH `w` methods as "2 definitions share that name" even though
    // each scan target denoted exactly one of them. A bare `--function NAME`
    // from a human has no such provenance and keeps the fail-closed
    // ambiguity gate.
    match at_line {
        Some(line) => trust_vc_core::resolve_function_at_line(ast, func_name, line)
            .require_unique(func_name, file_path.display()),
        None => trust_vc_core::resolve_function_in_file(ast, func_name)
            .require_unique(func_name, file_path.display()),
    }
}

/// Extracts the verification context for an already-located `func`.
///
/// Width-DEPENDENT: `usize`/`isize` bounds are baked into the IR here, so this
/// must run under the same guard as the `verify()` that consumes it.
fn context_from_func(
    ast: &syn::File,
    siblings: &CrateSiblingView,
    file_path: &Path,
    func: &syn::ItemFn,
) -> Result<VerificationContext, String> {
    // LOCATED in `file_path`: `load_ast` parses the source after only the
    // offset-preserving `strip_pointer_width_directives`, so a span's line is
    // that file's line. This is the lane the whole ported corpus runs through,
    // and it is why a refuted obligation can now answer WHERE.
    let mut ctx = match file_path.to_str() {
        Some(path) => trust_vc_core::extract_verification_conditions_located_in_crate_file(
            ast, func, path, siblings,
        ),
        // A non-UTF-8 path cannot be rendered into a `file:line:column` string;
        // verify without locations rather than inventing a path. Without the
        // sibling view, the copied type names are read as this file's own,
        // which refuses at least as much.
        None => extract_verification_conditions_with_file_context(ast, func),
    }
    .map_err(|err| err.to_string())?;
    dependency_specs::import_dependency_spec_signatures(file_path, func, &mut ctx)?;
    Ok(ctx)
}

/// Append `enum` / `struct` / `type` alias items defined in the *other* `.rs`
/// files of the same crate `src/` tree into `ast`, so the verifier can resolve
/// datatypes the target function references across files (e.g. a `match` over an
/// enum declared in a sibling module).
///
/// Sound and conservative:
/// - Only type-defining items are imported (no functions, no bodies), so this
///   can never inject or weaken a proof obligation. The impls imported are
///   the headers of each sibling `impl Drop for ..`, `impl PartialEq for ..`
///   and `impl PartialOrd for ..`, with their methods left out: the drop rule
///   refuses a function that can drop a value of that type, since a
///   destructor runs wherever such a value is dropped, in any file; and a
///   comparison of values of that type runs the hand-written impl, which the
///   lowering and the run-time check rule then refuse to read as structural.
/// - The target file's own items stay first, so any same-named local definition
///   keeps precedence in the downstream `or_insert` registries.
/// - The copy drops the scope each item was written in (its file's `use`
///   items and its module path). The returned view, read from the files before
///   the copy, refuses a `Verified` answer where that changes what a spelling
///   denotes, and tells the type-name rule which names the copy brought in.
///   It also refuses one where the files read need not be all the files of
///   the crate: a file under the source directory that cannot be read or
///   parsed, a `mod` whose file does not exist yet ([`missing_module_files`]),
///   the verified file reached under the source directory through a symbolic
///   link, whose modules rustc opens beside the link and the lane beside the
///   file, or a source directory [`crate_src_root`] cannot settle.
fn augment_with_sibling_type_defs(file_path: &Path, ast: &mut syn::File) -> CrateSiblingView {
    let source = match crate_src_root(file_path) {
        Ok(Some(source)) => source,
        Ok(None) => return CrateSiblingView::default(),
        Err(why) => return trust_vc_core::crate_sibling_view(ast, &[], &[why]),
    };
    let target = file_path.canonicalize().ok();
    let mut files: Vec<SiblingFile> = Vec::new();
    let mut unread: Vec<String> = Vec::new();
    collect_sibling_files(
        &source.src,
        &source.src,
        target.as_deref(),
        &mut files,
        &mut unread,
    );
    let target_path = target.unwrap_or_else(|| file_path.to_path_buf());
    let mut declared_modules: BTreeSet<String> = module_names(ast);
    for file in &files {
        declared_modules.extend(module_names(&file.ast));
    }
    unread.extend(missing_module_files(
        &source,
        &target_path,
        ast,
        &declared_modules,
    ));
    for file in &files {
        unread.extend(missing_module_files(
            &source,
            &file.path,
            &file.ast,
            &declared_modules,
        ));
    }
    let siblings: Vec<(String, syn::File)> = files
        .into_iter()
        .map(|file| (file.shown, file.ast))
        .collect();
    let view = trust_vc_core::crate_sibling_view(ast, &siblings, &unread);
    let mut sibling_type_items: Vec<syn::Item> = Vec::new();
    for (_, sibling) in &siblings {
        collect_type_items_from_items(&sibling.items, &mut sibling_type_items);
    }
    ast.items.extend(sibling_type_items);
    view
}

/// What the crate lane reads as one crate.
#[derive(Debug, PartialEq)]
struct CrateSource {
    /// The package's `src` directory, canonical, whose `.rs` files are read.
    src: PathBuf,
    /// The canonical paths of the target roots the manifest names, all under
    /// `src`.
    roots: Vec<PathBuf>,
}

/// The crate the crate lane reads for `file_path`, `Ok(None)` when it reads
/// the file alone, or why no directory can be taken to hold the whole crate.
///
/// The nearest `Cargo.toml` above the file names the package. Its `src`
/// directory is read when the file lies under it, and no directory otherwise:
/// a test, example or build script is a crate root of its own, and a file with
/// no manifest above it belongs to no crate the lane can name. The manifest
/// must not move a target's root out of `src` ([`manifest_target_roots`]), no
/// package further up may have the file under its own `src`, and `src` must
/// not be a module directory a file outside it can declare: with `src/mod.rs`
/// or `src.rs` present, `mod src;` in any root beside `src` (a `[lib]` path,
/// another package's target, the default `build.rs`) makes the files of `src`
/// modules of a crate whose root the lane does not read.
fn crate_src_root(file_path: &Path) -> Result<Option<CrateSource>, String> {
    let path = file_path
        .canonicalize()
        .unwrap_or_else(|_| file_path.to_path_buf());
    let mut manifests = path
        .ancestors()
        .skip(1)
        .filter(|dir| dir.join("Cargo.toml").is_file());
    let Some(package) = manifests.next() else {
        // Without a manifest nothing says which files form the crate, nor
        // where its root is (`#[path = "src/t.rs"] mod t;` in a root beside
        // `src`).
        return Ok(None);
    };
    let src = package.join("src");
    if !path.starts_with(&src) {
        return Ok(None);
    }
    let manifest = package.join("Cargo.toml");
    let text = fs::read_to_string(&manifest)
        .map_err(|err| format!("`{}` cannot be read ({err})", manifest.display()))?;
    let roots = manifest_target_roots(package, &src, &text)
        .map_err(|why| format!("`{}` {why}", manifest.display()))?;
    if let Some(outer) = manifests.find(|dir| path.starts_with(dir.join("src"))) {
        return Err(format!(
            "the file lies under the `src` directories of two packages, `{}` and `{}`",
            package.display(),
            outer.display()
        ));
    }
    for module_file in [src.join("mod.rs"), package.join("src.rs")] {
        if module_file.is_file() {
            return Err(format!(
                "`{}` exists, so `src` can be the module `src` of a crate whose root lies \
                 outside it (`mod src;`)",
                module_file.display()
            ));
        }
    }
    Ok(Some(CrateSource { src, roots }))
}

/// The canonical paths of the target roots that `manifest`, the text of the
/// `Cargo.toml` of `package`, names under `src`, or why the manifest can
/// place a root elsewhere.
///
/// The text is read as TOML, so every spelling of a key reaches the same
/// table: a quoted key (`"path" = ..`), a quoted table header (`["lib"]`), a
/// dotted key in the root table (`lib."path" = ..`) and an escape in a string
/// (`"src/../lib.rs"`). The targets are the `lib` table and each
/// table of `bin`, `example`, `test` and `bench`. Each `path` they give must
/// be a string that names an existing file under `src` once its `.` and `..`
/// segments and symbolic links are resolved. A build script (`build` in the
/// package table) is a crate of its own, as the default `build.rs` beside
/// `src` is, and is a root of `src` only when it lies there. A manifest that
/// does not parse, or a target of another shape, is refused.
///
/// A root under `src` must also be named without a symbolic link in its
/// path ([`linked_component`]). rustc opens the modules of a root in the
/// directory of the path cargo gives it, not of the file a link there
/// resolves to: with `path = "lib.rs"` and `lib.rs` beside the manifest a
/// link to `src/lib.rs`, `mod b;` opens `b.rs` beside the manifest, which
/// the lane does not read.
fn manifest_target_roots(
    package: &Path,
    src: &Path,
    manifest: &str,
) -> Result<Vec<PathBuf>, String> {
    let table: toml::Table = manifest
        .parse()
        .map_err(|err| format!("does not parse as TOML ({err})"))?;
    let shape = |key: &str, what: &str| format!("gives `{key}` a value that is not {what}");
    // Each `path` value of a target, with whether it must lie under `src`.
    let mut paths: Vec<(&toml::Value, bool)> = Vec::new();
    if let Some(lib) = table.get("lib") {
        let lib = lib.as_table().ok_or_else(|| shape("lib", "a table"))?;
        paths.extend(lib.get("path").map(|path| (path, true)));
    }
    for kind in ["bin", "example", "test", "bench"] {
        let Some(targets) = table.get(kind) else {
            continue;
        };
        let targets = targets
            .as_array()
            .ok_or_else(|| shape(kind, "an array of tables"))?;
        for target in targets {
            let target = target
                .as_table()
                .ok_or_else(|| shape(kind, "an array of tables"))?;
            paths.extend(target.get("path").map(|path| (path, true)));
        }
    }
    for package_table in ["package", "project"] {
        let Some(build) = table.get(package_table).and_then(|it| it.get("build")) else {
            continue;
        };
        match build {
            toml::Value::Boolean(_) => {}
            toml::Value::Array(scripts) => paths.extend(scripts.iter().map(|path| (path, false))),
            path => paths.push((path, false)),
        }
    }
    let mut roots = Vec::new();
    for (value, must_lie_in_src) in paths {
        let written = value.as_str().ok_or_else(|| {
            format!(
                "gives a target a `path` of type {}, not a string",
                value.type_str()
            )
        })?;
        match package.join(written).canonicalize() {
            Ok(root) if root.starts_with(src) => {
                if let Some(link) = linked_component(package, Path::new(written)) {
                    return Err(format!(
                        "places a crate root at `{written}` through the symbolic link `{}`, and \
                         rustc opens that root's modules beside the link, where the lane need \
                         not read them",
                        link.strip_prefix(package).unwrap_or(&link).display()
                    ));
                }
                roots.push(root);
            }
            Ok(_) | Err(_) if !must_lie_in_src => {}
            Ok(_) => return Err(format!("places a crate root at `{written}`, outside `src`")),
            Err(err) => {
                return Err(format!(
                    "places a crate root at `{written}`, which does not resolve to a file \
                     ({err})"
                ))
            }
        }
    }
    Ok(roots)
}

/// The first of the paths from `package` down to `written`, a path the
/// manifest of `package` gives, that is a symbolic link; `None` when no part
/// of `written` is one. An absolute `written` is walked from the file system
/// root.
fn linked_component(package: &Path, written: &Path) -> Option<PathBuf> {
    let mut path = package.to_path_buf();
    for component in written.components() {
        path.push(component.as_os_str());
        if matches!(component, std::path::Component::Normal(_))
            && fs::symlink_metadata(&path).is_ok_and(|meta| meta.file_type().is_symlink())
        {
            return Some(path);
        }
    }
    None
}

/// A file of the crate other than the one verified.
struct SiblingFile {
    /// Where the file is, under the canonical `src`.
    path: PathBuf,
    /// The path relative to the directory above `src`, for messages.
    shown: String,
    ast: syn::File,
}

/// `path` relative to the directory above `src_root`, for messages.
fn shown_path(src_root: &Path, path: &Path) -> String {
    src_root
        .parent()
        .and_then(|base| path.strip_prefix(base).ok())
        .unwrap_or(path)
        .display()
        .to_string()
}

/// Parses every module file under `dir` except the target into `out`. A
/// module file is one whose extension is `rs` in any case: rustc opens
/// `b.rs` for `mod b;`, and a case-insensitive file system gives it `B.RS`.
/// A file whose extension is not ASCII is described in `unread`, since such a
/// file system can fold a letter of it to `rs` (`b.rſ`), and so is a file
/// that cannot be read or parsed, and a path other than the target's own at
/// which the target is reached through a symbolic link. A shebang first line,
/// which rustc skips, is read as an empty line ([`without_shebang`]).
fn collect_sibling_files(
    src_root: &Path,
    dir: &Path,
    target_canonical: Option<&Path>,
    out: &mut Vec<SiblingFile>,
    unread: &mut Vec<String>,
) {
    let entries = match fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(err) => {
            unread.push(format!(
                "the directory `{}` cannot be read ({err})",
                shown_path(src_root, dir)
            ));
            return;
        }
    };
    let mut paths: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    paths.sort();
    for path in paths {
        if path.is_dir() {
            collect_sibling_files(src_root, &path, target_canonical, out, unread);
            continue;
        }
        let name = path
            .file_name()
            .map(|name| name.to_string_lossy().into_owned())
            .unwrap_or_default();
        let Some((stem, extension)) = name.rsplit_once('.') else {
            continue;
        };
        if !extension.is_ascii() {
            unread.push(format!(
                "`{}` has an extension that is not ASCII, which a case-insensitive file \
                 system can read as `rs`",
                shown_path(src_root, &path)
            ));
            continue;
        }
        if stem.is_empty() || !extension.eq_ignore_ascii_case("rs") {
            continue;
        }
        // Skip the target file itself — its items are already in the AST.
        // Reached through a symbolic link, it is also a module whose own
        // modules rustc opens beside the link, while the lane reads them
        // beside the file the link resolves to.
        if let (Some(target), Ok(this)) = (target_canonical, path.canonicalize()) {
            if this == target {
                if path != target {
                    unread.push(format!(
                        "`{}` is the verified file reached through a symbolic link, where \
                         rustc opens its modules beside the link",
                        shown_path(src_root, &path)
                    ));
                }
                continue;
            }
        }
        let shown = shown_path(src_root, &path);
        let source = match fs::read_to_string(&path) {
            Ok(source) => source,
            Err(err) => {
                unread.push(format!("`{shown}` cannot be read ({err})"));
                continue;
            }
        };
        match parse_file_allow_tracked(&without_shebang(&source)) {
            Ok(ast) => out.push(SiblingFile { path, shown, ast }),
            Err(err) => unread.push(format!("`{shown}` does not parse ({err})")),
        }
    }
}

/// The name of every `mod` in `file`, inline or not, at any depth.
fn module_names(file: &syn::File) -> BTreeSet<String> {
    #[derive(Default)]
    struct Collect(BTreeSet<String>);
    impl<'ast> syn::visit::Visit<'ast> for Collect {
        fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
            self.0
                .insert(syn::ext::IdentExt::unraw(&item.ident).to_string());
            syn::visit::visit_item_mod(self, item);
        }
    }
    let mut collect = Collect::default();
    syn::visit::Visit::visit_file(&mut collect, file);
    collect.0
}

/// Describes each `mod name;` of `file`, the crate file at `path`, whose file
/// is not where rustc looks for it: `name.rs` or `name/mod.rs` in the module
/// directory of the module that declares it, below the directories of the
/// inline modules around it. A build script can write that file after the
/// lane has read the crate (`mod gen;`), so its items are not read.
///
/// The module directory of `src/a/b.rs` is `src/a/b/`. That of a `mod.rs`,
/// and of a crate root (`src/lib.rs`, `src/main.rs`, a file of `src/bin/`, or
/// a root the manifest names), is its own directory. A root that some `mod`
/// of the crate also declares (`mod main;`) is read both ways. A `mod` in a
/// function body needs a `path` attribute, which rule 0 of
/// [`trust_vc_core::crate_sibling_view`] refuses, and is not read here.
fn missing_module_files(
    source: &CrateSource,
    path: &Path,
    file: &syn::File,
    declared_modules: &BTreeSet<String>,
) -> Vec<String> {
    fn out_of_line(items: &[syn::Item], prefix: &mut Vec<String>, out: &mut Vec<Vec<String>>) {
        for item in items {
            let syn::Item::Mod(module) = item else {
                continue;
            };
            prefix.push(syn::ext::IdentExt::unraw(&module.ident).to_string());
            match &module.content {
                None => out.push(prefix.clone()),
                Some((_, inner)) => out_of_line(inner, prefix, out),
            }
            prefix.pop();
        }
    }
    let mut modules = Vec::new();
    out_of_line(&file.items, &mut Vec::new(), &mut modules);
    let (Some(dir), Some(name), Some(stem)) = (
        path.parent(),
        path.file_name().map(|name| name.to_string_lossy()),
        path.file_stem().map(|stem| stem.to_string_lossy()),
    ) else {
        return Vec::new();
    };
    let named = |dir: Option<&Path>, expected: &str| {
        dir.and_then(Path::file_name)
            .is_some_and(|name| name.to_string_lossy().eq_ignore_ascii_case(expected))
    };
    let in_bin = named(Some(dir), "bin") && dir.parent() == Some(&*source.src);
    let root = source.roots.iter().any(|root| root == path)
        || (dir == source.src
            && (stem.eq_ignore_ascii_case("lib") || stem.eq_ignore_ascii_case("main")))
        || in_bin
        || (stem.eq_ignore_ascii_case("main")
            && named(dir.parent(), "bin")
            && dir.parent().and_then(Path::parent) == Some(&*source.src));
    let mod_rs = name.eq_ignore_ascii_case("mod.rs");
    let mut module_dirs = Vec::new();
    if mod_rs || root {
        module_dirs.push(dir.to_path_buf());
    }
    let declared_as_module = declared_modules
        .iter()
        .any(|module| module.eq_ignore_ascii_case(&stem));
    if !mod_rs && (!root || declared_as_module) {
        module_dirs.push(dir.join(&*stem));
    }
    let shown = |path: &Path| shown_path(&source.src, path);
    let mut missing = Vec::new();
    for module in &modules {
        let Some((leaf, inline)) = module.split_last() else {
            continue;
        };
        for module_dir in &module_dirs {
            let base = inline
                .iter()
                .fold(module_dir.clone(), |base, it| base.join(it));
            let file = base.join(format!("{leaf}.rs"));
            let directory_file = base.join(leaf).join("mod.rs");
            if !file.is_file() && !directory_file.is_file() {
                missing.push(format!(
                    "`{}` declares `mod {leaf}`, and neither `{}` nor `{}` exists",
                    shown(path),
                    shown(&file),
                    shown(&directory_file)
                ));
            }
        }
    }
    missing
}

/// `source` with a shebang first line blanked, as rustc skips it. Only a
/// line whose `#!` is followed at once by a character that cannot start an
/// inner attribute's `[` (`#!/usr/bin/env run`) is blanked; any other `#!`
/// line is left for the parser, which refuses what it cannot read.
fn without_shebang(source: &str) -> std::borrow::Cow<'_, str> {
    let plain = match source.strip_prefix("#!").map(str::as_bytes) {
        Some([b'/', next, ..]) => *next != b'/' && *next != b'*',
        Some([first, ..]) => !first.is_ascii_whitespace() && *first != b'[',
        _ => false,
    };
    if !plain {
        return std::borrow::Cow::Borrowed(source);
    }
    let line_end = source.find('\n').unwrap_or(source.len());
    std::borrow::Cow::Owned(format!("{}{}", " ".repeat(line_end), &source[line_end..]))
}

/// Recursively gather `enum` / `struct` / `type` items (including those nested in
/// inline modules) as standalone top-level items, and each `impl Drop for ..`,
/// `impl PartialEq for ..` and `impl PartialOrd for ..` as an impl with no
/// items.
fn collect_type_items_from_items(items: &[syn::Item], out: &mut Vec<syn::Item>) {
    for item in items {
        match item {
            syn::Item::Enum(_) | syn::Item::Struct(_) | syn::Item::Type(_) => {
                out.push(item.clone());
            }
            syn::Item::Impl(impl_block)
                if impl_block
                    .trait_
                    .as_ref()
                    .and_then(|(_, path, _)| path.segments.last())
                    .is_some_and(|segment| {
                        segment.ident == "Drop"
                            || segment.ident == "PartialEq"
                            || segment.ident == "PartialOrd"
                    }) =>
            {
                let mut header = impl_block.clone();
                header.attrs.clear();
                header.items.clear();
                out.push(syn::Item::Impl(header));
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner)) = &module.content {
                    collect_type_items_from_items(inner, out);
                }
            }
            _ => {}
        }
    }
}

/// Environment switch that makes an obligation fingerprint SELF-DESCRIBING.
///
/// An `obligation_fingerprints` pin in `evals/verus/verus-tests.json` is a
/// sha256 of the obligation's CONDITION TEXT and nothing else, so when the
/// engine changes how it RENDERS a condition the pin goes red with two opaque
/// hashes and no way to tell a rendering change from an encoder regression.
/// (That is exactly how 7d300d66's marker-macro rendering change reached
/// `assert_forall_by.rs` and sat unexplained.) Setting this variable prints
/// every obligation's condition beside the hash it produces, so the next drift
/// is answered by reading two strings instead of by bisecting.
const DUMP_OBLIGATION_CONDITIONS_ENV: &str = "TRUST_VC_DUMP_OBLIGATION_CONDITIONS";

/// The fingerprint written into the evidence report: sha256 of the obligation's
/// condition text. Emits the preimage to stderr when `dump` is set.
fn condition_fingerprint(obligation: &trust_vc_core::vc::ProofObligation, dump: bool) -> String {
    let hash = sha256_hex(obligation.condition());
    if dump {
        eprintln!(
            "trust-vc obligation condition: kind={} name={} location={} fingerprint={} condition={}",
            obligation_kind_name(obligation.kind()),
            obligation.name(),
            obligation.location().unwrap_or("<none>"),
            hash,
            obligation.condition()
        );
    }
    hash
}

fn collect_obligation_verifications(
    ctx: &VerificationContext,
    report: &VerificationReport,
) -> Vec<ObligationVerification> {
    let dump_conditions = std::env::var_os(DUMP_OBLIGATION_CONDITIONS_ENV).is_some();
    let mut steps_by_label: HashMap<String, VecDeque<StepStatus>> = HashMap::new();
    for step in report.steps() {
        steps_by_label
            .entry(step.label().to_string())
            .or_default()
            .push_back(StepStatus {
                condition: step.condition().map(str::to_string),
                location: step.location().map(str::to_string),
                status: step_result_status(step.result()),
                unknown_category: step
                    .unknown()
                    .map(|unknown| format!("{:?}", unknown.category()).to_ascii_lowercase()),
            });
    }

    let mut obligations = ctx
        .obligations()
        .iter()
        .map(|obligation| {
            let label = obligation
                .step_meta()
                .map(|meta| meta.label().to_string())
                .unwrap_or_else(|| obligation.name().to_string());
            let matched_step = match obligation.kind() {
                ObligationKind::Assume
                | ObligationKind::BroadcastAssume
                | ObligationKind::Requires
                | ObligationKind::LoopGuard
                | ObligationKind::PostLoopAssume => None,
                _ => take_matching_step(steps_by_label.get_mut(&label), obligation.location()),
            };

            let (status, location, unknown_category) = match matched_step {
                Some(step) => (
                    step.status,
                    step.location
                        .or_else(|| obligation.location().map(str::to_string)),
                    step.unknown_category,
                ),
                None => {
                    let (status, unknown_category) =
                        fallback_status_for_result(obligation.kind(), &label, report.result());
                    (
                        status,
                        obligation.location().map(str::to_string),
                        unknown_category,
                    )
                }
            };

            ObligationVerification {
                name: label,
                kind: obligation_kind_name(obligation.kind()).to_string(),
                // Carried only when it AGREES with the reported string, so the
                // two channels can never name different lines: a step that
                // supplied its own location wins the string, and the structured
                // half is dropped rather than contradicting it.
                source_location: obligation
                    .source_location()
                    .filter(|structured| location.as_deref() == Some(structured.render().as_str()))
                    .cloned(),
                location,
                condition_hash: condition_fingerprint(obligation, dump_conditions),
                status,
                unknown_category,
            }
        })
        .collect::<Vec<_>>();

    for (label, steps) in steps_by_label {
        for step in steps {
            if !captured_obligation_status(&step.status) {
                continue;
            }
            let condition = step.condition.as_deref().unwrap_or(&label);
            obligations.push(ObligationVerification {
                name: label.clone(),
                kind: "verification_step".to_string(),
                // A leftover STEP carries no obligation record to read a
                // structured position from; the string is all there is.
                source_location: None,
                location: step.location,
                condition_hash: sha256_hex(condition),
                status: step.status,
                unknown_category: step.unknown_category,
            });
        }
    }

    obligations
}

fn take_matching_step(
    queue: Option<&mut VecDeque<StepStatus>>,
    obligation_location: Option<&str>,
) -> Option<StepStatus> {
    let queue = queue?;
    if let Some(location) = obligation_location {
        if let Some(index) = queue
            .iter()
            .position(|step| step.location.as_deref() == Some(location))
        {
            return queue.remove(index);
        }
    }
    queue.pop_front()
}

fn default_status_for_kind(kind: ObligationKind) -> ObligationStatus {
    match kind {
        ObligationKind::Assume
        | ObligationKind::BroadcastAssume
        | ObligationKind::Requires
        | ObligationKind::LoopGuard
        | ObligationKind::PostLoopAssume => ObligationStatus::Assumed,
        ObligationKind::Reveal => ObligationStatus::Skipped,
        _ => ObligationStatus::Uncaptured,
    }
}

fn fallback_status_for_result(
    kind: ObligationKind,
    label: &str,
    result: &VerifyResult,
) -> (ObligationStatus, Option<String>) {
    let default = default_status_for_kind(kind);
    if default != ObligationStatus::Uncaptured {
        return (default, None);
    }

    match result {
        VerifyResult::Verified => (ObligationStatus::Verified, None),
        VerifyResult::Counterexample {
            obligation_name, ..
        } => {
            if obligation_name == label || obligation_name.starts_with(&format!("{label}:")) {
                (ObligationStatus::Counterexample, None)
            } else {
                (ObligationStatus::Uncaptured, None)
            }
        }
        // Per-obligation attribution needs an obligation NAME to match against
        // `label`, and `NotProved` deliberately carries none (its name lives
        // inside `reason`, and guessing by substring would mis-attribute).
        // So it stays `Uncaptured` here — exactly as strong as the `Unknown`
        // arm it replaces — while the function-level verdict still records the
        // failure via `verdict_from_result`. The category is recorded for
        // triage.
        VerifyResult::NotProved { category, .. } | VerifyResult::Unknown { category, .. } => (
            ObligationStatus::Uncaptured,
            Some(format!("{category:?}").to_ascii_lowercase()),
        ),
        VerifyResult::Error { .. } => (ObligationStatus::Uncaptured, None),
        _ => (ObligationStatus::Uncaptured, None),
    }
}

fn obligation_kind_name(kind: ObligationKind) -> &'static str {
    match kind {
        ObligationKind::Assert => "assert",
        ObligationKind::Assume => "assume",
        ObligationKind::BroadcastAssume => "broadcast_assume",
        ObligationKind::Requires => "requires",
        ObligationKind::Ensures => "ensures",
        ObligationKind::MeasureNonNegative => "measure_non_negative",
        ObligationKind::MeasureDecreases => "measure_decreases",
        ObligationKind::LoopInvariant => "loop_invariant",
        ObligationKind::LoopGuard => "loop_guard",
        ObligationKind::InvariantExceptBreak => "invariant_except_break",
        ObligationKind::LoopEnsures => "loop_ensures",
        ObligationKind::AssertBy => "assert_by",
        ObligationKind::Reveal => "reveal",
        ObligationKind::InvariantOpen => "invariant_open",
        ObligationKind::InvariantClose => "invariant_close",
        ObligationKind::Recommends => "recommends",
        ObligationKind::PostLoopAssume => "post_loop_assume",
        _ => "other",
    }
}

fn verdict_from_result(
    result: &VerifyResult,
) -> (VerdictKind, Option<String>, Vec<CounterexampleBinding>) {
    match result {
        VerifyResult::Verified => (VerdictKind::Verified, None, Vec::new()),
        VerifyResult::Counterexample {
            obligation_name,
            location,
            model,
            bindings,
            ..
        } => {
            // NAME and LOCATION are separate fields on the result; the
            // `<name> (at <file:line:col>)` spelling every detail consumer
            // reads is composed HERE, by the renderer, from the two of them.
            // The engine never glues them together — doing so is what broke
            // the name-keyed `proof_note`/`custom_err` channel.
            let subject = match location {
                Some(location) => format!("{obligation_name} (at {location})"),
                None => obligation_name.clone(),
            };
            let detail = match model {
                Some(model) => format!("{subject}: {model}"),
                None => subject,
            };
            (VerdictKind::Counterexample, Some(detail), bindings.clone())
        }
        // Split Unknown by cause (design-unknown-as-failure.md):
        //
        // A genuine theory-INCOMPLETENESS Unknown on a proof obligation (the
        // fact may be valid but the decision procedure cannot decide it —
        // NRA/nonlinear, unsupported fragment, permanently-non-retriable
        // quantifier) is surfaced as a model-less verification FAILURE. This is
        // the conservative reading — we never claim verification we did not
        // achieve — and it matches Verus, which maps Z3's incompleteness
        // `unknown` to `Invalid(None, None, None)` (an assert-fails outcome with
        // no model). We emit NO model and NO bindings: no counterexample is
        // fabricated. It maps to the gate's `counterexample` expectation, which
        // means "assert_fails", not "a model exists".
        //
        // A RESOURCE/timeout Unknown stays `Unknown`: a timeout does not mean
        // the fact is false (more budget might prove it), so reporting it as a
        // failure would be wrong. This category split is the soundness boundary.
        //
        // THE THIRD CATEGORY. `NotProved` is reached by two DIFFERENT
        // diagnoses, and until 2026-09-17 both were rendered with the same
        // "solver incompleteness" line — which told a user whose proof is fine
        // that their proof is wrong. `ModelGateRejected` means ay produced a
        // model, its own independent model-check gate refuted that model, and
        // ay fail-closed. The VERDICT is identical (both categories are
        // `is_incompleteness()`, so both land here and both report
        // `Counterexample`); only the sentence changes. See
        // `docs/ay-defect-2026-09-17-quantified-axiom-family.md`.
        VerifyResult::NotProved { reason, category } => (
            VerdictKind::Counterexample,
            Some(
                if *category == trust_vc_core::UnknownCategory::ModelGateRejected {
                    format!(
                        "not discharged (solver produced a model it could not independently \
                     confirm and fail-closed; NOT a refutation of this proof): {reason}"
                    )
                } else {
                    format!("not discharged (solver incompleteness, no model): {reason}")
                },
            ),
            // NO bindings: the outcome carries no model, and none is invented.
            Vec::new(),
        ),
        VerifyResult::Unknown { reason, .. } => {
            (VerdictKind::Unknown, Some(reason.clone()), Vec::new())
        }
        VerifyResult::Error { message } => (VerdictKind::Error, Some(message.clone()), Vec::new()),
        _ => (
            VerdictKind::Unknown,
            Some("unrecognized verification result".into()),
            Vec::new(),
        ),
    }
}

fn localized_failure_from_report(report: &VerificationReport) -> Option<LocalizedFailure> {
    report
        .first_non_verified_step()
        .map(localized_failure_from_step)
}

fn localized_failure_from_step(step: &trust_vc_core::StepDiagnostic) -> LocalizedFailure {
    LocalizedFailure {
        label: step.label().to_string(),
        phase: step.phase().to_string(),
        location: step.location().map(str::to_string),
        result: verdict_kind_from_step(step.result()),
        duration_ms: u64::try_from(step.elapsed().as_millis()).unwrap_or(u64::MAX),
        unknown_category: step
            .unknown()
            .map(|unknown| format!("{:?}", unknown.category()).to_ascii_lowercase()),
        suggestion: step
            .unknown()
            .map(|unknown| unknown.suggestion().to_string()),
        used_assumptions: step.used_assumptions().to_vec(),
    }
}

fn verdict_kind_from_step(result: StepResultKind) -> VerdictKind {
    match result {
        StepResultKind::Verified => VerdictKind::Verified,
        StepResultKind::Counterexample => VerdictKind::Counterexample,
        // The gate's `counterexample` label means "assert_fails", not "a model
        // exists" — so the model-less incompleteness failure maps onto it.
        StepResultKind::NotProved => VerdictKind::Counterexample,
        StepResultKind::Unknown => VerdictKind::Unknown,
        StepResultKind::Error => VerdictKind::Error,
        StepResultKind::Skipped => VerdictKind::Skipped,
        _ => VerdictKind::Unknown,
    }
}

fn step_result_status(result: StepResultKind) -> ObligationStatus {
    match result {
        StepResultKind::Verified => ObligationStatus::Verified,
        // Attribution is unambiguous here — this status belongs to the very
        // step that produced the result — so the failure is recorded against
        // this obligation. The two failure kinds stay APART: `Counterexample`
        // is a refutation the engine produced, `NotProved` is a model-less
        // non-discharge. Folding `NotProved` onto `Counterexample` (as this
        // arm used to) made the certificate claim a refutation that was never
        // found, and the corpus gate then credited the non-decision as the one
        // failure upstream's `assert_one_fails` requires.
        StepResultKind::Counterexample => ObligationStatus::Counterexample,
        StepResultKind::NotProved => ObligationStatus::NotProved,
        StepResultKind::Unknown => ObligationStatus::Unknown,
        StepResultKind::Error => ObligationStatus::Error,
        StepResultKind::Skipped => ObligationStatus::Skipped,
        _ => ObligationStatus::Uncaptured,
    }
}

fn source_hash(path: &Path) -> Option<String> {
    match fs::read_to_string(path) {
        Ok(source) => Some(sha256_hex(&source)),
        Err(err) => {
            eprintln!(
                "warning: failed to read source for hashing: {}: {}",
                path.display(),
                err,
            );
            None
        }
    }
}

fn sha256_hex(text: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(text.as_bytes());
    let digest = hasher.finalize();
    let mut output = String::with_capacity(7 + digest.len() * 2);
    output.push_str("sha256:");
    for byte in digest {
        output.push_str(&format!("{byte:02x}"));
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    /// The corpus verify path must apply the `global size_of usize == N`
    /// directive: install the declared pointer width across verification and
    /// strip the directive so the file still parses. Before this wiring, a
    /// directive file failed to parse (error "expected `!`") and yielded no
    /// verification at all. Part of the #2778 arch-width corpus support.
    #[test]
    fn corpus_path_applies_pointer_width_directive() {
        let dir = std::env::temp_dir().join("trust_vc_corpus_directive_test");
        std::fs::create_dir_all(&dir).expect("create temp dir");
        let path = dir.join("arch32.rs");
        std::fs::write(
            &path,
            "global size_of usize == 4;\nfn demo(x: usize) -> usize { x }\n",
        )
        .expect("write temp file");

        // The directive installs a 32-bit usize width for the verification scope.
        {
            let guard = install_pointer_width_for(&path);
            assert!(guard.is_some(), "directive must install a width guard");
            assert_eq!(
                trust_vc_core::ir::pointer_width(),
                32,
                "usize must be pinned to 32 bits while the guard is held"
            );
        }
        // Dropping the guard restores the host width (no leakage across files).
        assert_eq!(trust_vc_core::ir::pointer_width(), usize::BITS);

        // The directive line no longer breaks the corpus parse (load_context
        // strips it before parse_file_allow_tracked).
        let source = std::fs::read_to_string(&path).unwrap();
        let stripped = trust_vc_core::ir::strip_pointer_width_directives(&source);
        assert!(
            parse_file_allow_tracked(&stripped).is_ok(),
            "directive file must parse after stripping"
        );

        let _ = std::fs::remove_file(&path);
    }

    /// Builds the check target for `name` the way production does — by SCANNING
    /// the file — instead of hand-writing an [`AnnotatedFunction`].
    ///
    /// Hand-written targets in these tests carried the ATTRIBUTE's line while
    /// `scan::extract_from_items` records the signature IDENTIFIER's line. That
    /// disagreement was invisible while the resolver ignored the line and looked
    /// the function up by bare name. Now that the line SELECTS the item, a test
    /// that invents one is testing a target production never produces — so the
    /// tests take theirs from the scanner and cannot drift from it again.
    fn scanned_target(path: &Path, name: &str) -> AnnotatedFunction {
        crate::scan::scan_file(path)
            .into_iter()
            .find(|func| func.name == name)
            .unwrap_or_else(|| panic!("scan should discover `{name}` in {}", path.display()))
    }

    /// Writes `source` to a fresh temp file and returns its path.
    fn temp_source(label: &str, source: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "trust_vc_width_plan_{}_{label}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).expect("create temp dir");
        let path = dir.join(format!("{label}.rs"));
        std::fs::write(&path, source).expect("write temp source");
        path
    }

    fn plan_for(label: &str, source: &str, func_name: &str) -> WidthPlan {
        let path = temp_source(label, source);
        let (ast, _) = load_ast(&path).expect("temp source should parse");
        // `None`: these width-plan fixtures name their functions uniquely, and
        // the helper is handed a bare name with no scan behind it — which is
        // precisely the case the bare-name resolver is for.
        let func =
            find_target_function(&ast, &path, func_name, None).expect("target fn should be found");
        let plan = width_plan_for(&path, &ast, func);
        let _ = std::fs::remove_file(&path);
        plan
    }

    /// NARROWNESS PIN (FV-3): a unit that names neither `usize` nor `isize` is
    /// width-invariant, so it must stay on the single-solve host-width path —
    /// no guard installed, no second solve, verdict byte-identical to the
    /// pre-dual-width CLI. This is the pin that stops the dual-width fix from
    /// degenerating into "solve everything twice".
    #[test]
    fn non_width_polymorphic_unit_plans_a_single_host_solve() {
        assert_eq!(
            plan_for(
                "invariant",
                "#[trust_vc::ensures(result >= x)]\nfn dbl_u64(x: u64) -> u64 { x * 2 }\n",
                "dbl_u64",
            ),
            WidthPlan::Host,
        );
    }

    /// The reproducer's shape: naming `usize` anywhere in the unit (signature,
    /// contract attributes or body) forces BOTH widths.
    #[test]
    fn width_polymorphic_unit_plans_both_widths() {
        assert_eq!(
            plan_for(
                "polymorphic",
                "#[trust_vc::ensures(result >= x)]\nfn dbl(x: usize) -> usize { x * 2 }\n",
                "dbl",
            ),
            WidthPlan::Dual,
        );
        // `isize` counts too, and so does a mention that appears only in the
        // contract attribute rather than the signature.
        assert_eq!(
            plan_for(
                "isize_body",
                "#[trust_vc::ensures(result >= x)]\nfn widen(x: i32) -> i64 { x as isize as i64 }\n",
                "widen",
            ),
            WidthPlan::Dual,
        );
    }

    /// FV-2 REGRESSION — the plan selector must see `usize` that reaches the
    /// unit through a definition, not just through a token inside it.
    ///
    /// Every source below has NO `usize`/`isize` token in the function itself,
    /// so the old unit-local token scan planned [`WidthPlan::Host`] and the
    /// 32-bit pass that refutes never ran. Each of these programs is FALSE at a
    /// 32-bit `usize` (measured: pinning `global size_of usize == 4` yields a
    /// counterexample for all of them), so `Host` here is a false verify.
    #[test]
    fn width_reaching_the_unit_through_a_definition_plans_both_widths() {
        // Type alias.
        assert_eq!(
            plan_for(
                "alias",
                "type Idx = usize;\n#[trust_vc::ensures(result >= x)]\nfn dbl(x: Idx) -> Idx { x * 2 }\n",
                "dbl",
            ),
            WidthPlan::Dual,
        );
        // NESTED alias — one hop further from any `usize` token.
        assert_eq!(
            plan_for(
                "nested_alias",
                "type Idx = usize;\ntype Idx2 = Idx;\n#[trust_vc::ensures(result >= x)]\nfn dbl(x: Idx2) -> Idx2 { x * 2 }\n",
                "dbl",
            ),
            WidthPlan::Dual,
        );
        // `isize` through an alias.
        assert_eq!(
            plan_for(
                "alias_isize",
                "type SIdx = isize;\n#[trust_vc::ensures(result >= x)]\nfn dbl(x: SIdx) -> SIdx { x * 2 }\n",
                "dbl",
            ),
            WidthPlan::Dual,
        );
        // Struct FIELD.
        assert_eq!(
            plan_for(
                "struct_field",
                "struct H { n: usize }\n#[trust_vc::requires(h.n <= 100)]\nfn f(h: H) { assert!(h.n * 2 >= h.n); }\n",
                "f",
            ),
            WidthPlan::Dual,
        );
        // Numeric literal SUFFIX. This arm existed in the library copy and was
        // missing from the CLI's hand-copied one — the drift that made
        // `(4294967295usize + 1) as u64` verify from `cargo trust-vc check`
        // while the library refuted the same bytes.
        assert_eq!(
            plan_for(
                "literal_suffix",
                "#[trust_vc::ensures(result == 4294967296)]\nfn f() -> u64 { (4294967295usize + 1) as u64 }\n",
                "f",
            ),
            WidthPlan::Dual,
        );
    }

    /// A file whose definitions we cannot see is treated as width-dependent:
    /// an out-of-line `mod m;` and a crate-local `use` both name items that are
    /// not in this file's tokens, so a `usize` may hide behind either.
    #[test]
    fn unresolvable_module_scope_plans_both_widths() {
        assert_eq!(
            plan_for(
                "out_of_line_mod",
                "mod helper;\n#[trust_vc::ensures(result >= x)]\nfn dbl(x: u64) -> u64 { x * 2 }\n",
                "dbl",
            ),
            WidthPlan::Dual,
        );
        assert_eq!(
            plan_for(
                "crate_local_use",
                "use crate::helper::Idx;\n#[trust_vc::ensures(result >= x)]\nfn dbl(x: u64) -> u64 { x * 2 }\n",
                "dbl",
            ),
            WidthPlan::Dual,
        );
    }

    /// NARROWNESS PIN — the widened scan must not swallow every import. A `use`
    /// of an EXTERNAL crate names items that are never resolved into the type
    /// environment (they fail closed on their own), so it must NOT by itself
    /// force a second solve; and an inline `mod { .. }` IS in the file's tokens,
    /// so a width-invariant one stays on the single-solve path.
    #[test]
    fn external_import_and_inline_module_stay_on_the_host_plan() {
        assert_eq!(
            plan_for(
                "external_use",
                "use std::collections::BTreeMap;\n#[trust_vc::ensures(result >= x)]\nfn dbl(x: u64) -> u64 { x * 2 }\n",
                "dbl",
            ),
            WidthPlan::Host,
        );
        assert_eq!(
            plan_for(
                "inline_mod",
                "mod helper { pub struct H { pub n: u32 } }\n#[trust_vc::ensures(result >= x)]\nfn dbl(x: u64) -> u64 { x * 2 }\n",
                "dbl",
            ),
            WidthPlan::Host,
        );
        // ...but an inline module that DOES carry a `usize` is caught, because
        // its body is part of the file's token stream.
        assert_eq!(
            plan_for(
                "inline_mod_usize",
                "mod helper { pub struct H { pub n: usize } }\n#[trust_vc::ensures(result >= x)]\nfn dbl(x: u64) -> u64 { x * 2 }\n",
                "dbl",
            ),
            WidthPlan::Dual,
        );
    }

    /// An explicit `global size_of usize == N` directive pins the target arch,
    /// so a width-polymorphic unit is verified ONCE at the declared width. The
    /// dual path must not override the directive.
    #[test]
    fn pinned_directive_overrides_the_dual_plan() {
        assert_eq!(
            plan_for(
                "pinned",
                "global size_of usize == 4;\n#[trust_vc::ensures(result >= x)]\nfn dbl(x: usize) -> usize { x * 2 }\n",
                "dbl",
            ),
            WidthPlan::Pinned(32),
        );
        // Reading the directive must not leak an override past the scan.
        assert_eq!(trust_vc_core::ir::pointer_width(), usize::BITS);
    }

    #[cfg(feature = "named-assertions")]
    use std::sync::MutexGuard;
    #[cfg(feature = "named-assertions")]
    use trust_vc_core::env::{lock_env, ScopedEnvVar};
    #[cfg(feature = "named-assertions")]
    use trust_vc_core::ir::TrustVcType;
    #[cfg(feature = "named-assertions")]
    use trust_vc_core::vc::{ProofObligation, VerificationContext};
    #[cfg(feature = "named-assertions")]
    use trust_vc_core::{VerificationReportOptions, VerifyResult};

    /// Disables the VC-level cache for the caller's scope, serialized behind the
    /// process-wide env lock and restored on drop (the `ScopedEnvVar` restores
    /// the previous value before the lock guard releases). Hold the guards for
    /// the test.
    #[cfg(feature = "named-assertions")]
    #[must_use = "hold the returned guards while the VC cache must stay disabled"]
    fn disable_vc_cache() -> (ScopedEnvVar, MutexGuard<'static, ()>) {
        let lock = lock_env();
        let cache = ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
        (cache, lock)
    }

    #[test]
    fn test_skip_proof_only_function() {
        let func = AnnotatedFunction {
            file_path: PathBuf::from("test.rs"),
            name: "lemma".into(),
            line: 1,
            attributes: vec!["proof".into()],
        };
        let verdict = verify_one(&func);
        assert_eq!(verdict.result, VerdictKind::Skipped);
        assert!(verdict.detail.unwrap().contains("test mode"));
        assert!(verdict.localized_failure.is_none());
    }

    #[test]
    fn test_verify_nonexistent_file() {
        let func = AnnotatedFunction {
            file_path: PathBuf::from("/nonexistent/file.rs"),
            name: "foo".into(),
            line: 1,
            attributes: vec!["requires".into(), "ensures".into()],
        };
        let verdict = verify_one(&func);
        assert_eq!(verdict.result, VerdictKind::Error);
        assert!(verdict.detail.is_some());
        assert!(verdict.localized_failure.is_none());
    }

    #[test]
    fn test_verify_one_detailed_collects_obligation_metadata() {
        let source = r#"
            #[ensures(result == x)]
            fn identity(x: i32) -> i32 {
                assert!(x == x);
                x
            }
        "#;
        let path = std::env::temp_dir().join("cargo_trust_vc_identity.rs");
        std::fs::write(&path, source).expect("temp source should be written");

        let func = scanned_target(&path, "identity");
        let verification = verify_one_detailed(&func);

        assert_eq!(verification.verdict.result, VerdictKind::Verified);
        assert!(verification.verdict.localized_failure.is_none());
        assert!(verification
            .source_hash
            .as_deref()
            .is_some_and(|hash| hash.starts_with("sha256:")));

        let statuses: HashMap<_, _> = verification
            .obligations
            .iter()
            .map(|obligation| (obligation.name.as_str(), obligation.status))
            .collect();
        assert_eq!(
            statuses.get("postcondition"),
            Some(&ObligationStatus::Verified)
        );
        assert_eq!(
            statuses.get("assertion_0"),
            Some(&ObligationStatus::Verified)
        );
        assert_eq!(
            statuses.get("return_value"),
            Some(&ObligationStatus::Assumed)
        );

        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn test_verify_one_detailed_keeps_requires_as_assumed() {
        let source = r#"
            #[requires(x > 0)]
            #[ensures(result == x)]
            fn identity(x: i32) -> i32 {
                assert!(x > 0);
                x
            }
        "#;
        let path = std::env::temp_dir().join("cargo_trust_vc_identity_requires.rs");
        std::fs::write(&path, source).expect("temp source should be written");

        let func = scanned_target(&path, "identity");
        let verification = verify_one_detailed(&func);

        assert_eq!(verification.verdict.result, VerdictKind::Verified);
        assert!(verification.verdict.localized_failure.is_none());

        let precondition = verification
            .obligations
            .iter()
            .find(|obligation| obligation.name == "precondition")
            .expect("requires should emit a precondition obligation");
        assert_eq!(precondition.kind, "assume");
        assert_eq!(precondition.status, ObligationStatus::Assumed);

        let postcondition = verification
            .obligations
            .iter()
            .find(|obligation| obligation.name == "postcondition")
            .expect("ensures should emit a postcondition obligation");
        assert_eq!(postcondition.kind, "assert");
        assert_eq!(postcondition.status, ObligationStatus::Verified);

        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn test_verify_one_detailed_accepts_contract_attribute() {
        let source = r#"
            #[trust_vc::contract(
                requires(x > 0),
                ensures(result == x),
                returns(result),
            )]
            fn identity(x: i32) -> i32 {
                assert!(x > 0);
                x
            }
        "#;
        let path = std::env::temp_dir().join("cargo_trust_vc_identity_contract.rs");
        std::fs::write(&path, source).expect("temp source should be written");

        let func = scanned_target(&path, "identity");
        let verification = verify_one_detailed(&func);

        assert_eq!(verification.verdict.result, VerdictKind::Verified);
        assert!(verification.verdict.localized_failure.is_none());

        let precondition = verification
            .obligations
            .iter()
            .find(|obligation| obligation.name == "precondition")
            .expect("contract requires should emit a precondition obligation");
        assert_eq!(precondition.kind, "assume");
        assert_eq!(precondition.status, ObligationStatus::Assumed);

        let postcondition = verification
            .obligations
            .iter()
            .find(|obligation| obligation.name == "postcondition")
            .expect("contract ensures should emit a postcondition obligation");
        assert_eq!(postcondition.kind, "assert");
        assert_eq!(postcondition.status, ObligationStatus::Verified);

        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn test_verify_one_detailed_captures_localized_counterexample() {
        let source = r#"
            #[ensures(result == x + 1)]
            fn broken(x: i32) -> i32 {
                x
            }
        "#;
        let path = std::env::temp_dir().join("cargo_trust_vc_localized_counterexample.rs");
        std::fs::write(&path, source).expect("temp source should be written");

        let func = scanned_target(&path, "broken");
        let verification = verify_one_detailed(&func);

        assert_eq!(verification.verdict.result, VerdictKind::Counterexample);
        let localized = verification
            .verdict
            .localized_failure
            .as_ref()
            .expect("counterexample should record the failing step");
        assert_eq!(localized.label, "postcondition");
        assert_eq!(localized.result, VerdictKind::Counterexample);

        std::fs::remove_file(&path).ok();
    }

    #[cfg(feature = "named-assertions")]
    #[test]
    fn test_localized_failure_carries_used_assumptions_from_report() {
        let _env = disable_vc_cache();

        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
        ctx.push_obligation(ProofObligation::assume("gt_zero", "x > 0"));
        ctx.push_obligation(ProofObligation::assume("lt_zero", "x < 0"));
        ctx.push_obligation(ProofObligation::assert("post", "x == 0"));

        let report = ctx.verify_with_report(VerificationReportOptions::new());
        assert!(
            matches!(report.result(), VerifyResult::Unknown { .. }),
            "contradictory assumptions should surface as Unknown, got {:?}",
            report.result()
        );

        let localized =
            localized_failure_from_report(&report).expect("unknown report should localize");
        assert_eq!(localized.label, "vacuous truth precheck");
        assert_eq!(localized.result, VerdictKind::Unknown);
        assert_eq!(localized.used_assumptions.len(), 2);
        assert!(
            localized
                .used_assumptions
                .iter()
                .any(|name| name == "gt_zero"),
            "localized failure should include gt_zero, got {:?}",
            localized.used_assumptions
        );
        assert!(
            localized
                .used_assumptions
                .iter()
                .any(|name| name == "lt_zero"),
            "localized failure should include lt_zero, got {:?}",
            localized.used_assumptions
        );
    }

    #[test]
    fn test_verify_one_fast_path_omits_localized_failure() {
        let source = r#"
            #[ensures(result == x + 1)]
            fn broken(x: i32) -> i32 {
                x
            }
        "#;
        let path = std::env::temp_dir().join("cargo_trust_vc_fast_path_counterexample.rs");
        std::fs::write(&path, source).expect("temp source should be written");

        let func = scanned_target(&path, "broken");
        let verdict = verify_one(&func);

        assert_eq!(verdict.result, VerdictKind::Counterexample);
        assert!(verdict.localized_failure.is_none());
        assert!(!verdict.bindings.is_empty());

        std::fs::remove_file(&path).ok();
    }

    /// Unknown-as-failure split (design-unknown-as-failure.md).
    ///
    /// `real_nonlinear2`: the SAME true fact as `real_nonlinear1` but WITHOUT a
    /// `by(nonlinear_arith)` hint. Historically the bare decision procedure
    /// could not decide it, so ay returned a genuine INCOMPLETENESS Unknown
    /// and the gate verdict mapper had to surface a model-less
    /// `Counterexample` (matching upstream `assert_one_fails`). Since ay's
    /// NRA interval branch-and-prune lane (ay 43034c4b0c) the bare procedure
    /// PROVES the (true) fact, so `Verified` is the sound outcome — a known,
    /// audited proves-more divergence from Verus parity that the corpus
    /// manifest (not this unit test) adjudicates. The load-bearing,
    /// solver-version-independent gate properties are: the verdict is NEVER
    /// `Unknown`, and a non-proof must be a model-less Counterexample
    /// labelled as solver incompleteness (no fabricated model).
    #[test]
    fn test_real_nonlinear2_gate_verdict_never_unknown() {
        let source = r#"
            #[trust_vc::ensures(true)]
            fn real_nonlinear2(a: real, b: real, q: real) {
                trust_vc::assert!(
                    !(a >= 0 && b >= 0 && (a * a + b * b == (a * b + 1) * q)) || (q >= 0)
                );
            }
        "#;
        let path = std::env::temp_dir().join("cargo_trust_vc_real_nonlinear2.rs");
        std::fs::write(&path, source).expect("temp source should be written");

        let func = scanned_target(&path, "real_nonlinear2");
        let verdict = verify_one(&func);

        // Load-bearing gate properties (solver-version-independent): the gate
        // verdict is NEVER `unknown`. The fact is TRUE, so `Verified` is the
        // sound outcome now that ay's bare NRA lane decides it (43034c4b0c);
        // if the solver does NOT prove it, the only acceptable verdict is
        // `Counterexample` (== upstream `assert_one_fails`), and under default
        // features that failure must be model-LESS (no fabricated
        // counterexample) and labelled as solver incompleteness. This is the
        // exact configuration the corpus gate runs in.
        match verdict.result {
            VerdictKind::Verified => {
                // Sound proves-more outcome; Verus-parity classification of
                // this divergence is owned by the corpus manifest refresh.
            }
            VerdictKind::Counterexample => {
                #[cfg(not(feature = "named-assertions"))]
                {
                    assert!(
                        verdict.bindings.is_empty(),
                        "incompleteness failure must carry no fabricated model bindings, got {:?}",
                        verdict.bindings
                    );
                    assert!(
                        verdict
                            .detail
                            .as_deref()
                            .is_some_and(|d| d.contains("incompleteness")),
                        "detail should label this a solver-incompleteness non-proof, got {:?}",
                        verdict.detail
                    );
                }
            }
            other => panic!(
                "real_nonlinear2 gate verdict must be Verified or Counterexample, never {:?} ({:?})",
                other, verdict.detail,
            ),
        }

        std::fs::remove_file(&path).ok();
    }

    /// The soundness boundary: a NON-incompleteness Unknown (here a vacuous-truth
    /// / contradictory-assumption Unknown — the same class as a resource/timeout
    /// Unknown for verdict-mapping purposes) must STAY `Unknown`. A timeout does
    /// not mean the fact is false, so it must never be reported as a failure.
    #[cfg(feature = "named-assertions")]
    #[test]
    fn test_non_incompleteness_unknown_stays_unknown() {
        let _env = disable_vc_cache();

        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
        ctx.push_obligation(ProofObligation::assume("gt_zero", "x > 0"));
        ctx.push_obligation(ProofObligation::assume("lt_zero", "x < 0"));
        ctx.push_obligation(ProofObligation::assert("post", "x == 0"));

        let result = ctx.verify();
        assert!(
            result.is_unknown(),
            "contradictory assumptions should surface as Unknown, got {result:?}"
        );
        assert!(
            !result
                .unknown_category()
                .expect("unknown carries a category")
                .is_incompleteness(),
            "vacuous-truth Unknown must NOT be classified as incompleteness"
        );

        // The verdict mapper must keep it Unknown (not flip to a failure).
        let (kind, _detail, bindings) = verdict_from_result(&result);
        assert_eq!(
            kind,
            VerdictKind::Unknown,
            "a non-incompleteness Unknown must stay Unknown (resource != false)"
        );
        assert!(bindings.is_empty());
    }

    /// A resource/timeout Unknown stays `Unknown` (not a failure). This pins the
    /// load-bearing soundness boundary at the engine's category surface: the
    /// `Timeout` category is never `is_incompleteness()`, so `verdict_from_result`
    /// leaves it `Unknown`.
    #[test]
    fn test_timeout_unknown_is_not_incompleteness() {
        use trust_vc_core::UnknownCategory;
        // `Timeout` is the canonical resource category; a timeout does not mean
        // the asserted fact is false.
        assert!(!UnknownCategory::Timeout.is_incompleteness());
        assert!(!UnknownCategory::SolverUnknown.is_incompleteness());
        // Only genuine theory incompleteness flips the verdict to a failure.
        assert!(UnknownCategory::Incompleteness.is_incompleteness());
    }

    /// The gate boundary: an incompleteness non-proof reaches the gate's
    /// `counterexample` expectation (which means "assert_fails", not "a model
    /// exists") and carries NO bindings.
    #[test]
    fn test_not_proved_maps_to_counterexample_label_with_no_bindings() {
        use trust_vc_core::UnknownCategory;

        let result = VerifyResult::NotProved {
            reason: "Solver returned unknown (incomplete) for 'test1_fails1'".to_string(),
            category: UnknownCategory::Incompleteness,
        };

        let (kind, detail, bindings) = verdict_from_result(&result);
        assert_eq!(
            kind,
            VerdictKind::Counterexample,
            "a model-less incompleteness failure must reach the gate's counterexample label"
        );
        assert!(
            bindings.is_empty(),
            "no counterexample bindings may be fabricated for a model-less failure"
        );
        let detail = detail.expect("detail should explain the non-proof");
        assert!(
            detail.contains("no model"),
            "detail must state that no model exists, got: {detail}"
        );
    }

    /// THE THIRD CATEGORY, at the CLI channel that actually prints to a user.
    ///
    /// `actionable_suggestion` is pinned in `trust-vc-core`, but it flows
    /// through `verification_report`/`trust-vc-oracle` — a DIFFERENT channel
    /// from what `cargo trust-vc check` prints. This pins the printed sentence
    /// itself: disabling the `ModelGateRejected` branch in `verdict_from_result`
    /// killed no test before this one existed.
    #[test]
    fn model_gate_rejected_tells_the_user_it_is_not_a_refutation() {
        use trust_vc_core::UnknownCategory;

        let result = VerifyResult::NotProved {
            reason: "Solver returned unknown (incomplete) for 'assertion_2'".to_string(),
            category: UnknownCategory::ModelGateRejected,
        };
        let (kind, detail, bindings) = verdict_from_result(&result);

        // VERDICT-PRESERVING: identical routing to plain incompleteness.
        assert_eq!(
            kind,
            VerdictKind::Counterexample,
            "the relabel must not move the verdict — both categories are `is_incompleteness()`"
        );
        assert!(
            bindings.is_empty(),
            "no model exists, so none may be invented"
        );

        let detail = detail.expect("detail should explain the non-proof");
        assert!(
            detail.contains("NOT a refutation of this proof"),
            "the user must be told their proof was not disproved, got: {detail}"
        );
        assert!(
            detail.contains("could not independently confirm"),
            "the user must be told the solver refuted its OWN model, got: {detail}"
        );
        assert!(
            !detail.contains("solver incompleteness"),
            "a caught invalid model must NOT be reported as theory incompleteness, got: {detail}"
        );
    }

    /// LIAR TWIN for the pin above, at the same mapper: plain
    /// `Incompleteness` must still get the OLD sentence and must NOT claim the
    /// solver caught its own model. Without this, the pin above would pass on a
    /// mapper that printed the new sentence unconditionally.
    #[test]
    fn liar_twin_plain_incompleteness_does_not_claim_a_caught_model() {
        use trust_vc_core::UnknownCategory;

        let result = VerifyResult::NotProved {
            reason: "Solver returned unknown (incomplete) for 'assertion_2'".to_string(),
            category: UnknownCategory::Incompleteness,
        };
        let (kind, detail, _bindings) = verdict_from_result(&result);
        assert_eq!(kind, VerdictKind::Counterexample);

        let detail = detail.expect("detail should explain the non-proof");
        assert!(
            detail.contains("solver incompleteness, no model"),
            "plain incompleteness keeps its own sentence, got: {detail}"
        );
        assert!(
            !detail.contains("NOT a refutation of this proof"),
            "an ordinary incompleteness must not borrow the model-gate sentence, got: {detail}"
        );
    }

    /// The opposite side of the same boundary, at the same mapper: a
    /// resource/timeout Unknown must NOT reach the `counterexample` label.
    #[test]
    fn test_resource_unknown_does_not_reach_counterexample_label() {
        use trust_vc_core::UnknownCategory;

        for category in [UnknownCategory::Timeout, UnknownCategory::SolverUnknown] {
            let result = VerifyResult::Unknown {
                reason: "solver ran out of budget".to_string(),
                category,
            };
            let (kind, _detail, bindings) = verdict_from_result(&result);
            assert_eq!(
                kind,
                VerdictKind::Unknown,
                "{category:?} must stay Unknown — a timeout does not mean the fact is false"
            );
            assert!(bindings.is_empty());
        }
    }

    /// A genuine, model-bearing counterexample is untouched by the mapping.
    #[test]
    fn test_genuine_counterexample_still_carries_model_through_the_mapper() {
        let result = VerifyResult::Counterexample {
            obligation_name: "ensures".to_string(),
            location: None,
            model: Some("x = -1".to_string()),
            bindings: vec![CounterexampleBinding::new("x", "x", "i32", "-1")],
        };

        let (kind, detail, bindings) = verdict_from_result(&result);
        assert_eq!(kind, VerdictKind::Counterexample);
        assert_eq!(bindings.len(), 1, "real model bindings must survive");
        assert!(detail.expect("detail").contains("x = -1"));
    }

    /// The `<name> (at <file:line:col>)` spelling every detail consumer reads
    /// is COMPOSED HERE from two separate fields. The engine hands over a bare
    /// NAME and a bare LOCATION; gluing them in the engine is what silently
    /// removed the name-keyed `proof_note`/`custom_err` channel once already.
    #[test]
    fn the_detail_composes_the_name_and_the_location_the_engine_keeps_apart() {
        let result = VerifyResult::Counterexample {
            obligation_name: "postcondition".to_string(),
            location: Some("pins.rs:88:5".to_string()),
            model: Some("x = -1".to_string()),
            bindings: Vec::new(),
        };

        let (_, detail, _) = verdict_from_result(&result);
        let detail = detail.expect("detail");
        assert_eq!(detail, "postcondition (at pins.rs:88:5): x = -1");
    }

    /// LIAR TWIN for the composition: with NO location the renderer must emit
    /// the bare name — never a fabricated ` (at …)` and never an empty one.
    #[test]
    fn a_location_less_refutation_is_refuted_for_the_at_clause() {
        let result = VerifyResult::Counterexample {
            obligation_name: "postcondition".to_string(),
            location: None,
            model: None,
            bindings: Vec::new(),
        };

        let (_, detail, _) = verdict_from_result(&result);
        let detail = detail.expect("detail");
        assert_eq!(detail, "postcondition");
        assert!(
            !detail.contains(" (at "),
            "no location means no `(at …)` clause, got {detail:?}"
        );
    }

    /// A sibling file's `impl Drop for R` reaches the file that uses `R`: the
    /// destructor runs where `f` drops `r`, so `f` is refused. The same crate
    /// without the impl still verifies.
    #[test]
    fn a_sibling_drop_impl_refuses_a_function_that_drops_its_type() {
        fn verdict(tag: &str, drop_impl: &str) -> FunctionVerdict {
            let src = std::env::temp_dir()
                .join(format!(
                    "trust_vc_sibling_drop_{tag}_{}",
                    std::process::id()
                ))
                .join("src");
            create_package(&src);
            std::fs::write(src.join("lib.rs"), "mod a;\nmod b;\n").expect("write lib.rs");
            std::fs::write(
                src.join("a.rs"),
                format!("pub struct R {{ pub w: u64 }}\n{drop_impl}\n"),
            )
            .expect("write a.rs");
            let b = src.join("b.rs");
            std::fs::write(
                &b,
                "use crate::a::R;\n#[trust_vc::ensures(true)]\npub fn f(r: R) {}\n",
            )
            .expect("write b.rs");
            let result = verify_one(&AnnotatedFunction {
                file_path: b,
                name: "f".to_string(),
                line: 3,
                attributes: vec!["ensures".to_string()],
            });
            let _ = std::fs::remove_dir_all(src.parent().expect("temp crate dir"));
            result
        }
        let refused = verdict(
            "impl",
            "impl Drop for R { fn drop(&mut self) { panic!(\"drop\") } }",
        );
        assert_eq!(refused.result, VerdictKind::Error, "{:?}", refused.detail);
        let detail = refused.detail.unwrap_or_default();
        assert!(detail.contains("unmodeled drop"), "{detail}");
        assert!(detail.contains("`impl Drop for R`"), "{detail}");
        let kept = verdict("none", "");
        assert_eq!(kept.result, VerdictKind::Verified, "{:?}", kept.detail);
    }

    /// `R` in `a.rs` compares with a hand-written `eq` that `b.rs` does not
    /// show. The run-time check of `f`'s postcondition and `g`'s `assert!`
    /// run it, so neither is read as structural equality and both are
    /// refused. The same crate with `R` deriving `PartialEq` still verifies.
    #[test]
    fn a_sibling_partial_eq_impl_refuses_a_comparison_of_its_type() {
        fn verdicts(tag: &str, a_rs: &str) -> Vec<FunctionVerdict> {
            let src = std::env::temp_dir()
                .join(format!(
                    "trust_vc_sibling_partial_eq_{tag}_{}",
                    std::process::id()
                ))
                .join("src");
            create_package(&src);
            std::fs::write(src.join("lib.rs"), "mod a;\nmod b;\n").expect("write lib.rs");
            std::fs::write(src.join("a.rs"), a_rs).expect("write a.rs");
            let b = src.join("b.rs");
            std::fs::write(
                &b,
                "use crate::a::R;\n\
                 #[trust_vc::contract(ensures(r == x), returns(r))]\n\
                 pub fn f(x: R) -> R { x }\n\
                 #[trust_vc::contract(ensures(r == 0u64), returns(r))]\n\
                 pub fn g(x: R) -> u64 { assert!(x == x); 0u64 }\n",
            )
            .expect("write b.rs");
            let results = [("f", 3), ("g", 5)]
                .into_iter()
                .map(|(name, line)| {
                    verify_one(&AnnotatedFunction {
                        file_path: b.clone(),
                        name: name.to_string(),
                        line,
                        attributes: vec!["contract".to_string()],
                    })
                })
                .collect();
            let _ = std::fs::remove_dir_all(src.parent().expect("temp crate dir"));
            results
        }
        let refused = verdicts(
            "impl",
            "#[derive(Clone, Copy)]\npub struct R { pub w: u64 }\n\
             impl PartialEq for R { fn eq(&self, _o: &R) -> bool { false } }\n",
        );
        for verdict in &refused {
            assert_eq!(verdict.result, VerdictKind::Error, "{:?}", verdict.detail);
        }
        let kept = verdicts(
            "derive",
            "#[derive(Clone, Copy, PartialEq)]\npub struct R { pub w: u64 }\n",
        );
        for verdict in &kept {
            assert_eq!(
                verdict.result,
                VerdictKind::Verified,
                "{:?}",
                verdict.detail
            );
        }
    }

    /// `other.rs` renames `u8` to `u64`, and `lib.rs` glob-imports it, so
    /// `(a as u64) / 2 + 200` overflows for `a = 255`. The sibling's `use` is
    /// not among the items appended to `lib.rs`, so the glob is what the
    /// type-name rule sees, and it refuses the file. The twin's glob imports
    /// from std, and `u64` there is the primitive.
    #[test]
    fn a_sibling_primitive_rename_under_a_glob_refuses_the_file() {
        fn verdict(tag: &str, glob: &str) -> FunctionVerdict {
            let src = std::env::temp_dir()
                .join(format!(
                    "trust_vc_sibling_primitive_glob_{tag}_{}",
                    std::process::id()
                ))
                .join("src");
            create_package(&src);
            std::fs::write(
                src.join("other.rs"),
                "pub use core::primitive::u8 as u64;\n",
            )
            .expect("write other.rs");
            let lib = src.join("lib.rs");
            std::fs::write(
                &lib,
                format!(
                    "mod other;\n\
                     {glob}\n\
                     #[trust_vc::ensures(true)]\n\
                     pub fn g1(a: u8) {{ let y = (a as u64) / 2 + 200; }}\n"
                ),
            )
            .expect("write lib.rs");
            let result = verify_one(&AnnotatedFunction {
                file_path: lib,
                name: "g1".to_string(),
                line: 4,
                attributes: vec!["ensures".to_string()],
            });
            let _ = std::fs::remove_dir_all(src.parent().expect("temp crate dir"));
            result
        }
        let refused = verdict("crate", "use crate::other::*;");
        assert_eq!(refused.result, VerdictKind::Error, "{:?}", refused.detail);
        let detail = refused.detail.unwrap_or_default();
        assert!(detail.contains("type-name rebinding"), "{detail}");
        assert!(detail.contains("`use crate::other::*;`"), "{detail}");
        let kept = verdict("std", "use std::ops::*;");
        assert_eq!(kept.result, VerdictKind::Verified, "{:?}", kept.detail);
    }

    /// Creates `src` and a `Cargo.toml` beside it, which makes the files
    /// under `src` the crate the crate lane reads.
    fn create_package(src: &Path) {
        std::fs::create_dir_all(src).expect("create temp src dir");
        std::fs::write(
            src.parent().expect("temp crate dir").join("Cargo.toml"),
            "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
        )
        .expect("write Cargo.toml");
    }

    /// Writes `files` (paths under `src/`, sources) into a fresh crate and
    /// verifies `name`, annotated with `attribute`, in `target`.
    fn crate_verdict(
        tag: &str,
        files: &[(&str, &str)],
        target: &str,
        name: &str,
        attribute: &str,
    ) -> FunctionVerdict {
        let src = std::env::temp_dir()
            .join(format!("trust_vc_crate_types_{tag}_{}", std::process::id()))
            .join("src");
        create_package(&src);
        for (path, source) in files {
            std::fs::write(src.join(path), source).expect("write crate file");
        }
        let target_source = files
            .iter()
            .find_map(|(path, source)| (*path == target).then_some(*source))
            .expect("target among the files");
        let line = target_source
            .lines()
            .position(|line| line.contains(&format!("fn {name}(")))
            .expect("target function in the target file")
            + 1;
        let result = verify_one(&AnnotatedFunction {
            file_path: src.join(target),
            name: name.to_string(),
            line,
            attributes: vec![attribute.to_string()],
        });
        let _ = std::fs::remove_dir_all(src.parent().expect("temp crate dir"));
        result
    }

    fn assert_refused(verdict: &FunctionVerdict, text: &str) {
        assert_eq!(verdict.result, VerdictKind::Error, "{:?}", verdict.detail);
        let detail = verdict.detail.clone().unwrap_or_default();
        assert!(detail.contains("type-name rebinding"), "{detail}");
        assert!(detail.contains(text), "{detail}");
    }

    fn assert_verified(verdict: &FunctionVerdict) {
        assert_eq!(
            verdict.result,
            VerdictKind::Verified,
            "{:?}",
            verdict.detail
        );
    }

    const ALIAS_USER: &str = "mod b;\n\
                              use b::W;\n\
                              #[trust_vc::ensures(true)]\n\
                              pub fn w1(v: W) { let z = v / 2 + 200; }\n";

    /// `b.rs` renames `u8` to `u64` and declares `pub type W = u64;`, so `W`
    /// is `u8` and `v / 2 + 200` overflows at `v = 255`. The copy of the
    /// alias left the rename behind and was read as the primitive. The twin's
    /// `b.rs` has no rename.
    #[test]
    fn a_sibling_alias_over_a_renamed_primitive_refuses_the_file() {
        let refused = crate_verdict(
            "rename",
            &[
                ("lib.rs", ALIAS_USER),
                (
                    "b.rs",
                    "use core::primitive::u8 as u64;\npub type W = u64;\n",
                ),
            ],
            "lib.rs",
            "w1",
            "ensures",
        );
        assert_refused(&refused, "in `src/b.rs`, a `use` renames a primitive type");
        let kept = crate_verdict(
            "rename_twin",
            &[("lib.rs", ALIAS_USER), ("b.rs", "pub type W = u64;\n")],
            "lib.rs",
            "w1",
            "ensures",
        );
        assert_verified(&kept);
    }

    /// The rename reaches `b.rs` through a glob over another file that
    /// re-exports a third, or through a glob from another crate. The twins'
    /// `b.rs` has no glob.
    #[test]
    fn a_sibling_alias_under_a_glob_refuses_the_file() {
        let lib = "mod prims;\nmod mid;\nmod b;\nuse b::W;\n#[trust_vc::ensures(true)]\n\
                   pub fn c2(v: W) { let z = v / 2 + 200; }\n";
        let prims = "pub use core::primitive::u8 as u64;\n";
        let mid = "pub use crate::prims::*;\n";
        let refused = crate_verdict(
            "chain",
            &[
                ("lib.rs", lib),
                ("prims.rs", prims),
                ("mid.rs", mid),
                ("b.rs", "use crate::mid::*;\npub type W = u64;\n"),
            ],
            "lib.rs",
            "c2",
            "ensures",
        );
        assert_refused(&refused, "`use crate::mid::*;`");
        let kept = crate_verdict(
            "chain_twin",
            &[
                ("lib.rs", lib),
                ("prims.rs", prims),
                ("mid.rs", mid),
                ("b.rs", "pub type W = u64;\n"),
            ],
            "lib.rs",
            "c2",
            "ensures",
        );
        assert_verified(&kept);

        let refused = crate_verdict(
            "extern_glob",
            &[
                ("lib.rs", ALIAS_USER),
                ("b.rs", "use other_crate::*;\npub type W = u64;\n"),
            ],
            "lib.rs",
            "w1",
            "ensures",
        );
        assert_refused(&refused, "`use other_crate::*;`");
    }

    /// In `b.rs` a macro invocation, an attribute macro on another item or an
    /// `include!` can emit the rename, so `W` is `u8` and `v / 2 + 200`
    /// overflows at `v = 255`. The copy of the alias left the expansion
    /// behind. Each twin's `b.rs` lacks the line that can emit it (the macro
    /// is defined and not invoked; `helper` has no attribute; no `include!`).
    #[test]
    fn a_sibling_macro_that_can_emit_a_rename_refuses_the_file() {
        let verdict = |tag: &str, b: &str| {
            crate_verdict(
                tag,
                &[("lib.rs", ALIAS_USER), ("b.rs", b)],
                "lib.rs",
                "w1",
                "ensures",
            )
        };
        let rules = "macro_rules! rn { () => { use core::primitive::u8 as u64; } }\n";
        assert_refused(
            &verdict(
                "macro_rename",
                &format!("{rules}rn!();\npub type W = u64;\n"),
            ),
            "in `src/b.rs`, the file invokes its macro `rn!`",
        );
        assert_verified(&verdict(
            "macro_rename_twin",
            &format!("{rules}pub type W = u64;\n"),
        ));
        assert_refused(
            &verdict(
                "attribute_rename",
                "#[other_crate::rebind_u64]\nfn helper() {}\npub type W = u64;\n",
            ),
            "`#[other_crate::rebind_u64]`",
        );
        assert_verified(&verdict(
            "attribute_rename_twin",
            "fn helper() {}\npub type W = u64;\n",
        ));
        assert_refused(
            &verdict(
                "include_rename",
                "include!(\"rn.rs.txt\");\npub type W = u64;\n",
            ),
            "`include!`",
        );
        assert_verified(&verdict("include_rename_twin", "pub type W = u64;\n"));
    }

    /// A macro of `c.rs` declares a second `W`, a byte, which `lib.rs`
    /// imports, while the lane read the copy of `b.rs`'s `u64` alias. The
    /// twin's `c.rs` re-exports `b.rs`'s `W` in place of the invocation.
    #[test]
    fn a_sibling_macro_that_can_declare_a_copied_name_refuses_the_file() {
        let verdict = |tag: &str, c_last: &str| {
            let c = format!("macro_rules! mk {{ () => {{ pub type W = u8; }} }}\n{c_last}\n");
            crate_verdict(
                tag,
                &[
                    (
                        "lib.rs",
                        "mod b;\nmod c;\nuse c::W;\n#[trust_vc::ensures(true)]\n\
                         pub fn z1(v: W) { let z = v / 2 + 200; }\n",
                    ),
                    ("b.rs", "pub type W = u64;\n"),
                    ("c.rs", c.as_str()),
                ],
                "lib.rs",
                "z1",
                "ensures",
            )
        };
        assert_refused(
            &verdict("macro_declares", "mk!();"),
            "in `src/c.rs`, the file invokes its macro `mk!`",
        );
        assert_verified(&verdict("macro_declares_twin", "pub use crate::b::W;"));
    }

    /// `lib.rs` binds `W` to `c.rs`'s byte alias, or to another crate's `W`,
    /// while `a.rs` declares `pub type W = u64;`. The copy of `a.rs`'s alias
    /// was read for `W`. The twin imports `a.rs`'s `W`.
    #[test]
    fn a_use_that_binds_a_sibling_type_name_elsewhere_refuses_the_file() {
        let verdict = |tag: &str, import: &str| {
            let lib = format!(
                "mod a;\nmod c;\n{import}\n#[trust_vc::ensures(true)]\n\
                 pub fn h14(v: W) {{ let z = v / 2 + 200; }}\n"
            );
            crate_verdict(
                tag,
                &[
                    ("lib.rs", lib.as_str()),
                    ("a.rs", "pub type W = u64;\n"),
                    ("c.rs", "pub type V = u8;\n"),
                ],
                "lib.rs",
                "h14",
                "ensures",
            )
        };
        assert_refused(
            &verdict("use_rename", "use c::V as W;"),
            "to an item of another name",
        );
        assert_refused(
            &verdict("use_extern", "use other_crate::W;"),
            "from a path that does not stay in the crate",
        );
        assert_verified(&verdict("use_twin", "use a::W;"));
    }

    /// `b.rs` spells `W`, which `a.rs` declares, under a glob from another
    /// crate and without importing it, so `W` is that crate's (with `W =
    /// f64`, `r == w` is false for NaN). The twin's glob is over `a.rs`.
    #[test]
    fn a_sibling_type_name_under_a_glob_from_outside_refuses_the_file() {
        let verdict = |tag: &str, glob: &str| {
            let b = format!(
                "{glob}\n#[trust_vc::contract(ensures(r == w), returns(r))]\n\
                 pub fn h30(w: W) -> W {{ w }}\n"
            );
            crate_verdict(
                tag,
                &[
                    ("lib.rs", "mod a;\nmod b;\n"),
                    ("a.rs", "#[derive(Clone, Copy, PartialEq)]\npub struct W;\n"),
                    ("b.rs", b.as_str()),
                ],
                "b.rs",
                "h30",
                "contract",
            )
        };
        assert_refused(
            &verdict("outside_glob", "use other_crate::*;"),
            "from outside the crate",
        );
        assert_verified(&verdict("outside_glob_twin", "use crate::a::*;"));
    }

    /// An alias of `other_crate::W` was read as `a.rs`'s `W`. The twin
    /// aliases `a::W`.
    #[test]
    fn a_path_to_a_sibling_type_name_from_outside_refuses_the_file() {
        let verdict = |tag: &str, ty: &str| {
            let lib = format!(
                "mod a;\ntype V = {ty};\n#[trust_vc::ensures(true)]\n\
                 pub fn h17(v: V) {{ let z = v / 2 + 200; }}\n"
            );
            crate_verdict(
                tag,
                &[("lib.rs", lib.as_str()), ("a.rs", "pub type W = u64;\n")],
                "lib.rs",
                "h17",
                "ensures",
            )
        };
        assert_refused(
            &verdict("path", "other_crate::W"),
            "through a path that does not stay in the crate",
        );
        assert_verified(&verdict("path_twin", "a::W"));
    }

    /// Two files declare `W`. The copies land side by side, where the name
    /// no longer says which one `use z::W;` means: with `u64` and `u8` the
    /// lane fails closed on the ambiguity, and with two equal declarations
    /// the file is refused all the same.
    #[test]
    fn a_type_name_two_files_declare_refuses_the_file() {
        let verdict = |tag: &str, z: &str| {
            crate_verdict(
                tag,
                &[
                    (
                        "lib.rs",
                        "mod a;\nmod z;\nuse z::W;\n#[trust_vc::ensures(true)]\n\
                         pub fn d1(v: W) { let z = v / 2 + 200; }\n",
                    ),
                    ("a.rs", "pub type W = u64;\n"),
                    ("z.rs", z),
                ],
                "lib.rs",
                "d1",
                "ensures",
            )
        };
        let differing = verdict("duplicate", "pub type W = u8;\n");
        assert_ne!(
            differing.result,
            VerdictKind::Verified,
            "{:?}",
            differing.detail
        );
        assert_refused(
            &verdict("duplicate_equal", "pub type W = u64;\n"),
            "declares the type name `W` 2 times",
        );
    }

    /// Writes `files` (paths under a fresh package directory, sources) and
    /// verifies `name`, annotated with `attribute`, in `target` (a path under
    /// that directory). No `Cargo.toml` is written unless `files` holds one.
    fn package_verdict(
        tag: &str,
        files: &[(&str, &str)],
        target: &str,
        name: &str,
        attribute: &str,
    ) -> FunctionVerdict {
        linked_package_verdict(tag, files, &[], target, name, attribute)
    }

    /// [`package_verdict`] with `links`, each a path under the package and
    /// the symbolic link's text, created after the files.
    fn linked_package_verdict(
        tag: &str,
        files: &[(&str, &str)],
        links: &[(&str, &str)],
        target: &str,
        name: &str,
        attribute: &str,
    ) -> FunctionVerdict {
        let package =
            std::env::temp_dir().join(format!("trust_vc_package_{tag}_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&package);
        for (path, source) in files {
            let path = package.join(path);
            std::fs::create_dir_all(path.parent().expect("file in a directory"))
                .expect("create package dir");
            std::fs::write(path, source).expect("write package file");
        }
        for (path, text) in links {
            let path = package.join(path);
            std::fs::create_dir_all(path.parent().expect("link in a directory"))
                .expect("create package dir");
            std::os::unix::fs::symlink(text, path).expect("create link");
        }
        let target_source =
            std::fs::read_to_string(package.join(target)).expect("target among the files");
        let line = target_source
            .lines()
            .position(|line| line.contains(&format!("fn {name}(")))
            .expect("target function in the target file")
            + 1;
        let result = verify_one(&AnnotatedFunction {
            file_path: package.join(target),
            name: name.to_string(),
            line,
            attributes: vec![attribute.to_string()],
        });
        let _ = std::fs::remove_dir_all(&package);
        result
    }

    const MANIFEST: &str =
        "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n";

    fn assert_not_verified(verdict: &FunctionVerdict) {
        assert_ne!(
            verdict.result,
            VerdictKind::Verified,
            "{:?}",
            verdict.detail
        );
    }

    /// A path that starts at a module of the crate leaves it through a later
    /// segment: `c.rs` re-exports `core::ffi`, another crate's module, the
    /// crate `core` itself or another crate, and `c_uchar` or `W` is then
    /// that crate's (`c_uchar` is `u8`, so `v / 2 + 200` overflows at `v =
    /// 255`), while the lane read `a.rs`'s `u64` alias. The same holds for a
    /// `use` in an inline module that rebinds a module name of the crate, and
    /// for a root `use` of a name only a nested module declares. Each twin
    /// differs by one line and reaches `a.rs`'s declaration.
    #[test]
    fn a_path_through_a_module_that_leaves_the_crate_refuses_the_file() {
        let a = "pub type c_uchar = u64;\n";
        let user = |import: &str| {
            format!(
                "mod a;\nmod c;\n{import}\n#[trust_vc::ensures(true)]\n\
                 pub fn r1(v: c_uchar) {{ let z = v / 2 + 200; }}\n"
            )
        };
        let verdict = |tag: &str, lib: &str, c: &str| {
            crate_verdict(
                tag,
                &[("lib.rs", lib), ("a.rs", a), ("c.rs", c)],
                "lib.rs",
                "r1",
                "ensures",
            )
        };
        let reexport = "pub use core::ffi;\n";
        assert_refused(
            &verdict("ffi", &user("use c::ffi::c_uchar;"), reexport),
            "the `use` of `c::ffi::c_uchar` binds `c_uchar`",
        );
        assert_verified(&verdict("ffi_twin", &user("use a::c_uchar;"), reexport));
        let path = "mod a;\nmod c;\n#[trust_vc::ensures(true)]\n\
                    pub fn r1(v: c::ffi::c_uchar) { let z = v / 2 + 200; }\n";
        assert_refused(
            &verdict("ffi_path", path, reexport),
            "spells `c::ffi::c_uchar`",
        );
        assert_verified(&verdict(
            "ffi_path_twin",
            &path.replace("c::ffi::c_uchar", "a::c_uchar"),
            reexport,
        ));
        let extern_ffi = user("use c::oc::ffi::c_uchar;");
        assert_refused(
            &verdict(
                "extern_crate",
                &extern_ffi,
                "pub extern crate core as oc;\n",
            ),
            "the `use` of `c::oc::ffi::c_uchar`",
        );
        assert_verified(&verdict(
            "extern_crate_twin",
            &extern_ffi,
            "pub mod oc { pub mod ffi { pub use crate::a::c_uchar; } }\n",
        ));

        let w = |tag: &str, lib_import: &str, b: &str, c: &str| {
            let lib = format!(
                "mod a;\nmod b;\nmod c;\n{lib_import}\n#[trust_vc::ensures(true)]\n\
                 pub fn r3(v: W) {{ let z = v / 2 + 200; }}\n"
            );
            crate_verdict(
                tag,
                &[
                    ("lib.rs", lib.as_str()),
                    ("a.rs", "pub type W = u64;\n"),
                    ("b.rs", b),
                    ("c.rs", c),
                ],
                "lib.rs",
                "r3",
                "ensures",
            )
        };
        assert_refused(
            &w("module", "use c::m::W;", "", "pub use other_crate::m;\n"),
            "the `use` of `c::m::W`",
        );
        assert_verified(&w(
            "module_twin",
            "use c::m::W;",
            "",
            "pub mod m { pub use crate::a::W; }\n",
        ));
        assert_refused(
            &w(
                "crate_alias",
                "use c::oc::W;",
                "",
                "pub use other_crate as oc;\n",
            ),
            "the `use` of `c::oc::W`",
        );
        assert_verified(&w(
            "crate_alias_twin",
            "use c::oc::W;",
            "",
            "pub mod oc { pub use crate::a::W; }\n",
        ));
        assert_refused(
            &w(
                "sibling",
                "use b::W;",
                "pub use crate::c::m::W;\n",
                "pub use other_crate::m;\n",
            ),
            "in `src/b.rs`, the `use` of `crate::c::m::W`",
        );
        assert_verified(&w(
            "sibling_twin",
            "use b::W;",
            "pub use crate::a::W;\n",
            "pub use other_crate::m;\n",
        ));

        let inner = |tag: &str, line: &str| {
            let lib = format!(
                "mod a;\nmod c;\nmod q {{ {line}\n#[trust_vc::ensures(true)]\n\
                 pub fn r1(v: c::c_uchar) {{ let z = v / 2 + 200; }} }}\n"
            );
            verdict(tag, &lib, "pub use crate::a::c_uchar;\n")
        };
        assert_refused(
            &inner("inner_use", "use core::ffi as c;"),
            "spells `c::c_uchar`",
        );
        assert_verified(&inner(
            "inner_use_twin",
            "pub mod c { pub use crate::a::c_uchar; }",
        ));
        let nested = |tag: &str, line: &str| {
            let lib = format!(
                "mod a;\nmod inner {{ pub mod c {{}} }}\n{line}\n#[trust_vc::ensures(true)]\n\
                 pub fn r1(v: c::c_uchar) {{ let z = v / 2 + 200; }}\n"
            );
            crate_verdict(
                tag,
                &[("lib.rs", lib.as_str()), ("a.rs", a)],
                "lib.rs",
                "r1",
                "ensures",
            )
        };
        assert_refused(
            &nested("nested_mod", "use core::ffi as c;"),
            "spells `c::c_uchar`",
        );
        assert_verified(&nested(
            "nested_mod_twin",
            "mod c { pub use crate::a::c_uchar; }",
        ));
    }

    /// A glob from `core` binds `c_uchar` (`u8`) where `a.rs` declares
    /// `pub type c_uchar = u64;`, in `lib.rs` itself or in `c.rs`, whose
    /// `c_uchar` `lib.rs` imports. A std glob counts as a glob from outside
    /// the crate. Each twin's line names `a.rs`'s declaration.
    #[test]
    fn a_std_glob_that_binds_a_sibling_type_name_refuses_the_file() {
        let a = "pub type c_uchar = u64;\n";
        let direct = |tag: &str, import: &str| {
            let lib = format!(
                "mod a;\n{import}\n#[trust_vc::ensures(true)]\n\
                 pub fn r9(v: c_uchar) {{ let z = v / 2 + 200; }}\n"
            );
            crate_verdict(
                tag,
                &[("lib.rs", lib.as_str()), ("a.rs", a)],
                "lib.rs",
                "r9",
                "ensures",
            )
        };
        assert_refused(
            &direct("std_glob", "use core::ffi::*;"),
            "has the glob import `use core::ffi::*;`",
        );
        assert_verified(&direct("std_glob_twin", "use a::c_uchar;"));
        let via = |tag: &str, c: &str| {
            crate_verdict(
                tag,
                &[
                    (
                        "lib.rs",
                        "mod a;\nmod c;\nuse c::c_uchar;\n#[trust_vc::ensures(true)]\n\
                         pub fn r10(v: c_uchar) { let z = v / 2 + 200; }\n",
                    ),
                    ("a.rs", a),
                    ("c.rs", c),
                ],
                "lib.rs",
                "r10",
                "ensures",
            )
        };
        assert_refused(
            &via("std_glob_reexport", "pub use core::ffi::*;\n"),
            "`src/c.rs` has the glob import `use core::ffi::*;`",
        );
        assert_verified(&via("std_glob_reexport_twin", "pub use crate::a::*;\n"));
    }

    /// The crate holds a file the lane did not read: `#[path]` (or
    /// `#[r#path]`, in `lib.rs` or in `m.rs`) puts `b.rs` outside `src`, or a
    /// shebang line made the parse fail and the file was skipped, so `use
    /// b::W;` was read as `c.rs`'s `u64` alias while `b.rs` declares `W =
    /// u8`. A `path` attribute now refuses the file, a shebang
    /// is read as rustc reads it (the two declarations of `W` then refuse
    /// it), and a file that does not parse refuses it. The twins drop the
    /// attribute (`mod b;` is then `src/b.rs`, which re-exports `c.rs`'s
    /// `W`), re-export `c.rs`'s `W` after the shebang, and fix the parse.
    #[test]
    fn a_crate_file_the_lane_does_not_read_refuses_the_file() {
        let path = |tag: &str, attribute: &str| {
            let lib = format!(
                "{attribute}\nmod b;\nmod c;\nuse b::W;\n#[trust_vc::ensures(true)]\n\
                 pub fn p1(v: W) {{ let z = v / 2 + 200; }}\n"
            );
            package_verdict(
                tag,
                &[
                    ("Cargo.toml", MANIFEST),
                    ("src/lib.rs", lib.as_str()),
                    ("src/b.rs", "pub use crate::c::W;\n"),
                    ("src/c.rs", "pub type W = u64;\n"),
                    ("gen/b.rs", "pub type W = u8;\n"),
                ],
                "src/lib.rs",
                "p1",
                "ensures",
            )
        };
        assert_refused(
            &path("path_attribute", "#[path = \"../gen/b.rs\"]"),
            "declares `mod b` with a `path` attribute",
        );
        assert_not_verified(&path(
            "cfg_path_attribute",
            "#[cfg_attr(all(), path = \"../gen/b.rs\")]",
        ));
        assert_refused(
            &path("raw_path_attribute", "#[r#path = \"../gen/b.rs\"]"),
            "declares `mod b` with a `path` attribute",
        );
        assert_not_verified(&path(
            "raw_cfg_path_attribute",
            "#[cfg_attr(all(), r#path = \"../gen/b.rs\")]",
        ));
        assert_verified(&path("path_attribute_twin", ""));
        let sibling_path = |tag: &str, attribute: &str| {
            let m = format!("{attribute}\npub mod b;\n");
            package_verdict(
                tag,
                &[
                    ("Cargo.toml", MANIFEST),
                    (
                        "src/lib.rs",
                        "mod m;\nmod c;\nuse m::b::W;\n#[trust_vc::ensures(true)]\n\
                         pub fn p4(v: W) { let z = v / 2 + 200; }\n",
                    ),
                    ("src/m.rs", m.as_str()),
                    ("src/m/b.rs", "pub use crate::c::W;\n"),
                    ("src/c.rs", "pub type W = u64;\n"),
                    ("gen/b.rs", "pub type W = u8;\n"),
                ],
                "src/lib.rs",
                "p4",
                "ensures",
            )
        };
        assert_refused(
            &sibling_path("raw_path_sibling", "#[r#path = \"../gen/b.rs\"]"),
            "`src/m.rs` declares `mod b` with a `path` attribute",
        );
        assert_verified(&sibling_path("raw_path_sibling_twin", ""));

        let shebang = |tag: &str, b_last: &str| {
            let b = format!("#!/usr/bin/env run\n{b_last}\n");
            crate_verdict(
                tag,
                &[
                    (
                        "lib.rs",
                        "mod b;\nmod c;\nuse b::W;\n#[trust_vc::ensures(true)]\n\
                         pub fn p2(v: W) { let z = v / 2 + 200; }\n",
                    ),
                    ("b.rs", b.as_str()),
                    ("c.rs", "pub type W = u64;\n"),
                ],
                "lib.rs",
                "p2",
                "ensures",
            )
        };
        assert_not_verified(&shebang("shebang", "pub type W = u8;"));
        assert_verified(&shebang("shebang_twin", "pub use crate::c::W;"));

        let unparsed = |tag: &str, x: &str| {
            crate_verdict(
                tag,
                &[
                    (
                        "lib.rs",
                        "mod c;\nuse c::W;\n#[trust_vc::ensures(true)]\n\
                         pub fn p8(v: W) { let z = v / 2 + 200; }\n",
                    ),
                    ("c.rs", "pub type W = u64;\n"),
                    ("x.rs", x),
                ],
                "lib.rs",
                "p8",
                "ensures",
            )
        };
        assert_refused(
            &unparsed("unparsed", "fn broken( {\n"),
            "`src/x.rs` does not parse",
        );
        assert_verified(&unparsed("unparsed_twin", "fn fixed() {}\n"));
    }

    /// `src/m/src/t.rs` is the module `m::src::t` of the crate whose root is
    /// `src/lib.rs`, so `crate::b::W` is `src/b.rs`'s byte alias, while the
    /// innermost `src` read for its crate held only `src/m/src/c.rs`'s `u64`
    /// alias. The package's manifest now names `src`, where the lane reads
    /// both declarations; the twin's `src/b.rs` re-exports `c.rs`'s `W`.
    /// Without a manifest the file is read alone.
    #[test]
    fn a_nested_src_directory_is_read_from_the_package_root() {
        let verdict = |tag: &str, manifest: Option<&str>, b: &str| {
            let mut files = vec![
                ("src/lib.rs", "mod b;\nmod m;\n"),
                ("src/b.rs", b),
                ("src/m.rs", "mod src;\n"),
                ("src/m/src.rs", "mod t;\nmod c;\n"),
                (
                    "src/m/src/t.rs",
                    "use crate::b::W;\n#[trust_vc::ensures(true)]\n\
                     pub fn p3(v: W) { let z = v / 2 + 200; }\n",
                ),
                ("src/m/src/c.rs", "pub type W = u64;\n"),
            ];
            files.extend(manifest.map(|manifest| ("Cargo.toml", manifest)));
            package_verdict(tag, &files, "src/m/src/t.rs", "p3", "ensures")
        };
        assert_not_verified(&verdict("nested_src", Some(MANIFEST), "pub type W = u8;\n"));
        assert_not_verified(&verdict("nested_src_alone", None, "pub type W = u8;\n"));
        assert_verified(&verdict(
            "nested_src_twin",
            Some(MANIFEST),
            "pub use crate::m::src::c::W;\n",
        ));
    }

    /// Which directory the crate lane reads, and when it can settle none.
    #[test]
    fn the_crate_source_directory_is_the_package_src() {
        let root = std::env::temp_dir().join(format!("trust_vc_src_root_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let write = |path: &str, text: &str| {
            let path = root.join(path);
            std::fs::create_dir_all(path.parent().expect("parent")).expect("create dir");
            std::fs::write(path, text).expect("write");
        };
        write("p/Cargo.toml", MANIFEST);
        write("p/src/lib.rs", "");
        write("p/src/m/src/t.rs", "");
        write("p/tests/x.rs", "");
        write("q/src/lib.rs", "");
        write(
            "r/Cargo.toml",
            &format!("{MANIFEST}[lib]\npath = \"lib.rs\"\n[dependencies]\nlibx = {{ path = \"../x\" }}\n"),
        );
        write("r/src/t.rs", "");
        write("s/Cargo.toml", MANIFEST);
        write("s/src/inner/Cargo.toml", MANIFEST);
        write("s/src/inner/src/lib.rs", "");
        write("t/Cargo.toml", MANIFEST);
        write("t/src/lib.rs", "");
        write("t/src/mod.rs", "");
        write("u/Cargo.toml", MANIFEST);
        write("u/src/lib.rs", "");
        write("u/src.rs", "");
        write("v/Cargo.toml", "[package\nname = \"v\"\n");
        write("v/src/lib.rs", "");
        let canonical = |path: &str| root.join(path).canonicalize().expect("canonical");
        let src_of = |path: &str| crate_src_root(&root.join(path)).map(|it| it.map(|it| it.src));
        assert_eq!(src_of("p/src/lib.rs"), Ok(Some(canonical("p/src"))));
        assert_eq!(src_of("p/src/m/src/t.rs"), Ok(Some(canonical("p/src"))));
        assert_eq!(crate_src_root(&root.join("p/tests/x.rs")), Ok(None));
        assert_eq!(crate_src_root(&root.join("q/src/lib.rs")), Ok(None));
        let moved = crate_src_root(&root.join("r/src/t.rs")).expect_err("lib path outside src");
        assert!(moved.contains("places a crate root at `lib.rs`"), "{moved}");
        let nested =
            crate_src_root(&root.join("s/src/inner/src/lib.rs")).expect_err("two packages");
        assert!(nested.contains("two packages"), "{nested}");
        for (file, module_file) in [("t/src/lib.rs", "src/mod.rs"), ("u/src/lib.rs", "src.rs")] {
            let why = crate_src_root(&root.join(file)).expect_err(module_file);
            assert!(
                why.contains(&format!(
                    "{module_file}` exists, so `src` can be the module `src`"
                )),
                "{why}"
            );
        }
        let unparsed = crate_src_root(&root.join("v/src/lib.rs")).expect_err("not TOML");
        assert!(unparsed.contains("does not parse as TOML"), "{unparsed}");
        let _ = std::fs::remove_dir_all(&root);

        assert_eq!(
            without_shebang("#!/usr/bin/env run\nfn f() {}\n"),
            format!("{}\nfn f() {{}}\n", " ".repeat("#!/usr/bin/env run".len()))
        );
        assert_eq!(
            without_shebang("#![allow(unused)]\n"),
            "#![allow(unused)]\n"
        );
        assert_eq!(
            without_shebang("#! // note\n[allow(unused)]\n"),
            "#! // note\n[allow(unused)]\n"
        );
        assert_eq!(
            without_shebang("#!/* note */[allow(unused)]\n"),
            "#!/* note */[allow(unused)]\n"
        );
    }

    /// A macro of the crate declares a `struct` or an `enum` `W`, or the `V`
    /// that `b.rs`'s `W` aliases, beside `a.rs`'s `u64` alias. The macro's
    /// item is neither copied nor counted, and the file it is in does not
    /// bind the name, so the unread-item rule admitted it; under `trustc`
    /// `size_of::<W>()` is 1. Each twin keeps the macro and replaces the
    /// invocation with an import of `a.rs`'s declaration.
    #[test]
    fn a_crate_macro_that_declares_a_type_of_any_name_refuses_the_file() {
        let lib = "mod a;\nmod c;\nuse c::W;\n#[trust_vc::ensures(true)]\n\
                   pub fn z4() { assert!(core::mem::size_of::<W>() == 8); }\n";
        let verdict = |tag: &str, c: &str| {
            crate_verdict(
                tag,
                &[
                    ("lib.rs", lib),
                    ("a.rs", "pub type W = u64;\n"),
                    ("c.rs", c),
                ],
                "lib.rs",
                "z4",
                "ensures",
            )
        };
        let mk = "macro_rules! mk { () => { pub struct W(pub u8); } }\n";
        assert_refused(
            &verdict("macro_struct", &format!("{mk}mk!();\n")),
            "which declares the type `W`",
        );
        assert_verified(&verdict(
            "macro_struct_twin",
            &format!("{mk}pub use crate::a::W;\n"),
        ));
        assert_refused(
            &verdict(
                "macro_enum",
                "macro_rules! mk { () => { pub enum W { A } } }\nmk!();\n",
            ),
            "which declares the type `W`",
        );
        let via = |tag: &str, line: &str| {
            let b = format!(
                "macro_rules! mk {{ () => {{ pub struct V(pub u8); }} }}\n{line}\npub type W = V;\n"
            );
            crate_verdict(
                tag,
                &[
                    (
                        "lib.rs",
                        "mod a;\nmod b;\nuse b::W;\n#[trust_vc::ensures(true)]\n\
                         pub fn z5() { assert!(core::mem::size_of::<W>() == 8); }\n",
                    ),
                    ("a.rs", "pub type V = u64;\n"),
                    ("b.rs", b.as_str()),
                ],
                "lib.rs",
                "z5",
                "ensures",
            )
        };
        assert_refused(&via("macro_alias", "mk!();"), "which declares the type `V`");
        assert_verified(&via("macro_alias_twin", "use crate::a::V;"));
    }

    /// `lib.rs` declares `mod vstd;`, whose `int` is another crate's byte,
    /// and imports `use vstd::int;`. Another file's glob from another crate
    /// can bind `vstd` too where a 2015-edition `use` starts. Both read
    /// `int` as the toolchain's. The twins name another module, or import a
    /// single item in place of the glob.
    #[test]
    fn a_crate_file_that_binds_a_toolchain_crate_name_refuses_the_file() {
        let verdict = |tag: &str, module: &str| {
            let lib = format!(
                "{module}\nuse vstd::int;\n#[trust_vc::requires(x >= 0 && x < 100)]\n\
                 pub fn v1(x: int) {{ let y = x * 100; }}\n"
            );
            crate_verdict(
                tag,
                &[
                    ("lib.rs", lib.as_str()),
                    ("vstd.rs", "pub use other_crate::Byte as int;\n"),
                    ("other.rs", ""),
                ],
                "lib.rs",
                "v1",
                "requires",
            )
        };
        assert_refused(
            &verdict("toolchain_module", "mod vstd;"),
            "the file binds `vstd`, the name of a crate of this toolchain, with `mod vstd`",
        );
        assert_verified(&verdict("toolchain_module_twin", "mod other;"));
        let glob = |tag: &str, import: &str| {
            let lib = format!("mod a;\n{import}\n");
            crate_verdict(
                tag,
                &[
                    ("lib.rs", lib.as_str()),
                    (
                        "a.rs",
                        "use vstd::int;\n#[trust_vc::requires(x >= 0 && x < 100)]\n\
                         pub fn vg(x: int) { let y = x * 100; }\n",
                    ),
                ],
                "a.rs",
                "vg",
                "requires",
            )
        };
        assert_refused(
            &glob("toolchain_glob", "use other_crate::*;"),
            "can bind a module named like a crate of this toolchain",
        );
        assert_verified(&glob("toolchain_glob_twin", "use other_crate::Thing;"));
    }

    /// In an impl of a trait, `Self::W` is the impl's associated type (`u8`),
    /// not the variant `W` of `a`'s enum, while the lane read `a`'s `u64`
    /// alias `W`; with `v = 255`, `v / 2 + 200` overflows. In a single file
    /// and in the crate lane. Each twin's method takes the byte by name and
    /// adds 20, which fits; the file twin verifies.
    #[test]
    fn self_names_an_associated_type_before_a_variant() {
        let tr = |method: &str| {
            format!(
                "pub struct X;\nimpl Tr for X {{ type W = u8;\n#[trust_vc::ensures(true)]\n\
                 {method} }}\npub trait Tr {{ type W; fn g(v: u8); }}\n"
            )
        };
        let liar = "fn g(v: Self::W) { let z = v / 2 + 200; }";
        let twin = "fn g(v: u8) { let z = v / 2 + 20; }";
        let file = |tag: &str, method: &str| {
            let source = format!(
                "mod a {{ pub type W = u64; pub enum E {{ W }} }}\n{}",
                tr(method)
            );
            package_verdict(tag, &[("f.rs", source.as_str())], "f.rs", "g", "ensures")
        };
        assert_refused(
            &file("self_assoc_file", liar),
            "the path `Self :: W` spells `W`",
        );
        assert_verified(&file("self_assoc_file_twin", twin));
        let in_crate = |tag: &str, method: &str| {
            let lib = format!("mod a;\n{}", tr(method));
            crate_verdict(
                tag,
                &[
                    ("lib.rs", lib.as_str()),
                    ("a.rs", "pub type W = u64;\npub enum E { W }\n"),
                ],
                "lib.rs",
                "g",
                "ensures",
            )
        };
        assert_refused(&in_crate("self_assoc_crate", liar), "spells `Self::W`");
        // The crate-lane twin is true, and the drop rule refuses it: `mod a;`
        // can implement `Drop` for `E`, which the impl's names reach.
        let twin = in_crate("self_assoc_crate_twin", twin);
        assert_eq!(twin.result, VerdictKind::Error, "{:?}", twin.detail);
        assert!(
            twin.detail
                .unwrap_or_default()
                .starts_with("unmodeled drop"),
            "the twin is refused by the drop rule only"
        );
    }

    /// The package's root `lib.rs` declares `mod b;` (`W = u8`) and
    /// `#[path = "src/t.rs"] mod t;`, and the manifest makes it the crate
    /// root in a spelling the lane's line reader missed: a quoted key, a
    /// quoted table header, a dotted key in the root table, or an escape in
    /// the string. `src/t.rs`'s `crate::W` is then the byte, while the lane
    /// read `src` as the crate, whose `W` is `src/c.rs`'s `u64`; with `v =
    /// 255`, `v / 2 + 200` overflows. The manifest is now read as TOML, and
    /// the lane copies no type into the file (`W` is then unknown, so the
    /// answer fails closed before the refusal; the refusal's text is pinned
    /// by `the_manifest_target_roots_are_read_as_toml`). The twin's manifest
    /// line names `src/lib.rs`, which re-exports `c.rs`'s `W`.
    #[test]
    fn a_manifest_that_moves_the_crate_root_refuses_in_any_spelling() {
        let verdict = |tag: &str, head: &str, tail: &str| {
            let manifest = format!("{head}{MANIFEST}{tail}");
            package_verdict(
                tag,
                &[
                    ("Cargo.toml", manifest.as_str()),
                    (
                        "lib.rs",
                        "mod b;\n#[path = \"src/t.rs\"]\nmod t;\npub use b::W;\n",
                    ),
                    ("b.rs", "pub type W = u8;\n"),
                    ("src/lib.rs", "mod t;\nmod c;\npub use c::W;\n"),
                    (
                        "src/t.rs",
                        "use crate::W;\n#[trust_vc::ensures(true)]\n\
                         pub fn a1(v: W) { let z = v / 2 + 200; }\n",
                    ),
                    ("src/c.rs", "pub type W = u64;\n"),
                ],
                "src/t.rs",
                "a1",
                "ensures",
            )
        };
        for (tag, head, tail) in [
            ("quoted_key", "", "[lib]\n\"path\" = \"lib.rs\"\n"),
            ("single_quoted_key", "", "[lib]\n'path' = \"lib.rs\"\n"),
            ("quoted_header", "", "[\"lib\"]\npath = \"lib.rs\"\n"),
            ("dotted_root_key", "lib.\"path\" = \"lib.rs\"\n", ""),
            (
                "escaped_dots",
                "",
                "[lib]\npath = \"src/\\u002e\\u002e/lib.rs\"\n",
            ),
        ] {
            assert_not_verified(&verdict(&format!("manifest_{tag}"), head, tail));
        }
        assert_verified(&verdict(
            "manifest_twin",
            "",
            "[lib]\npath = \"src/lib.rs\"\n",
        ));
    }

    /// The default build script beside `src` declares `mod src;`, which
    /// `src/mod.rs` answers, and re-exports `b.rs`'s byte as `W`. `src/t.rs`
    /// is then also a module of the build script, whose `crate::W` is the
    /// byte, and `a1(255)` overflows when the script runs, while the lane
    /// read only `src`, whose `W` is `c.rs`'s `u64`. A `src/mod.rs`, or a
    /// `src.rs` beside `src`, now refuses the crate: either lets a root the
    /// lane does not read declare `src` as a module (the refusal's text is
    /// pinned by `the_crate_source_directory_is_the_package_src`; here `W` is
    /// unknown once nothing is copied, and the answer fails closed first).
    /// The twin has neither the `mod src;` line nor `src/mod.rs`.
    #[test]
    fn a_module_file_for_src_itself_refuses_the_crate() {
        let verdict = |tag: &str, build: &str, src_module: Option<(&str, &str)>| {
            let mut files = vec![
                ("Cargo.toml", MANIFEST),
                ("build.rs", build),
                ("b.rs", "pub type W = u8;\n"),
                ("src/lib.rs", "pub mod t;\nmod c;\npub use c::W;\n"),
                (
                    "src/t.rs",
                    "use crate::W;\n#[trust_vc::ensures(true)]\n\
                     pub fn a1(v: W) { let z = v / 2 + 200; }\n",
                ),
                ("src/c.rs", "pub type W = u64;\n"),
            ];
            files.extend(src_module);
            package_verdict(tag, &files, "src/t.rs", "a1", "ensures")
        };
        let build = "mod b;\nmod src;\npub use b::W;\nfn main() { src::t::a1(255); }\n";
        assert_not_verified(&verdict(
            "src_mod_rs",
            build,
            Some(("src/mod.rs", "pub mod t;\npub mod c;\n")),
        ));
        assert_not_verified(&verdict(
            "src_rs_beside",
            build,
            Some(("src.rs", "pub mod t;\npub mod c;\n")),
        ));
        assert_verified(&verdict(
            "src_module_twin",
            "mod b;\npub use b::W;\nfn main() {}\n",
            None,
        ));
    }

    /// Whether the file system under the temporary directory opens a file by
    /// a name that differs from it in case only.
    fn case_insensitive_file_system() -> bool {
        let dir = std::env::temp_dir().join(format!("trust_vc_case_probe_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("create probe dir");
        std::fs::write(dir.join("PROBE.RS"), "").expect("write probe");
        let insensitive = dir.join("probe.rs").is_file();
        let _ = std::fs::remove_dir_all(&dir);
        insensitive
    }

    /// `mod b;` opens `src/b.rs`, which a case-insensitive file system gives
    /// as `src/B.RS`, `src/b.Rs` or the directory module `src/b/MOD.RS`, and
    /// which this one also gives as `src/b.rſ` (it folds `ſ` to `s`).
    /// `trustc` reads that file's byte `W`, and `v / 2 + 200` overflows at
    /// `v = 255`. The lane skipped a file whose extension was not a lowercase
    /// `rs` and read `c.rs`'s `u64`. It now reads an `rs` extension in any
    /// case, where the two declarations of `W` fail closed in the lowering,
    /// and refuses a file whose extension is not ASCII. Each twin re-exports
    /// `c.rs`'s `W`;
    /// a file system that keeps case does not open `B.RS` for `mod b;`, and
    /// there the missing `src/b.rs` refuses it.
    #[test]
    fn a_module_file_named_in_another_case_is_read() {
        let verdict = |tag: &str, module_file: &str, b: &str| {
            package_verdict(
                tag,
                &[
                    ("Cargo.toml", MANIFEST),
                    (
                        "src/lib.rs",
                        "mod b;\nmod c;\nuse b::W;\n#[trust_vc::ensures(true)]\n\
                         pub fn n1(v: W) { let z = v / 2 + 200; }\n",
                    ),
                    (module_file, b),
                    ("src/c.rs", "pub type W = u64;\n"),
                ],
                "src/lib.rs",
                "n1",
                "ensures",
            )
        };
        let insensitive = case_insensitive_file_system();
        for (tag, module_file) in [
            ("upper", "src/B.RS"),
            ("mixed", "src/b.Rs"),
            ("directory_upper", "src/b/MOD.RS"),
        ] {
            assert_not_verified(&verdict(
                &format!("case_{tag}"),
                module_file,
                "pub type W = u8;\n",
            ));
            let twin = verdict(
                &format!("case_{tag}_twin"),
                module_file,
                "pub use crate::c::W;\n",
            );
            if insensitive {
                assert_verified(&twin);
            } else {
                assert_not_verified(&twin);
            }
        }
        assert_refused(
            &verdict("case_long_s", "src/b.r\u{17f}", "pub type W = u8;\n"),
            "has an extension that is not ASCII",
        );
        assert_verified(&verdict(
            "case_long_s_twin",
            "src/b.rs",
            "pub use crate::c::W;\n",
        ));
    }

    /// `lib.rs` declares `mod gen;`, whose file a build script writes
    /// (`pub type W = u8;`) after the lane has read the crate, so `use
    /// gen::W;` is the byte and `v / 2 + 200` overflows at `v = 255` (built
    /// with such a script, `targo` prints `u8`). The lane read the crate
    /// without `gen` and took `c.rs`'s `u64`. A `mod` whose file is missing
    /// now refuses the file. The twin's `src/gen.rs` re-exports `c.rs`'s `W`.
    #[test]
    fn a_module_whose_file_is_missing_refuses_the_file() {
        let verdict = |tag: &str, generated: Option<&str>| {
            let mut files = vec![
                ("Cargo.toml", MANIFEST),
                (
                    "src/lib.rs",
                    "mod gen;\nmod c;\nuse gen::W;\n#[trust_vc::ensures(true)]\n\
                     pub fn m1(v: W) { let z = v / 2 + 200; }\n",
                ),
                ("src/c.rs", "pub type W = u64;\n"),
            ];
            files.extend(generated.map(|text| ("src/gen.rs", text)));
            package_verdict(tag, &files, "src/lib.rs", "m1", "ensures")
        };
        assert_refused(
            &verdict("missing_module", None),
            "`src/lib.rs` declares `mod gen`, and neither `src/gen.rs` nor `src/gen/mod.rs` exists",
        );
        assert_verified(&verdict(
            "missing_module_twin",
            Some("pub use crate::c::W;\n"),
        ));
        // The module directory of `src/m.rs` is `src/m/`, and an inline
        // module adds its own name below it.
        let nested = |tag: &str, inner: Option<&str>| {
            let mut files = vec![
                ("Cargo.toml", MANIFEST),
                (
                    "src/lib.rs",
                    "mod m;\nmod c;\nuse m::i::gen::W;\n#[trust_vc::ensures(true)]\n\
                     pub fn m2(v: W) { let z = v / 2 + 200; }\n",
                ),
                ("src/m.rs", "pub mod i { pub mod gen; }\n"),
                ("src/c.rs", "pub type W = u64;\n"),
                ("src/gen.rs", "pub use crate::c::W;\n"),
            ];
            files.extend(inner.map(|text| ("src/m/i/gen.rs", text)));
            package_verdict(tag, &files, "src/lib.rs", "m2", "ensures")
        };
        assert_refused(
            &nested("missing_nested_module", None),
            "`src/m.rs` declares `mod gen`, and neither `src/m/i/gen.rs`",
        );
        assert_verified(&nested(
            "missing_nested_module_twin",
            Some("pub use crate::c::W;\n"),
        ));
    }

    /// In a trait, `Self::Item` is the associated type of a supertrait that
    /// no file declares: `trait Tr: Iterator<Item = u8>`, or `where Self:
    /// Iterator<Item = u8>`, makes it the byte (`Add<Output = u8>` does the
    /// same for `Self::Output`), and `<IntoIter<u8> as Tr>::h(255)`
    /// overflows. The rules read it as the variant `Item` of an enum of the
    /// file or crate, and the lane read the `u64` alias `Item`. `Self::Name`
    /// is now a variant only in a value or a pattern inside an `impl` of an
    /// enum with that variant. Each twin's method takes the byte by name and
    /// adds 20, which fits.
    #[test]
    fn self_in_a_trait_names_a_supertrait_associated_type() {
        let liar = "fn h(v: Self::Item) { let z = v / 2 + 200; }";
        let twin = "fn h(v: u8) { let z = v / 2 + 20; }";
        let head = "pub type Item = u64;\npub enum K { Item }\n";
        let file = |tag: &str, source: &str| {
            package_verdict(tag, &[("f.rs", source)], "f.rs", "h", "ensures")
        };
        for (tag, header) in [
            ("supertrait", "pub trait Tr: Iterator<Item = u8>"),
            (
                "where_clause",
                "pub trait Tr where Self: Iterator<Item = u8>",
            ),
        ] {
            let source = |method: &str| {
                format!("{head}{header} {{\n#[trust_vc::ensures(true)]\n{method}\n}}\n")
            };
            assert_refused(
                &file(&format!("self_{tag}"), &source(liar)),
                "the path `Self :: Item` spells `Item`",
            );
            assert_verified(&file(&format!("self_{tag}_twin"), &source(twin)));
        }
        let output = |method: &str| {
            format!(
                "pub type Output = u64;\npub enum K {{ Output }}\n\
                 pub trait Tr: Sized + core::ops::Add<Output = u8> {{\n\
                 #[trust_vc::ensures(true)]\n{method}\n}}\n"
            )
        };
        assert_refused(
            &file(
                "self_output",
                &output("fn h(v: Self::Output) { let z = v / 2 + 200; }"),
            ),
            "the path `Self :: Output` spells `Output`",
        );
        assert_verified(&file("self_output_twin", &output(twin)));

        let tr = |method: &str| {
            format!(
                "pub trait Tr: Iterator<Item = u8> {{\n#[trust_vc::ensures(true)]\n{method}\n}}\n"
            )
        };
        let in_crate = |tag: &str, lib: &str, a: &str| {
            package_verdict(
                tag,
                &[
                    ("Cargo.toml", MANIFEST),
                    ("src/lib.rs", lib),
                    ("src/a.rs", a),
                ],
                "src/lib.rs",
                "h",
                "ensures",
            )
        };
        // `src/a.rs`, which no `mod` declares, holds the alias and the enum.
        assert_refused(
            &in_crate("self_crate_unlisted", &tr(liar), head),
            "spells `Self::Item`",
        );
        assert_verified(&in_crate("self_crate_unlisted_twin", &tr(twin), head));
        // The enum is in `lib.rs` and the alias in `src/a.rs`.
        let enum_here = |method: &str| format!("pub enum K {{ Item }}\n{}", tr(method));
        assert_refused(
            &in_crate(
                "self_crate_enum_here",
                &enum_here(liar),
                "pub type Item = u64;\n",
            ),
            "spells `Self::Item`",
        );
        assert_verified(&in_crate(
            "self_crate_enum_here_twin",
            &enum_here(twin),
            "pub type Item = u64;\n",
        ));
    }

    /// A target `path` in each spelling TOML allows, and the build script.
    #[test]
    fn the_manifest_target_roots_are_read_as_toml() {
        let root =
            std::env::temp_dir().join(format!("trust_vc_manifest_roots_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        for path in [
            "lib.rs",
            "build.rs",
            "src/lib.rs",
            "src/x/lib.rs",
            "src/build.rs",
        ] {
            let path = root.join(path);
            std::fs::create_dir_all(path.parent().expect("parent")).expect("create dir");
            std::fs::write(path, "").expect("write");
        }
        let package = root.canonicalize().expect("canonical package");
        let src = package.join("src");
        let roots = |manifest: &str| manifest_target_roots(&package, &src, manifest);
        let refused = |manifest: &str, text: &str| {
            let why = roots(manifest).expect_err(manifest);
            assert!(why.contains(text), "{manifest}: {why}");
        };
        assert_eq!(
            roots("[lib]\npath = \"src/x/lib.rs\"\n"),
            Ok(vec![src.join("x/lib.rs")])
        );
        assert_eq!(
            roots("[dependencies]\nlibc = { path = \"../libc\" }\n"),
            Ok(Vec::new())
        );
        assert_eq!(roots("[package]\nbuild = \"build.rs\"\n"), Ok(Vec::new()));
        assert_eq!(roots("[package]\nbuild = false\n"), Ok(Vec::new()));
        assert_eq!(
            roots("[package]\nbuild = \"src/build.rs\"\n"),
            Ok(vec![src.join("build.rs")])
        );
        for manifest in [
            "[lib]\npath = \"lib.rs\"\n",
            "lib = { path = \"lib.rs\" }\n",
            "[lib]\n\"path\" = \"lib.rs\"\n",
            "[lib]\n'path' = \"lib.rs\"\n",
            "[\"lib\"]\npath = \"lib.rs\"\n",
            "lib.\"path\" = \"lib.rs\"\n[package]\nname = \"p\"\n",
            "[lib]\n\"p\\u0061th\" = \"lib.rs\"\n",
        ] {
            refused(manifest, "places a crate root at `lib.rs`, outside `src`");
        }
        refused(
            "[lib]\npath = \"src/\\u002e\\u002e/lib.rs\"\n",
            "places a crate root at `src/../lib.rs`, outside `src`",
        );
        refused(
            "bin = [\n  { name = \"b\", path = \"build.rs\" },\n]\n",
            "places a crate root at `build.rs`, outside `src`",
        );
        refused(
            "[[test]]\nname = \"t\"\npath = \"src/missing.rs\"\n",
            "places a crate root at `src/missing.rs`, which does not resolve to a file",
        );
        refused(
            "[lib]\npath = 5\n",
            "a `path` of type integer, not a string",
        );
        refused(
            "lib = \"lib.rs\"\n",
            "gives `lib` a value that is not a table",
        );
        refused("[lib\npath = \"lib.rs\"\n", "does not parse as TOML");

        // A root named through a symbolic link, at any part of its path.
        std::os::unix::fs::symlink("src/lib.rs", root.join("linked.rs")).expect("link file");
        std::os::unix::fs::symlink("src", root.join("srcl")).expect("link dir");
        std::fs::create_dir_all(root.join("tool")).expect("create tool");
        std::os::unix::fs::symlink("../src/lib.rs", root.join("tool/main.rs")).expect("link");
        std::os::unix::fs::symlink("lib.rs", root.join("src/l.rs")).expect("link in src");
        for (manifest, link) in [
            ("[lib]\npath = \"linked.rs\"\n", "linked.rs"),
            ("[lib]\npath = \"srcl/lib.rs\"\n", "srcl"),
            ("[lib]\npath = \"src/l.rs\"\n", "src/l.rs"),
            ("[lib]\npath = \"./srcl/x/../lib.rs\"\n", "srcl"),
            (
                "[[bin]]\nname = \"b\"\npath = \"tool/main.rs\"\n",
                "tool/main.rs",
            ),
            ("[package]\nbuild = \"linked.rs\"\n", "linked.rs"),
        ] {
            refused(manifest, &format!("through the symbolic link `{link}`"));
        }
        assert_eq!(
            roots("[lib]\npath = \"src/lib.rs\"\n"),
            Ok(vec![src.join("lib.rs")])
        );
        let absolute = format!("[lib]\npath = \"{}\"\n", src.join("lib.rs").display());
        assert_eq!(roots(&absolute), Ok(vec![src.join("lib.rs")]));
        let _ = std::fs::remove_dir_all(&root);
    }

    const LINKED_ROOT: &str = "mod b;\nmod c;\nuse b::W;\n#[trust_vc::ensures(true)]\n\
                               pub fn s1(v: W) { let z = v / 2 + 200; }\n";

    /// The manifest names a crate root through a symbolic link outside
    /// `src` that resolves into it: `lib.rs` beside the manifest links to
    /// `src/lib.rs`. rustc opens the root's modules beside the link, so `mod
    /// b;` is `b.rs` beside the manifest, whose `W` is `u8`, and `s1(255)`
    /// overflows (built with `trustc` through the link, `size_of::<b::W>()`
    /// is 1). The lane resolved the link and read `src/b.rs`, whose `W` is
    /// `src/c.rs`'s `u64`. The same holds for a `[[bin]]` root, for a link in
    /// another directory (`tool/main.rs`, whose modules rustc opens in
    /// `tool/`), and for a module of the linked root checked on its own. A
    /// root named through a link now refuses the crate (the refusal's text
    /// is pinned by `the_manifest_target_roots_are_read_as_toml`; here `W` is
    /// unknown once nothing is copied, and the answer fails closed first).
    /// Each twin's manifest names the root under `src` and leaves the links
    /// in place.
    #[test]
    fn a_manifest_root_named_through_a_link_refuses_the_crate() {
        for (tag, root, link, text, liar, twin) in [
            (
                "lib",
                "src/lib.rs",
                "lib.rs",
                "src/lib.rs",
                "[lib]\npath = \"lib.rs\"\n",
                "[lib]\npath = \"src/lib.rs\"\n",
            ),
            (
                "bin",
                "src/main.rs",
                "main.rs",
                "src/main.rs",
                "[[bin]]\nname = \"t\"\npath = \"main.rs\"\n",
                "[[bin]]\nname = \"t\"\npath = \"src/main.rs\"\n",
            ),
            (
                "other_name",
                "src/x.rs",
                "root.rs",
                "src/x.rs",
                "[lib]\npath = \"root.rs\"\n",
                "[lib]\npath = \"src/x.rs\"\n",
            ),
            (
                "tool_dir",
                "src/main.rs",
                "tool/main.rs",
                "../src/main.rs",
                "[[bin]]\nname = \"t\"\npath = \"tool/main.rs\"\n",
                "[[bin]]\nname = \"t\"\npath = \"src/main.rs\"\n",
            ),
        ] {
            for (suffix, tail) in [("", liar), ("_twin", twin)] {
                let manifest = format!("{MANIFEST}{tail}");
                let verdict = linked_package_verdict(
                    &format!("linked_root_{tag}{suffix}"),
                    &[
                        ("Cargo.toml", manifest.as_str()),
                        (root, LINKED_ROOT),
                        ("src/b.rs", "pub use crate::c::W;\n"),
                        ("src/c.rs", "pub type W = u64;\n"),
                        ("b.rs", "pub type W = u8;\n"),
                        ("c.rs", "pub type W = u64;\n"),
                        ("tool/b.rs", "pub type W = u8;\n"),
                        ("tool/c.rs", "pub type W = u64;\n"),
                    ],
                    &[(link, text)],
                    root,
                    "s1",
                    "ensures",
                );
                if suffix.is_empty() {
                    assert_not_verified(&verdict);
                } else {
                    assert_verified(&verdict);
                }
            }
        }
        let module = |tag: &str, tail: &str| {
            let manifest = format!("{MANIFEST}{tail}");
            linked_package_verdict(
                tag,
                &[
                    ("Cargo.toml", manifest.as_str()),
                    ("src/lib.rs", "mod b;\nmod t;\nmod c;\npub use b::W;\n"),
                    (
                        "src/t.rs",
                        "use crate::W;\n#[trust_vc::ensures(true)]\n\
                         pub fn a1(v: W) { let z = v / 2 + 200; }\n",
                    ),
                    ("src/b.rs", "pub use crate::c::W;\n"),
                    ("src/c.rs", "pub type W = u64;\n"),
                    ("b.rs", "pub type W = u8;\n"),
                    ("c.rs", "pub type W = u64;\n"),
                ],
                &[("lib.rs", "src/lib.rs"), ("t.rs", "src/t.rs")],
                "src/t.rs",
                "a1",
                "ensures",
            )
        };
        assert_not_verified(&module("linked_root_module", "[lib]\npath = \"lib.rs\"\n"));
        assert_verified(&module(
            "linked_root_module_twin",
            "[lib]\npath = \"src/lib.rs\"\n",
        ));
    }

    /// `src/t.rs` is a symbolic link to `src/x/t.rs`, the verified file, and
    /// `src/lib.rs` declares both `mod x { pub mod t; }` and `mod t;`. As
    /// `t`, rustc opens the file's `mod c;` beside the link, at `src/t/c.rs`,
    /// which a build script writes (`pub type W = u8;`) after the lane has
    /// read the crate, so `s2(255)` overflows through `crate::t::s2` (built
    /// with such a script, `targo` panics there). The lane read the module
    /// beside the file, `src/x/t/c.rs`, whose `W` is `u64`, and found every
    /// module file present. A path at which the verified file is reached
    /// through a link now refuses it. The twin's `src/t.rs` is a file that
    /// re-exports `s2`.
    #[test]
    fn the_verified_file_reached_through_a_link_refuses_the_crate() {
        let verdict = |tag: &str, linked: bool, target: &str| {
            let mut files = vec![
                ("Cargo.toml", MANIFEST),
                ("src/lib.rs", "mod x {\n    pub mod t;\n}\nmod t;\n"),
                (
                    "src/x/t.rs",
                    "mod c;\nuse c::W;\n#[trust_vc::ensures(true)]\n\
                     pub fn s2(v: W) { let z = v / 2 + 200; }\n",
                ),
                ("src/x/t/c.rs", "pub type W = u64;\n"),
            ];
            let mut links = Vec::new();
            if linked {
                links.push(("src/t.rs", "x/t.rs"));
            } else {
                files.push(("src/t.rs", "pub use crate::x::t::s2;\n"));
            }
            linked_package_verdict(tag, &files, &links, target, "s2", "ensures")
        };
        assert_refused(
            &verdict("linked_target", true, "src/x/t.rs"),
            "`src/t.rs` is the verified file reached through a symbolic link",
        );
        assert_refused(
            &verdict("linked_target_at_link", true, "src/t.rs"),
            "`src/t.rs` is the verified file reached through a symbolic link",
        );
        assert_verified(&verdict("linked_target_twin", false, "src/x/t.rs"));
    }

    /// `verdict` is refused because a file spells an identifier whose
    /// character `code` is outside ASCII.
    fn assert_spelling_refused(verdict: &FunctionVerdict, code: &str) {
        assert_eq!(verdict.result, VerdictKind::Error, "{:?}", verdict.detail);
        let detail = verdict.detail.clone().unwrap_or_default();
        assert!(
            detail.contains(&format!("whose character {code} is outside ASCII")),
            "{detail}"
        );
    }

    /// `src/z.rs` declares `pub type \u{212A} = u8;` with the Kelvin sign,
    /// which rustc reads in Unicode normalization form C as `K`, so `use
    /// z::K;` and the path `z::K` in `src/lib.rs` are the byte and `v / 2 +
    /// 200` overflows at `v = 255` (built with `targo`, `u8_(255)` panics).
    /// The lane compared the strings as written and read `K` as
    /// `src/a.rs`'s `u64`. The same holds for `src/z.rs` declaring `W`
    /// followed by a combining acute accent, which `use z::W\u{e9};`
    /// imports; every line that names that type spells it outside ASCII, so
    /// it has no twin the rule admits. A crate file that spells an
    /// identifier outside ASCII now refuses the file, whatever the
    /// identifier names: a sibling whose only such identifier is a
    /// function's makes a true program that is refused. Each twin's
    /// `src/z.rs` is ASCII.
    #[test]
    fn a_crate_file_that_spells_an_identifier_outside_ascii_refuses_the_file() {
        for (tag, lib, name) in [
            (
                "use",
                "mod a;\nmod z;\nuse z::K;\n#[trust_vc::ensures(true)]\n\
                 pub fn u8_(v: K) { let z = v / 2 + 200; }\n",
                "u8_",
            ),
            (
                "path",
                "mod a;\nmod z;\n#[trust_vc::ensures(true)]\n\
                 pub fn u11(v: z::K) { let z = v / 2 + 200; }\n",
                "u11",
            ),
        ] {
            let verdict = |suffix: &str, z: &str| {
                crate_verdict(
                    &format!("kelvin_{tag}{suffix}"),
                    &[
                        ("lib.rs", lib),
                        ("a.rs", "pub type K = u64;\n"),
                        ("z.rs", z),
                    ],
                    "lib.rs",
                    name,
                    "ensures",
                )
            };
            assert_spelling_refused(&verdict("", "pub type \u{212A} = u8;\n"), "U+212A");
            assert_verified(&verdict("_twin", "pub use crate::a::K;\n"));
        }
        let nfd = crate_verdict(
            "nfd_use",
            &[
                (
                    "lib.rs",
                    "mod a;\nmod z;\nuse z::W\u{e9};\n#[trust_vc::ensures(true)]\n\
                     pub fn u10(v: W\u{e9}) { let z = v / 2 + 200; }\n",
                ),
                ("a.rs", "pub type W\u{e9} = u64;\n"),
                ("z.rs", "pub type We\u{301} = u8;\n"),
            ],
            "lib.rs",
            "u10",
            "ensures",
        );
        assert_spelling_refused(&nfd, "U+00E9");
        let function_only = |tag: &str, z: &str| {
            crate_verdict(
                tag,
                &[
                    (
                        "lib.rs",
                        "mod a;\nmod z;\nuse a::K;\n#[trust_vc::ensures(true)]\n\
                         pub fn u14(v: K) { let z = v / 2 + 200; }\n",
                    ),
                    ("a.rs", "pub type K = u64;\n"),
                    ("z.rs", z),
                ],
                "lib.rs",
                "u14",
                "ensures",
            )
        };
        assert_refused(
            &function_only("kelvin_fn_only", "pub fn \u{212A}() {}\n"),
            "in `src/z.rs`, the file spells the identifier",
        );
        assert_verified(&function_only("kelvin_fn_only_twin", "pub fn k() {}\n"));
    }
    /// The path dependency `dep` declares the spec function `\u{212A}` with
    /// the Kelvin sign, which rustc reads as `K`, so the running code of
    /// `d1` calls a spec function through `dep::K`, which has no executable
    /// body (built with the real macros, the call panics). The import matched
    /// names as written, found no `K`, and `d1` was `Verified`; with the
    /// ASCII `K` it is refused for that call. A dependency source that spells
    /// an identifier outside ASCII now refuses the import. The twin's `dep`
    /// declares an exec `K`.
    #[test]
    fn a_dependency_that_spells_an_identifier_outside_ascii_refuses_the_import() {
        let verdict = |tag: &str, dep: &str| {
            package_verdict(
                tag,
                &[
                    (
                        "Cargo.toml",
                        "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\n\
                         edition = \"2021\"\n[dependencies]\ndep = { path = \"dep\" }\n",
                    ),
                    (
                        "src/lib.rs",
                        "#[trust_vc::ensures(true)]\npub fn d1(x: u64) { let y = dep::K(x); }\n",
                    ),
                    (
                        "dep/Cargo.toml",
                        "[package]\nname = \"dep\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
                    ),
                    ("dep/src/lib.rs", dep),
                ],
                "src/lib.rs",
                "d1",
                "ensures",
            )
        };
        assert_spelling_refused(
            &verdict(
                "dep_kelvin",
                "#[trust_vc::spec]\npub fn \u{212A}(x: u64) -> u64 { x }\n",
            ),
            "U+212A",
        );
        assert_verified(&verdict(
            "dep_kelvin_twin",
            "pub fn K(x: u64) -> u64 { x }\n",
        ));
    }
}
