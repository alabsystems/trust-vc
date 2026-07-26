// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Per-function verification wrapper with timing and certificate metadata.

mod dependency_specs;

use crate::scan::AnnotatedFunction;
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::{HashMap, VecDeque};
use std::fs;
use std::path::Path;
use std::time::Instant;
use trust_vc_core::{
    extract_verification_conditions_with_file_context, parse_file_allow_tracked,
    vc::{ObligationKind, VerificationContext},
    CounterexampleBinding, StepResultKind, VerificationReport, VerificationReportOptions,
    VerifyResult,
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
    Counterexample,
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
            | ObligationStatus::Unknown
            | ObligationStatus::Error
    )
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
fn verify_conformance_obligation(
    func: &AnnotatedFunction,
) -> (VerdictKind, Option<String>, Vec<CounterexampleBinding>) {
    let Some(path) = func.file_path.to_str() else {
        return (
            VerdictKind::Error,
            Some(format!(
                "cannot verify trait conformance in non-UTF-8 path {}",
                func.file_path.display()
            )),
            Vec::new(),
        );
    };
    // Hold the pointer-width guard across the (re-)extraction AND verification,
    // exactly as the function path does.
    let _width_guard = install_pointer_width_for(&func.file_path);
    match trust_vc_core::verify_trait_conformance_obligation(path, &func.name) {
        Ok(result) => verdict_from_result(&result),
        Err(err) => (VerdictKind::Error, Some(err.to_string()), Vec::new()),
    }
}

/// Verifies a single annotated function. Returns a verdict with timing.
pub fn verify_one(func: &AnnotatedFunction) -> FunctionVerdict {
    if crate::scan::is_trait_conformance_target(func) {
        let start = Instant::now();
        let (result, detail, bindings) = verify_conformance_obligation(func);
        return FunctionVerdict {
            function: func.clone(),
            result,
            duration_ms: u64::try_from(start.elapsed().as_millis()).unwrap_or(u64::MAX),
            detail,
            localized_failure: None,
            bindings,
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

    // Hold the pointer-width guard across extraction (load_context) AND the
    // ctx.verify() below, so directive-pinned `usize` reasoning is consistent.
    let _width_guard = install_pointer_width_for(&func.file_path);
    let start = Instant::now();
    let (result_kind, detail, cx_bindings) = match load_context(&func.file_path, &func.name) {
        Ok(ctx) => {
            let result = ctx.verify();
            let (kind, detail, bindings) = verdict_from_result(&result);
            (kind, detail, bindings)
        }
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
    if crate::scan::is_trait_conformance_target(func) {
        let start = Instant::now();
        let source_hash = source_hash(&func.file_path);
        let (result, detail, bindings) = verify_conformance_obligation(func);
        let status = match result {
            VerdictKind::Verified => ObligationStatus::Verified,
            VerdictKind::Counterexample => ObligationStatus::Counterexample,
            VerdictKind::Unknown => ObligationStatus::Unknown,
            VerdictKind::Error => ObligationStatus::Error,
            VerdictKind::Skipped => ObligationStatus::Skipped,
        };
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
                condition_hash: sha256_hex(&func.name),
                status,
                unknown_category: None,
            }],
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
        match load_context_and_report(&func.file_path, &func.name) {
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
fn install_pointer_width_for(file_path: &Path) -> Option<trust_vc_core::ir::PointerWidthGuard> {
    let source = fs::read_to_string(file_path).ok()?;
    trust_vc_core::ir::scan_pointer_width_directive(&source)
        .ok()
        .flatten()
}

fn load_context_and_report(
    file_path: &Path,
    func_name: &str,
) -> Result<(VerificationContext, VerificationReport), String> {
    // Hold the pointer-width guard across extraction AND verification.
    let _width_guard = install_pointer_width_for(file_path);
    let ctx = load_context(file_path, func_name)?;
    let report = ctx.verify_with_report(VerificationReportOptions::new());
    Ok((ctx, report))
}

fn load_context(file_path: &Path, func_name: &str) -> Result<VerificationContext, String> {
    let source = fs::read_to_string(file_path).map_err(|err| err.to_string())?;
    // Strip the `global size_of usize == N` directive before parsing (it is not
    // valid Rust at item position); the width it declares is installed by the
    // caller's `install_pointer_width_for` guard. Offsets are preserved.
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
    augment_with_sibling_type_defs(file_path, &mut ast);
    let func = find_function(&ast, func_name).ok_or_else(|| {
        format!(
            "Function '{func_name}' not found in {}",
            file_path.display()
        )
    })?;
    let mut ctx = extract_verification_conditions_with_file_context(&ast, func)
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
/// - Only type-defining items are imported (no functions, no impls, no bodies),
///   so this can never inject or weaken a proof obligation.
/// - The target file's own items stay first, so any same-named local definition
///   keeps precedence in the downstream `or_insert` registries.
/// - Best-effort: unreadable / unparseable siblings are silently skipped; if a
///   referenced type still cannot be found, lowering fails closed as before.
fn augment_with_sibling_type_defs(file_path: &Path, ast: &mut syn::File) {
    let Some(src_root) = src_root_for(file_path) else {
        return;
    };
    let target = file_path.canonicalize().ok();
    let mut sibling_type_items: Vec<syn::Item> = Vec::new();
    collect_sibling_type_items(&src_root, target.as_deref(), &mut sibling_type_items);
    ast.items.extend(sibling_type_items);
}

/// Walk up from a source file to the nearest ancestor directory named `src`.
fn src_root_for(file_path: &Path) -> Option<std::path::PathBuf> {
    let mut cur = file_path.parent();
    while let Some(dir) = cur {
        if dir.file_name().is_some_and(|name| name == "src") {
            return Some(dir.to_path_buf());
        }
        cur = dir.parent();
    }
    None
}

fn collect_sibling_type_items(
    dir: &Path,
    target_canonical: Option<&Path>,
    out: &mut Vec<syn::Item>,
) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_sibling_type_items(&path, target_canonical, out);
            continue;
        }
        if path.extension().is_none_or(|ext| ext != "rs") {
            continue;
        }
        // Skip the target file itself — its items are already in the AST.
        if let (Some(target), Ok(this)) = (target_canonical, path.canonicalize()) {
            if this == target {
                continue;
            }
        }
        let Ok(source) = fs::read_to_string(&path) else {
            continue;
        };
        let Ok(ast) = parse_file_allow_tracked(&source) else {
            continue;
        };
        collect_type_items_from_items(&ast.items, out);
    }
}

/// Recursively gather `enum` / `struct` / `type` items (including those nested in
/// inline modules) as standalone top-level items.
fn collect_type_items_from_items(items: &[syn::Item], out: &mut Vec<syn::Item>) {
    for item in items {
        match item {
            syn::Item::Enum(_) | syn::Item::Struct(_) | syn::Item::Type(_) => {
                out.push(item.clone());
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

fn find_function<'a>(ast: &'a syn::File, func_name: &str) -> Option<&'a syn::ItemFn> {
    find_in_items(&ast.items, func_name)
}

/// Recursive search matching trust-vc-core's function_discovery logic:
/// top-level functions first, then impl/mod/trait blocks.
fn find_in_items<'a>(items: &'a [syn::Item], name: &str) -> Option<&'a syn::ItemFn> {
    // First pass: top-level functions (preferred for name-collision avoidance).
    for item in items {
        if let syn::Item::Fn(func) = item {
            if func.sig.ident == name {
                return Some(func);
            }
        }
    }

    // Second pass: impl blocks, inline modules, trait blocks.
    for item in items {
        match item {
            syn::Item::Impl(impl_block) => {
                for impl_item in &impl_block.items {
                    if let syn::ImplItem::Fn(method) = impl_item {
                        if method.sig.ident == name {
                            return Some(impl_fn_to_item_fn_leak(method));
                        }
                    }
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, ref inner_items)) = module.content {
                    if let Some(found) = find_in_items(inner_items, name) {
                        return Some(found);
                    }
                }
            }
            syn::Item::Trait(trait_block) => {
                for trait_item in &trait_block.items {
                    if let syn::TraitItem::Fn(method) = trait_item {
                        if method.sig.ident == name {
                            if let Some(ref block) = method.default {
                                return Some(trait_fn_to_item_fn_leak(method, block));
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    None
}

fn impl_fn_to_item_fn_leak(method: &syn::ImplItemFn) -> &'static syn::ItemFn {
    Box::leak(Box::new(syn::ItemFn {
        attrs: method.attrs.clone(),
        vis: method.vis.clone(),
        sig: method.sig.clone(),
        block: Box::new(method.block.clone()),
    }))
}

fn trait_fn_to_item_fn_leak(method: &syn::TraitItemFn, block: &syn::Block) -> &'static syn::ItemFn {
    Box::leak(Box::new(syn::ItemFn {
        attrs: method.attrs.clone(),
        vis: syn::Visibility::Inherited,
        sig: method.sig.clone(),
        block: Box::new(block.clone()),
    }))
}

fn collect_obligation_verifications(
    ctx: &VerificationContext,
    report: &VerificationReport,
) -> Vec<ObligationVerification> {
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
                location,
                condition_hash: sha256_hex(obligation.condition()),
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
            model,
            bindings,
            ..
        } => {
            let detail = match model {
                Some(model) => format!("{obligation_name}: {model}"),
                None => obligation_name.clone(),
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
        VerifyResult::NotProved { reason, .. } => (
            VerdictKind::Counterexample,
            Some(format!(
                "not discharged (solver incompleteness, no model): {reason}"
            )),
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
        // Unlike `fallback_status_for_result`, attribution is unambiguous here
        // — this status belongs to the very step that produced the result — so
        // the failure is recorded against this obligation. `ObligationStatus`
        // is a certificate-schema enum whose `Counterexample` means "this
        // obligation did not hold up", which is exactly what a model-less
        // non-proof records; no model field is populated from it.
        StepResultKind::Counterexample | StepResultKind::NotProved => {
            ObligationStatus::Counterexample
        }
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

        let func = AnnotatedFunction {
            file_path: path.clone(),
            name: "identity".into(),
            line: 2,
            attributes: vec!["ensures".into()],
        };
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

        let func = AnnotatedFunction {
            file_path: path.clone(),
            name: "identity".into(),
            line: 3,
            attributes: vec!["requires".into(), "ensures".into()],
        };
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

        let func = AnnotatedFunction {
            file_path: path.clone(),
            name: "identity".into(),
            line: 2,
            attributes: vec!["contract".into()],
        };
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

        let func = AnnotatedFunction {
            file_path: path.clone(),
            name: "broken".into(),
            line: 2,
            attributes: vec!["ensures".into()],
        };
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

        let func = AnnotatedFunction {
            file_path: path.clone(),
            name: "broken".into(),
            line: 2,
            attributes: vec!["ensures".into()],
        };
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

        let func = AnnotatedFunction {
            file_path: path.clone(),
            name: "real_nonlinear2".into(),
            line: 2,
            attributes: vec!["ensures".into()],
        };
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
            model: Some("x = -1".to_string()),
            bindings: vec![CounterexampleBinding::new("x", "x", "i32", "-1")],
        };

        let (kind, detail, bindings) = verdict_from_result(&result);
        assert_eq!(kind, VerdictKind::Counterexample);
        assert_eq!(bindings.len(), 1, "real model bindings must survive");
        assert!(detail.expect("detail").contains("x = -1"));
    }
}
