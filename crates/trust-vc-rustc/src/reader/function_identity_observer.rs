//! Explicitly unverified adapter for observing function-declaration identities.
//!
//! This is not the proof-active engine hook and grants no import authority.
//! Original lowered owners remain untouched. Session-state closures only copy
//! or store owned data: the per-type mutex is held across those closures, so
//! compiler queries and file/expansion inspection must stay outside them.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

extern crate rustc_session;

use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use rustc_hir::def_id::{DefId, LocalDefId, LOCAL_CRATE};
use rustc_interface::interface::Config;
use rustc_middle::hir::ProjectedMaybeOwner;
use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;
use rustc_session::Session;
use rustc_span::{FileName, SourceFileHash, SourceFileHashAlgorithm, Symbol};
use serde_json::{json, Value};

use super::{function_identity, function_identity_projection, function_identity_resolution};

const INPUT_ENV: &str = "TRUST_VC_UNVERIFIED_FUNCTION_IDENTITY_MANIFEST";
const MARKER: &str = "verus::verus_builtin::reveal_hide_internal_path";

#[derive(Clone)]
pub(crate) struct Inputs {
    builtin: (PathBuf, String),
    macros: BTreeMap<PathBuf, String>,
    sources: BTreeMap<PathBuf, String>,
}

fn sha256(bytes: &[u8]) -> String {
    SourceFileHash::new_in_memory(SourceFileHashAlgorithm::Sha256, bytes)
        .to_string()
        .trim_start_matches("sha256=")
        .to_owned()
}

fn artifact(value: &Value) -> Result<(PathBuf, String), String> {
    let path = value["path"]
        .as_str()
        .ok_or("an artifact path is missing")?;
    let digest = value["sha256"]
        .as_str()
        .ok_or("an artifact digest is missing")?;
    if digest.len() != 64 || !digest.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err("an artifact digest is not SHA256".into());
    }
    let path = Path::new(path)
        .canonicalize()
        .map_err(|error| error.to_string())?;
    let bytes = std::fs::read(&path).map_err(|error| error.to_string())?;
    if sha256(&bytes) != digest {
        return Err(format!("observation input changed: {}", path.display()));
    }
    Ok((path, digest.to_owned()))
}

impl Inputs {
    /// Configure the unverified adapter from the staging owner's checked
    /// snapshots, without an environment manifest or receipt-JSON handoff.
    /// These byte selections still grant no execution or import authority.
    pub(crate) fn from_staging(
        sources: &crate::declaration_alignment::source_bindings::Sources,
        builtin: &crate::declaration_alignment::source_bindings::PinnedFile,
        macros: &[crate::declaration_alignment::source_bindings::PinnedFile],
    ) -> Result<Self, String> {
        let pin = |file: &crate::declaration_alignment::source_bindings::PinnedFile| {
            file.read()?;
            let path = file.path.canonicalize().map_err(|e| e.to_string())?;
            let hash = file
                .sha256
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>();
            Ok::<_, String>((path, hash))
        };
        sources.revalidate()?;
        let mut macro_files = BTreeMap::new();
        for file in macros {
            let (path, digest) = pin(file)?;
            if macro_files.insert(path, digest).is_some() {
                return Err("duplicate staging macro path".into());
            }
        }
        let mut source_files = BTreeMap::new();
        for file in sources.source_files() {
            let (path, digest) = pin(&file)?;
            if source_files.insert(path, digest).is_some() {
                return Err("duplicate staging source path".into());
            }
        }
        if macro_files.is_empty() || source_files.is_empty() {
            return Err("empty staging adapter inputs".into());
        }
        Ok(Self {
            builtin: pin(builtin)?,
            macros: macro_files,
            sources: source_files,
        })
    }

    /// This manifest authenticates measurement inputs only. It is not a
    /// self-authorizing sidecar and cannot become a final import receipt.
    pub(crate) fn from_environment() -> Result<Option<Self>, String> {
        let Some(path) = std::env::var_os(INPUT_ENV) else {
            return Ok(None);
        };
        let value: Value =
            serde_json::from_slice(&std::fs::read(path).map_err(|error| error.to_string())?)
                .map_err(|error| error.to_string())?;
        if value["schema"] != "trust-vc.unverified-function-identity-observer@1"
            || value["compiler_commit"] != env!("VC_SHIM_COMPILER_COMMIT")
            || value["observation_only"] != true
            || value["import_authorized"] != false
            || !value["verified_functions"].is_null()
        {
            return Err(
                "the identity adapter requires its explicit unverified observation input schema"
                    .into(),
            );
        }
        let builtin = artifact(&value["builtin_artifact"])?;
        let mut macros = BTreeMap::new();
        for row in value["macro_artifacts"]
            .as_array()
            .ok_or("macro artifacts are missing")?
        {
            let (path, digest) = artifact(row)?;
            if macros.insert(path, digest).is_some() {
                return Err("duplicate macro artifact".into());
            }
        }
        let mut sources = BTreeMap::new();
        for (path, digest) in value["source_files"]
            .as_object()
            .ok_or("source manifest is missing")?
        {
            let (path, digest) = artifact(&json!({"path": path, "sha256": digest}))?;
            if sources.insert(path, digest).is_some() {
                return Err("duplicate canonical source path".into());
            }
        }
        if macros.is_empty() || sources.is_empty() {
            return Err("an observation cohort is empty".into());
        }
        Ok(Some(Self {
            builtin,
            macros,
            sources,
        }))
    }
}

#[derive(Clone)]
struct Armed {
    inputs: Arc<Inputs>,
    marker: DefId,
}

#[derive(Default)]
struct State {
    armed: Option<Armed>,
    projected: HashMap<LocalDefId, OriginalHelperKey>,
    refused: HashMap<LocalDefId, String>,
    diagnostics: Counters,
}

#[derive(Clone, Default)]
struct Counters {
    provider_installs: usize,
    arm_attempts: usize,
    arm_successes: usize,
    owner_requests: usize,
    candidate_requests: usize,
    unarmed_candidates: usize,
    parse_attempts: usize,
    parse_successes: usize,
    projection_successes: usize,
    complete_attempts: usize,
    complete_successes: usize,
}

/// A fatal type-analysis error unwinds past the normal completion callback.
/// This guard preserves only session-owned diagnostic counters/categories.
/// Its Drop never queries HIR/typeck/DefIds or changes the compiler result.
pub(crate) struct DiagnosticGuard<'session> {
    session: &'session Session,
    activation_input_present: bool,
}

pub(crate) fn diagnostic_guard(
    session: &Session,
    activation_input_present: bool,
) -> DiagnosticGuard<'_> {
    DiagnosticGuard {
        session,
        activation_input_present,
    }
}

impl Drop for DiagnosticGuard<'_> {
    fn drop(&mut self) {
        let (counters, armed, projected, reasons) =
            self.session.with_trust_compiler_state::<State, _>(|state| {
                (
                    state.diagnostics.clone(),
                    state.armed.is_some(),
                    state.projected.len(),
                    state.refused.values().cloned().collect::<Vec<_>>(),
                )
            });
        // The Session mutex has been released. Neither aggregation, JSON
        // formatting nor stderr IO is allowed inside its critical section.
        // No DefId Debug formatter is called while the compiler is unwinding.
        let mut categories = BTreeMap::<String, usize>::new();
        for reason in reasons {
            *categories.entry(reason).or_default() += 1;
        }
        let refused_owner_count = categories.values().sum::<usize>();
        let category_count = categories.len();
        let mut omitted_refused_owner_count = 0;
        let categories = categories
            .into_iter()
            .enumerate()
            .filter_map(|(index, (reason, count))| {
                if index < 32 {
                    Some((reason, count))
                } else {
                    omitted_refused_owner_count += count;
                    None
                }
            })
            .collect::<BTreeMap<_, _>>();
        let report = json!({
            "phase": "UnverifiedIdentityObserverDiagnosticInventory",
            "during_unwind": std::thread::panicking(),
            "activation_input_present": self.activation_input_present,
            "armed": armed, "projected_owner_count": projected,
            "refusal_categories": categories,
            "refused_owner_count": refused_owner_count,
            "refusal_category_count": category_count,
            "omitted_refused_owner_count": omitted_refused_owner_count,
            "counters": {
                "provider_installs": counters.provider_installs,
                "arm_attempts": counters.arm_attempts, "arm_successes": counters.arm_successes,
                "owner_requests": counters.owner_requests, "candidate_requests": counters.candidate_requests,
                "unarmed_candidates": counters.unarmed_candidates,
                "parse_attempts": counters.parse_attempts, "parse_successes": counters.parse_successes,
                "projection_successes": counters.projection_successes,
                "complete_attempts": counters.complete_attempts, "complete_successes": counters.complete_successes,
            },
            "compiler_queries_from_guard": false,
            "compiler_error_or_panic_suppressed": false,
            "import_authorized": false, "verified_functions": null,
        });
        if let Ok(text) = serde_json::to_string(&report) {
            let _ = writeln!(
                std::io::stderr().lock(),
                "vstd-function-identity-inventory: {text}"
            );
        }
    }
}

/// These IDs identify ORIGINAL cached lowering only. Dense projection reuses
/// owner-local IDs for different nodes, so they must NEVER be passed to
/// hir_node_by_hir_id, projected typeck tables or other projected-body queries.
/// Consumers reparse lower_to_hir and compare this key before native
/// declaration-level resolution. A key is not a typeck result or authority.
#[derive(Clone, Debug, PartialEq, Eq)]
struct OriginalHelperKey {
    owner: LocalDefId,
    body_value: rustc_hir::ItemLocalId,
    marker_call: rustc_hir::ItemLocalId,
    operand: rustc_hir::ItemLocalId,
    receiver_nodes: Vec<rustc_hir::ItemLocalId>,
}

impl OriginalHelperKey {
    fn new(
        owner: LocalDefId,
        helper: &function_identity::ParsedHelper<'_>,
    ) -> Result<Self, String> {
        let ids = [
            helper.original_body.value.hir_id,
            helper.original_call.hir_id,
            helper.original_operand.hir_id,
        ];
        if ids.iter().any(|id| id.owner.def_id != owner) {
            return Err("an original identity operand belongs to another owner".into());
        }
        let receiver_ids = helper.target.original_receiver_ids();
        if receiver_ids.iter().any(|id| id.owner.def_id != owner) {
            return Err("an original identity receiver argument belongs to another owner".into());
        }
        Ok(Self {
            owner,
            body_value: ids[0].local_id,
            marker_call: ids[1].local_id,
            operand: ids[2].local_id,
            receiver_nodes: receiver_ids.into_iter().map(|id| id.local_id).collect(),
        })
    }
}

fn unverified_only(session: &Session) -> bool {
    !session.trust_verification_enabled()
        && !session.trust_ir_lower_enabled()
        && !session.opts.unstable_opts.trust_targo_test_monitor
        && !session.opts.unstable_opts.trust_certified_test_monitors
}

fn override_providers(session: &Session, providers: &mut Providers) {
    // The compiler rejects this callback before invocation in active modes.
    // Keep the same effective-policy guard here too; no earlier off argv can
    // authorize a later active verification/IR/monitor configuration.
    if !unverified_only(session) {
        session
            .dcx()
            .fatal("function-identity observation cannot override proof-active compiler providers");
    }
    session.with_trust_compiler_state::<State, _>(|state| {
        state.diagnostics.provider_installs += 1;
    });
    providers.queries.hir_owner = projected_owner;
}

pub(crate) fn configure(config: &mut Config) -> Result<(), String> {
    if config.override_queries.is_some() {
        return Err("identity observation does not compose with another query override".into());
    }
    config.override_queries = Some(override_providers);
    Ok(())
}

/// Copy only the adapter's owner quarantine state. Callers must perform any
/// compiler/body queries before this short Session-state critical section.
pub(super) fn body_is_quarantined(session: &Session, owner: LocalDefId) -> bool {
    session.with_trust_compiler_state::<State, _>(|state| {
        state.projected.contains_key(&owner) || state.refused.contains_key(&owner)
    })
}

/// Bind the actual compiler-selected foreign metadata/artifact before arming.
/// This runs after expansion, with the original resolver complete.
pub(crate) fn arm(tcx: TyCtxt<'_>, inputs: Inputs) -> Result<Value, String> {
    tcx.sess.with_trust_compiler_state::<State, _>(|state| {
        state.diagnostics.arm_attempts += 1;
    });
    if !unverified_only(tcx.sess) {
        return Err("identity observation requires unverified compiler semantics".into());
    }
    let mut marker = None;
    let mut macro_crates = HashSet::new();
    let mut selected = Vec::new();
    for &krate in tcx.crates(()) {
        let source = tcx.used_crate_source(krate);
        // Follow the same metadata preference as the compiler's source row;
        // a matching companion rlib cannot authenticate a different rmeta.
        let Some(path) = source
            .rmeta
            .as_ref()
            .or(source.rlib.as_ref())
            .or(source.dylib.as_ref())
        else {
            continue;
        };
        let path = path.canonicalize().map_err(|error| error.to_string())?;
        let expected = if path == inputs.builtin.0 {
            Some(&inputs.builtin.1)
        } else {
            inputs.macros.get(&path)
        };
        let Some(expected) = expected else {
            continue;
        };
        if sha256(&std::fs::read(&path).map_err(|error| error.to_string())?) != *expected {
            return Err("the selected identity artifact changed".into());
        }
        if path == inputs.builtin.0 {
            if krate == LOCAL_CRATE {
                return Err("the identity marker must be an external genuine builtin".into());
            }
            marker = tcx
                .diagnostic_items(krate)
                .name_to_id
                .get(&Symbol::intern(MARKER))
                .copied();
        } else {
            macro_crates.insert(krate);
        }
        selected.push(
            json!({"path": path.display().to_string(), "sha256": expected,
            "stable_crate_id": format!("{:016x}", tcx.stable_crate_id(krate).as_u64()),
            "svh": tcx.crate_hash(krate).to_string()}),
        );
    }
    let marker = marker.ok_or("the actual selected builtin has no native identity marker")?;
    if macro_crates.len() != inputs.macros.len() {
        return Err(
            "the compiler did not select the complete approved macro artifact cohort".into(),
        );
    }
    // NO compiler query is called while this per-type state lock is held.
    let inputs = Arc::new(inputs);
    let already_armed = tcx.sess.with_trust_compiler_state::<State, _>(|state| {
        if state.armed.is_some() {
            true
        } else {
            state.armed = Some(Armed { inputs, marker });
            state.diagnostics.arm_successes += 1;
            false
        }
    });
    if already_armed {
        return Err("identity observation was already armed in this compiler session".into());
    }
    Ok(
        json!({"state": "UnverifiedObservationAdapterArmed", "selected_artifacts": selected,
        "import_authorized": false, "verified_functions": null,
        "permanent_proof_active_hook": "Required; this adapter cannot supply it"}),
    )
}

/// Bind only the ORIGINAL caller file and its coordinates. This is input
/// reproducibility, not authentication of expanded tokens or wrapper semantics.
/// Macro-generated/dummy/foreign anchors do not silently become authenticated.
fn approved_original_source(
    tcx: TyCtxt<'_>,
    owner: &rustc_hir::OwnerInfo<'_>,
    inputs: &Inputs,
) -> Result<Value, String> {
    let rustc_hir::OwnerNode::Item(item) = owner.node() else {
        return Err("an identity source binding requires an original item owner".into());
    };
    let span = item.span.source_callsite();
    if span.is_dummy() {
        return Err("the original identity caller has no real source span".into());
    }
    let file = tcx.sess.source_map().lookup_source_file(span.lo());
    if !file.contains(span.hi()) {
        return Err("the original identity caller crosses source files".into());
    }
    let FileName::Real(name) = &file.name else {
        return Err("the original identity caller is not a real source file".into());
    };
    let path = name
        .local_path()
        .and_then(|path| path.canonicalize().ok())
        .ok_or("the original identity caller has no canonical local source path")?;
    let expected = inputs
        .sources
        .get(&path)
        .ok_or("the original identity caller is outside the approved source manifest")?;
    let bytes =
        std::fs::read(&path).map_err(|_| "the original identity source file cannot be read")?;
    if sha256(&bytes) != *expected
        || SourceFileHash::new_in_memory(file.src_hash.kind, &bytes) != file.src_hash
    {
        return Err(
            "the original identity source bytes differ from the manifest/compiler source hash"
                .into(),
        );
    }
    let anchor = super::declaration_facts::source_anchor(tcx, span);
    if anchor["state"] != "ObservedRealSourceAnchor" {
        return Err("the original identity caller has no valid original-byte coordinates".into());
    }
    Ok(
        json!({"state": "ObservedApprovedOriginalCallerFile", "canonical_path": path.display().to_string(),
        "sha256": expected, "anchor": anchor,
        "authentication_scope": "caller file bytes and coordinates only",
        "expanded_token_provenance": {"state": "Unknown", "reason": "a source-callsite binding does not authenticate every expanded token"},
        "wrapper_semantics": {"state": "Unknown", "reason": "wrapper ancestry is not declaration-identity authority"},
        "import_authorized": false}),
    )
}

fn projected_owner<'tcx>(tcx: TyCtxt<'tcx>, id: LocalDefId) -> ProjectedMaybeOwner<'tcx> {
    tcx.sess.with_trust_compiler_state::<State, _>(|state| {
        state.diagnostics.owner_requests += 1;
    });
    let raw = tcx.lower_to_hir(id);
    let ordinary = ProjectedMaybeOwner::new(raw);
    let Some(owner) = raw.as_owner() else {
        return ordinary;
    };
    if !function_identity::is_candidate(owner) {
        return ordinary;
    }
    // Snapshot only. The state mutex is released before EVERY compiler query.
    let armed = tcx.sess.with_trust_compiler_state::<State, _>(|state| {
        state.diagnostics.candidate_requests += 1;
        if state.armed.is_none() {
            state.diagnostics.unarmed_candidates += 1;
        }
        state.armed.clone()
    });
    let Some(armed) = armed else {
        tcx.sess.with_trust_compiler_state::<State, _>(|state| {
            state.refused.insert(
                id,
                "an identity helper was queried before artifact authentication".into(),
            );
        });
        return ordinary;
    };
    let result = (|| {
        approved_original_source(tcx, owner, &armed.inputs)?;
        tcx.sess.with_trust_compiler_state::<State, _>(|state| {
            state.diagnostics.parse_attempts += 1;
        });
        let Some(helper) = function_identity::parse(owner, armed.marker)
            .map_err(|problem| problem.detail.to_owned())?
        else {
            return Ok(None);
        };
        tcx.sess.with_trust_compiler_state::<State, _>(|state| {
            state.diagnostics.parse_successes += 1;
        });
        let original_key = OriginalHelperKey::new(id, &helper)?;
        let projection =
            function_identity_projection::unverified_observation_projection(tcx, owner, &helper)
                .map_err(|problem| problem.detail.to_owned())?;
        Ok(Some((projection.projected, original_key)))
    })();
    match result {
        Ok(Some((projected, original_key))) => {
            tcx.sess.with_trust_compiler_state::<State, _>(|state| {
                state.projected.insert(id, original_key);
                state.diagnostics.projection_successes += 1;
            });
            projected
        }
        Ok(None) => ordinary,
        Err(error) => {
            tcx.sess.with_trust_compiler_state::<State, _>(|state| {
                state.refused.insert(id, error);
            });
            ordinary
        }
    }
}

/// Finalize after the ordinary analysis/projection queries, outside locks.
/// An unresolved associated form remains an explicit failed prerequisite.
pub(crate) fn complete(tcx: TyCtxt<'_>) -> Result<Value, String> {
    tcx.sess.with_trust_compiler_state::<State, _>(|state| {
        state.diagnostics.complete_attempts += 1;
    });
    let (armed, projected, refused) = tcx.sess.with_trust_compiler_state::<State, _>(|state| {
        (
            state.armed.clone(),
            state.projected.clone(),
            state.refused.clone(),
        )
    });
    let armed = armed.ok_or("identity observation was not armed")?;
    if !refused.is_empty() {
        let mut ordered_refusals = refused.into_iter().collect::<Vec<_>>();
        ordered_refusals.sort_by_key(|(id, _)| tcx.def_path_hash(id.to_def_id()));
        return Err(format!(
            "identity observation refused {} original owners: {:?}",
            ordered_refusals.len(),
            ordered_refusals
        ));
    }
    // Observe the whole ORIGINAL owner inventory, not merely the subset a
    // projected query happened to request. A cached pre-arm/raw helper or an
    // omitted candidate must fail rather than silently disappear from output.
    let mut original_candidates = HashSet::new();
    for owner in tcx.hir_crate_items(()).owners() {
        let id = owner.def_id;
        if tcx
            .lower_to_hir(id)
            .as_owner()
            .is_some_and(function_identity::is_candidate)
        {
            original_candidates.insert(id);
        }
    }
    if original_candidates != projected.keys().copied().collect::<HashSet<_>>() {
        return Err("the original identity helper inventory differs from projected owners".into());
    }
    let mut identities = Vec::new();
    let mut unresolved = Vec::new();
    // Stable hashes order observations only. Native DefId equality remains
    // the inventory/uniqueness authority, independent of diagnostic order.
    let mut ordered_owners = projected.keys().copied().collect::<Vec<_>>();
    ordered_owners.sort_by_key(|id| tcx.def_path_hash(id.to_def_id()));
    for id in ordered_owners {
        let expected_original_key = &projected[&id];
        // Re-read the ORIGINAL cached lowering, not the projected hir_owner.
        let Some(owner) = tcx.lower_to_hir(id).as_owner() else {
            return Err("an original projected owner disappeared".into());
        };
        let original_source_binding = approved_original_source(tcx, owner, &armed.inputs)?;
        let Some(helper) = function_identity::parse(owner, armed.marker)
            .map_err(|problem| problem.detail.to_owned())?
        else {
            return Err("an original helper changed shape".into());
        };
        if OriginalHelperKey::new(id, &helper)? != *expected_original_key {
            return Err("an original identity helper key changed after projection".into());
        }
        if super::declaration_modes::original_body_available(tcx, id) {
            return Err(
                "a projected identity helper unexpectedly acquired original-body mode provenance"
                    .into(),
            );
        }
        match function_identity_resolution::resolve_declaration(tcx, id, &helper.target) {
            Ok(identity) => identities.push(json!({
                "original_helper": super::declaration_facts::definition(tcx, id.to_def_id()),
                "syntax_view": "canonical lower_to_hir; no projected operand/typeck lookup",
                "original_source_binding": original_source_binding,
                "original_body_mode_check": {"state": "Unknown", "reason": "the helper is quarantined/projected; its replacement body supplies no original whole-body mode/header receipt"},
                "original_body_header_check": {"state": "Unknown", "reason": "the replacement Unit body is not evidence of the original helper's headers"},
                "actual_marker_definition": super::declaration_facts::definition(tcx, helper.marker_definition),
                "enclosing_ancestry_authority": "Unknown; wrapper provenance is not declaration-identity permission",
                "metadata_only_execution_context": "Unknown; this observer grants no executable semantics",
                "original_local_ids_debug": format!("{expected_original_key:?}"),
                "identity": identity,
            })),
            Err(reason) => unresolved.push(format!("{}: {reason}", tcx.def_path_str(id.to_def_id()))),
        }
    }
    let current = tcx.sess.with_trust_compiler_state::<State, _>(|state| {
        (
            state.projected.keys().copied().collect::<HashSet<_>>(),
            state.refused.len(),
        )
    });
    if current.0 != projected.keys().copied().collect::<HashSet<_>>() || current.1 != 0 {
        return Err("the identity projection inventory changed during native resolution".into());
    }
    if !unresolved.is_empty() {
        return Err(format!(
            "native associated identity support remains incomplete for {} helpers: {unresolved:?}",
            unresolved.len()
        ));
    }
    tcx.sess.with_trust_compiler_state::<State, _>(|state| {
        state.diagnostics.complete_successes += 1;
    });
    Ok(
        json!({"state": "ObservedNativeDeclarationIdentities", "identities": identities,
        "input_view": "explicitly unverified metadata helper projection", "import_authorized": false,
        "verified_functions": null, "original_keep_helper_type_analysis": "Not claimed",
        "permanent_proof_active_hook": "Required; not supplied by this observation adapter"}),
    )
}
