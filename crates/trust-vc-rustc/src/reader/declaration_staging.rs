//! Sequential native Erase emission, metadata loading and Keep consumption.
//!
//! The private handoff is owned Rust data created by real callbacks. It is
//! never reconstructed from an observation file or an authentication boolean.
//! Declaration import remains refused until the other typed prerequisites
//! (predicates/WF, generic values and macro build provenance) are supplied.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

extern crate rustc_driver;
extern crate rustc_hir_analysis;

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::Path;
use std::process::ExitCode;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::ty::TyCtxt;
use serde_json::{json, Value};

use crate::declaration_alignment::source_bindings::{Metadata, PinnedFile};
use crate::declaration_alignment::{self as alignment, NativeKey, Observation, View};

use super::{
    declaration_factory as factory, declaration_fields, declaration_modes, declaration_native,
    declaration_policy, declaration_wf, function_identity_observer,
};

mod build_origin;
mod builtins;
mod capability;
mod client_images;
mod collect;
mod emitted_rlib;
mod fields;
mod identity;
mod inputs;
mod invocation;
mod keep;
mod macro_context;
mod meaning;
mod nominal_helpers;
mod profile;
mod source_nominals;
mod spec_graph;
mod standalone_client;

pub(in crate::reader) use source_nominals::SourceNominals;
pub(in crate::reader) use spec_graph::{CheckedSourceFunction, OwnedSourceHeader};

pub(super) use capability::ClientImports;
pub(crate) use capability::LiveNormalClientRead;
pub(crate) use capability::StagedLibrary;
use inputs::Inputs;
use invocation::Invocation;
pub use macro_context::main as macro_context_main;
pub(crate) use macro_context::{NormalClientArgs, NormalClientPlan, NormalPlanIdentity};
pub(in crate::reader) use spec_graph::ClientDefinitions;
pub use standalone_client::coordinator_main as standalone_sdk_coordinator_main;
pub use standalone_client::main as standalone_client_main;
pub use standalone_client::normal_verification_main as standalone_client_normal_verify_main;
pub use standalone_client::verification_main as standalone_client_verify_main;

/// Local facts captured before encoding. This deliberately contains no
/// local SVH: that query is invalid at the pre-metadata callback seam.
struct EraseAnalysis {
    view: View,
    spec_view: spec_graph::View,
    invocation: Invocation,
}

struct EmittedErase {
    analysis: EraseAnalysis,
    file: PinnedFile,
    rlib: PinnedFile,
}

/// No TyCtxt, DefId, CrateNum or original HIR ID escapes its compiler session.
/// Only `LoadErase::after_analysis` constructs this private handoff.
struct LoadedEraseMetadata {
    view: View,
    spec_view: spec_graph::View,
    spec_roundtrip_unknown: BTreeSet<NativeKey>,
    invocation: Invocation,
    target_metadata: Metadata,
    target_svh: u128,
    file: PinnedFile,
    roundtrip_unknown: BTreeMap<NativeKey, String>,
    loader_observation: Value,
    rlib: PinnedFile,
}

/// The same fresh compiler emission has survived both real metadata loaders.
/// The RLIB pin is never supplied by a request or reconstructed from a report.
struct OwnedErase {
    view: View,
    spec_view: spec_graph::View,
    spec_roundtrip_unknown: BTreeSet<NativeKey>,
    invocation: Invocation,
    target_metadata: Metadata,
    target_svh: u128,
    file: PinnedFile,
    roundtrip_unknown: BTreeMap<NativeKey, String>,
    loader_observation: Value,
    rlib: emitted_rlib::CheckedRlib,
}

impl OwnedErase {
    fn native_images(&self) -> [&PinnedFile; 2] {
        [&self.file, self.rlib.file()]
    }

    fn contains_image(&self, selected: &PinnedFile) -> bool {
        self.native_images()
            .into_iter()
            .any(|image| image.path == selected.path && image.sha256 == selected.sha256)
    }

    fn revalidate_artifacts(&self) -> Result<(), String> {
        self.file.read()?;
        self.target_metadata.revalidate()?;
        self.rlib.revalidate()
    }
}

fn diagnostics(tcx: TyCtxt<'_>) -> Result<(), String> {
    if tcx.dcx().has_errors().is_some() {
        Err("native compiler diagnostics reject this staging phase".into())
    } else {
        Ok(())
    }
}

struct CompileErase<'a> {
    inputs: &'a Inputs,
    argv: &'a [String],
    result: Option<Result<EraseAnalysis, String>>,
}

impl Callbacks for CompileErase<'_> {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        self.result = Some((|| {
            diagnostics(tcx)?;
            let invocation = Invocation::capture(tcx, self.argv)?;
            let (metadata, _) = collect::selections(tcx, self.inputs, None)?;
            let view = collect::view(tcx, LOCAL_CRATE, self.inputs, &metadata, &invocation, None)?;
            let spec_view = spec_graph::View::capture(tcx, LOCAL_CRATE, self.inputs, &metadata)?;
            diagnostics(tcx)?;
            Ok(EraseAnalysis {
                view,
                spec_view,
                invocation,
            })
        })());
        // The genuine compiler must finish metadata emission and its normal
        // analysis. A captured declaration is not a successful build result.
        if self.result.as_ref().is_some_and(Result::is_ok) {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

fn equal_fact<T: PartialEq>(a: &Observation<T>, b: &Observation<T>) -> bool {
    match (a, b) {
        (Observation::Observed(a), Observation::Observed(b)) => a == b,
        (Observation::Unknown(_), Observation::Unknown(_)) => true,
        _ => false,
    }
}

fn roundtrip(local: &View, loaded: &View) -> Result<BTreeMap<NativeKey, String>, String> {
    if local.common != loaded.common || local.stable_crate_id != loaded.stable_crate_id {
        return Err(
            "fresh metadata does not belong to the actual Erase compiler invocation".into(),
        );
    }
    let mut definitions = BTreeMap::new();
    for declaration in &local.declarations {
        if definitions.insert(declaration.key, declaration).is_some() {
            return Err("the local Erase invocation has duplicate native declaration keys".into());
        }
    }
    let mut seen = BTreeSet::new();
    let mut unknown = BTreeMap::new();
    for declaration in &loaded.declarations {
        if !seen.insert(declaration.key) {
            return Err("fresh metadata repeats a native declaration key".into());
        }
        let valid = definitions.get(&declaration.key).is_some_and(|local| {
            equal_fact(&local.source, &declaration.source)
                && equal_fact(&local.generics, &declaration.generics)
                && equal_fact(&local.shape, &declaration.shape)
        });
        if !valid {
            unknown.insert(
                declaration.key,
                "fresh metadata does not preserve all observed local declaration facts".into(),
            );
        }
    }
    for key in definitions.keys().filter(|key| !seen.contains(key)) {
        unknown.insert(
            *key,
            "the actual local Erase declaration is absent from the loaded metadata inventory"
                .into(),
        );
    }
    Ok(unknown)
}

struct LoadErase<'a> {
    inputs: &'a Inputs,
    emitted: Option<EmittedErase>,
    argv: &'a [String],
    result: Option<Result<LoadedEraseMetadata, String>>,
}

impl Callbacks for LoadErase<'_> {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        self.result = Some((|| {
            diagnostics(tcx)?;
            let emitted = self
                .emitted
                .take()
                .ok_or("Erase emission handoff was already consumed")?;
            emitted.rlib.read()?;
            let loader = Invocation::capture(tcx, self.argv)?;
            if !loader.same_target(&emitted.analysis.invocation) {
                return Err(
                    "the fresh metadata loader uses a different native target/sysroot".into(),
                );
            }
            let (common, target) = collect::selections(tcx, self.inputs, Some(&emitted.file))?;
            let target =
                target.ok_or("the fresh Erase artifact was not selected by the native compiler")?;
            let view = collect::view(
                tcx,
                target.native_crate,
                self.inputs,
                &common,
                &emitted.analysis.invocation,
                Some(emitted.file.sha256),
            )?;
            let unknown = roundtrip(&emitted.analysis.view, &view)?;
            let spec_view =
                spec_graph::View::capture(tcx, target.native_crate, self.inputs, &common)?;
            let spec_roundtrip_unknown =
                spec_graph::roundtrip(&emitted.analysis.spec_view, &spec_view);
            if target.stable_crate_id != view.stable_crate_id {
                return Err(
                    "the loaded target native identity differs from its declaration view".into(),
                );
            }
            diagnostics(tcx)?;
            Ok(LoadedEraseMetadata {
                view,
                spec_view,
                spec_roundtrip_unknown,
                invocation: emitted.analysis.invocation,
                target_metadata: target.metadata,
                target_svh: target.svh,
                file: target.file,
                roundtrip_unknown: unknown,
                loader_observation: loader.observation(),
                rlib: emitted.rlib,
            })
        })());
        Compilation::Stop
    }
}

fn run_compiler(args: &[String], callbacks: &mut (dyn Callbacks + Send)) -> Result<(), String> {
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(args, callbacks))
        .map_err(|_| "the native compiler rejected a staging phase".into())
}

fn record_phase<T>(
    inputs: &Inputs,
    phase: &str,
    compiler: &Result<(), String>,
    callback: Option<&Result<T, String>>,
) -> Result<(), String> {
    let callback = match callback {
        Some(Ok(_)) => json!({"state": "Checked"}),
        Some(Err(reason)) => json!({"state": "Rejected", "reason": reason}),
        None => json!({"state": "NotReached"}),
    };
    let bytes = serde_json::to_vec(&json!({"phase": phase,
        "compiler_result": match compiler { Ok(()) => "Returned", Err(_) => "FatalError" },
        "compiler_error": compiler.as_ref().err(), "callback": callback,
        "import_authorized": false, "verified_functions": null}))
    .map_err(|e| e.to_string())?;
    let mut file = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(inputs.output.join("phases.jsonl"))
        .map_err(|e| e.to_string())?;
    file.write_all(&bytes)
        .and_then(|_| file.write_all(b"\n"))
        .map_err(|e| e.to_string())
}

pub(crate) fn produce(path: &Path) -> Result<StagedLibrary, String> {
    #[cfg(test)]
    {
        produce_inner(path, None)
    }
    #[cfg(not(test))]
    {
        produce_inner(path)
    }
}

fn produce_inner(
    path: &Path,
    #[cfg(test)] probe: Option<nominal_helpers::TransactionProbe>,
) -> Result<StagedLibrary, String> {
    profile::check_compiler()?;
    let inputs = Inputs::load(path)?;
    if inputs.output.starts_with(inputs.sources.root()) {
        return Err("staging outputs cannot modify the approved source graph".into());
    }
    std::fs::create_dir(&inputs.output).map_err(|e| e.to_string())?;
    for name in ["erase", "load", "keep"] {
        std::fs::create_dir(inputs.output.join(name)).map_err(|e| e.to_string())?;
    }
    inputs.revalidate()?;
    let metadata_path = collect::target_path(&inputs.output);
    let erase_args = inputs.library_args(false);
    let mut compiler = CompileErase {
        inputs: &inputs,
        argv: &erase_args,
        result: None,
    };
    let result = run_compiler(&erase_args, &mut compiler);
    record_phase(
        &inputs,
        "EraseCompileAndEmit",
        &result,
        compiler.result.as_ref(),
    )?;
    result?;
    let analysis = compiler
        .result
        .ok_or("the Erase native callback was not reached")??;
    let file = emitted_rlib::pin_output(&metadata_path)?;
    let rlib_path = metadata_path.with_extension("rlib");
    let rlib = emitted_rlib::pin_output(&rlib_path)?;
    inputs.revalidate()?;
    let client = inputs.output.join("load/client.rs");
    std::fs::write(&client, "extern crate verus_builtin;\nextern crate verus_builtin_macros;\nextern crate verus_state_machines_macros;\nextern crate vstd as staged_library;\n")
        .map_err(|e| e.to_string())?;
    let mut load_args = inputs.client_args(&file.path, &client);
    load_args.extend([
        "-o".into(),
        inputs
            .output
            .join("load/unused.rmeta")
            .display()
            .to_string(),
    ]);
    let mut loader = LoadErase {
        inputs: &inputs,
        emitted: Some(EmittedErase {
            analysis,
            file,
            rlib,
        }),
        argv: &load_args,
        result: None,
    };
    let result = run_compiler(&load_args, &mut loader);
    record_phase(
        &inputs,
        "LoadFreshEraseMetadata",
        &result,
        loader.result.as_ref(),
    )?;
    result?;
    let metadata = loader
        .result
        .ok_or("the fresh metadata callback was not reached")??;
    inputs.revalidate()?;
    let erase = emitted_rlib::load(&inputs, metadata, &client)?;
    erase.revalidate_artifacts()?;
    let adapter = function_identity_observer::Inputs::from_staging(
        &inputs.sources,
        &inputs.builtin,
        &inputs.macros,
    )?;
    let keep_args = inputs.library_args(true);
    let mut keep = keep::ConsumeKeep::new(&inputs, erase, &keep_args, adapter);
    #[cfg(test)]
    keep.set_transaction_probe(probe);
    let result = run_compiler(&keep_args, &mut keep);
    record_phase(
        &inputs,
        "ConsumeInActualKeepCallback",
        &result,
        keep.result(),
    )?;
    result?;
    let prepared = keep.finish()?;
    inputs.revalidate()?;
    StagedLibrary::new(inputs, prepared)
}

fn run(path: &Path) -> Result<(), String> {
    let library = produce(path)?;
    library.write_observation()
}

fn write_observation(inputs: &Inputs, report: &Value) -> Result<(), String> {
    inputs.revalidate()?;
    std::fs::write(
        inputs.output.join("declarations.json"),
        serde_json::to_vec_pretty(report).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())
}

/// Run the closed staging recipe from byte inputs. This infrastructure tool
/// emits diagnostics and owned native facts, never an import permission.
pub fn main() -> ExitCode {
    let mut args = std::env::args_os().skip(1);
    let result = args
        .next()
        .ok_or_else(|| "expected staging request path".into())
        .and_then(|path| {
            if args.next().is_some() {
                Err("staging accepts one request path and no compiler flag passthrough".into())
            } else {
                run(Path::new(&path))
            }
        });
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("native declaration staging: {error}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
#[path = "declaration_staging/tests.rs"]
mod tests;

/// Ordinary worker input identity/checking only; this creates no staging owner.
pub(crate) fn ordinary_file_digest(path: &Path) -> Result<alignment::Digest, String> {
    inputs::digest(path)
}
pub(crate) fn check_ordinary_native_options(
    expected: &rustc_session::config::Options,
    actual: &rustc_session::config::Options,
) -> Result<(), String> {
    invocation::check_ordinary_options(expected, actual)
}
