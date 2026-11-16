//! An owned standalone client context for the actual copied macro cohort.
//!
//! Construction changes the standalone process environment once. It never
//! restores that environment after a client could have started solver workers.
//! No observation or caller-supplied flag constructs this owner.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::path::Path;

use super::macro_context::ClientSource;
use super::*;
mod coordinator;
pub(super) mod footprint;
mod normal;
pub(super) mod prepared_sdk;
mod verification;
pub use coordinator::main as coordinator_main;
pub use normal::main as normal_verification_main;
pub use verification::main as verification_main;

/// Only this module's standalone entry constructs the owner. All client
/// frames borrow its exact staged library and its genuine fresh macro copies.
/// This is not a body, ownership, private-axiom or verification permission.
pub(super) struct StandaloneImported<'library> {
    images: client_images::ClientImages<'library>,
}

impl<'library> StandaloneImported<'library> {
    /// # Safety
    /// The caller is the dedicated standalone entry. Every producer compiler
    /// has returned and joined its workers; no other environment users or AY
    /// solver/global workers exist. No later code may restore IsVstd or start
    /// another producer in this process. Embedding callbacks cannot call this.
    unsafe fn enter(library: &'library StagedLibrary) -> Result<Self, String> {
        if std::env::var("VSTD_KIND").as_deref() != Ok("IsVstd") {
            return Err(
                "the standalone client transition requires its original IsVstd producer".into(),
            );
        }
        library.inputs.revalidate()?;
        let images = client_images::ClientImages::prepare(library)?;
        images.revalidate()?;
        // The process finishes in Imported context, including every error
        // path after this point. There is deliberately no Drop restoration.
        unsafe {
            std::env::set_var("VSTD_KIND", "Imported");
        }
        Ok(Self { images })
    }

    pub(super) fn library(&self) -> &'library StagedLibrary {
        self.images.library()
    }

    pub(super) fn current(&self) -> Result<(), String> {
        if std::env::var("VSTD_KIND").as_deref() != Ok("Imported") {
            return Err("the standalone client process left its one-way Imported context".into());
        }
        Ok(())
    }

    pub(super) fn check_retained_inputs(&self) -> Result<(), String> {
        self.current()?;
        self.library().inputs.revalidate()?;
        self.library().prepared.erase.revalidate_artifacts()?;
        self.images.revalidate()
    }

    /// Observe the actual old/copy macro-cache difference before admitting
    /// coordinator requests. This fixed client has no crate-local `prelude`:
    /// IsVstd expansion selects that missing module, while Imported expansion
    /// selects the actual loaded vstd prelude. No verification runs here.
    fn compare_macro_context(&self) -> Result<(), String> {
        self.check_retained_inputs()?;
        let path = self
            .library()
            .inputs
            .output
            .join("coordinator-macro-context.rs");
        let text = "#![feature(sized_hierarchy)]\nuse vstd::prelude::*;\nverus! { proof fn cache_mode_discriminator() { assert(true); } }\n";
        use std::io::Write;
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .map_err(|error| error.to_string())?;
        file.write_all(text.as_bytes())
            .map_err(|error| error.to_string())?;
        drop(file);
        let source = ClientSource::read(&path)?;
        macro_context::compare_imported_images(self.library(), &source, &self.images)?;
        self.check_retained_inputs()
    }

    pub(super) fn common_files(&self) -> &BTreeMap<std::path::PathBuf, PinnedFile> {
        self.images.common_files()
    }

    pub(super) fn macro_files(&self) -> impl Iterator<Item = &PinnedFile> {
        self.images.macro_files()
    }

    /// This closed two-macro owner derives lookup paths from its checked
    /// copied dependency view. Explicit extern paths and actual native CStore
    /// checks are independent; this is not a general-library search recipe.
    pub(super) fn native_dependency_directories(
        &self,
    ) -> Result<BTreeSet<std::path::PathBuf>, String> {
        self.check_retained_inputs()?;
        let macros = self.macro_files().collect::<Vec<_>>();
        let directories = macro_context::client_dependency_directories(self.library(), &macros)?;
        self.check_retained_inputs()?;
        Ok(directories)
    }

    /// This checks native Session state and the complete actual CStore/image
    /// selections. A raw ObservedImages or its JSON is never its constructor.
    pub(super) fn inspect<'scope, 'tcx>(
        &'scope self,
        tcx: TyCtxt<'tcx>,
        argv: &[String],
    ) -> Result<client_images::ObservedImages<'scope, 'tcx>, String> {
        self.current()?;
        diagnostics(tcx)?;
        let library = self.library();
        library.inputs.revalidate()?;
        library.prepared.erase.revalidate_artifacts()?;
        let invocation = Invocation::capture_client(tcx, argv)?;
        if !invocation.same_target(&library.prepared.erase.invocation) {
            return Err("the actual client target/sysroot differs from its staged producer".into());
        }
        let images = self.images.observe(tcx)?;
        images.current(tcx)?;
        self.current()?;
        diagnostics(tcx)?;
        Ok(images)
    }

    pub(super) fn for_client<'scope, 'tcx>(
        &'scope self,
        tcx: TyCtxt<'tcx>,
        argv: &[String],
    ) -> Result<ClientImports<'scope, 'tcx>, String>
    where
        'library: 'scope,
    {
        self.current()?;
        ClientImports::new(tcx, argv, self)
    }

    fn args(&self, source: &ClientSource, phase: &str) -> Result<Vec<String>, String> {
        self.current()?;
        let macros = self.images.macro_files().collect::<Vec<_>>();
        macro_context::client_args(
            self.library(),
            source,
            &macros,
            &self.library().inputs.output.join(format!("{phase}.rmeta")),
        )
    }
}

struct ReadClient<'scope> {
    owner: &'scope StandaloneImported<'scope>,
    source: &'scope ClientSource,
    argv: &'scope [String],
    result: Option<Result<Value, String>>,
}

impl Callbacks for ReadClient<'_> {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        self.result = Some((|| {
            diagnostics(tcx)?;
            self.source.file().read()?;
            let imports = self.owner.for_client(tcx, self.argv)?;
            let read = imports.read(tcx, super::super::ReadOptions::default())?;
            let meanings = imports.matched_meaning_observation(tcx)?;
            let wfs = trust_vc_vcir::check_crate(&read.krate);
            let footprint = footprint::capture(tcx, &read, &imports, self.source)?;
            let refused = read
                .refusals()
                .map(|refusal| {
                    json!({
                        "tag": refusal.tag, "detail": refusal.detail,
                    })
                })
                .collect::<Vec<_>>();
            let deferred = read
                .fns
                .iter()
                .filter(|function| matches!(function.status, super::super::FnStatus::Deferred(_)))
                .count();
            let complete = refused.is_empty()
                && read.errors.is_empty()
                && read.verify_refusals.is_empty()
                && read.pending_item_refusals.is_empty()
                && deferred == 0
                && wfs.is_empty();
            let report = json!({"state": "OwnedClientRead",
                "source_path": self.source.file().path,
                "source_sha256": self.source.file().sha256,
                "declarations": imports.observation(), "current_meanings": meanings,
                "footprint": footprint,
                "vcir_schema": trust_vc_vcir::SCHEMA,
                "vcir": trust_vc_vcir::pretty::crate_to_string(&read.krate),
                "read_complete": complete, "refusals": refused,
                "errors": read.errors.iter().map(|error| json!({
                    "phase_diagnostic": format!("{:?}", error.phase),
                    "message": error.message,
                })).collect::<Vec<_>>(),
                "verify_refusals": read.verify_refusals.iter().map(|refusal|
                    json!({"tag": refusal.tag, "detail": refusal.detail})).collect::<Vec<_>>(),
                "pending_item_refusals": read.pending_item_refusals.iter().map(|refusal|
                    json!({"tag": refusal.tag, "detail": refusal.detail})).collect::<Vec<_>>(),
                "wf_diagnostics": wfs.iter().map(|error| format!("{error:?}")).collect::<Vec<_>>(),
                "deferred_ownership_functions": deferred,
                "native_ownership_required": read.native_ownership.len(),
                "native_ownership_checked": false, "product_import_activated": false,
                "solver_executed": false, "verified_functions": null,
                "imported_verified_functions": 0});
            imports.revalidate(tcx)?;
            self.source.file().read()?;
            diagnostics(tcx)?;
            Ok(report)
        })());
        Compilation::Stop
    }
}

fn read_one(
    owner: &StandaloneImported<'_>,
    source: &ClientSource,
    index: usize,
) -> Result<(), String> {
    let phase = format!("OwnedClientRead{index}");
    let args = owner.args(source, &phase)?;
    let mut callback = ReadClient {
        owner,
        source,
        argv: &args,
        result: None,
    };
    let compiler = run_compiler(&args, &mut callback);
    record_phase(
        &owner.library().inputs,
        &phase,
        &compiler,
        callback.result.as_ref(),
    )?;
    let report = json!({"phase": phase, "argv": args,
        "compiler_returned": compiler.is_ok(), "compiler_error": compiler.as_ref().err(),
        "callback": match &callback.result {
            Some(Ok(value)) => json!({"state": "Read", "value": value}),
            Some(Err(reason)) => json!({"state": "Rejected", "reason": reason}),
            None => json!({"state": "NotReached"}),
        },
        "product_import_activated": false, "solver_executed": false,
        "verified_functions": null});
    std::fs::write(
        owner.library().inputs.output.join(format!("{phase}.json")),
        serde_json::to_vec_pretty(&report).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    owner.library().inputs.revalidate()?;
    owner.images.revalidate()?;
    source.file().read()?;
    compiler?;
    let value = callback
        .result
        .ok_or("the owned client callback was not reached")??;
    if value["read_complete"] != true {
        return Err("the actual owned client read retained language errors or refusals".into());
    }
    Ok(())
}

/// # Safety
/// The dedicated standalone caller excludes all other environment/engine
/// users through the producer and one-way transition. No solver is started
/// here, and no later code may restore the environment after this returns.
unsafe fn run(request: &Path, sources: &[std::path::PathBuf]) -> Result<(), String> {
    if std::env::var("VSTD_KIND").as_deref() != Ok("IsVstd") {
        return Err(
            "the standalone reader must begin before the one-way Imported transition".into(),
        );
    }
    if sources.is_empty() || sources.len() > 2 {
        return Err("the standalone reader accepts one client or its unchanged pair".into());
    }
    let sources = sources
        .iter()
        .map(|path| ClientSource::read(path))
        .collect::<Result<Vec<_>, _>>()?;
    let library = produce(request)?;
    library.write_observation()?;
    let owner = unsafe { StandaloneImported::enter(&library)? };
    for (index, source) in sources.iter().enumerate() {
        read_one(&owner, source, index)?;
    }
    owner.current()
}

/// Read actual clients through the owned native declaration handoff, without
/// invoking a solver or publishing verification. Ordinary product activation
/// remains closed and is independent of this standalone infrastructure tool.
///
/// # Safety
/// The caller must be the dedicated standalone process entry, with no other
/// environment users or existing solver/global workers before `run` begins.
pub unsafe fn main() -> ExitCode {
    let mut args = std::env::args_os().skip(1);
    let result = if let Some(request) = args.next() {
        let clients = args
            .map(std::path::PathBuf::from)
            .take(3)
            .collect::<Vec<_>>();
        unsafe { run(Path::new(&request), &clients) }
    } else {
        Err(
            "expected one staging request and one or two unchanged clients; no flag passthrough"
                .into(),
        )
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(reason) => {
            eprintln!("native owned client read: {reason}");
            ExitCode::FAILURE
        }
    }
}
