// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Connected normal owned-client entry. The producer and one-way macro owner
//! stay live; the normal shim performs original MIR, genuine erase child and
//! impl comparison before AY. The ghost-only entry remains independent.

use super::*;
use crate::shim::OwnedNormalVerifier;
use crate::verdict::{Outcome, Record};

struct NormalClient<'plan, 'scope> {
    owner: &'scope StandaloneImported<'scope>,
    source: &'scope ClientSource,
    plan: &'plan macro_context::NormalClientPlan<'scope>,
    verifier: OwnedNormalVerifier<'plan, 'scope>,
    imported: Option<usize>,
    native_ownership_roots: Option<usize>,
    result: Option<Result<(), String>>,
}

impl Callbacks for NormalClient<'_, '_> {
    fn config(&mut self, config: &mut Config) {
        crate::diagnostic_compat::configure(config);
    }

    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let Some(mut preparation) = self.verifier.after_expansion(tcx) else {
            return Compilation::Stop;
        };
        self.result = Some((|| {
            self.owner.check_retained_inputs()?;
            self.source.file().read()?;
            let imports = self.owner.for_client(tcx, self.plan.verify())?;
            let live = imports.read_for_normal_verification(&preparation, self.source)?;
            self.imported = Some(live.imported_count());
            self.native_ownership_roots = Some(live.native_ownership_roots());
            preparation.decide(&live)
        })());
        if let Some(Err(reason)) = &self.result {
            tcx.dcx()
                .struct_err(format!("normal owned verification refused: {reason}"))
                .emit();
        }
        Compilation::Stop
    }
}

fn verify_one(
    owner: &StandaloneImported<'_>,
    source: &ClientSource,
    index: usize,
) -> Result<bool, String> {
    let phase = format!("OwnedNormalClientVerify{index}");
    let output = owner.library().inputs.output.join(format!("{phase}.rmeta"));
    let erase_output = owner
        .library()
        .inputs
        .output
        .join(format!("{phase}-erase.rmeta"));
    owner.check_retained_inputs()?;
    let plan = macro_context::NormalClientPlan::closed(owner, source, &output, &erase_output)?;
    verify_plan(owner, source, &phase, &plan, output)
}

fn verify_plan(
    owner: &StandaloneImported<'_>,
    source: &ClientSource,
    phase: &str,
    plan: &macro_context::NormalClientPlan<'_>,
    output: std::path::PathBuf,
) -> Result<bool, String> {
    let mut callback = NormalClient {
        owner,
        source,
        plan,
        verifier: OwnedNormalVerifier::new(plan),
        imported: None,
        native_ownership_roots: None,
        result: None,
    };
    let compiler = run_compiler(plan.verify(), &mut callback);
    // Preserve actual compiler and callback errors before final input checks.
    record_phase(
        &owner.library().inputs,
        phase,
        &compiler,
        callback.result.as_ref(),
    )?;
    owner.check_retained_inputs()?;
    source.file().read()?;
    let reached = callback.result.as_ref().is_some_and(Result::is_ok);
    let mut record: Record = callback.verifier.into_record(output);
    let succeeded = compiler.is_ok()
        && reached
        && record.outcome == Some(Outcome::Checked)
        && !record.any_refused()
        && record.erase_exit
            == (if plan.invocation().expects_erase() {
                Some(0)
            } else {
                None
            });
    record.exit_code = Some(if succeeded { 0 } else { 1 });
    let report = json!({"schema": "trust-vc.owned-normal-client-verification@1", "phase": phase,
        "verify_argv": plan.verify(), "erase_argv": plan.erase(),
        "compiler_returned": compiler.is_ok(), "compiler_error": compiler.as_ref().err(),
        "callback": match &callback.result {
            Some(Ok(())) => json!({"state": "NormalPipelineReturned"}),
            Some(Err(reason)) => json!({"state": "Rejected", "reason": reason}),
            None => json!({"state": "NotReached"}),
        },
        "normal_verdict": record.to_json(), "source_path": source.file().path,
        "imported_declarations": callback.imported, "imported_verified_functions": 0,
        "original_native_ownership_roots": callback.native_ownership_roots,
        "source_sha256": source.file().sha256,
        "publication": if succeeded { "CompilerReturned0AndOwnedInputsRevalidated" } else { "NoSuccessfulPublication" },
        "ordinary_import_cli_enabled": false, "layout_or_broadcast_capability": false});
    let bytes = serde_json::to_vec_pretty(&report).map_err(|e| e.to_string())?;
    if bytes.len() > 2_097_152 {
        return Err("the normal owned report exceeds its bound".into());
    }
    std::fs::write(
        owner.library().inputs.output.join(format!("{phase}.json")),
        bytes,
    )
    .map_err(|e| e.to_string())?;
    Ok(succeeded)
}

/// # Safety
/// Dedicated process only: producer compiler workers have joined before the
/// one-way Imported transition. No later code restores global macro context.
unsafe fn run(request: &Path, sources: &[std::path::PathBuf]) -> Result<bool, String> {
    if std::env::var("VSTD_KIND").as_deref() != Ok("IsVstd") {
        return Err("normal owned verification must start in the genuine producer context".into());
    }
    if sources.is_empty() || sources.len() > 2 {
        return Err("expected one or two normal owned clients".into());
    }
    let sources = sources
        .iter()
        .map(|path| ClientSource::read(path))
        .collect::<Result<Vec<_>, _>>()?;
    let library = produce(request)?;
    library.write_observation()?;
    // SAFETY: this dedicated process has no engine workers; all producer
    // compiler calls have returned, and this owner never restores IsVstd.
    let owner = unsafe { StandaloneImported::enter(&library)? };
    owner.current()?;
    // Producer compiler workers have joined before this owned transition.
    // Frame the client stream without changing or discarding producer output;
    // later client/orchestration diagnostics remain visible on stderr.
    let boundary = json!({"schema": "trust-vc.owned-normal-stream@1",
        "event": "clients-begin", "output": library.inputs.output, "clients": sources.len(),
        "source_manifest_sha256": library.inputs.sources.identity().manifest_sha256,
        "erase_metadata_sha256": library.prepared.erase.file.sha256,
        "compiler_driver_sha256": library.inputs.compiler_driver.sha256});
    {
        use std::io::Write;
        let mut stderr = std::io::stderr().lock();
        serde_json::to_writer(&mut stderr, &boundary).map_err(|e| e.to_string())?;
        stderr.write_all(b"\n").map_err(|e| e.to_string())?;
        stderr.flush().map_err(|e| e.to_string())?;
    }
    let mut succeeded = true;
    for (index, source) in sources.iter().enumerate() {
        succeeded &= verify_one(&owner, source, index)?;
    }
    owner.check_retained_inputs()?;
    Ok(succeeded)
}

/// # Safety
/// Must be called only by the dedicated process before any engine work.
pub unsafe fn main() -> ExitCode {
    // The actual normal erase child uses this same executable. Dispatch it
    // before staging arguments or IsVstd checks; it inherits Imported and
    // compiles genuine erase argv without constructing an import capability.
    if std::env::args().nth(1).as_deref() == Some(crate::shim::ERASE_RUN_FLAG) {
        return crate::shim::main();
    }
    let mut args = std::env::args_os().skip(1);
    let result = if let Some(request) = args.next() {
        let sources = args
            .map(std::path::PathBuf::from)
            .take(3)
            .collect::<Vec<_>>();
        // SAFETY: the dedicated binary owns this process until completion.
        unsafe { run(Path::new(&request), &sources) }
    } else {
        Err(
            "expected a genuine staging request and one or two normal clients; no flag passthrough"
                .into(),
        )
    };
    match result {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(reason) => {
            eprintln!("normal owned verification refused: {reason}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests;
