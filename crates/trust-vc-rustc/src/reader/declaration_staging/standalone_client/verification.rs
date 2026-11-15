// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Dedicated in-memory verification after the one-way owned client transition.
//! Saved observations are outputs only. Every invocation performs its genuine
//! producer and current client rematch before entering the existing verifier.

use super::super::capability::PendingVerification;
use super::*;

struct VerifyClient<'scope> {
    owner: &'scope StandaloneImported<'scope>,
    source: &'scope ClientSource,
    argv: &'scope [String],
    result: Option<Result<PendingVerification, String>>,
}
impl Callbacks for VerifyClient<'_> {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        self.result = Some((|| {
            diagnostics(tcx)?;
            self.source.file().read()?;
            let imports = self.owner.for_client(tcx, self.argv)?;
            let read = imports.read_for_verification(
                tcx,
                crate::reader::ReadOptions::default(),
                self.source,
            )?;
            let result = read.verify(crate::verify::VerifyOptions::default())?;
            imports.revalidate(tcx)?;
            self.source.file().read()?;
            diagnostics(tcx)?;
            Ok(result)
        })());
        Compilation::Stop
    }
}

fn verify_one(
    owner: &StandaloneImported<'_>,
    source: &ClientSource,
    index: usize,
) -> Result<bool, String> {
    let phase = format!("OwnedClientVerify{index}");
    let args = owner.args(source, &phase)?;
    let mut callback = VerifyClient {
        owner,
        source,
        argv: &args,
        result: None,
    };
    let compiler = run_compiler(&args, &mut callback);
    // Preserve the real compiler/callback terminal state before postchecks.
    // This phase record alone carries no verification result or permission.
    record_phase(
        &owner.library().inputs,
        &phase,
        &compiler,
        callback.result.as_ref(),
    )?;
    owner.current()?;
    owner.library().inputs.revalidate()?;
    owner.images.revalidate()?;
    source.file().read()?;
    compiler?;
    let result = callback
        .result
        .ok_or("the native verification callback was not reached")??;
    let (mut value, succeeded) = result.into_report();
    value["publication"] = json!("CompilerReturned0AndPhysicalInputsRevalidated");
    let report = json!({"phase": phase, "argv": args, "compiler_returned": true,
        "callback": {"state": "VerifiedRead", "value": value},
        "ordinary_reader_imports_enabled": false});
    let bytes = serde_json::to_vec_pretty(&report).map_err(|e| e.to_string())?;
    if bytes.len() > 2_097_152 {
        return Err("the owned verification report exceeds its bound".into());
    }
    std::fs::write(
        owner.library().inputs.output.join(format!("{phase}.json")),
        bytes,
    )
    .map_err(|e| e.to_string())?;
    Ok(succeeded)
}

/// # Safety
/// This is a dedicated standalone entry with no preexisting engine/global
/// workers. Producer compiler workers return before enter; after that single
/// transition no code may restore IsVstd or start another producer.
unsafe fn run(request: &Path, sources: &[std::path::PathBuf]) -> Result<bool, String> {
    if std::env::var("VSTD_KIND").as_deref() != Ok("IsVstd") {
        return Err("owned verification must start before the one-way Imported transition".into());
    }
    if sources.is_empty() || sources.len() > 2 {
        return Err("expected one client or two independently checked clients".into());
    }
    let sources = sources
        .iter()
        .map(|path| ClientSource::read(path))
        .collect::<Result<Vec<_>, _>>()?;
    let library = produce(request)?;
    library.write_observation()?;
    let owner = unsafe { StandaloneImported::enter(&library)? };
    let mut succeeded = true;
    for (index, source) in sources.iter().enumerate() {
        // Always observe the next independent client after a logical failure.
        // Setup/refusal failures stop through Result; no expected-outcome flag.
        succeeded &= verify_one(&owner, source, index)?;
    }
    owner.current()?;
    Ok(succeeded)
}

/// # Safety
/// Only the dedicated standalone binary may call this before any engine work.
/// Unlike the observation driver this entry can start AY workers; it never
/// restores process macro context after they may have started.
pub unsafe fn main() -> ExitCode {
    let mut args = std::env::args_os().skip(1);
    let result = if let Some(request) = args.next() {
        let sources = args
            .map(std::path::PathBuf::from)
            .take(3)
            .collect::<Vec<_>>();
        unsafe { run(Path::new(&request), &sources) }
    } else {
        Err("expected a genuine staging request and one or two clients; no flag passthrough".into())
    };
    match result {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(reason) => {
            eprintln!("native owned client verification refused: {reason}");
            ExitCode::FAILURE
        }
    }
}
