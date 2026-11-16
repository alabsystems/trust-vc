// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Dedicated fresh-producer entry. The runner receives a data socket only;
//! the actual library and its one-way owner remain on this stack until join.

use super::*;
use sha2::{Digest as _, Sha256};
use std::io::Read;
use std::process::{Command, ExitCode};

mod input;
use input::Input;

fn json(path: &std::path::Path) -> Result<(PinnedFile, Value), String> {
    let path = path.canonicalize().map_err(|error| error.to_string())?;
    let metadata = std::fs::symlink_metadata(&path).map_err(|error| error.to_string())?;
    if !metadata.file_type().is_file() || metadata.len() > 1_048_576 {
        return Err("the coordinator input must be a bounded regular JSON file".into());
    }
    let pin = PinnedFile {
        sha256: inputs::digest(&path)?,
        path,
    };
    let mut bytes = Vec::new();
    std::fs::File::open(&pin.path)
        .map_err(|error| error.to_string())?
        .take(1_048_577)
        .read_to_end(&mut bytes)
        .map_err(|error| error.to_string())?;
    if bytes.len() > 1_048_576 {
        return Err("the coordinator input exceeds its bound".into());
    }
    let observed: [u8; 32] = Sha256::digest(&bytes).into();
    if observed != pin.sha256 {
        return Err("the coordinator input changed while it was read".into());
    }
    pin.read()?;
    let value = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    Ok((pin, value))
}

/// # Safety
/// This is the dedicated binary entry before any other engine work. All
/// producer calls join before the one-way Imported transition; the runner is
/// data only and joins before these borrowed owners are released.
unsafe fn run(path: &std::path::Path) -> Result<bool, String> {
    // This check is before the producer and its workers. The dedicated entry
    // also requires the closed macro cohort's no-environment-writers contract;
    // observing absence alone does not establish that contract.
    crate::compiler_environment::CompilerEnvironment::require_absent_process()
        .map_err(|error| error.to_string())?;
    if std::env::var("VSTD_KIND").as_deref() != Ok("IsVstd") {
        return Err("the coordinator must start in its genuine producer context".into());
    }
    let (input_pin, value) = json(path)?;
    let input = Input::parse(value)?;
    if input.schema != "trust-vc.native-sdk-coordinator-request@1"
        || input.frontends.is_empty()
        || input.frontends.len() > 20
        || input.runner.arguments.len() > 4096
        || !input
            .runner
            .arguments
            .iter()
            .any(|argument| argument == "--owned-stdin")
    {
        return Err("unrepresented coordinator input or missing owned runner lease".into());
    }
    if !input.runner.program.is_absolute()
        || !input.runner.program.is_file()
        || !input.runner.cwd.is_absolute()
        || input
            .runner
            .cwd
            .canonicalize()
            .map_err(|error| error.to_string())?
            != input.runner.cwd
    {
        return Err("the runner program/cwd must be explicit actual absolute inputs".into());
    }
    let (producer_pin, producer) = json(&input.producer_request)?;
    if producer["schema"] != "trust-vc.native-declaration-staging-request@2"
        || producer.get("builtin").is_some()
        || producer.get("macros").is_some()
    {
        return Err("the coordinator requires the actual fresh @2 producer".into());
    }
    let frontends = input
        .frontends
        .iter()
        .map(|frontend| {
            (
                frontend.name.as_str(),
                PinnedFile {
                    path: frontend.path.clone(),
                    sha256: frontend.sha256,
                },
            )
        })
        .collect::<Vec<_>>();
    let library = produce(&producer_pin.path)?;
    library.write_observation()?;
    producer_pin.read()?;
    input_pin.read()?;
    // SAFETY: this dedicated entry has joined all producer workers and never
    // restores IsVstd after constructing the actual imported owner.
    let owner = unsafe { StandaloneImported::enter(&library)? };
    owner.compare_macro_context()?;
    let sdk = PreparedSdk::prepare_with_frontends(&owner, &input.sdk, &frontends)?;
    let mut session = Session::new(&owner, &sdk)?;
    let (server, client) = crate::native_requests::pair().map_err(|error| error.to_string())?;
    let mut command = Command::new(&input.runner.program);
    command
        .args(&input.runner.arguments)
        .current_dir(&input.runner.cwd);
    // Keep this guard after both borrowed owners: error/panic closes the stdin
    // lease and directly joins the maintained runner before they are dropped.
    let mut runner = runner::Runner::spawn(&client, command).map_err(|error| error.to_string())?;
    // SAFETY: this single callback loop owns process cwd/stdio and all native
    // compiler work; the runner itself carries only requests and process data.
    unsafe { session.serve_runner(&server, &mut runner) }.map_err(|error| error.to_string())?;
    let status = runner.wait().map_err(|error| error.to_string())?;
    sdk.check_owner(&owner)?;
    producer_pin.read()?;
    input_pin.read()?;
    let report = serde_json::json!({"schema": "trust-vc.native-sdk-coordinator-completion@1",
        "runner_actual_exit_code": status.code(), "runner_actual_success": status.success(),
        "requests": session.requests, "sdk": sdk.root(),
        "actual_owner_and_inputs_revalidated_after_runner_join": true,
        "permission_from_report": false, "all_functions_verified": null});
    std::fs::write(
        library.inputs.output.join("coordinator-completion.json"),
        serde_json::to_vec_pretty(&report).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    Ok(status.success())
}

/// # Safety
/// Dedicated entry after native resource capture, before other worker work.
pub unsafe fn main() -> ExitCode {
    if std::env::args().nth(1).as_deref() == Some(crate::shim::ERASE_RUN_FLAG) {
        return crate::shim::main();
    }
    let mut args = std::env::args_os().skip(1);
    let result = match (args.next(), args.next()) {
        (Some(path), None) => unsafe { run(std::path::Path::new(&path)) },
        _ => Err("expected one native SDK coordinator request file".into()),
    };
    match result {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(reason) => {
            eprintln!("native SDK coordinator refused: {reason}");
            ExitCode::FAILURE
        }
    }
}
