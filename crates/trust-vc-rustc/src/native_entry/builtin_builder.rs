// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A separate native coordinator retains the genuine GNU owner while the
//! closed builtin recipe runs. It imports only at its own process entry.

extern crate jobserver_utils;

use std::ffi::OsString;
use std::path::PathBuf;
use std::process::{Command, ExitCode};
use std::sync::OnceLock;

const FLAG: &str = "--trust-vc-owned-builtin-builder";
const SCRIPT: &[u8] = include_bytes!("../../../../scripts/verus_suite/build_verus_builtins.sh");
const GNU: &[&str] = &[
    "CARGO_JOBSERVER_HANDOFF",
    "CARGO_MAKEFLAGS",
    "MAKEFLAGS",
    "MFLAGS",
];
const UNSUPPORTED: &[&str] = &[
    "TRUST_CPU_HANDOFF",
    "TRUST_CPU_IMPLICIT_FD",
    "TRUST_FIXED_CLAIM_HANDOFF_V1",
    "BUILD_SLOT_FENCE_FDS",
    "ATERM_SDK_LEASE_V3",
    "ATERM_WORKLOAD_CPU_FDS_V1",
    "ATERM_WORKLOAD_HOST_STORE_FD_V1",
    "ATERM_WORKLOAD_HOST_CONTROL_FDS_V1",
];
const COUNTS: &[&str] = &[
    "BUILD_SLOT_HELD",
    "BUILD_SLOT_CPU_PROTOCOL",
    "CARGO_BUILD_JOBS",
];

pub(super) struct Forwarding(Vec<(&'static str, Option<OsString>)>);
static FORWARDING: OnceLock<Forwarding> = OnceLock::new();

pub(super) fn snapshot() -> Forwarding {
    Forwarding(
        GNU.iter()
            .chain(UNSUPPORTED)
            .chain(COUNTS)
            .map(|&name| (name, std::env::var_os(name)))
            .collect(),
    )
}

pub(super) fn retain(snapshot: Forwarding) -> Result<(), ExitCode> {
    if FORWARDING.set(snapshot).is_err() {
        eprintln!("error: native child transport was already captured");
        return Err(ExitCode::from(75));
    }
    Ok(())
}

/// Route the original entry observations to a separate early importer. These
/// strings grant nothing: the child must obtain a real typed GNU owner, and
/// configure_make installs that owner's actual transport for the builder.
pub(crate) fn configure_child(
    command: &mut Command,
    script: &std::path::Path,
    output: &std::path::Path,
    source: &std::path::Path,
) -> Result<(), String> {
    let original = FORWARDING
        .get()
        .ok_or("native builtin construction requires captured process-entry transport")?;
    command.arg(FLAG).arg(script).arg(output).arg(source);
    for (name, value) in &original.0 {
        match value {
            Some(value) => {
                command.env(name, value);
            }
            None => {
                command.env_remove(name);
            }
        }
    }
    Ok(())
}

pub(super) type Request = Result<[PathBuf; 3], &'static str>;

fn parse(mut arguments: impl Iterator<Item = OsString>) -> Option<Request> {
    let first = arguments.next()?;
    if !first.as_encoded_bytes().starts_with(FLAG.as_bytes()) {
        return None;
    }
    if first != FLAG {
        return Some(Err("malformed native builtin coordinator selector"));
    }
    let paths = arguments.by_ref().take(4).collect::<Vec<_>>();
    if paths.len() != 3 || paths.iter().any(|p| p.as_encoded_bytes().len() > 4096) {
        return Some(Err(
            "native builtin coordinator requires exactly three bounded paths",
        ));
    }
    Some(Ok([
        PathBuf::from(&paths[0]),
        PathBuf::from(&paths[1]),
        PathBuf::from(&paths[2]),
    ]))
}

pub(super) fn request() -> Option<Request> {
    parse(std::env::args_os().skip(1))
}

unsafe fn execute(request: Request) -> Result<ExitCode, String> {
    let paths = request.map_err(str::to_owned)?;
    if UNSUPPORTED
        .iter()
        .any(|name| std::env::var_os(name).is_some())
    {
        return Err(
            "this builtin coordinator cannot replace existing native CPU/SDK custody".into(),
        );
    }
    if std::env::var_os("BUILD_SLOT_CPU_PROTOCOL").is_some_and(|value| value != "1") {
        return Err(
            "this builtin coordinator supports only original fixed-v1 CPU admission".into(),
        );
    }
    // SAFETY: only the fixed argv/environment observations above precede this
    // importer at native entry; no file, argument sidecar or callback ran.
    let mut scheduler = unsafe { jobserver_utils::Jobserver::from_env_with_handoff() }
        .map_err(|error| error.to_string())?
        .ok_or("native builtin coordinator has no genuine inherited GNU scheduler")?;
    scheduler
        .enable_descendant_handoff()
        .map_err(|error| error.to_string())?;
    let [script, output, source] = paths;
    for path in [&script, &output, &source] {
        if !path.is_absolute() || path.canonicalize().map_err(|e| e.to_string())? != *path {
            return Err("native builtin coordinator paths must be canonical and absolute".into());
        }
    }
    if script.parent() != Some(output.as_path())
        || !std::fs::symlink_metadata(&script)
            .map_err(|e| e.to_string())?
            .is_file()
        || std::fs::read(&script).map_err(|e| e.to_string())? != SCRIPT
        || !output.is_dir()
        || !source.is_dir()
    {
        return Err("native builtin coordinator requires the exact owned builtin script".into());
    }
    let mut command = Command::new("/bin/bash");
    command.arg(script).arg(output).arg(source);
    scheduler.configure_make(&mut command);
    // Both this typed owner and its authenticated descendant endpoint remain
    // alive until the actual script child has returned from the owning wait.
    let status = command.status().map_err(|error| error.to_string())?;
    drop(command);
    drop(scheduler);
    match status.code() {
        Some(code) if (0..=255).contains(&code) => Ok(ExitCode::from(code as u8)),
        _ => Err("the genuine builtin script terminated without a normal exit status".into()),
    }
}

pub(super) unsafe fn run(request: Request) -> ExitCode {
    // SAFETY: the native-entry caller guarantees the early-import boundary.
    match unsafe { execute(request) } {
        Ok(code) => code,
        Err(error) => {
            eprintln!("error: native builtin coordinator refused: {error}");
            ExitCode::from(75)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn private_dispatch_requires_exact_bounded_shape() {
        assert!(parse([OsString::from("--ordinary")].into_iter()).is_none());
        for args in [
            vec![FLAG.into()],
            vec![format!("{FLAG}=wrong").into()],
            vec![
                FLAG.into(),
                "/a".into(),
                "/b".into(),
                "/c".into(),
                "/d".into(),
            ],
        ] {
            assert!(matches!(parse(args.into_iter()), Some(Err(_))));
        }
        assert!(matches!(
            parse([FLAG.into(), "/a".into(), "/b".into(), "/c".into()].into_iter()),
            Some(Ok(_))
        ));
    }
}
