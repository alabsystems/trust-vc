//! Protocol obligations through the `ty` binary.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! The end-to-end cases run the `ty` this process resolves
//! (`TRUST_VC_TY_BIN`, else `ty` on `PATH`) and fail, never skip, without
//! one advertising every required capability. The rest run fake binaries
//! written here, through the same spawn the lane uses, and need no `ty`.

use std::ffi::OsString;
use std::path::{Path, PathBuf};

use super::binary::{resolve_from, BIN_VAR};
use super::config::Request;
use super::document::{judge, Expected};
use super::{run, ProtocolObligation, TyEncoder};
use crate::VerifyResult;

/// A counter over `0..3` with the invariant `Inv == <invariant>`.
fn counter(invariant: &str) -> ProtocolObligation {
    ProtocolObligation {
        name: "Counter".to_string(),
        spec: format!(
            "---- MODULE Counter ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\n\
             Next == x' = (x + 1) % 3\nInv == {invariant}\n===="
        ),
        config: "INIT Init\nNEXT Next\nINVARIANT Inv\n".to_string(),
        shape: None,
    }
}

/// The counter reaches 2, so `x < 2` is violated: a counterexample named by
/// the invariant, with no source position.
#[test]
fn a_violated_invariant_is_a_counterexample_named_by_the_invariant() {
    match TyEncoder::verify_protocol(&[counter("x < 2")]) {
        VerifyResult::Counterexample {
            obligation_name,
            location,
            model,
            ..
        } => {
            assert_eq!(obligation_name, "Inv");
            assert_eq!(location, None);
            assert_eq!(model.as_deref(), Some("3 state(s) in trace"));
        }
        other => panic!("expected a counterexample, got {other:?}"),
    }
}

/// Twin: `x < 3` holds on every reachable state.
#[test]
fn a_holding_invariant_verifies() {
    assert_eq!(
        TyEncoder::verify_protocol(&[counter("x < 3")]),
        VerifyResult::Verified
    );
}

/// `#[protocol]` names a field's type by the type Rust resolves for it
/// (`verification_bridge::ProtocolFieldType`); each name it can give is one the
/// translator reads, and the translator reads no other.
#[test]
fn the_macro_names_exactly_the_field_types_the_translator_reads() {
    let mut from_macro = crate::verification_bridge::MODELLED_FIELD_TYPES.to_vec();
    let mut read = super::rust_expr::type_names();
    from_macro.sort_unstable();
    read.sort_unstable();
    assert_eq!(from_macro, read);
}

/// A scratch directory for one test, removed when it drops.
struct Scratch(PathBuf);

impl Scratch {
    fn new(tag: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "trust-vc-protocol-{tag}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map_or(0, |d| d.as_nanos())
        ));
        std::fs::create_dir_all(&path).expect("scratch dir");
        Self(path)
    }

    /// An executable shell script `name` holding `body`.
    fn script(&self, name: &str, body: &str) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let path = self.0.join(name);
        std::fs::write(&path, format!("#!/bin/sh\n{body}\n")).expect("write script");
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755))
            .expect("chmod script");
        path
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn the_binary_is_trust_vc_ty_bin_without_fallback_else_ty_on_path() {
    let scratch = Scratch::new("resolve");
    let ty = scratch.script("ty", "exit 0");
    let set = |value: &Path| Some(OsString::from(value));
    let path = Some(OsString::from(&scratch.0));

    assert_eq!(resolve_from(set(&ty), None), Ok(ty.clone()));
    // Set but wrong: an error, never a fall back to PATH.
    for (bad, why) in [
        (PathBuf::from("ty"), "not an absolute path"),
        (scratch.0.clone(), "not a regular file"),
        (scratch.0.join("missing"), "missing"),
    ] {
        let error = resolve_from(set(&bad), path.clone()).expect_err("refused");
        assert!(error.starts_with(BIN_VAR) && error.contains(why), "{error}");
    }
    assert_eq!(resolve_from(None, path), Ok(ty));
    let error = resolve_from(None, Some(OsString::from("/nonexistent"))).expect_err("none");
    assert!(
        error.contains("no ty binary") && error.contains("check-enabled-contract-v1"),
        "{error}"
    );
    // A `ty` that is not executable is not one.
    let plain = Scratch::new("plain");
    std::fs::write(plain.0.join("ty"), "").expect("write");
    assert!(resolve_from(None, Some(OsString::from(&plain.0))).is_err());
}

fn judged(bin: &Path, spec: &str, config: &str) -> VerifyResult {
    let request = Request::parse(config).expect("a valid config");
    let run = run::check(bin, spec, &request.canonical()).expect("the fake runs");
    judge(
        &Expected {
            name: "P",
            spec,
            request: &request,
            shape: None,
        },
        &run,
    )
}

#[track_caller]
fn error_containing(result: VerifyResult, needle: &str) {
    match result {
        VerifyResult::Error { message } => assert!(message.contains(needle), "{message}"),
        other => panic!("expected an Error containing {needle:?}, got {other:?}"),
    }
}

/// The spec is written under its module's name, as SANY reads files.
#[test]
fn the_spec_file_is_named_like_its_module() {
    use super::run::module_file_stem;
    assert_eq!(
        module_file_stem("---- MODULE Counter ----\n====\n"),
        "Counter"
    );
    assert_eq!(
        module_file_stem("--------  MODULE\n  F2 ----\n====\n"),
        "F2"
    );
    assert_eq!(
        module_file_stem("(* notes *)\n---- MODULE Spec ----\n"),
        "Spec"
    );
    // No header SANY reads: the default name, which ty refuses.
    assert_eq!(module_file_stem("----\tMODULE X ----\n"), "Spec");
    assert_eq!(module_file_stem("---- MODULE ../x ----\n"), "Spec");
}

/// What reaches `ty`: the frozen flags, the canonical config (not the
/// obligation's text), a private directory as `HOME`, `TMPDIR` and working
/// directory, and nothing else of this process's environment.
#[test]
fn ty_runs_in_a_private_directory_with_only_home_and_tmpdir() {
    let scratch = Scratch::new("env");
    let dump = scratch.0.join("dump");
    let fake = scratch.script(
        "ty",
        &format!(
            "{{ echo \"ARGS $*\"; env; echo \"CWD $(pwd -P)\"; \
             echo \"HOMEDIR $(cd \"$HOME\" && pwd -P)\"; ls -ld \"$HOME\"; \
             echo CONFIG; cat \"$HOME/Spec.cfg\"; }} > '{}'\nexit 2",
            dump.display()
        ),
    );
    error_containing(
        judged(
            &fake,
            "---- MODULE Spec ----\n====\n",
            "  NEXT   Next\nINIT Init\n\nINVARIANT Inv\n",
        ),
        "output refused",
    );
    let dump = std::fs::read_to_string(&dump).expect("the fake ran");
    let field = |prefix: &str| {
        dump.lines()
            .find_map(|line| line.strip_prefix(prefix))
            .unwrap_or_else(|| panic!("{prefix} in:\n{dump}"))
    };
    let dir = field("HOME=");
    assert_eq!(field("TMPDIR="), dir, "{dump}");
    assert_eq!(
        field("CWD "),
        field("HOMEDIR "),
        "the working directory is HOME:\n{dump}"
    );
    assert!(
        dump.contains(&format!(
            "ARGS check {dir}/Spec.tla -c {dir}/Spec.cfg --output json --no-cache --quiet \
             --workers 1 --bfs-only --no-reduction --backend interpreter --no-gpu\n"
        )),
        "{dump}"
    );
    assert!(dump.contains("drwx------"), "mode 0700:\n{dump}");
    assert!(
        dump.ends_with("CONFIG\nINIT Init\nNEXT Next\nINVARIANT Inv\n"),
        "{dump}"
    );
    // Nothing of this process's environment but what the shell itself sets.
    for (name, value) in std::env::vars() {
        if ["HOME", "TMPDIR", "PWD", "OLDPWD", "SHLVL", "_", "PATH"].contains(&name.as_str()) {
            continue;
        }
        assert!(
            !dump.contains(&format!("\n{name}={value}\n")),
            "{name} reached ty:\n{dump}"
        );
    }
    assert!(
        !std::path::Path::new(dir).exists(),
        "the private directory is removed"
    );
}

/// A `ty` that predates `ty capabilities` and the JSON contract answers the
/// flags with a usage error and no document: refused, as is one killed by a
/// signal and one that writes something else than a JSON object.
#[test]
fn a_binary_that_writes_no_document_is_refused() {
    let scratch = Scratch::new("fakes");
    let spec = "---- MODULE Spec ----\n====\n";
    let config = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let old = scratch.script(
        "old",
        "echo \"error: unexpected argument '--no-cache' found\" >&2\nexit 2",
    );
    error_containing(
        judged(&old, spec, config),
        "unexpected argument '--no-cache'",
    );
    let killed = scratch.script("killed", "kill -9 $$");
    error_containing(judged(&killed, spec, config), "signal");
    let astral = scratch.script("astral", "echo 'ty 0.0.1 (a Python type checker)'");
    error_containing(judged(&astral, spec, config), "not one JSON document");
    let lacking = scratch.script(
        "lacking",
        "echo '{\"version\":\"1.4\",\"tool\":\"ty\",\"result\":{\"status\":\"ok\"}}'",
    );
    error_containing(
        judged(&lacking, spec, config),
        "lacks check-json-contract-v2, check-exact-source-v2, check-enabled-contract-v1",
    );
}
