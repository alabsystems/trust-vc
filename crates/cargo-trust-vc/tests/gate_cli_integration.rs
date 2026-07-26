// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integration coverage for the local `gate`, `fuzz`, `new`, and top-level
//! help commands exposed by `cargo-trust-vc`.

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn temp_dir(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    let sequence = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "cargo_trust_vc_gate_{label}_{}_{}_{}",
        std::process::id(),
        unique,
        sequence
    ))
}

fn cargo_trust_vc_bin() -> PathBuf {
    for key in [
        "CARGO_BIN_EXE_cargo-trust-vc",
        "CARGO_BIN_EXE_cargo_trust_vc",
    ] {
        if let Ok(path) = std::env::var(key) {
            return PathBuf::from(path);
        }
    }

    let binary_name = format!("cargo-trust-vc{}", std::env::consts::EXE_SUFFIX);

    if let Ok(target_dir) = std::env::var("CARGO_TARGET_DIR") {
        let candidate = PathBuf::from(target_dir).join("debug").join(&binary_name);
        if candidate.exists() {
            return candidate;
        }
    }

    let fallback = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/debug")
        .join(&binary_name);
    if fallback.exists() {
        return fallback;
    }

    panic!("cargo-trust-vc binary not found; run `cargo build` first");
}

fn run(args: &[&str]) -> (String, String, i32) {
    let output = Command::new(cargo_trust_vc_bin())
        .args(args)
        .output()
        .expect("cargo-trust-vc should execute");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let code = output.status.code().unwrap_or(-1);
    (stdout, stderr, code)
}

fn run_in(dir: &PathBuf, args: &[&str]) -> (String, String, i32) {
    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(dir)
        .args(args)
        .output()
        .expect("cargo-trust-vc should execute");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let code = output.status.code().unwrap_or(-1);
    (stdout, stderr, code)
}

#[test]
fn top_level_help_lists_every_subcommand() {
    let (stdout, _stderr, code) = run(&["trust-vc", "--help"]);
    assert_eq!(code, 0);
    for subcommand in [
        "check",
        "gate",
        "fuzz",
        "evidence",
        "suggest",
        "new",
        "verus-compat",
    ] {
        assert!(
            stdout.contains(subcommand),
            "top-level help should list `{subcommand}`: {stdout}"
        );
    }
}

#[test]
fn bare_invocation_prints_help_index() {
    let (stdout, _stderr, code) = run(&[]);
    assert_eq!(code, 0);
    assert!(stdout.contains("Subcommands:"), "{stdout}");
    assert!(stdout.contains("gate"), "{stdout}");
}

#[test]
fn check_help_is_not_swallowed_by_top_level_help() {
    // `check --help` must show the check-specific help, not the index.
    let (stdout, _stderr, _code) = run(&["trust-vc", "check", "--help"]);
    assert!(
        stdout.contains("[PATH]") || stdout.contains("--function"),
        "check --help should show check options: {stdout}"
    );
    assert!(
        !stdout.contains("Subcommands:"),
        "check --help should not show the top-level index: {stdout}"
    );
}

#[test]
fn gate_help_lists_stages_and_flags() {
    let (stdout, _stderr, code) = run(&["trust-vc", "gate", "--help"]);
    assert_eq!(code, 0);
    for needle in [
        "fmt",
        "clippy",
        "test",
        "examples",
        "evidence",
        "--quick",
        "--no-fuzz",
    ] {
        assert!(
            stdout.contains(needle),
            "gate help should mention `{needle}`: {stdout}"
        );
    }
}

#[test]
fn gate_rejects_unknown_flag() {
    let (_stdout, stderr, code) = run(&["trust-vc", "gate", "--bogus"]);
    assert_eq!(code, 2, "unknown gate flag should be a CLI error: {stderr}");
    assert!(stderr.contains("--bogus"), "{stderr}");
}

#[test]
fn fuzz_help_lists_targets() {
    let (stdout, _stderr, code) = run(&["trust-vc", "fuzz", "--help"]);
    assert_eq!(code, 0);
    for target in [
        "ensures_false",
        "strict_inequality",
        "mode_crossing",
        "collections_contradiction",
    ] {
        assert!(
            stdout.contains(target),
            "fuzz help should list `{target}`: {stdout}"
        );
    }
}

#[test]
fn fuzz_rejects_unknown_target() {
    let (_stdout, stderr, code) = run(&["trust-vc", "fuzz", "definitely_not_a_target"]);
    assert_eq!(code, 2);
    assert!(stderr.contains("definitely_not_a_target"), "{stderr}");
    assert!(stderr.contains("available targets"), "{stderr}");
}

#[test]
fn fuzz_without_cargo_fuzz_prints_install_instructions() {
    // Force cargo-fuzz to be unavailable by pointing CARGO at a missing binary.
    let output = Command::new(cargo_trust_vc_bin())
        .env("CARGO", "definitely-not-a-real-cargo-binary")
        .args(["trust-vc", "fuzz"])
        .output()
        .expect("cargo-trust-vc should execute");
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert_eq!(
        output.status.code().unwrap_or(-1),
        2,
        "missing cargo-fuzz must exit 2 (not pretend to run): {stderr}"
    );
    assert!(
        stderr.contains("cargo install cargo-fuzz"),
        "should print the exact install instruction: {stderr}"
    );
}

#[test]
fn new_lib_scaffolds_verifiable_crate() {
    let parent = temp_dir("new_lib");
    std::fs::create_dir_all(&parent).expect("temp parent should be creatable");

    let (_stdout, stderr, code) = run_in(&parent, &["trust-vc", "new", "--lib", "demolib"]);
    assert_eq!(code, 0, "new --lib should succeed: {stderr}");

    let project = parent.join("demolib");
    let manifest = std::fs::read_to_string(project.join("Cargo.toml"))
        .expect("scaffold should write a Cargo.toml");
    assert!(
        manifest.contains("trust-vc") || manifest.contains("trust_vc"),
        "scaffolded manifest should depend on trust_vc: {manifest}"
    );

    let lib = std::fs::read_to_string(project.join("src/lib.rs"))
        .expect("scaffold should write src/lib.rs");
    assert!(
        lib.contains("trust_vc::contract") || lib.contains("requires"),
        "scaffolded lib should carry a verification contract: {lib}"
    );

    // `check` must now find and verify the scaffolded function (no dead end).
    let (stdout, stderr, code) = run_in(&parent, &["trust-vc", "check", "demolib"]);
    assert_eq!(
        code, 0,
        "check on scaffold should pass: stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("1 function found"),
        "check should find the scaffolded function: {stdout}"
    );
    assert!(
        stdout.contains("Verified") || stdout.contains("verified"),
        "scaffolded function should verify: {stdout}"
    );

    std::fs::remove_dir_all(&parent).ok();
}

#[test]
fn new_bin_scaffolds_verifiable_crate() {
    let parent = temp_dir("new_bin");
    std::fs::create_dir_all(&parent).expect("temp parent should be creatable");

    let (_stdout, stderr, code) = run_in(&parent, &["trust-vc", "new", "--bin", "demobin"]);
    assert_eq!(code, 0, "new --bin should succeed: {stderr}");

    let project = parent.join("demobin");
    let main = std::fs::read_to_string(project.join("src/main.rs"))
        .expect("scaffold should write src/main.rs");
    assert!(
        main.contains("trust_vc::contract"),
        "scaffolded main should carry a verification contract: {main}"
    );

    let (stdout, stderr, code) = run_in(&parent, &["trust-vc", "check", "demobin"]);
    assert_eq!(
        code, 0,
        "check on scaffold should pass: stdout={stdout} stderr={stderr}"
    );
    assert!(stdout.contains("1 function found"), "{stdout}");

    std::fs::remove_dir_all(&parent).ok();
}
