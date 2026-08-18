// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integration coverage for the one-word `trust-vc` bin.
//!
//! The promise under test is the FIRST RUN: `trust-vc example > demo.rs &&
//! trust-vc demo.rs` verifies with nothing installed, `--version` / `--help`
//! answer without touching a sysroot or a solver, and an unsupported flag or an
//! empty target fails loudly instead of silently reporting nothing to do.

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
        "trust_vc_one_word_{label}_{}_{}_{}",
        std::process::id(),
        unique,
        sequence
    ))
}

fn trust_vc_bin() -> PathBuf {
    for key in ["CARGO_BIN_EXE_trust-vc", "CARGO_BIN_EXE_trust_vc"] {
        if let Ok(path) = std::env::var(key) {
            return PathBuf::from(path);
        }
    }

    let binary_name = format!("trust-vc{}", std::env::consts::EXE_SUFFIX);

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

    panic!("trust-vc binary not found; run `cargo build` first");
}

fn run(args: &[&str]) -> (String, String, i32) {
    let output = Command::new(trust_vc_bin())
        .args(args)
        .output()
        .expect("trust-vc should execute");
    (
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
        output.status.code().unwrap_or(-1),
    )
}

#[test]
fn version_prints_without_any_toolchain() {
    for flag in ["--version", "-V"] {
        let (stdout, stderr, code) = run(&[flag]);
        assert_eq!(code, 0, "`{flag}` should exit 0: {stderr}");
        assert!(
            stdout.starts_with("trust-vc "),
            "`{flag}` should print the tool name and version: {stdout}"
        );
    }
}

#[test]
fn bare_invocation_and_help_show_the_first_run() {
    for args in [vec![], vec!["--help"], vec!["-h"], vec!["help"]] {
        let (stdout, stderr, code) = run(&args);
        assert_eq!(code, 0, "help should exit 0: {stderr}");
        assert!(
            stdout.contains("trust-vc example > demo.rs && trust-vc demo.rs"),
            "help should lead with the zero-setup first run: {stdout}"
        );
        assert!(stdout.contains("example"), "{stdout}");
        assert!(stdout.contains("verify"), "{stdout}");
        assert!(stdout.contains("Exit codes:"), "{stdout}");
    }
}

#[test]
fn verify_help_lists_the_real_flags() {
    let (stdout, stderr, code) = run(&["verify", "--help"]);
    assert_eq!(code, 0, "{stderr}");
    for flag in ["--function", "--filter", "--json", "--timeout"] {
        assert!(
            stdout.contains(flag),
            "verify help should list `{flag}`: {stdout}"
        );
    }
}

#[test]
fn example_writes_a_contract_to_stdout() {
    let (stdout, stderr, code) = run(&["example"]);
    assert_eq!(code, 0, "{stderr}");
    assert!(stdout.contains("trust_vc::contract"), "{stdout}");
    assert!(stdout.contains("requires("), "{stdout}");
    assert!(stdout.contains("ensures("), "{stdout}");
}

#[test]
fn example_then_verify_is_a_working_first_run() {
    let dir = temp_dir("first_run");
    std::fs::create_dir_all(&dir).expect("temp dir should be creatable");
    let demo = dir.join("demo.rs");

    let (sample, stderr, code) = run(&["example"]);
    assert_eq!(code, 0, "{stderr}");
    std::fs::write(&demo, sample).expect("sample should be writable");

    let (stdout, stderr, code) = run(&[demo.to_str().expect("utf-8 temp path")]);
    assert_eq!(
        code, 0,
        "the sample must verify out of the box: stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("1 function found"),
        "single-file verification should find the sample's function: {stdout}"
    );
    assert!(
        stdout.contains("Verified"),
        "the sample's contract should be proven: {stdout}"
    );
    assert!(
        stdout.contains("demo.rs"),
        "the report should name the file it verified: {stdout}"
    );

    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn unsupported_flag_names_itself_and_the_alternative() {
    let (_stdout, stderr, code) = run(&["--rlimit", "10", "demo.rs"]);
    assert_eq!(code, 2, "an unsupported flag must not be ignored: {stderr}");
    assert!(stderr.contains("--rlimit"), "{stderr}");
    assert!(stderr.contains("--timeout"), "{stderr}");
}

#[test]
fn cargo_selection_flags_point_at_the_cargo_subcommand() {
    let (_stdout, stderr, code) = run(&["--manifest-path", "Cargo.toml"]);
    assert_eq!(code, 2, "{stderr}");
    assert!(stderr.contains("--manifest-path"), "{stderr}");
    assert!(stderr.contains("cargo trust-vc"), "{stderr}");
}

#[test]
fn a_missing_target_is_actionable() {
    let missing = temp_dir("missing").join("nope.rs");
    let (_stdout, stderr, code) = run(&[missing.to_str().expect("utf-8 temp path")]);
    assert_eq!(code, 2, "{stderr}");
    assert!(stderr.contains("no such file"), "{stderr}");
    assert!(stderr.contains("trust-vc example"), "{stderr}");
}

#[test]
fn a_directory_without_sources_is_not_a_silent_success() {
    let dir = temp_dir("empty");
    std::fs::create_dir_all(&dir).expect("temp dir should be creatable");

    let (stdout, stderr, code) = run(&[dir.to_str().expect("utf-8 temp path")]);
    assert_eq!(
        code, 2,
        "an empty directory should be reported, not passed: stdout={stdout}"
    );
    assert!(stderr.contains("src/"), "{stderr}");

    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn a_non_rust_file_is_rejected_by_name() {
    let dir = temp_dir("not_rust");
    std::fs::create_dir_all(&dir).expect("temp dir should be creatable");
    let readme = dir.join("README.md");
    std::fs::write(&readme, "# not rust\n").expect("file should be writable");

    let (_stdout, stderr, code) = run(&[readme.to_str().expect("utf-8 temp path")]);
    assert_eq!(code, 2, "{stderr}");
    assert!(stderr.contains("not a Rust source file"), "{stderr}");

    std::fs::remove_dir_all(&dir).ok();
}
