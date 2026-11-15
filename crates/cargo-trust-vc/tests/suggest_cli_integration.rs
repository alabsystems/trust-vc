// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn temp_dir(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    std::env::temp_dir().join(format!(
        "cargo_trust_vc_suggest_{label}_{}_{}",
        std::process::id(),
        unique
    ))
}

fn write_source(label: &str, source: &str) -> PathBuf {
    let dir = temp_dir(label);
    std::fs::create_dir_all(&dir).expect("temp dir should be creatable");
    let path = dir.join("test.rs");
    std::fs::write(&path, source).expect("temp source should be writable");
    path
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

    panic!(
        "cargo-trust-vc binary not found; run `targo --unverified build -p targo-trust-vc` first"
    );
}

fn run_cli(args: &[&str]) -> (String, String, i32) {
    let output = Command::new(cargo_trust_vc_bin())
        .arg("suggest")
        .args(args)
        .output()
        .expect("cargo-trust-vc suggest should execute");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let code = output.status.code().unwrap_or(-1);
    (stdout, stderr, code)
}

#[test]
fn suggest_cli_runs_oracle_for_each_function() {
    let source_path = write_source(
        "all_functions",
        "fn alpha(x: u32) -> u32 { x }\nfn beta(x: u32) -> u32 { x + 1 }\n",
    );

    let (stdout, stderr, code) = run_cli(&[
        "--file",
        source_path.to_str().expect("path should be utf-8"),
        "--backend",
        "mock",
    ]);

    assert_eq!(code, 0, "stderr={stderr}");
    assert!(stdout.contains("--- fn alpha(x: u32) -> u32 ---"));
    assert!(stdout.contains("--- fn beta(x: u32) -> u32 ---"));
    assert!(stdout.contains("Status: VERIFIED"));

    std::fs::remove_dir_all(source_path.parent().expect("temp dir should exist")).ok();
}

#[test]
fn suggest_cli_respects_function_filter() {
    let source_path = write_source(
        "function_filter",
        "fn alpha(x: u32) -> u32 { x }\nfn beta(x: u32) -> u32 { x + 1 }\n",
    );

    let (stdout, stderr, code) = run_cli(&[
        "--file",
        source_path.to_str().expect("path should be utf-8"),
        "--function",
        "beta",
        "--backend",
        "mock",
        "--model",
        "test-model",
    ]);

    assert_eq!(code, 0, "stderr={stderr}");
    assert!(!stdout.contains("--- fn alpha(x: u32) -> u32 ---"));
    assert!(stdout.contains("--- fn beta(x: u32) -> u32 ---"));

    std::fs::remove_dir_all(source_path.parent().expect("temp dir should exist")).ok();
}

#[test]
fn suggest_cli_reports_missing_function() {
    let source_path = write_source("missing_function", "fn alpha(x: u32) -> u32 { x }\n");

    let (_stdout, stderr, code) = run_cli(&[
        "--file",
        source_path.to_str().expect("path should be utf-8"),
        "--function",
        "beta",
        "--backend",
        "mock",
    ]);

    assert_eq!(code, 2);
    assert!(stderr.contains("no function named 'beta'"));

    std::fs::remove_dir_all(source_path.parent().expect("temp dir should exist")).ok();
}

#[test]
fn suggest_cli_rejects_invalid_backend() {
    let source_path = write_source("invalid_backend", "fn alpha(x: u32) -> u32 { x }\n");

    let (_stdout, stderr, code) = run_cli(&[
        "--file",
        source_path.to_str().expect("path should be utf-8"),
        "--backend",
        "invalid-backend",
    ]);

    assert_ne!(code, 0);
    assert!(stderr.contains("invalid value"));

    std::fs::remove_dir_all(source_path.parent().expect("temp dir should exist")).ok();
}

#[test]
fn suggest_cli_reports_parse_errors() {
    let source_path = write_source("parse_error", "fn broken(");

    let (_stdout, stderr, code) = run_cli(&[
        "--file",
        source_path.to_str().expect("path should be utf-8"),
        "--backend",
        "mock",
    ]);

    assert_eq!(code, 2);
    assert!(stderr.contains("cannot parse"));

    std::fs::remove_dir_all(source_path.parent().expect("temp dir should exist")).ok();
}
