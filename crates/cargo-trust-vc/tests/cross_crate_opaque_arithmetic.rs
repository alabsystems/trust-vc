// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! End-to-end CLI test for cross-CRATE opaque spec imports.
//!
//! This is the cross-crate analogue of the in-file `arithmetic::opaque_arith`
//! and same-crate cross-file `cross_file_arith_import` suites in `trust-vc-std`.
//! Here the opaque `#[trust_vc::spec] #[trust_vc::opaque]` definitions of
//! `mul`/`add` live in a SEPARATE crate (the real `trust-vc-std`, in its
//! `arithmetic` *file* submodule) and are reached only through the
//! `cargo trust-vc check` path-dependency spec importer, which reads the
//! dependency's source from disk (the dependency's proof-mode body is
//! `#[cfg(test)]`-gated, so it cannot register itself at runtime in a
//! downstream crate — the importer is the only route).
//!
//! Differential, through the real `cargo trust-vc check` pipeline:
//! * opaque-by-default: `trust_vc_std::arithmetic::mul(2, 3) == 6` is REJECTED
//!   (the imported body axiom is suppressed until revealed);
//! * after `reveal!(mul)`: the same goal VERIFIES (load-bearing — the body axiom
//!   can only come from the cross-crate import);
//! * SOUNDNESS: a revealed-but-FALSE goal (`mul(2, 3) == 7`) is REJECTED — the
//!   import never fabricates a value and never lets a false goal pass;
//! * reveal is exact across crates: `reveal!(mul)` does not disclose `add`.
//!
//! The `assert_rejected` helper (mirroring the hardened version landed in
//! `d735580`) requires a GENUINE non-`verified` verdict (`counterexample` /
//! `unknown`), not an infrastructure/import `error`, so a malformed import that
//! left the symbol uninterpreted "for the wrong reason" cannot masquerade as a
//! passing opacity test.

use serde_json::Value;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repo root should canonicalize")
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
    let fallback = repo_root().join("target/debug").join(&binary_name);
    assert!(
        fallback.exists(),
        "cargo-trust-vc binary not found; run `targo --unverified build -p targo-trust-vc` first"
    );
    fallback
}

fn temp_consumer_dir() -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    let sequence = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "cargo_trust_vc_xcrate_opaque_{}_{}_{}",
        std::process::id(),
        unique,
        sequence
    ))
}

/// Writes a self-contained consumer crate that path-depends on the real
/// `trust-vc-std` and calls its opaque `arithmetic::{mul, add}` by fully
/// qualified path. Returns the crate root (containing `Cargo.toml`).
fn write_consumer_crate() -> PathBuf {
    let root = temp_consumer_dir();
    std::fs::create_dir_all(root.join("src")).expect("consumer src dir should be created");

    let trust_vc_std = repo_root().join("crates/trust-vc-std");
    std::fs::write(
        root.join("Cargo.toml"),
        format!(
            "[package]\nname = \"xcrate_opaque_consumer\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[dependencies]\ntrust-vc-std = {{ path = {std:?} }}\n\n[workspace]\n",
            std = trust_vc_std
        ),
    )
    .expect("consumer manifest should be written");

    // These consumers are proof functions: the body-call probes are ghost
    // code, and exec-to-spec refusal must not replace an opacity verdict.
    // Every asserted call is also "touched" in a real expression statement so
    // the importer's body-call scan sees the qualified call and fires (calls
    // that appear only inside `assert!(...)` macro tokens are not scanned).
    std::fs::write(
        root.join("src/lib.rs"),
        r#"// Test consumer for cross-crate opaque spec imports.

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn xc_mul_without_reveal() {
    let _ = trust_vc_std::arithmetic::mul(2, 3);
    trust_vc::assert!(trust_vc_std::arithmetic::mul(2, 3) == 6);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn xc_mul_with_reveal() {
    let _ = trust_vc_std::arithmetic::mul(2, 3);
    trust_vc::reveal!(mul);
    trust_vc::assert!(trust_vc_std::arithmetic::mul(2, 3) == 6);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn xc_mul_revealed_false_goal() {
    let _ = trust_vc_std::arithmetic::mul(2, 3);
    trust_vc::reveal!(mul);
    trust_vc::assert!(trust_vc_std::arithmetic::mul(2, 3) == 7);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn xc_reveal_mul_does_not_reveal_add() {
    let _ = trust_vc_std::arithmetic::mul(2, 3);
    let _ = trust_vc_std::arithmetic::add(2, 3);
    trust_vc::reveal!(mul);
    trust_vc::assert!(trust_vc_std::arithmetic::add(2, 3) == 5);
}
"#,
    )
    .expect("consumer source should be written");

    root
}

fn check_function(consumer_root: &Path, function: &str) -> (Option<i32>, Value, String) {
    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(consumer_root)
        .arg("check")
        .arg("--json")
        .arg("--function")
        .arg(function)
        .arg(".")
        .output()
        .expect("cargo-trust-vc should execute");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let json: Value = serde_json::from_str(&stdout)
        .unwrap_or_else(|err| panic!("stdout should be cargo-trust-vc JSON: {err}\n{stdout}"));
    (output.status.code(), json, stderr)
}

fn function_result(report: &Value, function: &str) -> String {
    let functions = report["functions"]
        .as_array()
        .expect("functions should be an array");
    assert_eq!(
        functions.len(),
        1,
        "expected exactly one checked function `{function}`: {report:#?}"
    );
    assert_eq!(functions[0]["name"], function);
    functions[0]["result"]
        .as_str()
        .expect("function result should be a string")
        .to_string()
}

fn assert_verifies(consumer_root: &Path, function: &str) {
    let (_code, report, stderr) = check_function(consumer_root, function);
    assert_eq!(
        function_result(&report, function),
        "verified",
        "`{function}` should verify after the opaque body axiom is revealed\nstderr={stderr}\nreport={report:#?}"
    );
}

fn assert_rejected(consumer_root: &Path, function: &str) {
    let (_code, report, stderr) = check_function(consumer_root, function);
    let result = function_result(&report, function);
    // The rejection MUST be a genuine non-`verified` verdict (counterexample or
    // unknown), NOT an infrastructure / import `error`. Otherwise a malformed
    // import could make the proof "fail" for the wrong reason and mask a real
    // opacity break (or an import break that silently left the symbol
    // uninterpreted). Mirrors the hardened helper from d735580.
    assert!(
        result == "counterexample" || result == "unknown",
        "`{function}` should be rejected by a GENUINE verification verdict \
         (counterexample/unknown), got `{result}`\nstderr={stderr}\nreport={report:#?}"
    );
}

#[test]
fn cross_crate_opaque_mul_without_reveal_stays_hidden() {
    let consumer = write_consumer_crate();
    assert_rejected(&consumer, "xc_mul_without_reveal");
    std::fs::remove_dir_all(&consumer).ok();
}

#[test]
fn cross_crate_opaque_mul_with_reveal_verifies() {
    let consumer = write_consumer_crate();
    assert_verifies(&consumer, "xc_mul_with_reveal");
    std::fs::remove_dir_all(&consumer).ok();
}

#[test]
fn cross_crate_revealed_mul_rejects_false_goal() {
    let consumer = write_consumer_crate();
    assert_rejected(&consumer, "xc_mul_revealed_false_goal");
    std::fs::remove_dir_all(&consumer).ok();
}

#[test]
fn cross_crate_reveal_mul_does_not_leak_add() {
    let consumer = write_consumer_crate();
    assert_rejected(&consumer, "xc_reveal_mul_does_not_reveal_add");
    std::fs::remove_dir_all(&consumer).ok();
}
