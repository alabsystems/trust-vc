// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use serde_json::Value;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn temp_dir(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    std::env::temp_dir().join(format!(
        "cargo_trust_vc_evidence_{label}_{}_{}",
        std::process::id(),
        unique
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

fn write_minimal_manifest(crate_root: &Path) {
    let manifest_dir = crate_root.join("evals/verus");
    std::fs::create_dir_all(&manifest_dir).expect("manifest dir should be creatable");
    std::fs::write(
        manifest_dir.join("verus-tests.json"),
        r##"{
  "schema_version": 1,
  "manifest_id": "upstream-verus-corpus",
  "description": "Minimal test manifest.",
  "upstream": {
    "repo": "https://github.com/verus-lang/verus",
    "ref": "abc123",
    "test_roots": ["source/rust_verify_test/tests"]
  },
  "gate": {
    "missing_entry": "fail",
    "failing_classifications": ["unclassified", "unsupported-gap"]
  },
  "entries": []
}
"##,
    )
    .expect("manifest should be writable");
}

#[test]
fn evidence_cli_refuses_replacement_without_pinned_clean_verus_checkout() {
    let crate_root = temp_dir("missing_verus_checkout");
    std::fs::create_dir_all(&crate_root).expect("crate root should be creatable");
    write_minimal_manifest(&crate_root);

    let output = Command::new(cargo_trust_vc_bin())
        .arg("evidence")
        .arg(&crate_root)
        .arg("--strict")
        .arg("--run-verus")
        .arg("--manifest")
        .arg("evals/verus/verus-tests.json")
        .arg("--json")
        .env_remove("TRUST_VC_VERUS_PATH")
        .env_remove("VERUS_PATH")
        .output()
        .expect("cargo-trust-vc evidence should execute");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert_eq!(
        output.status.code(),
        Some(1),
        "stdout={stdout}\nstderr={stderr}"
    );

    let report: Value = serde_json::from_str(&stdout).expect("stdout should be evidence JSON");
    assert_eq!(report["replacement_verdict"], "not_proven");

    let blockers = report["blocking_reasons"]
        .as_array()
        .expect("blocking_reasons should be an array")
        .iter()
        .filter_map(Value::as_str)
        .collect::<Vec<_>>();
    assert!(
        blockers
            .iter()
            .any(|reason| reason.contains("Verus revision pin")
                && reason.contains("--verus-path is required")),
        "missing Verus revision blocker: {blockers:?}"
    );
    assert!(
        blockers
            .iter()
            .any(|reason| reason.contains("Verus worktree clean")
                && reason.contains("--verus-path is required")),
        "missing Verus worktree blocker: {blockers:?}"
    );
    assert!(
        blockers
            .iter()
            .any(|reason| reason.contains("schema_version 2") && reason.contains("got 1")),
        "missing canonical schema v2 blocker: {blockers:?}"
    );

    let gates = report["gates"]
        .as_array()
        .expect("gates should be an array");
    assert!(
        gates.iter().any(|gate| {
            gate["name"] == "upstream Verus tests"
                && gate["status"] == "failed"
                && gate["detail"]
                    .as_str()
                    .is_some_and(|detail| detail.contains("--run-verus requires --verus-path"))
        }),
        "missing upstream Verus test runner gate: {gates:?}"
    );

    std::fs::remove_dir_all(crate_root).ok();
}
