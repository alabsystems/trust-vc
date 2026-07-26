// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use serde_json::Value;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

const VERIFIED_REQUEST_JSON: &str = r#"{
  "source_id": "runner-golden",
  "units": [
    {
      "unit_id": "crate::verified",
      "variables": [],
      "obligations": [
        {
          "id": "post",
          "role": "assertion",
          "kind": "postcondition",
          "expr": "true",
          "typed_expr": {
            "kind": "bool_literal",
            "value": true
          }
        }
      ]
    }
  ],
  "mode": "full",
  "proof_policy": "evidence_only"
}"#;

const REFUTED_REQUEST_JSON: &str = r#"{
  "source_id": "runner-golden-refuted",
  "units": [
    {
      "unit_id": "crate::refuted",
      "variables": [],
      "obligations": [
        {
          "id": "post",
          "role": "assertion",
          "kind": "postcondition",
          "expr": "false",
          "typed_expr": {
            "kind": "bool_literal",
            "value": false
          }
        }
      ]
    }
  ],
  "mode": "full",
  "proof_policy": "evidence_only"
}"#;

const MIR_MEMORY_REQUEST_JSON: &str = r#"{
  "source_id": "runner-mir-memory",
  "unit_id": "crate::take_shared",
  "display_name": "take_shared",
  "native_context": {
    "function_signature": {
      "name": "crate::take_shared",
      "params": [
        {
          "name": "ptr_live",
          "sort": {
            "kind": "bool"
          }
        }
      ],
      "return_sort": {
        "kind": "bool"
      }
    },
    "ownership": {
      "places": [
        {
          "place": "x",
          "sort": {
            "kind": "bit_vector",
            "width": 32,
            "signed": false
          }
        }
      ],
      "borrows": [
        {
          "region": "r0",
          "place": "x",
          "kind": "shared"
        }
      ]
    }
  },
  "obligations": [
    {
      "id": "mir.memory.ptr_live",
      "predicate": {
        "kind": "compare",
        "op": "eq",
        "left": {
          "kind": "variable",
          "name": "ptr_live",
          "sort": {
            "kind": "bool"
          }
        },
        "right": {
          "kind": "variable",
          "name": "ptr_live",
          "sort": {
            "kind": "bool"
          }
        }
      },
      "location": "src/lib.rs:12:9"
    }
  ],
  "metadata": {
    "trust.cache.ay_version": "ay:runner-test"
  }
}"#;

const MIR_MEMORY_EMPTY_OWNERSHIP_JSON: &str = r#"{
  "source_id": "runner-mir-memory-empty-ownership",
  "unit_id": "crate::take_shared",
  "native_context": {
    "function_signature": {
      "name": "crate::take_shared",
      "params": [
        {
          "name": "ptr_live",
          "sort": {
            "kind": "bool"
          }
        }
      ],
      "return_sort": {
        "kind": "bool"
      }
    },
    "ownership": {}
  },
  "obligations": [
    {
      "id": "mir.memory.ptr_live",
      "predicate": {
        "kind": "compare",
        "op": "eq",
        "left": {
          "kind": "variable",
          "name": "ptr_live",
          "sort": {
            "kind": "bool"
          }
        },
        "right": {
          "kind": "variable",
          "name": "ptr_live",
          "sort": {
            "kind": "bool"
          }
        }
      }
    }
  ]
}"#;

const TRUST_X86_LOAD_TRUST_IR_ADAPTER_GOLDEN: &str =
    "fixtures/trust_ir_adapter/trust_x86_load_trust_ir_adapter_golden.json";
const TRUST_UNRESOLVED_BRANCH_UNSUPPORTED_TRUST_IR_ADAPTER_GOLDEN: &str =
    "fixtures/trust_ir_adapter/trust_unresolved_indirect_branch_unsupported_trust_ir_adapter_golden.json";
const TRUST_INCREMENT_CONTRACT_CFG_TRUST_IR_ADAPTER_GOLDEN: &str =
    "fixtures/trust_ir_adapter/trust_increment_contract_cfg_trust_ir_adapter_golden.json";
const NATIVE_REQUEST_TRUST_BUNDLE: &str =
    "fixtures/trust_ir_native/native_request_trust_bundle.json";

struct TempCase {
    root: PathBuf,
}

impl TempCase {
    fn new(label: &str) -> Self {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock should be after UNIX_EPOCH")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "trust_vc_trust_runner_{label}_{}_{}",
            std::process::id(),
            nanos
        ));
        std::fs::create_dir_all(&root).expect("temp dir should be creatable");
        Self { root }
    }

    fn request_path(&self) -> PathBuf {
        self.root.join("request.json")
    }

    fn report_path(&self) -> PathBuf {
        self.root.join("report.json")
    }

    fn write_request(&self, json: &str) -> PathBuf {
        let path = self.request_path();
        std::fs::write(&path, json).expect("request fixture should write");
        path
    }
}

impl Drop for TempCase {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.root);
    }
}

fn runner_bin() -> PathBuf {
    for key in [
        "CARGO_BIN_EXE_trust-vc-trust-runner",
        "CARGO_BIN_EXE_trust_vc_trust_runner",
    ] {
        if let Ok(path) = std::env::var(key) {
            return PathBuf::from(path);
        }
    }

    let binary_name = format!("trust-vc-trust-runner{}", std::env::consts::EXE_SUFFIX);
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

    panic!("trust-vc-trust-runner binary not found; run `cargo build -p trust-vc-trust-engine --bin trust-vc-trust-runner` first");
}

fn fixture_path(rel_path: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel_path)
}

fn run_runner(args: &[&str]) -> (i32, String, String) {
    let output = Command::new(runner_bin())
        .args(args)
        .output()
        .expect("trust-vc-trust-runner should execute");
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

fn run_runner_with_stdin(args: &[&str], stdin: &str) -> (i32, String, String) {
    let mut child = Command::new(runner_bin())
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("trust-vc-trust-runner should spawn");
    child
        .stdin
        .as_mut()
        .expect("stdin should be piped")
        .write_all(stdin.as_bytes())
        .expect("request should write to runner stdin");
    let output = child
        .wait_with_output()
        .expect("trust-vc-trust-runner should finish");
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

fn read_report(path: &Path) -> Value {
    let payload = std::fs::read_to_string(path).expect("report should be readable");
    assert!(
        payload.ends_with('\n'),
        "runner should write deterministic newline-terminated JSON"
    );
    serde_json::from_str(&payload).expect("report should be valid JSON")
}

#[test]
fn runner_auto_detects_and_verifies_real_trust_ir_adapter_fixture() {
    let temp = TempCase::new("trust_ir_adapter");
    let request = fixture_path(TRUST_X86_LOAD_TRUST_IR_ADAPTER_GOLDEN);
    let report = temp.report_path();

    let (code, stdout, stderr) = run_runner(&[
        "--input",
        request.to_str().expect("request path should be utf-8"),
        "--output",
        report.to_str().expect("report path should be utf-8"),
    ]);

    assert_eq!(code, 0, "stdout={stdout}\nstderr={stderr}");
    assert!(stdout.is_empty(), "runner should write report to file only");
    assert!(stderr.is_empty(), "unexpected stderr: {stderr}");

    let json = read_report(&report);
    assert_eq!(
        json["source_id"],
        "tRust::trust-integration-tests::binary_decompile_convert_llvm2_production_positive_golden"
    );
    assert_eq!(json["units"][0]["unit_id"], "trust_fixture_x86_load");
    assert_eq!(json["units"][0]["outcome"]["status"], "verified");
    assert_eq!(
        json["units"][0]["proof_evidence"][0]["evidence_profile"],
        "ownership_memory"
    );
    assert_eq!(
        json["units"][0]["proof_evidence"][0]["proof_lineage"]["source"],
        "trust_ir_ownership"
    );
    assert_eq!(
        json["units"][0]["proof_evidence"][0]["cache_key"]["trust_ir_body_hash"],
        "sha256:dbd30d3b634f45a82b2453ef67a7ba279f32be9fddefcb0afb8e6d94dff144b5"
    );
    assert_eq!(
        json["units"][0]["proof_evidence"][2]["evidence_profile"],
        "typed_translation_validation"
    );
}

#[test]
fn runner_auto_detects_and_consumes_native_trust_ir_bundle_fixture() {
    let temp = TempCase::new("native_trust_ir_bundle");
    let request = fixture_path(NATIVE_REQUEST_TRUST_BUNDLE);
    let report = temp.report_path();

    let (code, stdout, stderr) = run_runner(&[
        "--input",
        request.to_str().expect("request path should be utf-8"),
        "--output",
        report.to_str().expect("report path should be utf-8"),
    ]);

    assert_eq!(code, 0, "stdout={stdout}\nstderr={stderr}");
    assert!(stdout.is_empty(), "runner should write report to file only");
    assert!(stderr.is_empty(), "unexpected stderr: {stderr}");

    let json = read_report(&report);
    assert_eq!(json["producer"], "tRust");
    assert_eq!(json["input_kind"], "rust_mir");
    assert_eq!(json["module_name"], "trust_native_request_bundle");
    assert_eq!(json["requests"][0]["request_id"], 0);
    assert_eq!(json["requests"][0]["mode"], "import_proof_certificates");
    assert_eq!(
        json["requests"][0]["proof_evidence"][0]["formula_schema"],
        "trust-types.Formula@1"
    );
    assert_eq!(
        json["requests"][0]["proof_evidence"][0]["evidence_kind"],
        "lean_proof"
    );
    assert_eq!(
        json["requests"][0]["proof_evidence"][0]["replay_metadata"]["source"],
        "lineage_node"
    );
    assert_eq!(
        json["requests"][0]["proof_evidence"][0]["replay_metadata"]["lineage_node_id"],
        0
    );
    assert_eq!(
        json["requests"][0]["proof_evidence"][0]["replay_metadata"]["engine"],
        "trust-full-verify"
    );
    assert!(
        json["requests"][0]["proof_evidence"][0]["replay_metadata"]["transcript_digest"]
            .as_str()
            .expect("native TrustIr report should include replay transcript digest")
            .starts_with("trust_ir-stable-v1:")
    );
    assert_eq!(json["requests"][0]["proof_evidence"][0]["trusted"], false);
}

#[test]
fn runner_rejects_unsupported_trust_ir_adapter_fixture_fail_closed() {
    let temp = TempCase::new("trust_ir_adapter_unsupported");
    let request = fixture_path(TRUST_UNRESOLVED_BRANCH_UNSUPPORTED_TRUST_IR_ADAPTER_GOLDEN);
    let report = temp.report_path();

    let (code, stdout, stderr) = run_runner(&[
        "--input",
        request.to_str().expect("request path should be utf-8"),
        "--output",
        report.to_str().expect("report path should be utf-8"),
        "--input-format",
        "trust_ir-adapter",
    ]);

    assert_eq!(code, 2, "stdout={stdout}\nstderr={stderr}");
    assert!(
        stdout.is_empty(),
        "runner should not write stdout on errors"
    );
    assert!(
        stderr.contains("TrustIr construct `CFG proof mode`"),
        "stderr should explain unsupported TrustIr construct: {stderr}"
    );
    assert!(
        !report.exists(),
        "runner should not write a report when adapter validation fails"
    );
}

#[test]
fn runner_auto_detects_trust_native_contract_cfg_fixture() {
    let temp = TempCase::new("trust_ir_adapter_contract_cfg");
    let request = fixture_path(TRUST_INCREMENT_CONTRACT_CFG_TRUST_IR_ADAPTER_GOLDEN);
    let report = temp.report_path();

    let (code, stdout, stderr) = run_runner(&[
        "--input",
        request.to_str().expect("request path should be utf-8"),
        "--output",
        report.to_str().expect("report path should be utf-8"),
    ]);

    assert_eq!(code, 0, "stdout={stdout}\nstderr={stderr}");
    assert!(stdout.is_empty(), "runner should write report to file only");
    assert!(stderr.is_empty(), "unexpected stderr: {stderr}");

    let json = read_report(&report);
    assert_eq!(
        json["source_id"],
        "tRust::compiler::trust_vc_trust_ir_adapter::increment_old_result_cfg"
    );
    assert_eq!(
        json["units"][0]["unit_id"],
        "trust_vc_fixture::increment_checked"
    );
    assert_eq!(json["units"][0]["outcome"]["status"], "verified");
    assert_eq!(
        json["units"][0]["proof_evidence"][0]["evidence_profile"],
        "typed_contract_frame"
    );
    assert_eq!(
        json["units"][0]["proof_evidence"][0]["proof_lineage"]["source"],
        "trust_types_contract"
    );
    assert_eq!(
        json["units"][0]["proof_evidence"][1]["obligation_id"],
        "ensures.old_result_reflexive"
    );
    assert_eq!(
        json["units"][0]["proof_evidence"][2]["evidence_profile"],
        "typed_translation_validation"
    );
    assert_eq!(
        json["units"][0]["proof_evidence"][2]["proof_lineage"]["rule"],
        "typed-cfg-proof"
    );
}

#[test]
fn runner_writes_golden_verified_report_json() {
    let temp = TempCase::new("verified");
    let request = temp.write_request(VERIFIED_REQUEST_JSON);
    let report = temp.report_path();

    let (code, stdout, stderr) = run_runner(&[
        "--input",
        request.to_str().expect("request path should be utf-8"),
        "--output",
        report.to_str().expect("report path should be utf-8"),
    ]);

    assert_eq!(code, 0, "stdout={stdout}\nstderr={stderr}");
    assert!(stdout.is_empty(), "runner should write report to file only");
    assert!(stderr.is_empty(), "unexpected stderr: {stderr}");

    let json = read_report(&report);
    assert_eq!(json["source_id"], "runner-golden");
    assert_eq!(json["units"][0]["unit_id"], "crate::verified");
    assert_eq!(json["units"][0]["outcome"]["status"], "verified");
    assert_eq!(json["units"][0]["cache_status"], "miss");
    assert_eq!(
        json["units"][0]["proof_evidence"][0]["source"],
        "typed_trust_vc_expr"
    );
    assert_eq!(
        json["units"][0]["proof_evidence"][0]["cache_key"]["proof_policy"],
        "evidence_only"
    );
    assert!(
        json["units"][0]["proof_evidence"][0]["cache_key"]["fingerprint"]
            .as_str()
            .expect("fingerprint should be a string")
            .starts_with("sha256:")
    );
}

#[test]
fn runner_auto_detects_mir_memory_proof_unit() {
    let temp = TempCase::new("mir_memory");
    let request = temp.write_request(MIR_MEMORY_REQUEST_JSON);
    let report = temp.report_path();

    let (code, stdout, stderr) = run_runner(&[
        "--input",
        request.to_str().expect("request path should be utf-8"),
        "--output",
        report.to_str().expect("report path should be utf-8"),
    ]);

    assert_eq!(code, 0, "stdout={stdout}\nstderr={stderr}");
    assert!(stdout.is_empty(), "runner should write report to file only");
    assert!(stderr.is_empty(), "unexpected stderr: {stderr}");

    let json = read_report(&report);
    assert_eq!(json["source_id"], "runner-mir-memory");
    assert_eq!(json["units"][0]["unit_id"], "crate::take_shared");
    assert_eq!(json["units"][0]["outcome"]["status"], "verified");
    assert_eq!(json["units"][0]["cache_status"], "miss");
    assert_eq!(
        json["units"][0]["proof_evidence"][0]["evidence_profile"],
        "ownership_memory"
    );
    assert_eq!(
        json["units"][0]["proof_evidence"][0]["reasoning_kind"],
        "ownership"
    );
    assert_eq!(
        json["units"][0]["proof_evidence"][0]["cache_key"]["ay_version"],
        "ay:runner-test"
    );
    assert!(
        json["units"][0]["proof_evidence"][0]["cache_key"]["ownership_digest"]
            .as_str()
            .expect("ownership digest should be present")
            .starts_with("sha256:")
    );
}

#[test]
fn runner_rejects_mir_memory_empty_ownership_fail_closed() {
    let temp = TempCase::new("mir_memory_empty_ownership");
    let request = temp.write_request(MIR_MEMORY_EMPTY_OWNERSHIP_JSON);
    let report = temp.report_path();

    let (code, stdout, stderr) = run_runner(&[
        "--input",
        request.to_str().expect("request path should be utf-8"),
        "--output",
        report.to_str().expect("report path should be utf-8"),
        "--input-format",
        "mir-memory",
    ]);

    assert_eq!(code, 2, "stdout={stdout}\nstderr={stderr}");
    assert!(
        stdout.is_empty(),
        "runner should not write stdout on errors"
    );
    assert!(
        stderr.contains("typed ownership and borrow state"),
        "stderr should explain fail-closed ownership rejection: {stderr}"
    );
    assert!(
        !report.exists(),
        "runner should not write a report when MIR ownership preflight fails"
    );
}

#[test]
fn runner_writes_refuted_report_and_exits_nonzero() {
    let temp = TempCase::new("refuted");
    let request = temp.write_request(REFUTED_REQUEST_JSON);
    let report = temp.report_path();

    let (code, stdout, stderr) = run_runner(&[
        "--input",
        request.to_str().expect("request path should be utf-8"),
        "--output",
        report.to_str().expect("report path should be utf-8"),
    ]);

    assert_eq!(code, 3, "stdout={stdout}\nstderr={stderr}");
    assert!(stdout.is_empty(), "runner should write report to file only");
    assert!(stderr.is_empty(), "unexpected stderr: {stderr}");

    let json = read_report(&report);
    assert_eq!(json["source_id"], "runner-golden-refuted");
    assert_eq!(json["units"][0]["outcome"]["status"], "refuted");
    assert_eq!(json["units"][0]["outcome"]["obligation_id"], "post");
}

#[test]
fn runner_reads_stdin_and_writes_stdout_when_path_is_dash() {
    let (code, stdout, stderr) =
        run_runner_with_stdin(&["--input", "-", "--output", "-"], VERIFIED_REQUEST_JSON);

    assert_eq!(code, 0, "stdout={stdout}\nstderr={stderr}");
    assert!(stderr.is_empty(), "unexpected stderr: {stderr}");
    assert!(
        stdout.ends_with('\n'),
        "stdout report should be deterministic newline-terminated JSON"
    );
    let json: Value = serde_json::from_str(&stdout).expect("stdout should be report JSON");
    assert_eq!(json["source_id"], "runner-golden");
    assert_eq!(json["units"][0]["outcome"]["status"], "verified");
}

#[cfg(not(feature = "proof-certificates"))]
#[test]
fn proof_policy_flag_overrides_request_and_fails_closed() {
    let temp = TempCase::new("policy_override");
    let request = temp.write_request(VERIFIED_REQUEST_JSON);
    let report = temp.report_path();

    let (code, stdout, stderr) = run_runner(&[
        "--input",
        request.to_str().expect("request path should be utf-8"),
        "--output",
        report.to_str().expect("report path should be utf-8"),
        "--proof-policy",
        "require-replayable-certificate",
    ]);

    assert_eq!(code, 2, "stdout={stdout}\nstderr={stderr}");
    assert!(
        stdout.is_empty(),
        "runner should not write stdout on errors"
    );
    assert!(
        stderr.contains("without the proof-certificates feature"),
        "stderr should explain fail-closed policy override: {stderr}"
    );
    assert!(
        !report.exists(),
        "runner should not write a report when verification returns an adapter error"
    );
}
