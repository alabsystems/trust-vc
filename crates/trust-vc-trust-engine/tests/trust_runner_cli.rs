// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use serde_json::Value;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

#[path = "support/admission_baseline.rs"]
mod admission_baseline;
#[path = "support/admission_edits.rs"]
mod admission_edits;

/// The runner's exit codes for a native TrustIr bundle (see the runner's
/// module doc): 0 = every certificate admitted at release grade, 2 = the
/// bundle refused (no report), 5 = consumed but at least one certificate
/// refused release admission.
const EXIT_OK: i32 = 0;
const EXIT_REFUSED: i32 = 2;
const EXIT_REJECTED: i32 = 5;

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
const DISCHARGE_SCALAR_BRANCH_LIAR: &str =
    "fixtures/trust_ir_native/discharge_scalar_branch_liar.json";

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

/// The runner binary this test target was built with. Cargo sets
/// `CARGO_BIN_EXE_<bin name>` (the name as-is, hyphens kept) for integration
/// tests at compile time, so this can never pick up a stale binary from
/// another target directory.
fn runner_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust_vc-trust-runner"))
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

/// ROUND 5. The producer-validator input gate does NOT carry
/// `CertifiedCleanCicKernelRecheckFailed` past it: a `Certified` claim whose
/// CleanCic certificate fails the in-process Clean-kernel re-check is refused
/// at the door — exit 2, no report — upstream's own word on the variant being
/// "Rejected, never faith-accepted".
///
/// The corpus's own directive-less contract certificate re-checks (the gate
/// re-derives the contract goal with `trust-ir-build`'s default
/// `clean-tv-anchor` feature), so the witness is the corpus bundle with its
/// certificate TERM corrupted: still non-empty and lineage-bound, and no
/// longer a proof of anything.
#[test]
fn runner_refuses_the_corpus_bundle_whose_certified_claim_fails_its_kernel_recheck() {
    use trust_ir::request::NativeVerificationBundle;

    let payload = std::fs::read_to_string(fixture_path(NATIVE_REQUEST_TRUST_BUNDLE))
        .expect("corpus native bundle should be readable");
    let mut bundle: NativeVerificationBundle =
        serde_json::from_str(&payload).expect("corpus native bundle should decode");
    assert_eq!(
        bundle.module.proof_obligations[0].status,
        trust_ir::ProofStatus::Certified
    );
    admission_edits::corrupt_clean_cic_term(&mut bundle);
    let temp = TempCase::new("native_trust_ir_bundle_raw");
    let request = temp
        .write_request(&serde_json::to_string(&bundle).expect("edited bundle should serialize"));
    let report = temp.report_path();

    let (code, stdout, stderr) = run_runner(&[
        "--input",
        request.to_str().expect("request path should be utf-8"),
        "--output",
        report.to_str().expect("report path should be utf-8"),
    ]);

    assert_eq!(code, 2, "stdout={stdout}\nstderr={stderr}");
    assert!(stdout.is_empty(), "no report on a refusal: {stdout}");
    assert!(
        stderr.contains("clean-kernel re-check") && stderr.contains("Certified"),
        "the refusal must name what it refused on: {stderr}"
    );
    assert!(
        !report.exists(),
        "runner should not write a report when the input gate refuses"
    );
}

/// The VERBATIM corpus bundle is consumed and graded. Its obligation is
/// `Certified` and its directive-less CleanCic certificate was replayed in the
/// Clean kernel by this process, so trust-ir-build's basis K establishes
/// `Unbounded` coverage with no `assurance` row. The certificate is still
/// refused release admission, for one reason: upstream's TrustVc request
/// carries no `Assertion` replay atom, so the export seam publishes no id
/// (`missing_assertion_id`). The verdict and the exit code are both pinned.
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

    assert!(stdout.is_empty(), "runner should write report to file only");
    assert!(stderr.is_empty(), "unexpected stderr: {stderr}");

    let json = read_report(&report);
    assert_eq!(json["verdict"], "certificates_rejected", "{json}");
    assert_eq!(json["requests"][0]["verdict"], "certificates_rejected");
    let admission = &json["requests"][0]["proof_evidence"][0]["release_admission"];
    assert_eq!(
        admission["rejection_reasons"],
        serde_json::json!(["missing_assertion_id"]),
        "{admission}"
    );
    assert_eq!(admission["coverage_established"], true);
    assert_eq!(
        admission["coverage_basis"]["basis"],
        "kernel_replayed_claim"
    );
    assert_eq!(
        admission["coverage_basis"]["family"],
        "contract_ground_decision"
    );
    assert_eq!(
        json["requests"][0]["proof_evidence"][0]["obligation_status"],
        "certified"
    );
    assert_eq!(code, EXIT_REJECTED, "stdout={stdout}\nstderr={stderr}");
    assert_eq!(json["producer"], "tRust");
    assert_eq!(json["input_kind"], "rust_mir");
    assert_eq!(json["module_name"], "trust_native_request_bundle");
    assert_eq!(json["requests"][0]["request_id"], 0);
    assert_eq!(json["requests"][0]["mode"], "import_proof_certificates");
    // Both track the corpus fixture re-copied at 53ea6234: obligation 0 carries
    // an smtlib2 formula, and its certificate is a kernel-recheckable CleanCic
    // term — which the report now names as such instead of flattening it to
    // `trusted`. If either drifts, check whether the corpus moved or the runner
    // stopped carrying the field, before editing the literal.
    assert_eq!(
        json["requests"][0]["proof_evidence"][0]["formula_schema"],
        "smtlib2"
    );
    assert_eq!(
        json["requests"][0]["proof_evidence"][0]["evidence_kind"],
        "clean_cic"
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
            .starts_with("sha256:")
    );
    assert_eq!(json["requests"][0]["proof_evidence"][0]["trusted"], false);
}

/// Writes `bundle` to a fresh case directory and runs the runner on it.
fn run_bundle(
    label: &str,
    bundle: &trust_ir::request::NativeVerificationBundle,
) -> (TempCase, PathBuf, i32, String, String) {
    let temp = TempCase::new(label);
    let request =
        temp.write_request(&serde_json::to_string(bundle).expect("bundle should serialize"));
    let report = temp.report_path();
    let (code, stdout, stderr) = run_runner(&[
        "--input",
        request.to_str().expect("request path should be utf-8"),
        "--output",
        report.to_str().expect("report path should be utf-8"),
    ]);
    (temp, report, code, stdout, stderr)
}

/// The release-ADMISSIBLE baseline — the corpus bundle with a discharged
/// obligation, no coverage row, and the `Assertion` replay atom Trust's bridge
/// writes in its TrustVc request — exits 0 with `certificates_admitted`.
///
/// Its liar twins exit 2 with no report: the atom's id forged (L1, refused by
/// trust-ir at the door), the atom asserting another formula than the
/// certificate's obligation (L3, refused by trust-vc's atom gate), and the old
/// shape with the id inside a JSON payload (L9, which trust-ir never replays).
#[test]
fn runner_exits_zero_only_for_an_admitted_native_trust_ir_bundle() {
    let bundle = admission_baseline::native_bundle_fixture();
    let (_temp, report, code, stdout, stderr) =
        run_bundle("native_trust_ir_bundle_admitted", &bundle);
    let json = read_report(&report);
    assert_eq!(json["verdict"], "certificates_admitted", "{json}");
    let evidence = &json["requests"][0]["proof_evidence"][0];
    assert_eq!(evidence["release_admission"]["status"], "admissible");
    assert_eq!(evidence["release_admission"]["coverage_established"], true);
    assert_eq!(evidence["assertion_id"], 1);
    assert_eq!(evidence["independent_assertion_id"], 1);
    assert_eq!(code, EXIT_OK, "stdout={stdout}\nstderr={stderr}");

    let obligation = bundle.module.proof_obligations[0].id;
    let mut forged_id = bundle.clone();
    admission_edits::forge_atom_id(&mut forged_id, 0, obligation, 2);
    let mut forged_formula = bundle.clone();
    admission_edits::forge_atom_formula(
        &mut forged_formula,
        0,
        obligation,
        admission_edits::another_formula(
            bundle.module.proof_obligations[0]
                .formula
                .as_ref()
                .expect("baseline formula"),
        ),
    );
    let mut payload_id = bundle.clone();
    admission_baseline::install_payload_assertion_id(&mut payload_id, 0, 1);
    for (label, liar, names) in [
        (
            "native_trust_ir_bundle_forged_atom_id",
            &forged_id,
            "does not match obligation 0 source assertion",
        ),
        (
            "native_trust_ir_bundle_forged_atom_formula",
            &forged_formula,
            "must be ONE formula",
        ),
        (
            "native_trust_ir_bundle_payload_id",
            &payload_id,
            admission_baseline::PAYLOAD_ID_REFUSAL,
        ),
    ] {
        let (_temp, report, code, stdout, stderr) = run_bundle(label, liar);
        assert_eq!(
            code, EXIT_REFUSED,
            "{label}: stdout={stdout}\nstderr={stderr}"
        );
        assert!(
            stdout.is_empty(),
            "{label}: no report on a refusal: {stdout}"
        );
        assert!(
            stderr.contains(names),
            "{label}: the refusal must name what it refused on: {stderr}"
        );
        assert!(
            !report.exists(),
            "{label}: runner should not write a report when the bundle is refused"
        );
    }
}

/// The baseline plus a FORGED in-module row — an uncited SMT sibling of the kernel-replayed
/// certificate recording `Unbounded` coverage nothing derived for it — is
/// consumed, refused for the whole bundle (`certificate_coverage_refused`,
/// on the untouched kernel-replayed certificate too), and exits 5.
#[test]
fn runner_exits_rejected_for_a_forged_in_module_coverage_row() {
    let temp = TempCase::new("native_trust_ir_bundle_forged_row");
    let mut bundle = admission_baseline::native_bundle_fixture();
    let request_digest = bundle.requests[0].stable_digest();
    admission_baseline::add_sibling_certificate(
        &mut bundle,
        "trust_vc-smt",
        trust_ir::ProofEvidence::SmtProof(b"(proof)".to_vec()),
        Some(trust_ir::proof::CoverageAssurance {
            bound: trust_ir::proof::CoverageBound::Unbounded,
            request_digest,
        }),
    );
    let request =
        temp.write_request(&serde_json::to_string(&bundle).expect("bundle should serialize"));
    let report = temp.report_path();

    let (code, stdout, stderr) = run_runner(&[
        "--input",
        request.to_str().expect("request path should be utf-8"),
        "--output",
        report.to_str().expect("report path should be utf-8"),
    ]);

    let json = read_report(&report);
    assert_eq!(json["verdict"], "certificates_rejected", "{json}");
    let admission = &json["requests"][0]["proof_evidence"][0]["release_admission"];
    assert_eq!(admission["status"], "rejected", "{admission}");
    assert_eq!(
        admission["rejection_reasons"],
        serde_json::json!(["certificate_coverage_refused"])
    );
    assert!(
        admission["coverage_detail"]
            .as_str()
            .is_some_and(|detail| detail.contains("in-module coverage")),
        "{admission}"
    );
    assert_eq!(
        code, EXIT_REJECTED,
        "a forged row must not exit 0: stdout={stdout}\nstderr={stderr}"
    );
}

/// A/B, through the binary. Obligation 0's `smtlib2` payload `(>= 0 5)` is
/// FALSE and its `smtlib` rendering `(>= 5 0)` true; the CleanCic
/// certificate is re-bound to it with trust-ir's own lineage digest. Before
/// coverage rule 5 the runner exited 0 with `certificates_admitted`. Upstream
/// (trust-ir `dcc5b9a3`) now refuses the bundle, so the runner exits 2 and
/// writes no report.
#[test]
fn runner_refuses_a_bundle_whose_payload_and_rendering_disagree() {
    let temp = TempCase::new("native_trust_ir_bundle_two_texts");
    let mut bundle = admission_baseline::native_bundle_fixture();
    admission_baseline::edit_replayed_obligation(&mut bundle, |obligation| {
        let formula = obligation
            .formula
            .as_mut()
            .expect("the corpus obligation 0 has a formula");
        assert_eq!(formula.schema, "smtlib2");
        formula.payload = "(>= 0 5)".to_string();
        formula.smtlib = Some("(>= 5 0)".to_string());
    });
    let request =
        temp.write_request(&serde_json::to_string(&bundle).expect("bundle should serialize"));
    let report = temp.report_path();

    let (code, stdout, stderr) = run_runner(&[
        "--input",
        request.to_str().expect("request path should be utf-8"),
        "--output",
        report.to_str().expect("report path should be utf-8"),
    ]);

    assert_eq!(
        code, 2,
        "a false payload must not exit 0: stdout={stdout}\nstderr={stderr}"
    );
    // trust-ir-build's validator, this crate's input gate, refuses it first;
    // the bundle validator's own refusal ("obligation #0 states two formulas")
    // would follow.
    assert!(
        stderr.contains("states two SMT-LIB texts"),
        "stderr should name the two texts: {stderr}"
    );
    assert!(
        stdout.is_empty(),
        "runner should not write stdout on errors"
    );
    assert!(
        !report.exists(),
        "runner should not write a report for a refused bundle"
    );
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

/// A REFUTED discharge request must be visible to a shell that only reads `$?`.
///
/// The fixture is the liar twin: `fn clamp(x: u32) -> u32` whose `ensures
/// result >= 2` is false at `x = 1`. Before the discharge verdicts existed the
/// runner exited 0 for every native bundle, so "trust-vc refuted your
/// postcondition" and "trust-vc admitted every certificate" were the same
/// observable.
#[test]
fn native_trust_ir_discharge_refutation_exits_refuted() {
    let temp = TempCase::new("native_discharge_refuted");
    let request = fixture_path(DISCHARGE_SCALAR_BRANCH_LIAR);
    let report = temp.report_path();

    let (code, _stdout, stderr) = run_runner(&[
        "--input",
        request.to_str().expect("request path should be utf-8"),
        "--output",
        report.to_str().expect("report path should be utf-8"),
        "--input-format",
        "native-trust_ir-bundle",
    ]);

    assert_eq!(
        code, 3,
        "a refuted discharge must exit EXIT_REFUTED: {stderr}"
    );
    let json = read_report(&report);
    assert_eq!(json["verdict"], "refuted");
    assert_eq!(
        json["requests"][0]["mode"], "discharge_proof_obligations",
        "{json}"
    );
    // The request cites the postcondition alone: trust-ir refuses a discharge
    // request that cites the unsited def-site precondition, which the lane
    // assumes rather than proves.
    assert_eq!(
        json["requests"][0]["discharge"].as_array().map(Vec::len),
        Some(1),
        "{json}"
    );
    assert_eq!(
        json["requests"][0]["discharge"][0]["public_obligation_id"],
        "vc:clamp:postcondition:0"
    );
    assert_eq!(
        json["requests"][0]["discharge"][0]["outcome"]["status"],
        "counterexample"
    );
    // The model names the parameter the refutation turns on, and the path
    // conditions show WHICH branch it took — `x = 1` takes the else arm, so the
    // result is 1 and `result >= 2` is false.
    let bindings = json["requests"][0]["discharge"][0]["outcome"]["bindings"]
        .as_array()
        .expect("a counterexample carries bindings");
    assert!(
        bindings
            .iter()
            .any(|binding| binding["display_name"] == "x" && binding["value"] == "1"),
        "{bindings:?}"
    );
}
