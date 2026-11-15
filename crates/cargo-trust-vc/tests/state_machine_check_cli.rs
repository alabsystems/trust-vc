// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `cargo trust-vc check` over files that declare a D1a `state_machine!`.
//!
//! This is the half of the harness that proves the generated obligations are
//! DISCOVERED: the inductiveness lemmas are ordinary `#[trust_vc::proof]`
//! functions at the file root, so the scan finds them by ident and line, and a
//! machine whose lemma fails cannot produce a clean file-level report. A
//! refused or poisoned invocation is reported as a file-level failure at its
//! own line, so a file whose machine was never expanded cannot report clean
//! either.

use serde_json::Value;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

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
    panic!("cargo-trust-vc binary not found; build the workspace first");
}

fn temp_file(label: &str, source: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "trust_vc_state_machine_{label}_{}_{}",
        std::process::id(),
        unique
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join(format!("{label}.rs"));
    std::fs::write(&file, source).expect("write fixture");
    file
}

struct Run {
    json: Value,
    exit_code: i32,
}

impl Run {
    fn result_of(&self, name: &str) -> String {
        self.json["functions"]
            .as_array()
            .expect("functions is an array")
            .iter()
            .find(|entry| entry["name"] == name)
            .unwrap_or_else(|| {
                panic!(
                    "function `{name}` is absent from the report: {}",
                    serde_json::to_string_pretty(&self.json).unwrap_or_default()
                )
            })["result"]
            .as_str()
            .expect("result is a string")
            .to_string()
    }

    fn file_errors(&self) -> Vec<(u64, String)> {
        self.json["file_errors"]
            .as_array()
            .map(|entries| {
                entries
                    .iter()
                    .map(|entry| {
                        (
                            entry["line"].as_u64().unwrap_or(0),
                            entry["detail"].as_str().unwrap_or_default().to_string(),
                        )
                    })
                    .collect()
            })
            .unwrap_or_default()
    }
}

fn run_check(file: &Path, extra: &[&str]) -> Run {
    let mut command = Command::new(cargo_trust_vc_bin());
    command.args(["trust-vc", "check", "--json"]);
    command.args(extra);
    let output = command
        .arg(file)
        .env("TRUST_VC_DISABLE_VC_CACHE", "1")
        .output()
        .expect("run cargo-trust-vc");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let json: Value = serde_json::from_str(&stdout).unwrap_or_else(|err| {
        panic!(
            "check did not emit JSON ({err}).\nstdout:\n{stdout}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stderr)
        )
    });
    Run {
        json,
        exit_code: output.status.code().unwrap_or(-1),
    }
}

const CONTROL: &str = r#"
use trust_vc_types::int;

trust_vc::state_machine! { Y {
    fields {
        pub y: int,
        pub z: int,
    }

    init! {
        initialize(y: int, z: int) {
            require(y <= z);
            init y = y;
            init z = z;
        }
    }

    transition! {
        tr1(n: int) {
            require pre.y <= pre.z;
            require n >= 0;
            update z = pre.z + n;
        }
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        self.y <= self.z
    }

    #[inductive(initialize)]
    fn y_initialize_inductive(post: Self, y: int, z: int) {}

    #[inductive(tr1)]
    fn y_tr1_inductive(pre: Self, post: Self, n: int) {}
} }
"#;

/// One token away from `CONTROL`: `update y = pre.y + 2` breaks the invariant.
const LIAR: &str = r#"
use trust_vc_types::int;

trust_vc::state_machine! { Y {
    fields {
        pub y: int,
        pub z: int,
    }

    transition! {
        tr1(n: int) {
            require pre.y <= pre.z;
            require n >= 0;
            update y = pre.y + 2;
        }
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        self.y <= self.z
    }

    #[inductive(tr1)]
    fn y_tr1_inductive(pre: Self, post: Self, n: int) {}
} }
"#;

const ASSUME_FALSE: &str = r#"
use trust_vc_types::int;

trust_vc::state_machine! { Y {
    fields {
        pub z: int,
    }

    transition! {
        tr(n: int) {
            update z = pre.z - 1;
        }
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        self.z >= 0
    }

    #[inductive(tr)]
    fn y_tr_inductive(pre: Self, post: Self, n: int) {
        trust_vc::assume!(false);
    }
} }
"#;

#[test]
fn a_control_machine_reports_both_generated_lemmas_as_verified() {
    let file = temp_file("control", CONTROL);
    let run = run_check(&file, &[]);
    assert_eq!(run.result_of("y_initialize_inductive"), "verified");
    assert_eq!(run.result_of("y_tr1_inductive"), "verified");
    assert!(
        run.file_errors().is_empty(),
        "an admitted machine leaves no file-level failure: {:?}",
        run.file_errors()
    );
    assert_eq!(run.exit_code, 0, "a clean file exits 0");
}

#[test]
fn a_machine_whose_lemma_fails_cannot_report_clean() {
    let file = temp_file("liar", LIAR);
    let run = run_check(&file, &[]);
    assert_eq!(
        run.result_of("y_tr1_inductive"),
        "counterexample",
        "the generated lemma must be discovered and refuted by name"
    );
    assert_ne!(run.exit_code, 0, "a refuted lemma must exit non-zero");
}

#[test]
fn a_poisoned_invocation_is_reported_at_its_own_line_and_exits_non_zero() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../trust-vc/tests/fixtures/state_machine/sm_bare_unbound.rs");
    let run = run_check(&path, &[]);
    let file_errors = run.file_errors();
    assert!(
        file_errors.iter().any(|(line, detail)| *line == 12
            && detail.contains("bare state_machine! is not resolved to trust_vc here")),
        "the invocation line should be reported unscannable: {file_errors:?}"
    );
    assert_eq!(run.result_of("bare_unbound_client"), "error");
    assert_ne!(run.exit_code, 0);
}

#[test]
fn no_cheating_reports_an_assume_inside_a_generated_lemma() {
    let file = temp_file("assume_false", ASSUME_FALSE);
    let run = run_check(&file, &["--no-cheating"]);
    let rendered = serde_json::to_string(&run.json).unwrap_or_default();
    assert!(
        rendered.contains("source assumption"),
        "--no-cheating should report the lemma's assume!: {rendered}"
    );
    assert_ne!(run.exit_code, 0, "--no-cheating must fail on an assume");
}

// ---------------------------------------------------------------------------
// The manifest's `min_obligations` quantity, measured through the artifact the
// evidence gate actually reads.

/// The number of CAPTURED certificate obligations per non-error expected case
/// of the `state_machines.rs` manifest entry, MEASURED 2026-09-17.
///
/// `evidence.rs:6396` compares a row's `min_obligations` against
/// `observed_case.obligation_count`, and `evidence.rs:9259-9277` builds that
/// from the certificate obligations whose status is `verified` /
/// `counterexample` / `unknown` / `error` — never `assumed`, `skipped` or
/// `uncaptured` (`verify.rs:129-136`). That is a strictly smaller quantity
/// than `vc.obligations().len()`: a generated D1a inductiveness lemma extracts
/// 7 obligations and CHECKS exactly 1, because its requires conjuncts are
/// assumed.
const CAPTURED_CERTIFICATE_OBLIGATIONS: &[(&str, usize)] = &[
    ("state_machine_relation_codegen_tr1_verified", 6),
    ("state_machine_init_branch_relation_verified", 5),
    ("tokenized_bool_add_remove_surrogate_verified", 5),
    ("state_machine_relation_wrong_post_counterexample", 2),
    ("tokenized_bool_have_missing_counterexample", 2),
    ("rc_init_inductive", 1),
    ("rc_correct_init", 1),
    ("rc_rev_init", 1),
    ("rc_tr2_inductive", 1),
    ("rc_correct_tr2_noassert", 1),
    ("rc_rev_tr2_noassert", 1),
    ("rc_rev_init_wrong", 1),
    ("ldv_tr_inductive", 1),
    ("ldv_init_inductive", 1),
];

fn state_machines_manifest_floors() -> Vec<(String, usize)> {
    let manifest_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json");
    let manifest: Value = serde_json::from_str(
        &std::fs::read_to_string(&manifest_path).expect("verus manifest should be readable"),
    )
    .expect("verus manifest should be JSON");
    let entry = manifest["entries"]
        .as_array()
        .expect("entries is an array")
        .iter()
        .find(|entry| {
            entry["upstream_path"]
                .as_str()
                .is_some_and(|path| path.ends_with("state_machines.rs"))
        })
        .expect("the manifest carries a state_machines.rs entry");
    entry["expected_cases"]
        .as_array()
        .expect("expected_cases is an array")
        .iter()
        .filter(|case| case["expected_verdict"].as_str() != Some("error"))
        .map(|case| {
            (
                case["case_id"]
                    .as_str()
                    .expect("case_id is a string")
                    .to_string(),
                case["min_obligations"]
                    .as_u64()
                    .expect("min_obligations is an integer") as usize,
            )
        })
        .collect()
}

/// Every non-error `state_machines.rs` row declares a floor the EVIDENCE LANE
/// can meet.
///
/// This is the pin for a metadata defect this increment introduced and then
/// corrected: the D1a rows first declared the EXTRACTED obligation count
/// (7 / 4), which the corpus lane could never observe, so the rows would have
/// failed the moment the entry left `unsupported-gap`. The certificate is the
/// arbiter, so the test produces one and reads it.
#[test]
fn every_state_machines_row_declares_a_floor_the_certificate_meets() {
    let port = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/state_machines.rs");
    let source = std::fs::read_to_string(&port).expect("the ported corpus file should be readable");
    // A COPY, so the certificate lands in the temp directory rather than in
    // the corpus tree: `--emit-certificate` writes to the target's parent.
    let file = temp_file("state_machines_port", &source);
    let run = run_check(&file, &["--emit-certificate"]);
    assert_ne!(
        run.exit_code, 0,
        "the port carries counterexample and error cases by design"
    );

    let certificate_path = file
        .parent()
        .expect("the temp copy has a parent")
        .join(".trust_vc/proof-certificate.json");
    let certificate: Value = serde_json::from_str(
        &std::fs::read_to_string(&certificate_path).expect("the certificate should be written"),
    )
    .expect("the certificate should be JSON");

    let captured_by_case: std::collections::BTreeMap<String, usize> = certificate["functions"]
        .as_array()
        .expect("functions is an array")
        .iter()
        .map(|function| {
            let name = function["name"]
                .as_str()
                .expect("name is a string")
                .to_string();
            let captured = function["obligations"]
                .as_array()
                .map(|obligations| {
                    obligations
                        .iter()
                        .filter(|obligation| {
                            matches!(
                                obligation["status"].as_str(),
                                Some("verified")
                                    | Some("counterexample")
                                    | Some("unknown")
                                    | Some("error")
                            )
                        })
                        .count()
                })
                .unwrap_or(0);
            (name, captured)
        })
        .collect();

    let measured: std::collections::BTreeMap<&str, usize> =
        CAPTURED_CERTIFICATE_OBLIGATIONS.iter().copied().collect();
    let floors = state_machines_manifest_floors();
    assert_eq!(
        floors.len(),
        CAPTURED_CERTIFICATE_OBLIGATIONS.len(),
        "every non-error manifest row needs a measured captured count: {floors:?}"
    );

    for (case, min_obligations) in floors {
        let captured = *captured_by_case
            .get(&case)
            .unwrap_or_else(|| panic!("{case} should appear in the certificate"));
        let expected = *measured
            .get(case.as_str())
            .unwrap_or_else(|| panic!("{case} has no measured captured count"));
        assert_eq!(
            captured, expected,
            "{case} captured-obligation count moved: expected {expected}, got {captured}"
        );
        assert!(
            captured >= min_obligations,
            "{case} declares min_obligations {min_obligations} but the certificate captures only {captured}"
        );
    }
}
