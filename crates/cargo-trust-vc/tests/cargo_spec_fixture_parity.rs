// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use serde_json::Value;
use sha2::{Digest, Sha256};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

const VERUS_DRIVER_ARGS_FOR: &str = " __VERUS_DRIVER_ARGS_FOR_";
const VERUS_DRIVER_ARGS: &str = " __VERUS_DRIVER_ARGS__";
const VERUS_DRIVER_ARGS_SEP: &str = "__VERUS_DRIVER_ARGS_SEP__";
const VERUS_DRIVER_VERIFY: &str = "__VERUS_DRIVER_VERIFY_";
const TRUST_VC_RUSTC_WRAPPER_ARTIFACT_MAGIC: &str = "trust-vc-rustc-wrapper-artifact-v1\n";

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn temp_dir(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    let sequence = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "cargo_trust_vc_fixture_parity_{label}_{}_{}_{}",
        std::process::id(),
        unique,
        sequence
    ))
}

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
    if fallback.exists() {
        return fallback;
    }

    panic!("cargo-trust-vc binary not found; run `cargo build -p cargo-trust-vc` first");
}

fn fixture_path(name: &str) -> PathBuf {
    repo_root().join("evals/verus/ported").join(name)
}

fn pinned_verus_test_path(relative_under_tests: &str) -> PathBuf {
    let root = std::env::var_os("VERUS_ROOT")
        .or_else(|| std::env::var_os("TRUST_VC_VERUS_ROOT"))
        .map(PathBuf::from)
        .unwrap_or_else(|| repo_root().join("../verus"));

    root.join("source/rust_verify_test/tests")
        .join(relative_under_tests)
}

fn pinned_upstream_state_machine_macro_usage_path() -> PathBuf {
    pinned_verus_test_path("cargo-tests/verified/state_machine_macro_usage/src/lib.rs")
}

fn pinned_upstream_consume_machines_path() -> PathBuf {
    pinned_verus_test_path("cargo-tests/unverified/consume_machines/src/lib.rs")
}

fn rustc_command() -> PathBuf {
    if let Ok(path) = std::env::var("RUSTC") {
        return PathBuf::from(path);
    }
    if let Ok(path) = std::env::var("CARGO") {
        if let Some(parent) = PathBuf::from(path).parent() {
            let sibling = parent.join(format!("rustc{}", std::env::consts::EXE_SUFFIX));
            if sibling.exists() {
                return sibling;
            }
        }
    }
    PathBuf::from(format!("rustc{}", std::env::consts::EXE_SUFFIX))
}

fn cargo_command() -> PathBuf {
    std::env::var("CARGO")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from(format!("cargo{}", std::env::consts::EXE_SUFFIX)))
}

fn build_fake_rustc_recorder(root: &Path) -> PathBuf {
    let source = root.join("fake_rustc.rs");
    let binary = root.join(format!("fake-rustc{}", std::env::consts::EXE_SUFFIX));
    std::fs::write(
        &source,
        r#"
use std::{env, fs, process};

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    let mut index = 0;
    while index < args.len() {
        let value = if args[index] == "--emit" {
            index += 1;
            args.get(index).cloned()
        } else {
            args[index].strip_prefix("--emit=").map(ToString::to_string)
        };
        if let Some(value) = value {
            for emit in value.split(',') {
                if let Some(path) = emit.trim().strip_prefix("metadata=") {
                    if !path.is_empty() {
                        let path = std::path::Path::new(path);
                        if let Some(parent) = path.parent() {
                            fs::create_dir_all(parent).expect("create metadata parent");
                        }
                        fs::write(path, b"fake metadata").expect("write metadata");
                    }
                }
            }
        }
        index += 1;
    }
    if let Ok(record_path) = env::var("TRUST_VC_FAKE_RUSTC_RECORD") {
        fs::write(record_path, args.join("\n")).expect("write record");
    }
    let exit_code = env::var("TRUST_VC_FAKE_RUSTC_EXIT")
        .ok()
        .and_then(|value| value.parse::<i32>().ok())
        .unwrap_or(0);
    process::exit(exit_code);
}
"#,
    )
    .expect("fake rustc source should be writable");

    let output = Command::new(rustc_command())
        .arg("-Ztrust-verify=off")
        .arg(&source)
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("rustc should execute");
    assert!(
        output.status.success(),
        "fake rustc recorder should compile\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    binary
}

fn run_fixture_check(fixture: &str, function: &str) -> (Option<i32>, Value, String) {
    let fixture = fixture_path(fixture);
    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&fixture)
        .arg("check")
        .arg("--json")
        .arg("--function")
        .arg(function)
        .arg(".")
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let json = serde_json::from_str(&stdout)
        .unwrap_or_else(|err| panic!("stdout should be cargo-trust-vc JSON: {err}\n{stdout}"));
    (output.status.code(), json, stderr)
}

fn pack_driver_args(args: &[&str]) -> String {
    args.iter()
        .flat_map(|arg| [VERUS_DRIVER_ARGS_SEP, *arg])
        .collect()
}

fn package_env_id_from_manifest_path(
    package_name: &str,
    package_version: &str,
    manifest_path: &Path,
) -> String {
    let manifest_path = manifest_path
        .canonicalize()
        .unwrap_or_else(|_| manifest_path.to_path_buf())
        .to_string_lossy()
        .into_owned();
    let digest = Sha256::digest(manifest_path.as_bytes());
    let mut manifest_path_hash = String::with_capacity(12);
    for byte in &digest[..6] {
        write!(&mut manifest_path_hash, "{byte:02x}").expect("write to string should succeed");
    }
    format!("{package_name}-{package_version}-{manifest_path_hash}")
}

fn trust_vc_artifact_path(metadata_path: &Path) -> PathBuf {
    metadata_path.with_extension("vir")
}

fn read_structured_trust_vc_artifact(metadata_path: &Path) -> Value {
    let content = std::fs::read_to_string(trust_vc_artifact_path(metadata_path))
        .expect("artifact should be readable");
    let body = content
        .strip_prefix(TRUST_VC_RUSTC_WRAPPER_ARTIFACT_MAGIC)
        .expect("artifact should have the cargo-trust-vc magic header");
    serde_json::from_str(body).expect("artifact body should be structured JSON")
}

fn run_fixture_wrapper(
    fixture: &str,
    package_name: &str,
    crate_name: &str,
    fake_rustc: &Path,
    record_path: &Path,
    package_driver_args: &[&str],
    rustc_args: &[String],
) -> Output {
    run_fixture_wrapper_with_package_version(
        fixture,
        package_name,
        "0.1.0",
        crate_name,
        fake_rustc,
        record_path,
        package_driver_args,
        rustc_args,
    )
}

#[allow(clippy::too_many_arguments)]
fn run_fixture_wrapper_with_package_version(
    fixture: &str,
    package_name: &str,
    package_version: &str,
    crate_name: &str,
    fake_rustc: &Path,
    record_path: &Path,
    package_driver_args: &[&str],
    rustc_args: &[String],
) -> Output {
    let fixture = fixture_path(fixture)
        .canonicalize()
        .expect("fixture path should canonicalize");
    let manifest_path = fixture.join("Cargo.toml");
    let package_id =
        package_env_id_from_manifest_path(package_name, package_version, &manifest_path);
    let mut command = Command::new(cargo_trust_vc_bin());
    command
        .current_dir(&fixture)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", package_name)
        .env("CARGO_PKG_VERSION", package_version)
        .env("CARGO_MANIFEST_DIR", &fixture)
        .env("CARGO_CRATE_NAME", crate_name)
        .env("TRUST_VC_FAKE_RUSTC_RECORD", record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{package_id}"), "1")
        .arg(fake_rustc)
        .args(rustc_args);
    if !package_driver_args.is_empty() {
        command.env(
            format!("{VERUS_DRIVER_ARGS_FOR}{package_id}"),
            pack_driver_args(package_driver_args),
        );
    }
    command
        .output()
        .expect("cargo-trust-vc rustc wrapper should execute")
}

fn single_function<'a>(report: &'a Value, function: &str) -> &'a Value {
    let functions = report["functions"]
        .as_array()
        .expect("functions should be an array");
    assert_eq!(
        functions.len(),
        1,
        "expected exactly one checked function: {report:#?}"
    );
    assert_eq!(functions[0]["name"], function);
    &functions[0]
}

fn single_function_result(report: &Value, function: &str) -> String {
    single_function(report, function)["result"]
        .as_str()
        .expect("function result should be a string")
        .to_string()
}

#[test]
fn spec_def_fixtures_verify_spec_precondition_surface() {
    for fixture in ["cargo_spec_def", "cargo_spec_def2"] {
        let (code, report, stderr) = run_fixture_check(fixture, "lib");
        assert_eq!(
            code,
            Some(0),
            "{fixture} lib should verify with its exported spec-function precondition\nstderr={stderr}\nreport={report:#?}"
        );
        assert_eq!(single_function_result(&report, "lib"), "verified");
    }
}

#[test]
fn spec_use_imports_dependency_spec_signatures_for_direct_contracts() {
    for function in ["concrete_b", "lib"] {
        let (code, report, stderr) = run_fixture_check("cargo_spec_use", function);
        assert_eq!(
            code,
            Some(0),
            "{function} should verify after dependency spec signatures are imported\nstderr={stderr}\nreport={report:#?}"
        );
        assert_eq!(single_function_result(&report, function), "verified");
    }
}

#[test]
fn spec_use_dependency_concrete_postconditions_fail_closed_without_artifacts() {
    let (code, report, stderr) = run_fixture_check("cargo_spec_use", "concrete_caller");
    assert_ne!(code, Some(0), "concrete_caller should remain blocked until dependency concrete postconditions have semantic artifacts\nstderr={stderr}\nreport={report:#?}");
    assert_eq!(single_function_result(&report, "concrete_caller"), "error");
    assert!(
        report.to_string().contains("semantic proof artifacts")
            || stderr.contains("semantic proof artifacts"),
        "diagnostic should name the missing semantic artifact blocker\nstderr={stderr}\nreport={report:#?}"
    );
}

#[test]
fn spec_use_imports_dependency_spec_body_axioms_for_cross_crate_equality() {
    let (code, report, stderr) = run_fixture_check("cargo_spec_use", "test");
    assert_eq!(
        code,
        Some(0),
        "test should verify once supported dependency spec bodies are imported\nstderr={stderr}\nreport={report:#?}"
    );
    assert_eq!(single_function_result(&report, "test"), "verified");
}

#[test]
fn spec_use_imports_real_fixture_semantic_artifact_for_dependency_postcondition() {
    let temp = temp_dir("real_fixture_semantic_artifact");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    let fake_rustc = build_fake_rustc_recorder(&temp);
    let dep_metadata_path = temp
        .join("target")
        .join("debug")
        .join("deps")
        .join("libspec_def.rmeta");
    let dep_record_path = temp.join("dep-rustc-record.txt");
    let consumer_record_path = temp.join("consumer-rustc-record.txt");

    let dep_output = run_fixture_wrapper(
        "cargo_spec_def",
        "spec_def",
        "spec_def",
        &fake_rustc,
        &dep_record_path,
        &[],
        &[
            "--crate-name".to_string(),
            "spec_def".to_string(),
            "--emit".to_string(),
            format!("metadata={}", dep_metadata_path.display()),
        ],
    );
    assert!(
        dep_output.status.success(),
        "cargo_spec_def should verify and export a semantic sidecar\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&dep_output.stdout),
        String::from_utf8_lossy(&dep_output.stderr)
    );
    assert!(
        trust_vc_artifact_path(&dep_metadata_path).is_file(),
        "cargo_spec_def metadata emit should write a cargo-trust-vc sidecar"
    );
    let artifact = read_structured_trust_vc_artifact(&dep_metadata_path);
    let concrete_fact_names = artifact["semantic_payload"]["concrete_functions"]
        .as_array()
        .expect("semantic payload should list concrete facts")
        .iter()
        .filter_map(|fact| fact["name"].as_str())
        .collect::<Vec<_>>();
    assert!(
        concrete_fact_names.contains(&"concrete_a"),
        "semantic sidecar should export the public reexport used by cargo_spec_use: {artifact:#?}"
    );

    let consumer_output = run_fixture_wrapper(
        "cargo_spec_use",
        "spec_use",
        "spec_use",
        &fake_rustc,
        &consumer_record_path,
        &["import-dep-if-present=spec_def"],
        &[
            "--crate-name".to_string(),
            "spec_use".to_string(),
            "--emit".to_string(),
            "metadata".to_string(),
            "--extern".to_string(),
            format!("spec_def={}", dep_metadata_path.display()),
        ],
    );
    let consumer_stdout = String::from_utf8_lossy(&consumer_output.stdout);
    let consumer_stderr = String::from_utf8_lossy(&consumer_output.stderr);
    assert!(
        consumer_output.status.success(),
        "cargo_spec_use should import cargo_spec_def's semantic sidecar and verify concrete_caller\nstdout={}\nstderr={}",
        consumer_stdout,
        consumer_stderr
    );
    assert!(
        consumer_stdout
            .lines()
            .any(|line| line.contains("concrete_caller") && line.contains("Verified")),
        "fixture import should specifically verify concrete_caller\nstdout={consumer_stdout}\nstderr={consumer_stderr}"
    );
    assert!(
        consumer_record_path.is_file(),
        "fake rustc should run after fixture dependency artifact import succeeds"
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn spec_use_imports_real_fixture_semantic_artifacts_for_renamed_spec_def2() {
    let temp = temp_dir("real_fixture_renamed_semantic_artifact");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    let fake_rustc = build_fake_rustc_recorder(&temp);
    let dep1_metadata_path = temp
        .join("target")
        .join("debug")
        .join("deps")
        .join("libspec_def_0_1.rmeta");
    let dep2_metadata_path = temp
        .join("target")
        .join("debug")
        .join("deps")
        .join("libspec_def_0_2.rmeta");
    let dep1_record_path = temp.join("dep1-rustc-record.txt");
    let dep2_record_path = temp.join("dep2-rustc-record.txt");
    let consumer_record_path = temp.join("consumer-rustc-record.txt");

    let dep1_output = run_fixture_wrapper(
        "cargo_spec_def",
        "spec_def",
        "spec_def",
        &fake_rustc,
        &dep1_record_path,
        &[],
        &[
            "--crate-name".to_string(),
            "spec_def".to_string(),
            "--emit".to_string(),
            format!("metadata={}", dep1_metadata_path.display()),
        ],
    );
    assert!(
        dep1_output.status.success(),
        "cargo_spec_def should verify and export a semantic sidecar\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&dep1_output.stdout),
        String::from_utf8_lossy(&dep1_output.stderr)
    );

    let dep2_output = run_fixture_wrapper_with_package_version(
        "cargo_spec_def2",
        "spec_def",
        "0.2.0",
        "spec_def",
        &fake_rustc,
        &dep2_record_path,
        &[],
        &[
            "--crate-name".to_string(),
            "spec_def".to_string(),
            "--emit".to_string(),
            format!("metadata={}", dep2_metadata_path.display()),
        ],
    );
    assert!(
        dep2_output.status.success(),
        "cargo_spec_def2 should verify and export a semantic sidecar\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&dep2_output.stdout),
        String::from_utf8_lossy(&dep2_output.stderr)
    );

    let dep2_artifact = read_structured_trust_vc_artifact(&dep2_metadata_path);
    assert_eq!(dep2_artifact["crate_name"], "spec_def");
    assert_eq!(dep2_artifact["package_name"], "spec_def");
    assert_eq!(dep2_artifact["package_version"], "0.2.0");
    let dep2_fact_names = dep2_artifact["semantic_payload"]["concrete_functions"]
        .as_array()
        .expect("semantic payload should list concrete facts")
        .iter()
        .filter_map(|fact| fact["name"].as_str())
        .collect::<Vec<_>>();
    assert!(
        dep2_fact_names.contains(&"concrete_a"),
        "renamed spec_def2 sidecar should export its public concrete reexport: {dep2_artifact:#?}"
    );

    let consumer_output = run_fixture_wrapper(
        "cargo_spec_use",
        "spec_use",
        "spec_use",
        &fake_rustc,
        &consumer_record_path,
        &[
            "import-dep-if-present=spec_def",
            "import-dep-if-present=spec_def2",
        ],
        &[
            "--crate-name".to_string(),
            "spec_use".to_string(),
            "--emit".to_string(),
            "metadata".to_string(),
            "--extern".to_string(),
            format!("spec_def={}", dep1_metadata_path.display()),
            "--extern".to_string(),
            format!("spec_def2={}", dep2_metadata_path.display()),
        ],
    );
    let consumer_stdout = String::from_utf8_lossy(&consumer_output.stdout);
    let consumer_stderr = String::from_utf8_lossy(&consumer_output.stderr);
    assert!(
        consumer_output.status.success(),
        "cargo_spec_use should accept both real producer sidecars, including renamed spec_def2\nstdout={}\nstderr={}",
        consumer_stdout,
        consumer_stderr
    );
    assert!(
        consumer_stdout
            .lines()
            .any(|line| line.contains("concrete_caller") && line.contains("Verified")),
        "fixture import should still verify the concrete postcondition consumer\nstdout={consumer_stdout}\nstderr={consumer_stderr}"
    );
    assert!(
        consumer_stdout
            .lines()
            .any(|line| line.contains("test") && line.contains("Verified")),
        "fixture import should still verify the spec_def/spec_def2 equality witness\nstdout={consumer_stdout}\nstderr={consumer_stderr}"
    );
    assert!(
        consumer_record_path.is_file(),
        "fake rustc should run after renamed fixture dependency artifact import succeeds"
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn unverified_spec_use_fixture_typechecks_upstream_calling_shape() {
    let fixture = fixture_path("cargo_unverified_spec_use");
    let output = Command::new(cargo_command())
        .current_dir(&fixture)
        .args(["check", "--locked", "--offline"])
        .output()
        .expect("cargo check should execute for unverified spec_use fixture");
    assert!(
        output.status.success(),
        "cargo_unverified_spec_use should typecheck its upstream-shaped test_calling body\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn unverified_spec_use_fixture_verifies_unverified_consumer_wrapper() {
    let (code, report, stderr) = run_fixture_check("cargo_unverified_spec_use", "lib");
    assert_eq!(
        code,
        Some(0),
        "unverified spec_use wrapper should verify after delegating to the unverified upstream-shaped caller\nstderr={stderr}\nreport={report:#?}"
    );
    assert_eq!(single_function_result(&report, "lib"), "verified");
}

#[test]
fn unverified_spec_use_fixture_direct_body_call_records_concrete_postcondition_artifact_blocker() {
    let (code, report, stderr) = run_fixture_check("cargo_unverified_spec_use", "direct_body_call");
    assert_ne!(
        code,
        Some(0),
        "direct unverified spec_use consumer should stay blocked until dependency concrete postconditions have semantic artifacts\nstderr={stderr}\nreport={report:#?}"
    );
    assert_eq!(single_function_result(&report, "direct_body_call"), "error");
    assert!(
        report
            .to_string()
            .contains("dependency concrete function `spec_use::concrete_b` has postconditions")
            || stderr
                .contains("dependency concrete function `spec_use::concrete_b` has postconditions"),
        "diagnostic should identify the dependency concrete postcondition semantic artifact blocker\nstderr={stderr}\nreport={report:#?}"
    );
    assert!(
        report.to_string().contains("semantic proof artifacts")
            || stderr.contains("semantic proof artifacts"),
        "diagnostic should name the missing semantic proof artifact requirement\nstderr={stderr}\nreport={report:#?}"
    );
}

#[test]
fn unverified_spec_use_fixture_imports_real_spec_use_semantic_artifact_for_direct_body_call() {
    let temp = temp_dir("unverified_real_spec_use_semantic_artifact");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    let fake_rustc = build_fake_rustc_recorder(&temp);
    let dep1_metadata_path = temp
        .join("target")
        .join("debug")
        .join("deps")
        .join("libspec_def_0_1.rmeta");
    let dep2_metadata_path = temp
        .join("target")
        .join("debug")
        .join("deps")
        .join("libspec_def_0_2.rmeta");
    let spec_use_metadata_path = temp
        .join("target")
        .join("debug")
        .join("deps")
        .join("libspec_use.rmeta");
    let dep1_record_path = temp.join("dep1-rustc-record.txt");
    let dep2_record_path = temp.join("dep2-rustc-record.txt");
    let spec_use_record_path = temp.join("spec-use-rustc-record.txt");
    let consumer_record_path = temp.join("unverified-consumer-rustc-record.txt");

    let dep1_output = run_fixture_wrapper(
        "cargo_spec_def",
        "spec_def",
        "spec_def",
        &fake_rustc,
        &dep1_record_path,
        &[],
        &[
            "--crate-name".to_string(),
            "spec_def".to_string(),
            "--emit".to_string(),
            format!("metadata={}", dep1_metadata_path.display()),
        ],
    );
    assert!(
        dep1_output.status.success(),
        "cargo_spec_def should verify and export a semantic sidecar\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&dep1_output.stdout),
        String::from_utf8_lossy(&dep1_output.stderr)
    );

    let dep2_output = run_fixture_wrapper_with_package_version(
        "cargo_spec_def2",
        "spec_def",
        "0.2.0",
        "spec_def",
        &fake_rustc,
        &dep2_record_path,
        &[],
        &[
            "--crate-name".to_string(),
            "spec_def".to_string(),
            "--emit".to_string(),
            format!("metadata={}", dep2_metadata_path.display()),
        ],
    );
    assert!(
        dep2_output.status.success(),
        "cargo_spec_def2 should verify and export a semantic sidecar\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&dep2_output.stdout),
        String::from_utf8_lossy(&dep2_output.stderr)
    );

    let spec_use_output = run_fixture_wrapper(
        "cargo_spec_use",
        "spec_use",
        "spec_use",
        &fake_rustc,
        &spec_use_record_path,
        &[
            "import-dep-if-present=spec_def",
            "import-dep-if-present=spec_def2",
        ],
        &[
            "--crate-name".to_string(),
            "spec_use".to_string(),
            "--emit".to_string(),
            format!("metadata={}", spec_use_metadata_path.display()),
            "--extern".to_string(),
            format!("spec_def={}", dep1_metadata_path.display()),
            "--extern".to_string(),
            format!("spec_def2={}", dep2_metadata_path.display()),
        ],
    );
    assert!(
        spec_use_output.status.success(),
        "cargo_spec_use should verify using dependency sidecars and export its own semantic sidecar\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&spec_use_output.stdout),
        String::from_utf8_lossy(&spec_use_output.stderr)
    );
    let spec_use_artifact = read_structured_trust_vc_artifact(&spec_use_metadata_path);
    let spec_use_fact_names = spec_use_artifact["semantic_payload"]["concrete_functions"]
        .as_array()
        .expect("semantic payload should list concrete facts")
        .iter()
        .filter_map(|fact| fact["name"].as_str())
        .collect::<Vec<_>>();
    assert!(
        spec_use_fact_names.contains(&"concrete_b")
            && spec_use_fact_names.contains(&"concrete_caller"),
        "spec_use sidecar should export the concrete facts consumed by the unverified fixture: {spec_use_artifact:#?}"
    );

    let consumer_output = run_fixture_wrapper(
        "cargo_unverified_spec_use",
        "spec_use_unverified",
        "spec_use_unverified",
        &fake_rustc,
        &consumer_record_path,
        &["import-dep-if-present=spec_use"],
        &[
            "--crate-name".to_string(),
            "spec_use_unverified".to_string(),
            "--emit".to_string(),
            "metadata".to_string(),
            "--extern".to_string(),
            format!("spec_use={}", spec_use_metadata_path.display()),
        ],
    );
    let consumer_stdout = String::from_utf8_lossy(&consumer_output.stdout);
    let consumer_stderr = String::from_utf8_lossy(&consumer_output.stderr);
    assert!(
        consumer_output.status.success(),
        "unverified spec_use fixture should verify direct_body_call using the verified spec_use semantic sidecar\nstdout={consumer_stdout}\nstderr={consumer_stderr}"
    );
    assert!(
        consumer_stdout
            .lines()
            .any(|line| line.contains("direct_body_call") && line.contains("Verified")),
        "fixture import should specifically verify direct_body_call\nstdout={consumer_stdout}\nstderr={consumer_stderr}"
    );
    assert!(
        consumer_record_path.is_file(),
        "fake rustc should run after unverified fixture dependency artifact import succeeds"
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn state_machine_macro_usage_pinned_upstream_shape_is_present() {
    let path = pinned_upstream_state_machine_macro_usage_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream state_machine_macro_usage shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "state_machine!{ Y",
        "tokenized_state_machine!(",
        "struct_with_invariants!",
        "atomic_with_ghost!",
        "spawn(",
        "join_handle1.join()",
        "assert(x == 2)",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream state_machine_macro_usage should contain {expected:?}"
        );
    }
}

#[test]
fn state_machine_macro_usage_fixture_verifies_upstream_shaped_witnesses() {
    for function in [
        "y_transition_relation_witness",
        "x_tokenized_counter_relation_witness",
        "lib",
    ] {
        let (code, report, stderr) = run_fixture_check("cargo_state_machine_macro_usage", function);
        assert_eq!(
            code,
            Some(0),
            "state_machine_macro_usage {function} should verify its explicit upstream-shaped witness\nstderr={stderr}\nreport={report:#?}"
        );
        assert_eq!(single_function_result(&report, function), "verified");
    }
}

#[test]
fn state_machine_macro_usage_support_macros_fail_closed_when_invoked() {
    let macro_crate_path = fixture_path("cargo_state_machine_macro_usage")
        .join("verus_state_machines_macros")
        .to_string_lossy()
        .replace('\\', "\\\\");

    let probes = [
        (
            "state_machine",
            r#"
use verus_state_machines_macros::state_machine;

state_machine!{ Y {
    fields {
        pub x: int,
        pub y: int,
        pub z: int,
    }

    init!{
        initialize(x: int, y: int, z: int) {
            init x = x;
            init y = y;
            require(y <= z);
            if x == y {
                init z = z;
            } else {
                init z = z + 1;
            }
        }
    }

    transition!{
        tr1(b: bool, c: bool) {
            require(b);
            assert(pre.y <= pre.z);
            require(c);
            update z = pre.z + 1;
        }
    }

    transition!{
        tr2(b: bool, c: bool) {
            if b {
                update z = pre.z + 1;
            } else {
                assert(pre.y <= pre.z);
            }
            require(c);
        }
    }

    transition!{
        tr3(b: bool, c: bool) {
            if b {
                assert(pre.y <= pre.z);
            } else {
                let j = pre.z + 1;
                update z = j;
            }
            require(c);
        }
    }

    #[invariant]
    pub fn the_inv(self) -> bool { self.y <= self.z }

    #[inductive(initialize)]
    fn init_inductive(post: Self, x: int, y: int, z: int) { }

    #[inductive(tr1)]
    fn tr1_inductive(pre: Self, post: Self, b: bool, c: bool) { }

    #[inductive(tr2)]
    fn tr2_inductive(pre: Self, post: Self, b: bool, c: bool) { }

    #[inductive(tr3)]
    fn tr3_inductive(pre: Self, post: Self, b: bool, c: bool) { }
}}

fn main() {}
"#,
            "does not yet implement Verus state_machine! expansion",
        ),
        (
            "tokenized_state_machine",
            r#"
use verus_state_machines_macros::tokenized_state_machine;

tokenized_state_machine!(
    X {
        fields {
            #[sharding(variable)]
            pub counter: int,

            #[sharding(variable)]
            pub inc_a: bool,

            #[sharding(variable)]
            pub inc_b: bool,
        }

        #[invariant]
        pub fn main_inv(&self) -> bool {
            self.counter == (if self.inc_a { 1 as int } else { 0 }) + (if self.inc_b { 1 as int } else { 0 })
        }

        init!{
            initialize() {
                init counter = 0;
                init inc_a = false;
                init inc_b = false;
            }
        }

        transition!{
            tr_inc_a() {
                require(!pre.inc_a);
                update counter = pre.counter + 1;
                update inc_a = true;
            }
        }

        transition!{
            tr_inc_b() {
                require(!pre.inc_b);
                update counter = pre.counter + 1;
                update inc_b = true;
            }
        }

        property!{
            increment_will_not_overflow_u32() {
                assert 0 <= pre.counter < 0xffff_ffff;
            }
        }

        property!{
            finalize() {
                require(pre.inc_a);
                require(pre.inc_b);
                assert pre.counter == 2;
            }
        }

        #[inductive(tr_inc_a)]
        fn tr_inc_a_preserves(pre: Self, post: Self) {
        }

        #[inductive(tr_inc_b)]
        fn tr_inc_b_preserves(pre: Self, post: Self) {
        }

        #[inductive(initialize)]
        fn initialize_inv(post: Self) {
        }
    }
);

fn main() {}
"#,
            "does not yet implement Verus tokenized_state_machine! expansion",
        ),
    ];

    for (label, source, expected_error) in probes {
        let temp = temp_dir(&format!("state_machine_macro_usage_{label}_fail_closed"));
        std::fs::create_dir_all(temp.join("src")).expect("temp probe src dir should be created");
        std::fs::write(
            temp.join("Cargo.toml"),
            format!(
                r#"[package]
name = "{label}_probe"
version = "0.1.0"
edition = "2021"

[dependencies]
verus_state_machines_macros = {{ path = "{macro_crate_path}" }}

[workspace]
"#
            ),
        )
        .expect("temp probe manifest should be writable");
        std::fs::write(temp.join("src/main.rs"), source)
            .expect("temp probe source should be writable");

        let output = Command::new(cargo_command())
            .current_dir(&temp)
            .arg("check")
            .arg("--quiet")
            .arg("--offline")
            .output()
            .expect("cargo check should execute for macro fail-closed probe");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success(),
            "{label} probe should fail closed, but cargo check succeeded"
        );
        assert!(
            stderr.contains(expected_error),
            "{label} probe should report {expected_error:?}, got stderr:\n{stderr}"
        );

        std::fs::remove_dir_all(temp).ok();
    }
}

#[test]
fn consume_machines_pinned_upstream_foo_body_is_preserved() {
    let path = pinned_upstream_consume_machines_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream consume_machines shape check; missing {}",
            path.display()
        );
        return;
    }

    let upstream = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    assert_eq!(
        upstream.trim(),
        "pub fn foo(g: state_machine_macro_usage::Global) {\n    let _f = state_machine_macro_usage::Global { ..g };\n}",
        "pinned upstream consume_machines should remain the narrow Global rebuild case"
    );

    let local = std::fs::read_to_string(
        fixture_path("cargo_unverified_consume_machines").join("src/lib.rs"),
    )
    .expect("local consume_machines fixture source should be readable");
    assert!(
        local.contains(upstream.trim()),
        "local consume_machines fixture should preserve the upstream foo body"
    );
}

#[test]
fn consume_machines_fixture_typechecks_upstream_shaped_support_crate() {
    let fixture = fixture_path("cargo_unverified_consume_machines");
    let output = Command::new(cargo_command())
        .current_dir(&fixture)
        .args(["check", "--locked", "--offline"])
        .output()
        .expect("cargo check should execute for consume_machines fixture");
    assert!(
        output.status.success(),
        "consume_machines should typecheck the upstream-shaped Global dependency surface\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn consume_machines_fixture_verifies_upstream_foo_wrapper() {
    let (code, report, stderr) = run_fixture_check("cargo_unverified_consume_machines", "lib");
    assert_eq!(
        code,
        Some(0),
        "consume_machines lib should verify after rebuilding the upstream-shaped Global support value\nstderr={stderr}\nreport={report:#?}"
    );
    assert_eq!(single_function_result(&report, "lib"), "verified");
}

#[test]
fn consume_machines_dependency_postcondition_fails_closed_without_artifact() {
    let (code, report, stderr) = run_fixture_check(
        "cargo_unverified_consume_machines",
        "direct_verified_dependency_call",
    );
    assert_ne!(
        code,
        Some(0),
        "direct dependency concrete postcondition call should stay blocked without a semantic sidecar\nstderr={stderr}\nreport={report:#?}"
    );
    assert_eq!(
        single_function_result(&report, "direct_verified_dependency_call"),
        "error"
    );
    assert!(
        report.to_string().contains(
            "dependency concrete function `state_machine_macro_usage::verified_counter_witness` has postconditions"
        ) || stderr.contains(
            "dependency concrete function `state_machine_macro_usage::verified_counter_witness` has postconditions"
        ),
        "diagnostic should identify the state_machine_macro_usage dependency postcondition blocker\nstderr={stderr}\nreport={report:#?}"
    );
    assert!(
        report.to_string().contains("semantic proof artifacts")
            || stderr.contains("semantic proof artifacts"),
        "diagnostic should name the missing semantic proof artifact requirement\nstderr={stderr}\nreport={report:#?}"
    );
}

#[test]
fn consume_machines_imports_real_support_sidecar_for_dependency_call() {
    let temp = temp_dir("consume_machines_real_support_sidecar");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    let fake_rustc = build_fake_rustc_recorder(&temp);
    let dep_metadata_path = temp
        .join("target")
        .join("debug")
        .join("deps")
        .join("libstate_machine_macro_usage.rmeta");
    let dep_record_path = temp.join("state-machine-support-rustc-record.txt");
    let consumer_record_path = temp.join("consume-machines-rustc-record.txt");

    let dep_output = run_fixture_wrapper(
        "cargo_unverified_consume_machines/state_machine_macro_usage_support",
        "state_machine_macro_usage",
        "state_machine_macro_usage",
        &fake_rustc,
        &dep_record_path,
        &[],
        &[
            "--crate-name".to_string(),
            "state_machine_macro_usage".to_string(),
            "--emit".to_string(),
            format!("metadata={}", dep_metadata_path.display()),
        ],
    );
    assert!(
        dep_output.status.success(),
        "state_machine_macro_usage support should verify and export a semantic sidecar\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&dep_output.stdout),
        String::from_utf8_lossy(&dep_output.stderr)
    );
    assert!(
        trust_vc_artifact_path(&dep_metadata_path).is_file(),
        "state_machine_macro_usage metadata emit should write a cargo-trust-vc sidecar"
    );
    let artifact = read_structured_trust_vc_artifact(&dep_metadata_path);
    let concrete_fact_names = artifact["semantic_payload"]["concrete_functions"]
        .as_array()
        .expect("semantic payload should list concrete facts")
        .iter()
        .filter_map(|fact| fact["name"].as_str())
        .collect::<Vec<_>>();
    assert!(
        concrete_fact_names.contains(&"verified_counter_witness"),
        "support sidecar should export the concrete counter witness: {artifact:#?}"
    );

    let consumer_output = run_fixture_wrapper(
        "cargo_unverified_consume_machines",
        "consume_machines",
        "consume_machines",
        &fake_rustc,
        &consumer_record_path,
        &["import-dep-if-present=state_machine_macro_usage"],
        &[
            "--crate-name".to_string(),
            "consume_machines".to_string(),
            "--emit".to_string(),
            "metadata".to_string(),
            "--extern".to_string(),
            format!("state_machine_macro_usage={}", dep_metadata_path.display()),
        ],
    );
    let consumer_stdout = String::from_utf8_lossy(&consumer_output.stdout);
    let consumer_stderr = String::from_utf8_lossy(&consumer_output.stderr);
    assert!(
        consumer_output.status.success(),
        "consume_machines should import the support sidecar and verify its direct dependency call\nstdout={consumer_stdout}\nstderr={consumer_stderr}"
    );
    assert!(
        consumer_stdout
            .lines()
            .any(|line| line.contains("direct_verified_dependency_call") && line.contains("Verified")),
        "fixture import should specifically verify direct_verified_dependency_call\nstdout={consumer_stdout}\nstderr={consumer_stderr}"
    );
    assert!(
        consumer_record_path.is_file(),
        "fake rustc should run after consume_machines dependency artifact import succeeds"
    );

    std::fs::remove_dir_all(temp).ok();
}
