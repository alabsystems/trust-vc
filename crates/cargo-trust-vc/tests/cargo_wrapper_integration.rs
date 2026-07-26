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
const TRUST_VC_RUSTC_WRAPPER_ARTIFACT_KIND: &str =
    "cargo-trust-vc-rustc-wrapper-dependency-metadata";
const TRUST_VC_RUSTC_WRAPPER_SEMANTIC_PAYLOAD_KIND: &str = "none";
const TRUST_VC_RUSTC_WRAPPER_SEMANTIC_FACTS_PAYLOAD_KIND: &str = "trust-vc-semantic-facts-v1";

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn temp_dir(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    let sequence = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "cargo_trust_vc_wrapper_{label}_{}_{}_{}",
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

fn build_fake_cargo_recorder(root: &Path) -> PathBuf {
    let source = root.join("fake_cargo.rs");
    let binary = root.join(format!("fake-cargo{}", std::env::consts::EXE_SUFFIX));
    std::fs::write(
        &source,
        r#"
use std::{env, fs};

fn json_string(input: &str) -> String {
    let mut out = String::from("\"");
    for ch in input.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if ch.is_control() => out.push_str(&format!("\\u{:04x}", ch as u32)),
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}

fn main() {
    let record_path = env::var("TRUST_VC_FAKE_CARGO_RECORD").expect("record path");
    let args: Vec<String> = env::args().skip(1).collect();
    let mut env_vars: Vec<(String, String)> = env::vars_os()
        .filter_map(|(key, value)| Some((key.into_string().ok()?, value.into_string().ok()?)))
        .filter(|(key, _)| {
            key.starts_with(" __VERUS_DRIVER")
                || key.starts_with("__VERUS_DRIVER")
                || key == "RUSTC_WRAPPER"
                || key == "__CARGO_DEFAULT_LIB_METADATA"
        })
        .collect();
    env_vars.sort_by(|left, right| left.0.cmp(&right.0));

    let mut json = String::from("{\"args\":[");
    for (index, arg) in args.iter().enumerate() {
        if index > 0 {
            json.push(',');
        }
        json.push_str(&json_string(arg));
    }
    json.push_str("],\"env\":{");
    for (index, (key, value)) in env_vars.iter().enumerate() {
        if index > 0 {
            json.push(',');
        }
        json.push_str(&json_string(key));
        json.push(':');
        json.push_str(&json_string(value));
    }
    json.push_str("}}\n");
    fs::write(record_path, json).expect("write record");
}
"#,
    )
    .expect("fake cargo source should be writable");

    let output = Command::new(rustc_command())
        .arg("-Zno-trust-verify")
        .arg(&source)
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("rustc should execute");
    assert!(
        output.status.success(),
        "fake cargo recorder should compile\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    binary
}

fn build_fake_rustc_recorder(root: &Path) -> PathBuf {
    let source = root.join("fake_rustc.rs");
    let binary = root.join(format!("fake-rustc{}", std::env::consts::EXE_SUFFIX));
    std::fs::write(
        &source,
        r#"
use std::{env, fs, process};

fn json_string(input: &str) -> String {
    let mut out = String::from("\"");
    for ch in input.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if ch.is_control() => out.push_str(&format!("\\u{:04x}", ch as u32)),
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}

fn main() {
    let record_path = env::var("TRUST_VC_FAKE_RUSTC_RECORD").expect("record path");
    let args: Vec<String> = env::args().skip(1).collect();
    let mut index = 0;
    while index < args.len() {
        let value = if args[index] == "--emit" {
            index += 1;
            args.get(index).cloned()
        } else {
            args[index]
                .strip_prefix("--emit=")
                .map(ToString::to_string)
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
    let mut json = String::from("{\"args\":[");
    for (index, arg) in args.iter().enumerate() {
        if index > 0 {
            json.push(',');
        }
        json.push_str(&json_string(arg));
    }
    json.push_str("]}\n");
    fs::write(record_path, json).expect("write record");
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
        .arg("-Zno-trust-verify")
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

fn read_record(record_path: &Path) -> Value {
    serde_json::from_str(
        &std::fs::read_to_string(record_path).expect("fake cargo should write a record"),
    )
    .expect("fake cargo record should be valid JSON")
}

fn record_args(record: &Value) -> Vec<&str> {
    record
        .get("args")
        .and_then(Value::as_array)
        .expect("record args should be an array")
        .iter()
        .map(|arg| arg.as_str().expect("cargo arg should be a string"))
        .collect()
}

fn env_value<'a>(record: &'a Value, key: &str) -> Option<&'a str> {
    record.get("env")?.get(key)?.as_str()
}

fn env_keys(record: &Value) -> impl Iterator<Item = &str> {
    record
        .get("env")
        .and_then(Value::as_object)
        .expect("record env should be an object")
        .keys()
        .map(String::as_str)
}

fn packed_args(value: Option<&str>) -> Vec<&str> {
    value
        .unwrap_or("")
        .split(VERUS_DRIVER_ARGS_SEP)
        .filter(|arg| !arg.is_empty())
        .collect()
}

fn packed_args_for_key_prefix<'a>(record: &'a Value, key_prefix: &str) -> Vec<&'a str> {
    let Some((_, value)) = record
        .get("env")
        .and_then(Value::as_object)
        .expect("record env should be an object")
        .iter()
        .find(|(key, _)| key.starts_with(key_prefix))
    else {
        return Vec::new();
    };
    packed_args(value.as_str())
}

fn package_env_id(package_root: &Path, name: &str) -> String {
    let manifest_path = package_root.join("Cargo.toml");
    let manifest_path = manifest_path
        .canonicalize()
        .unwrap_or(manifest_path)
        .to_string_lossy()
        .into_owned();
    let digest = Sha256::digest(manifest_path.as_bytes());
    let mut manifest_path_hash = String::with_capacity(12);
    for byte in &digest[..6] {
        write!(&mut manifest_path_hash, "{byte:02x}").expect("write to string should succeed");
    }
    format!("{name}-0.1.0-{manifest_path_hash}")
}

fn package_env_id_from_manifest_path(name: &str, manifest_path: &Path) -> String {
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
    format!("{name}-0.1.0-{manifest_path_hash}")
}

fn pack_driver_args(args: &[&str]) -> String {
    args.iter()
        .flat_map(|arg| [VERUS_DRIVER_ARGS_SEP, *arg])
        .collect()
}

fn trust_vc_artifact_path(metadata_path: &Path) -> PathBuf {
    metadata_path.with_extension("vir")
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut hex = String::with_capacity(digest.len() * 2);
    for byte in digest {
        write!(&mut hex, "{byte:02x}").expect("write to string should succeed");
    }
    hex
}

fn structured_trust_vc_artifact(
    metadata_path: &Path,
    crate_name: &str,
    manifest_path: &Path,
) -> Value {
    let metadata = std::fs::read(metadata_path).expect("metadata should be readable");
    serde_json::json!({
        "schema_version": 1,
        "artifact_kind": TRUST_VC_RUSTC_WRAPPER_ARTIFACT_KIND,
        "crate_name": crate_name,
        "package_name": crate_name,
        "package_version": "0.1.0",
        "package_env_id": package_env_id_from_manifest_path(crate_name, manifest_path),
        "manifest_path": manifest_path
            .canonicalize()
            .unwrap_or_else(|_| manifest_path.to_path_buf())
            .to_string_lossy(),
        "metadata_path": metadata_path.display().to_string(),
        "metadata_len": metadata.len() as u64,
        "metadata_sha256": format!("sha256:{}", sha256_hex(&metadata)),
        "semantic_payload": {
            "kind": TRUST_VC_RUSTC_WRAPPER_SEMANTIC_PAYLOAD_KIND,
            "proof_facts_exported": false
        }
    })
}

fn write_structured_trust_vc_artifact(metadata_path: &Path, artifact: &Value) {
    let artifact_path = trust_vc_artifact_path(metadata_path);
    if let Some(parent) = artifact_path.parent() {
        std::fs::create_dir_all(parent).expect("artifact parent should be creatable");
    }
    let body = serde_json::to_string_pretty(artifact).expect("artifact JSON should serialize");
    std::fs::write(
        artifact_path,
        format!("{TRUST_VC_RUSTC_WRAPPER_ARTIFACT_MAGIC}{body}\n"),
    )
    .expect("artifact should be writable");
}

fn read_structured_trust_vc_artifact(metadata_path: &Path) -> Value {
    let content = std::fs::read_to_string(trust_vc_artifact_path(metadata_path))
        .expect("artifact should be readable");
    let body = content
        .strip_prefix(TRUST_VC_RUSTC_WRAPPER_ARTIFACT_MAGIC)
        .expect("artifact should have the cargo-trust-vc magic header");
    serde_json::from_str(body).expect("artifact body should be structured JSON")
}

fn write_trust_vc_artifact(metadata_path: &Path, crate_name: &str) {
    let artifact_parent = trust_vc_artifact_path(metadata_path)
        .parent()
        .expect("artifact should have a parent directory")
        .to_path_buf();
    let package_root = artifact_parent.join(format!("{crate_name}_artifact_package"));
    std::fs::create_dir_all(&package_root).expect("artifact package dir should be creatable");
    std::fs::write(
        package_root.join("Cargo.toml"),
        format!("[package]\nname = \"{crate_name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n"),
    )
    .expect("artifact package manifest should be writable");
    std::fs::write(metadata_path, b"fake metadata").expect("metadata should be writable");
    let artifact =
        structured_trust_vc_artifact(metadata_path, crate_name, &package_root.join("Cargo.toml"));
    write_structured_trust_vc_artifact(metadata_path, &artifact);
}

fn write_trust_vc_wrapper_package(package_root: &Path, name: &str) {
    std::fs::create_dir_all(package_root.join("src")).expect("package src dir should exist");
    std::fs::write(
        package_root.join("Cargo.toml"),
        format!(
            r#"[package]
name = "{name}"
version = "0.1.0"
edition = "2021"

[package.metadata.verus]
verify = true
"#
        ),
    )
    .expect("package manifest should be writable");
    std::fs::write(
        package_root.join("src/lib.rs"),
        r#"
#[trust_vc::contract(ensures(result == value), returns(result))]
pub fn id(value: u64) -> u64 {
    value
}
"#,
    )
    .expect("package source should be writable");
}

fn run_dependency_import_wrapper(
    package_root: &Path,
    package_name: &str,
    dep_name: &str,
    dep_metadata_path: &Path,
    record_path: &Path,
) -> Output {
    let fake_rustc = build_fake_rustc_recorder(package_root);
    let package_id = package_env_id(package_root, package_name);
    let import_arg = format!("import-dep-if-present={dep_name}");

    Command::new(cargo_trust_vc_bin())
        .current_dir(package_root)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", package_name)
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", package_root)
        .env("CARGO_CRATE_NAME", package_name)
        .env("TRUST_VC_FAKE_RUSTC_RECORD", record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{package_id}"), "1")
        .env(
            format!("{VERUS_DRIVER_ARGS_FOR}{package_id}"),
            pack_driver_args(&[import_arg.as_str()]),
        )
        .arg(&fake_rustc)
        .args(["--crate-name", package_name, "--emit", "metadata"])
        .arg("--extern")
        .arg(format!(
            "{}={}",
            rust_extern_name(dep_name),
            dep_metadata_path.display()
        ))
        .output()
        .expect("cargo-trust-vc rustc wrapper should execute")
}

fn rust_extern_name(dep_name: &str) -> String {
    dep_name.replace('-', "_")
}

fn run_cargo_trust_vc_new(root: &Path, args: &[&str]) {
    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(root)
        .arg("new")
        .args(args)
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc new should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );
}

fn run_build(root: &Path) -> Value {
    let fake_cargo = build_fake_cargo_recorder(root);
    let record_path = root.join("cargo-record.json");
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(root)
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", real_cargo)
        .env("TRUST_VC_FAKE_CARGO_RECORD", &record_path)
        .arg("build")
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc build should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );

    read_record(&record_path)
}

fn run_verify(root: &Path) -> Value {
    let fake_cargo = build_fake_cargo_recorder(root);
    let record_path = root.join("cargo-record.json");
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(root)
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", real_cargo)
        .env("TRUST_VC_FAKE_CARGO_RECORD", &record_path)
        .arg("verify")
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc verify should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );

    read_record(&record_path)
}

fn assert_env_has(record: &Value, key: &str) {
    assert!(
        env_value(record, key).is_some(),
        "fake cargo env should contain {key}: {record:#?}"
    );
}

fn assert_env_sets(record: &Value, key: &str, value: &str) {
    assert_eq!(
        env_value(record, key),
        Some(value),
        "fake cargo env should set {key}={value}: {record:#?}"
    );
}

fn assert_env_sets_key_prefix(record: &Value, key_prefix: &str, value: &str) {
    let matches = record
        .get("env")
        .and_then(Value::as_object)
        .expect("record env should be an object")
        .iter()
        .any(|(key, observed)| key.starts_with(key_prefix) && observed.as_str() == Some(value));
    assert!(
        matches,
        "fake cargo env should contain {key_prefix}*={value}: {record:#?}"
    );
}

fn assert_cargo_verus_env_contract(record: &Value) {
    assert_env_has(record, "RUSTC_WRAPPER");
    assert_env_sets(record, "__CARGO_DEFAULT_LIB_METADATA", "verus");
    assert_env_sets(record, "__VERUS_DRIVER_VIA_CARGO__", "1");
}

/// The scaffold's `trust-vc` dependency cannot resolve in a hermetic test:
/// crates.io has no `trust-vc` package (unpublished), and a git/path source
/// would drag the full trust-vc-core/ay git graph through `cargo metadata`
/// from an unconfigured temp dir. The wrapper-contract assertions exercise
/// argv delegation through the fake-cargo recorder only, so drop the
/// dependency line before invoking the wrapper.
fn make_scaffold_hermetic(project_dir: &Path) {
    let manifest_path = project_dir.join("Cargo.toml");
    let manifest =
        std::fs::read_to_string(&manifest_path).expect("generated manifest should be readable");
    let hermetic: String = manifest
        .lines()
        .filter(|line| !line.contains("package = \"trust-vc\""))
        .map(|line| format!("{line}\n"))
        .collect();
    std::fs::write(&manifest_path, hermetic).expect("hermetic manifest should be writable");
}

#[test]
fn cargo_new_bin_scaffold_drives_build_wrapper_contract() {
    let project_name = "test_project";
    let temp = temp_dir("cargo_new_bin_scaffold_drives_build_wrapper_contract");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");

    run_cargo_trust_vc_new(&temp, &["--bin", project_name]);

    let project_dir = temp
        .join(project_name)
        .canonicalize()
        .expect("new project should canonicalize");
    let manifest = std::fs::read_to_string(project_dir.join("Cargo.toml"))
        .expect("generated manifest should be readable");
    let source = std::fs::read_to_string(project_dir.join("src/main.rs"))
        .expect("generated bin source should be readable");

    assert!(manifest.contains("[package.metadata.verus]\nverify = true\n"));
    assert!(source.contains("fn main()"));
    assert!(project_dir.join(".git").is_dir());

    make_scaffold_hermetic(&project_dir);

    let record = run_build(&project_dir);
    assert_eq!(record_args(&record), vec!["build"]);
    assert_cargo_verus_env_contract(&record);

    let package_id = package_env_id(&project_dir, project_name);
    assert_env_sets_key_prefix(&record, &format!("{VERUS_DRIVER_VERIFY}{package_id}"), "1");
    let driver_args =
        packed_args_for_key_prefix(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{package_id}"));
    assert!(
        !driver_args.contains(&format!("import-dep-if-present={project_name}").as_str()),
        "bin-only generated package should not import its own lib: {record:#?}"
    );
    assert!(
        !env_keys(&record).any(|key| key.contains("__VERUS_DRIVER_IS_BUILTIN")),
        "generated package should not be marked as a Verus builtin: {record:#?}"
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn cargo_new_bin_scaffold_drives_verify_wrapper_contract() {
    let project_name = "test_project";
    let temp = temp_dir("cargo_new_bin_scaffold_drives_verify_wrapper_contract");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");

    run_cargo_trust_vc_new(&temp, &["--bin", project_name]);

    let project_dir = temp
        .join(project_name)
        .canonicalize()
        .expect("new project should canonicalize");
    let manifest = std::fs::read_to_string(project_dir.join("Cargo.toml"))
        .expect("generated manifest should be readable");
    let source = std::fs::read_to_string(project_dir.join("src/main.rs"))
        .expect("generated bin source should be readable");

    assert!(manifest.contains("[package.metadata.verus]\nverify = true\n"));
    assert!(source.contains("fn main()"));
    assert!(project_dir.join(".git").is_dir());

    make_scaffold_hermetic(&project_dir);

    let record = run_verify(&project_dir);
    assert_eq!(record_args(&record), vec!["check"]);
    assert_cargo_verus_env_contract(&record);

    let package_id = package_env_id(&project_dir, project_name);
    assert_env_sets_key_prefix(&record, &format!("{VERUS_DRIVER_VERIFY}{package_id}"), "1");
    let driver_args =
        packed_args_for_key_prefix(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{package_id}"));
    assert!(
        !driver_args.contains(&format!("import-dep-if-present={project_name}").as_str()),
        "verify on a bin-only generated package should not import its own lib: {record:#?}"
    );
    assert!(
        !env_keys(&record).any(|key| key.contains("__VERUS_DRIVER_IS_BUILTIN")),
        "generated package should not be marked as a Verus builtin: {record:#?}"
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_verifies_selected_package_then_runs_rustc() {
    let package_name = "selected_package";
    let temp = temp_dir("rustc_wrapper_verifies_selected_package_then_runs_rustc");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    write_trust_vc_wrapper_package(&temp, package_name);

    let fake_rustc = build_fake_rustc_recorder(&temp);
    let record_path = temp.join("rustc-record.json");
    let package_id = package_env_id(&temp, package_name);

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&temp)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", package_name)
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", temp.join("."))
        .env("CARGO_CRATE_NAME", package_name)
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{package_id}"), "1")
        .arg(&fake_rustc)
        .args(["--crate-name", package_name, "--emit", "metadata"])
        .output()
        .expect("cargo-trust-vc rustc wrapper should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "selected rustc-wrapper package should verify and then run rustc\nstdout={stdout}\nstderr={stderr}"
    );

    let record = read_record(&record_path);
    assert_eq!(
        record_args(&record),
        vec!["--crate-name", package_name, "--emit", "metadata"]
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_passes_unselected_package_directly_to_rustc() {
    let package_name = "unselected_package";
    let temp = temp_dir("rustc_wrapper_passes_unselected_package_directly_to_rustc");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");

    let fake_rustc = build_fake_rustc_recorder(&temp);
    let record_path = temp.join("rustc-record.json");

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&temp)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", package_name)
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &temp)
        .env("CARGO_CRATE_NAME", package_name)
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .arg(&fake_rustc)
        .args(["--crate-name", package_name, "--emit", "metadata"])
        .output()
        .expect("cargo-trust-vc rustc wrapper should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "unselected rustc-wrapper package should pass through to rustc\nstdout={stdout}\nstderr={stderr}"
    );

    let record = read_record(&record_path);
    assert_eq!(
        record_args(&record),
        vec!["--crate-name", package_name, "--emit", "metadata"]
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_honors_no_verify_package_arg_by_running_rustc() {
    let package_name = "no_verify_package";
    let temp = temp_dir("rustc_wrapper_honors_no_verify_package_arg_by_running_rustc");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");

    let fake_rustc = build_fake_rustc_recorder(&temp);
    let record_path = temp.join("rustc-record.json");
    let package_id = package_env_id(&temp, package_name);

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&temp)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", package_name)
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &temp)
        .env("CARGO_CRATE_NAME", package_name)
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{package_id}"), "1")
        .env(
            format!("{VERUS_DRIVER_ARGS_FOR}{package_id}"),
            pack_driver_args(&["--no-verify"]),
        )
        .arg(&fake_rustc)
        .args(["--crate-name", package_name, "--emit", "metadata"])
        .output()
        .expect("cargo-trust-vc rustc wrapper should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "--no-verify package should pass through to rustc\nstdout={stdout}\nstderr={stderr}"
    );

    let record = read_record(&record_path);
    assert_eq!(
        record_args(&record),
        vec!["--crate-name", package_name, "--emit", "metadata"]
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_accepts_non_semantic_verus_driver_args() {
    let package_name = "non_semantic_args_package";
    let temp = temp_dir("rustc_wrapper_accepts_non_semantic_verus_driver_args");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    write_trust_vc_wrapper_package(&temp, package_name);

    let fake_rustc = build_fake_rustc_recorder(&temp);
    let record_path = temp.join("rustc-record.json");
    let package_id = package_env_id(&temp, package_name);

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&temp)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", package_name)
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &temp)
        .env("CARGO_CRATE_NAME", package_name)
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{package_id}"), "1")
        .env(
            format!("{VERUS_DRIVER_ARGS_FOR}{package_id}"),
            pack_driver_args(&["--expand-errors", "--rlimit=100"]),
        )
        .arg(&fake_rustc)
        .args(["--crate-name", package_name, "--emit", "metadata"])
        .output()
        .expect("cargo-trust-vc rustc wrapper should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "non-semantic Verus driver args should not block selected package verification\nstdout={stdout}\nstderr={stderr}"
    );

    let record = read_record(&record_path);
    assert_eq!(
        record_args(&record),
        vec!["--crate-name", package_name, "--emit", "metadata"]
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_fails_closed_for_unsupported_verus_driver_args() {
    let package_name = "unsupported_args_package";
    let temp = temp_dir("rustc_wrapper_fails_closed_for_unsupported_verus_driver_args");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    write_trust_vc_wrapper_package(&temp, package_name);

    let fake_rustc = build_fake_rustc_recorder(&temp);
    let record_path = temp.join("rustc-record.json");
    let package_id = package_env_id(&temp, package_name);

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&temp)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", package_name)
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &temp)
        .env("CARGO_CRATE_NAME", package_name)
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{package_id}"), "1")
        .env(
            format!("{VERUS_DRIVER_ARGS_FOR}{package_id}"),
            pack_driver_args(&["--verify-module=top"]),
        )
        .arg(&fake_rustc)
        .args(["--crate-name", package_name, "--emit", "metadata"])
        .output()
        .expect("cargo-trust-vc rustc wrapper should execute");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "unsupported Verus driver args should fail closed"
    );
    assert!(
        stderr.contains(
            "unsupported Verus cargo driver arguments for cargo-trust-vc rustc-wrapper mode"
        ),
        "stderr should explain the unsupported driver arg gap: {stderr}"
    );
    assert!(
        !record_path.exists(),
        "fake rustc should not run after fail-closed wrapper rejection"
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_allows_absent_dependency_import_arg() {
    let package_name = "import_absent_package";
    let temp = temp_dir("rustc_wrapper_allows_absent_dependency_import_arg");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    write_trust_vc_wrapper_package(&temp, package_name);

    let fake_rustc = build_fake_rustc_recorder(&temp);
    let record_path = temp.join("rustc-record.json");
    let package_id = package_env_id(&temp, package_name);

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&temp)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", package_name)
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &temp)
        .env("CARGO_CRATE_NAME", package_name)
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{package_id}"), "1")
        .env(
            format!("{VERUS_DRIVER_ARGS_FOR}{package_id}"),
            pack_driver_args(&["import-dep-if-present=spec_def"]),
        )
        .arg(&fake_rustc)
        .args(["--crate-name", package_name, "--emit", "metadata"])
        .output()
        .expect("cargo-trust-vc rustc wrapper should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "absent import-dep-if-present extern should verify selected package and run rustc\nstdout={stdout}\nstderr={stderr}"
    );

    let record = read_record(&record_path);
    assert_eq!(
        record_args(&record),
        vec!["--crate-name", package_name, "--emit", "metadata"]
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_fails_closed_for_missing_dependency_import_artifact() {
    let package_name = "import_arg_package";
    let temp = temp_dir("rustc_wrapper_fails_closed_for_missing_dependency_import_artifact");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    write_trust_vc_wrapper_package(&temp, package_name);

    let fake_rustc = build_fake_rustc_recorder(&temp);
    let record_path = temp.join("rustc-record.json");
    let package_id = package_env_id(&temp, package_name);
    let dep_metadata_path = temp.join("target").join("libspec_def.rmeta");

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&temp)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", package_name)
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &temp)
        .env("CARGO_CRATE_NAME", package_name)
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{package_id}"), "1")
        .env(
            format!("{VERUS_DRIVER_ARGS_FOR}{package_id}"),
            pack_driver_args(&["import-dep-if-present=spec-def"]),
        )
        .arg(&fake_rustc)
        .args(["--crate-name", package_name, "--emit", "metadata"])
        .arg("--extern")
        .arg(format!("spec_def={}", dep_metadata_path.display()))
        .output()
        .expect("cargo-trust-vc rustc wrapper should execute");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "missing dependency import artifact should fail closed"
    );
    assert!(
        stderr.contains("could not find cargo-trust-vc dependency artifact for `spec_def`"),
        "stderr should identify the missing import artifact: {stderr}"
    );
    assert!(
        !record_path.exists(),
        "fake rustc should not run after fail-closed import artifact rejection"
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_rejects_stale_dependency_import_artifact_without_metadata() {
    let package_name = "import_stale_package";
    let temp = temp_dir("rustc_wrapper_rejects_stale_dependency_import_artifact_without_metadata");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    write_trust_vc_wrapper_package(&temp, package_name);

    let fake_rustc = build_fake_rustc_recorder(&temp);
    let record_path = temp.join("rustc-record.json");
    let package_id = package_env_id(&temp, package_name);
    let dep_metadata_path = temp.join("target").join("libspec_def.rmeta");
    let artifact_path = trust_vc_artifact_path(&dep_metadata_path);
    std::fs::create_dir_all(
        artifact_path
            .parent()
            .expect("artifact should have a parent directory"),
    )
    .expect("artifact parent should be creatable");
    std::fs::write(
        &artifact_path,
        format!(
            "{TRUST_VC_RUSTC_WRAPPER_ARTIFACT_MAGIC}crate-name=spec_def\nmetadata={}\n",
            dep_metadata_path.display()
        ),
    )
    .expect("stale artifact should be writable");

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&temp)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", package_name)
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &temp)
        .env("CARGO_CRATE_NAME", package_name)
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{package_id}"), "1")
        .env(
            format!("{VERUS_DRIVER_ARGS_FOR}{package_id}"),
            pack_driver_args(&["import-dep-if-present=spec_def"]),
        )
        .arg(&fake_rustc)
        .args(["--crate-name", package_name, "--emit", "metadata"])
        .arg("--extern")
        .arg(format!("spec_def={}", dep_metadata_path.display()))
        .output()
        .expect("cargo-trust-vc rustc wrapper should execute");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "stale dependency import artifact without metadata should fail closed"
    );
    assert!(
        stderr.contains("missing rustc metadata output"),
        "stderr should identify the stale import artifact: {stderr}"
    );
    assert!(
        !record_path.exists(),
        "fake rustc should not run after stale import artifact rejection"
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_rejects_legacy_marker_dependency_import_artifact_with_metadata() {
    let package_name = "import_legacy_marker_package";
    let temp = temp_dir("rustc_wrapper_rejects_legacy_marker_dependency_import_artifact");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    write_trust_vc_wrapper_package(&temp, package_name);

    let record_path = temp.join("rustc-record.json");
    let dep_metadata_path = temp.join("target").join("libspec_def.rmeta");
    let artifact_path = trust_vc_artifact_path(&dep_metadata_path);
    std::fs::create_dir_all(
        artifact_path
            .parent()
            .expect("artifact should have a parent directory"),
    )
    .expect("artifact parent should be creatable");
    std::fs::write(&dep_metadata_path, b"fake metadata").expect("metadata should be writable");
    std::fs::write(
        &artifact_path,
        format!(
            "{TRUST_VC_RUSTC_WRAPPER_ARTIFACT_MAGIC}crate-name=spec_def\nmetadata={}\n",
            dep_metadata_path.display()
        ),
    )
    .expect("legacy artifact should be writable");

    let output = run_dependency_import_wrapper(
        &temp,
        package_name,
        "spec_def",
        &dep_metadata_path,
        &record_path,
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "legacy marker-only dependency import artifact should fail closed"
    );
    assert!(
        stderr.contains("valid structured dependency metadata"),
        "stderr should identify the unsupported legacy marker body: {stderr}"
    );
    assert!(
        !record_path.exists(),
        "fake rustc should not run after legacy import artifact rejection"
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_rejects_dependency_import_artifact_with_metadata_hash_mismatch() {
    let package_name = "import_hash_mismatch_package";
    let temp = temp_dir("rustc_wrapper_rejects_dependency_import_artifact_hash_mismatch");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    write_trust_vc_wrapper_package(&temp, package_name);

    let record_path = temp.join("rustc-record.json");
    let dep_metadata_path = temp.join("target").join("libspec_def.rmeta");
    write_trust_vc_artifact(&dep_metadata_path, "spec_def");
    std::fs::write(&dep_metadata_path, b"FAKE metadata").expect("metadata should be rewritable");

    let output = run_dependency_import_wrapper(
        &temp,
        package_name,
        "spec_def",
        &dep_metadata_path,
        &record_path,
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "dependency import artifact with changed metadata should fail closed"
    );
    assert!(
        stderr.contains("metadata hash mismatch"),
        "stderr should identify the metadata hash mismatch: {stderr}"
    );
    assert!(
        !record_path.exists(),
        "fake rustc should not run after metadata hash mismatch rejection"
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_rejects_forged_dependency_import_artifact_package_identity() {
    let package_name = "import_forged_identity_package";
    let temp = temp_dir("rustc_wrapper_rejects_forged_dependency_import_artifact_identity");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    write_trust_vc_wrapper_package(&temp, package_name);

    let record_path = temp.join("rustc-record.json");
    let dep_metadata_path = temp.join("target").join("libspec_def.rmeta");
    std::fs::create_dir_all(
        dep_metadata_path
            .parent()
            .expect("metadata should have a parent directory"),
    )
    .expect("metadata parent should be creatable");
    std::fs::write(&dep_metadata_path, b"fake metadata").expect("metadata should be writable");
    let mut artifact =
        structured_trust_vc_artifact(&dep_metadata_path, "spec_def", &temp.join("Cargo.toml"));
    artifact["package_env_id"] = Value::String("spec_def-0.1.0-forged".to_string());
    write_structured_trust_vc_artifact(&dep_metadata_path, &artifact);

    let output = run_dependency_import_wrapper(
        &temp,
        package_name,
        "spec_def",
        &dep_metadata_path,
        &record_path,
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "dependency import artifact with forged package identity should fail closed"
    );
    assert!(
        stderr.contains("mismatched package identity metadata"),
        "stderr should identify the package identity mismatch: {stderr}"
    );
    assert!(
        !record_path.exists(),
        "fake rustc should not run after forged identity rejection"
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_exports_and_imports_dependency_artifact() {
    let temp = temp_dir("rustc_wrapper_exports_and_imports_dependency_artifact");
    let dep_root = temp.join("spec_def");
    let consumer_root = temp.join("consumer");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    write_trust_vc_wrapper_package(&dep_root, "spec_def");
    write_trust_vc_wrapper_package(&consumer_root, "consumer");

    let fake_rustc = build_fake_rustc_recorder(&temp);
    let dep_record_path = temp.join("dep-rustc-record.json");
    let consumer_record_path = temp.join("consumer-rustc-record.json");
    let dep_package_id = package_env_id(&dep_root, "spec_def");
    let consumer_package_id = package_env_id(&consumer_root, "consumer");
    let dep_metadata_path = temp
        .join("target")
        .join("debug")
        .join("deps")
        .join("libspec_def.rmeta");

    let dep_output = Command::new(cargo_trust_vc_bin())
        .current_dir(&dep_root)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", "spec_def")
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &dep_root)
        .env("CARGO_CRATE_NAME", "spec_def")
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &dep_record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{dep_package_id}"), "1")
        .arg(&fake_rustc)
        .args(["--crate-name", "spec_def", "--emit"])
        .arg(format!("metadata={}", dep_metadata_path.display()))
        .output()
        .expect("dependency wrapper invocation should execute");

    let dep_stdout = String::from_utf8_lossy(&dep_output.stdout);
    let dep_stderr = String::from_utf8_lossy(&dep_output.stderr);
    assert!(
        dep_output.status.success(),
        "dependency package should verify, run rustc, and export an artifact\nstdout={dep_stdout}\nstderr={dep_stderr}"
    );
    assert!(
        trust_vc_artifact_path(&dep_metadata_path).is_file(),
        "successful dependency metadata emit should write cargo-trust-vc artifact"
    );
    let exported_artifact = read_structured_trust_vc_artifact(&dep_metadata_path);
    let dep_metadata = std::fs::read(&dep_metadata_path).expect("metadata should be readable");
    let dep_source_path = dep_root
        .join("src/lib.rs")
        .canonicalize()
        .expect("dependency source should canonicalize");
    let dep_source = std::fs::read(&dep_source_path).expect("dependency source should be readable");
    let dep_source_path = dep_source_path.to_string_lossy().into_owned();
    let dep_source_sha256 = format!("sha256:{}", sha256_hex(&dep_source));
    assert_eq!(exported_artifact["schema_version"], 1);
    assert_eq!(
        exported_artifact["artifact_kind"],
        TRUST_VC_RUSTC_WRAPPER_ARTIFACT_KIND
    );
    assert_eq!(exported_artifact["crate_name"], "spec_def");
    assert_eq!(exported_artifact["package_name"], "spec_def");
    assert_eq!(
        exported_artifact["metadata_path"],
        dep_metadata_path.display().to_string()
    );
    assert_eq!(exported_artifact["metadata_len"], dep_metadata.len() as u64);
    assert_eq!(
        exported_artifact["metadata_sha256"],
        format!("sha256:{}", sha256_hex(&dep_metadata))
    );
    assert_eq!(
        exported_artifact["source_path"].as_str(),
        Some(dep_source_path.as_str())
    );
    assert_eq!(
        exported_artifact["source_len"].as_u64(),
        Some(dep_source.len() as u64)
    );
    assert_eq!(
        exported_artifact["source_sha256"].as_str(),
        Some(dep_source_sha256.as_str())
    );
    assert_eq!(
        exported_artifact["semantic_payload"]["kind"],
        TRUST_VC_RUSTC_WRAPPER_SEMANTIC_FACTS_PAYLOAD_KIND
    );
    assert_eq!(
        exported_artifact["semantic_payload"]["proof_facts_exported"],
        true
    );
    assert_eq!(
        exported_artifact["semantic_payload"]["concrete_functions"][0]["name"],
        "id"
    );
    assert_eq!(
        exported_artifact["semantic_payload"]["concrete_functions"][0]["ensures"],
        serde_json::json!(["result == value"])
    );

    let consumer_output = Command::new(cargo_trust_vc_bin())
        .current_dir(&consumer_root)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", "consumer")
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &consumer_root)
        .env("CARGO_CRATE_NAME", "consumer")
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &consumer_record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{consumer_package_id}"), "1")
        .env(
            format!("{VERUS_DRIVER_ARGS_FOR}{consumer_package_id}"),
            pack_driver_args(&["import-dep-if-present=spec_def"]),
        )
        .arg(&fake_rustc)
        .args(["--crate-name", "consumer", "--emit", "metadata", "--extern"])
        .arg(format!("spec_def={}", dep_metadata_path.display()))
        .output()
        .expect("consumer wrapper invocation should execute");

    let consumer_stdout = String::from_utf8_lossy(&consumer_output.stdout);
    let consumer_stderr = String::from_utf8_lossy(&consumer_output.stderr);
    assert!(
        consumer_output.status.success(),
        "consumer package should accept exported dependency artifact, verify, and run rustc\nstdout={consumer_stdout}\nstderr={consumer_stderr}"
    );

    let consumer_record = read_record(&consumer_record_path);
    let expected_extern_arg = format!("spec_def={}", dep_metadata_path.display());
    assert_eq!(
        record_args(&consumer_record),
        vec![
            "--crate-name",
            "consumer",
            "--emit",
            "metadata",
            "--extern",
            expected_extern_arg.as_str()
        ]
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_exports_dependency_artifact_only_for_mixed_crate_lib_metadata() {
    let temp = temp_dir("rustc_wrapper_exports_dependency_artifact_only_for_mixed_crate_lib");
    let mixed_root = temp.join("mixed_package");
    let consumer_root = temp.join("consumer");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    write_trust_vc_wrapper_package(&mixed_root, "mixed_package");
    write_trust_vc_wrapper_package(&consumer_root, "consumer");
    std::fs::create_dir_all(mixed_root.join("src/bin")).expect("bin dir should be creatable");
    std::fs::write(mixed_root.join("src/bin/mixed_bin.rs"), "fn main() {}\n")
        .expect("bin source should be writable");

    let fake_rustc = build_fake_rustc_recorder(&temp);
    let mixed_package_id = package_env_id(&mixed_root, "mixed_package");
    let lib_record_path = temp.join("mixed-lib-rustc-record.json");
    let bin_record_path = temp.join("mixed-bin-rustc-record.json");
    let lib_metadata_path = temp
        .join("target")
        .join("debug")
        .join("deps")
        .join("libmixed_package.rmeta");
    let bin_metadata_path = temp
        .join("target")
        .join("debug")
        .join("deps")
        .join("mixed_bin.rmeta");

    let lib_output = Command::new(cargo_trust_vc_bin())
        .current_dir(&mixed_root)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", "mixed_package")
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &mixed_root)
        .env("CARGO_CRATE_NAME", "mixed_package")
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &lib_record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{mixed_package_id}"), "1")
        .arg(&fake_rustc)
        .args(["--crate-name", "mixed_package", "--emit"])
        .arg(format!("metadata={}", lib_metadata_path.display()))
        .output()
        .expect("mixed lib wrapper invocation should execute");
    assert!(
        lib_output.status.success(),
        "mixed package lib target should verify, run rustc, and export an artifact\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&lib_output.stdout),
        String::from_utf8_lossy(&lib_output.stderr)
    );
    assert!(
        trust_vc_artifact_path(&lib_metadata_path).is_file(),
        "lib metadata should receive a dependency sidecar"
    );
    let lib_import_record_path = temp.join("consumer-lib-import-record.json");
    let lib_import_output = run_dependency_import_wrapper(
        &consumer_root,
        "consumer",
        "mixed_package",
        &lib_metadata_path,
        &lib_import_record_path,
    );
    assert!(
        lib_import_output.status.success(),
        "consumer should accept the mixed package lib sidecar\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&lib_import_output.stdout),
        String::from_utf8_lossy(&lib_import_output.stderr)
    );

    let bin_output = Command::new(cargo_trust_vc_bin())
        .current_dir(&mixed_root)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", "mixed_package")
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &mixed_root)
        .env("CARGO_CRATE_NAME", "mixed_bin")
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &bin_record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{mixed_package_id}"), "1")
        .arg(&fake_rustc)
        .args(["--crate-name", "mixed_bin", "--emit"])
        .arg(format!("metadata={}", bin_metadata_path.display()))
        .output()
        .expect("mixed bin wrapper invocation should execute");
    assert!(
        bin_output.status.success(),
        "mixed package bin target should verify and run rustc\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&bin_output.stdout),
        String::from_utf8_lossy(&bin_output.stderr)
    );
    assert!(
        bin_metadata_path.is_file(),
        "fake rustc should still produce the bin metadata output"
    );
    assert!(
        !trust_vc_artifact_path(&bin_metadata_path).exists(),
        "bin metadata must not receive a dependency sidecar with lib semantic facts"
    );

    let bin_import_record_path = temp.join("consumer-bin-import-record.json");
    let bin_import_output = run_dependency_import_wrapper(
        &consumer_root,
        "consumer",
        "mixed_bin",
        &bin_metadata_path,
        &bin_import_record_path,
    );
    let bin_import_stderr = String::from_utf8_lossy(&bin_import_output.stderr);
    assert!(
        !bin_import_output.status.success(),
        "consumer should fail closed instead of importing a mixed package bin artifact"
    );
    assert!(
        bin_import_stderr
            .contains("could not find cargo-trust-vc dependency artifact for `mixed_bin`"),
        "stderr should identify the missing bin dependency sidecar: {bin_import_stderr}"
    );
    assert!(
        !bin_import_record_path.exists(),
        "fake rustc should not run after missing bin sidecar rejection"
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_semantic_artifact_allows_dependency_concrete_postcondition() {
    let temp = temp_dir("rustc_wrapper_semantic_artifact_allows_dependency_concrete_postcondition");
    let dep_root = temp.join("spec_def");
    let consumer_root = temp.join("consumer");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    write_trust_vc_wrapper_package(&dep_root, "spec_def");
    write_trust_vc_wrapper_package(&consumer_root, "consumer");
    std::fs::write(
        consumer_root.join("Cargo.toml"),
        format!(
            r#"[package]
name = "consumer"
version = "0.1.0"
edition = "2021"

[package.metadata.verus]
verify = true

[dependencies]
spec_def = {{ path = "{}" }}
"#,
            dep_root.display()
        ),
    )
    .expect("consumer manifest should be writable");
    std::fs::write(
        consumer_root.join("src/lib.rs"),
        r#"
#[trust_vc::contract(ensures(result == value), returns(result))]
pub fn call_dep(value: u64) -> u64 {
    spec_def::id(value)
}
"#,
    )
    .expect("consumer source should be writable");

    let fake_rustc = build_fake_rustc_recorder(&temp);
    let dep_record_path = temp.join("dep-rustc-record.json");
    let consumer_record_path = temp.join("consumer-rustc-record.json");
    let dep_package_id = package_env_id(&dep_root, "spec_def");
    let consumer_package_id = package_env_id(&consumer_root, "consumer");
    let dep_metadata_path = temp
        .join("target")
        .join("debug")
        .join("deps")
        .join("libspec_def.rmeta");

    let dep_output = Command::new(cargo_trust_vc_bin())
        .current_dir(&dep_root)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", "spec_def")
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &dep_root)
        .env("CARGO_CRATE_NAME", "spec_def")
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &dep_record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{dep_package_id}"), "1")
        .arg(&fake_rustc)
        .args(["--crate-name", "spec_def", "--emit"])
        .arg(format!("metadata={}", dep_metadata_path.display()))
        .output()
        .expect("dependency wrapper invocation should execute");
    assert!(
        dep_output.status.success(),
        "dependency package should export a semantic artifact\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&dep_output.stdout),
        String::from_utf8_lossy(&dep_output.stderr)
    );

    let consumer_output = Command::new(cargo_trust_vc_bin())
        .current_dir(&consumer_root)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", "consumer")
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &consumer_root)
        .env("CARGO_CRATE_NAME", "consumer")
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &consumer_record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{consumer_package_id}"), "1")
        .env(
            format!("{VERUS_DRIVER_ARGS_FOR}{consumer_package_id}"),
            pack_driver_args(&["import-dep-if-present=spec_def"]),
        )
        .arg(&fake_rustc)
        .args(["--crate-name", "consumer", "--emit", "metadata", "--extern"])
        .arg(format!("spec_def={}", dep_metadata_path.display()))
        .output()
        .expect("consumer wrapper invocation should execute");

    assert!(
        consumer_output.status.success(),
        "consumer should verify using the dependency concrete postcondition from the matching semantic artifact\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&consumer_output.stdout),
        String::from_utf8_lossy(&consumer_output.stderr)
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_rejects_dependency_semantic_artifact_after_source_tamper() {
    let temp = temp_dir("rustc_wrapper_rejects_dependency_semantic_artifact_after_source_tamper");
    let dep_root = temp.join("spec_def");
    let consumer_root = temp.join("consumer");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    write_trust_vc_wrapper_package(&dep_root, "spec_def");
    write_trust_vc_wrapper_package(&consumer_root, "consumer");
    std::fs::write(
        consumer_root.join("Cargo.toml"),
        format!(
            r#"[package]
name = "consumer"
version = "0.1.0"
edition = "2021"

[package.metadata.verus]
verify = true

[dependencies]
spec_def = {{ path = "{}" }}
"#,
            dep_root.display()
        ),
    )
    .expect("consumer manifest should be writable");
    std::fs::write(
        consumer_root.join("src/lib.rs"),
        r#"
#[trust_vc::contract(ensures(result == value), returns(result))]
pub fn call_dep(value: u64) -> u64 {
    spec_def::id(value)
}
"#,
    )
    .expect("consumer source should be writable");

    let fake_rustc = build_fake_rustc_recorder(&temp);
    let dep_record_path = temp.join("dep-rustc-record.json");
    let consumer_record_path = temp.join("consumer-rustc-record.json");
    let dep_package_id = package_env_id(&dep_root, "spec_def");
    let consumer_package_id = package_env_id(&consumer_root, "consumer");
    let dep_metadata_path = temp
        .join("target")
        .join("debug")
        .join("deps")
        .join("libspec_def.rmeta");

    let dep_output = Command::new(cargo_trust_vc_bin())
        .current_dir(&dep_root)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", "spec_def")
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &dep_root)
        .env("CARGO_CRATE_NAME", "spec_def")
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &dep_record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{dep_package_id}"), "1")
        .arg(&fake_rustc)
        .args(["--crate-name", "spec_def", "--emit"])
        .arg(format!("metadata={}", dep_metadata_path.display()))
        .output()
        .expect("dependency wrapper invocation should execute");
    assert!(
        dep_output.status.success(),
        "dependency package should export a semantic artifact\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&dep_output.stdout),
        String::from_utf8_lossy(&dep_output.stderr)
    );

    std::fs::write(
        dep_root.join("src/lib.rs"),
        r#"
#[trust_vc::contract(ensures(result == value), returns(result))]
pub fn id(value: u64) -> u64 {
    0_u64
}
"#,
    )
    .expect("dependency source should be rewritable");

    let consumer_output = Command::new(cargo_trust_vc_bin())
        .current_dir(&consumer_root)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", "consumer")
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &consumer_root)
        .env("CARGO_CRATE_NAME", "consumer")
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &consumer_record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{consumer_package_id}"), "1")
        .env(
            format!("{VERUS_DRIVER_ARGS_FOR}{consumer_package_id}"),
            pack_driver_args(&["import-dep-if-present=spec_def"]),
        )
        .arg(&fake_rustc)
        .args(["--crate-name", "consumer", "--emit", "metadata", "--extern"])
        .arg(format!("spec_def={}", dep_metadata_path.display()))
        .output()
        .expect("consumer wrapper invocation should execute");

    let stderr = String::from_utf8_lossy(&consumer_output.stderr);
    assert!(
        !consumer_output.status.success(),
        "consumer should fail closed when dependency source no longer matches the semantic artifact"
    );
    assert!(
        stderr.contains("source hash mismatch"),
        "stderr should identify the dependency source hash mismatch: {stderr}"
    );
    assert!(
        !consumer_record_path.exists(),
        "fake rustc should not run after semantic artifact source mismatch"
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_rejects_tampered_dependency_concrete_postcondition_fact() {
    let temp = temp_dir("rustc_wrapper_rejects_tampered_dependency_concrete_postcondition_fact");
    let dep_root = temp.join("spec_def");
    let consumer_root = temp.join("consumer");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    write_trust_vc_wrapper_package(&dep_root, "spec_def");
    write_trust_vc_wrapper_package(&consumer_root, "consumer");
    std::fs::write(
        consumer_root.join("Cargo.toml"),
        format!(
            r#"[package]
name = "consumer"
version = "0.1.0"
edition = "2021"

[package.metadata.verus]
verify = true

[dependencies]
spec_def = {{ path = "{}" }}
"#,
            dep_root.display()
        ),
    )
    .expect("consumer manifest should be writable");
    std::fs::write(
        consumer_root.join("src/lib.rs"),
        r#"
#[trust_vc::contract(ensures(result == value), returns(result))]
pub fn call_dep(value: u64) -> u64 {
    spec_def::id(value)
}
"#,
    )
    .expect("consumer source should be writable");

    let fake_rustc = build_fake_rustc_recorder(&temp);
    let dep_record_path = temp.join("dep-rustc-record.json");
    let consumer_record_path = temp.join("consumer-rustc-record.json");
    let dep_package_id = package_env_id(&dep_root, "spec_def");
    let consumer_package_id = package_env_id(&consumer_root, "consumer");
    let dep_metadata_path = temp
        .join("target")
        .join("debug")
        .join("deps")
        .join("libspec_def.rmeta");

    let dep_output = Command::new(cargo_trust_vc_bin())
        .current_dir(&dep_root)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", "spec_def")
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &dep_root)
        .env("CARGO_CRATE_NAME", "spec_def")
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &dep_record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{dep_package_id}"), "1")
        .arg(&fake_rustc)
        .args(["--crate-name", "spec_def", "--emit"])
        .arg(format!("metadata={}", dep_metadata_path.display()))
        .output()
        .expect("dependency wrapper invocation should execute");
    assert!(
        dep_output.status.success(),
        "dependency package should export a semantic artifact\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&dep_output.stdout),
        String::from_utf8_lossy(&dep_output.stderr)
    );
    let mut artifact = read_structured_trust_vc_artifact(&dep_metadata_path);
    artifact["semantic_payload"]["concrete_functions"][0]["ensures"] =
        serde_json::json!(["result == value + 1u64"]);
    write_structured_trust_vc_artifact(&dep_metadata_path, &artifact);

    let consumer_output = Command::new(cargo_trust_vc_bin())
        .current_dir(&consumer_root)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", "consumer")
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &consumer_root)
        .env("CARGO_CRATE_NAME", "consumer")
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &consumer_record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{consumer_package_id}"), "1")
        .env(
            format!("{VERUS_DRIVER_ARGS_FOR}{consumer_package_id}"),
            pack_driver_args(&["import-dep-if-present=spec_def"]),
        )
        .arg(&fake_rustc)
        .args(["--crate-name", "consumer", "--emit", "metadata", "--extern"])
        .arg(format!("spec_def={}", dep_metadata_path.display()))
        .output()
        .expect("consumer wrapper invocation should execute");

    let stdout = String::from_utf8_lossy(&consumer_output.stdout);
    let stderr = String::from_utf8_lossy(&consumer_output.stderr);
    assert!(
        !consumer_output.status.success(),
        "consumer should fail closed when the semantic fact no longer matches the dependency source contract"
    );
    assert!(
        stdout.contains("matching semantic proof artifact")
            || stderr.contains("matching semantic proof artifact"),
        "output should identify the missing matching fact\nstdout={stdout}\nstderr={stderr}"
    );
    assert!(
        !consumer_record_path.exists(),
        "fake rustc should not run after semantic artifact mismatch"
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_import_dep_if_present_still_verifies_selected_package() {
    let package_name = "import_verification_failure";
    let temp = temp_dir("rustc_wrapper_import_dep_if_present_still_verifies_selected_package");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    write_trust_vc_wrapper_package(&temp, package_name);
    std::fs::write(
        temp.join("src/lib.rs"),
        r#"
#[trust_vc::contract(ensures(result == value + 1), returns(result))]
pub fn id(value: u64) -> u64 {
    value
}
"#,
    )
    .expect("failing package source should be writable");

    let fake_rustc = build_fake_rustc_recorder(&temp);
    let record_path = temp.join("rustc-record.json");
    let package_id = package_env_id(&temp, package_name);
    let dep_metadata_path = temp.join("target").join("libspec_def.rmeta");
    write_trust_vc_artifact(&dep_metadata_path, "spec_def");

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&temp)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", package_name)
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &temp)
        .env("CARGO_CRATE_NAME", package_name)
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{package_id}"), "1")
        .env(
            format!("{VERUS_DRIVER_ARGS_FOR}{package_id}"),
            pack_driver_args(&["import-dep-if-present=spec_def"]),
        )
        .arg(&fake_rustc)
        .args([
            "--crate-name",
            package_name,
            "--emit",
            "metadata",
            "--extern",
        ])
        .arg(format!("spec_def={}", dep_metadata_path.display()))
        .output()
        .expect("cargo-trust-vc rustc wrapper should execute");

    assert!(
        !output.status.success(),
        "selected package verification failure should not silently pass through import support"
    );
    assert!(
        !record_path.exists(),
        "fake rustc should not run when selected package verification fails"
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn rustc_wrapper_does_not_bypass_selected_crate_with_build_script_prefix_name() {
    let package_name = "build-script-selected";
    let crate_name = "build_script_selected";
    let temp =
        temp_dir("rustc_wrapper_does_not_bypass_selected_crate_with_build_script_prefix_name");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");
    write_trust_vc_wrapper_package(&temp, package_name);

    let fake_rustc = build_fake_rustc_recorder(&temp);
    let record_path = temp.join("rustc-record.json");
    let package_id = package_env_id(&temp, package_name);

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&temp)
        .env("__VERUS_DRIVER_VIA_CARGO__", "1")
        .env("CARGO_PKG_NAME", package_name)
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env("CARGO_MANIFEST_DIR", &temp)
        .env("CARGO_CRATE_NAME", crate_name)
        .env("TRUST_VC_FAKE_RUSTC_RECORD", &record_path)
        .env(
            VERUS_DRIVER_ARGS,
            pack_driver_args(&["--VIA-CARGO", "compile-when-not-primary-package"]),
        )
        .env(format!("{VERUS_DRIVER_VERIFY}{package_id}"), "1")
        .arg(&fake_rustc)
        .args([
            "--crate-name",
            crate_name,
            "--emit",
            "metadata",
            "src/lib.rs",
        ])
        .output()
        .expect("cargo-trust-vc rustc wrapper should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "selected crate with build_script_ crate-name prefix should verify and then run rustc\nstdout={stdout}\nstderr={stderr}"
    );

    let record = read_record(&record_path);
    assert_eq!(
        record_args(&record),
        vec![
            "--crate-name",
            crate_name,
            "--emit",
            "metadata",
            "src/lib.rs"
        ]
    );

    std::fs::remove_dir_all(temp).ok();
}

#[test]
fn cargo_subcommand_shape_new_lib_scaffold() {
    let project_name = "lib_project";
    let temp = temp_dir("cargo_subcommand_shape_new_lib_scaffold");
    std::fs::create_dir_all(&temp).expect("temp dir should be creatable");

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&temp)
        .args(["trust_vc", "new", "--lib", project_name])
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc trust_vc new should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );

    let project_dir = temp.join(project_name);
    assert!(project_dir.join("src/lib.rs").is_file());
    assert!(!project_dir.join("src/main.rs").exists());

    std::fs::remove_dir_all(temp).ok();
}
