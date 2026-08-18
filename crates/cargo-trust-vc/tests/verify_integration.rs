// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use serde_json::Value;
use sha2::{Digest, Sha256};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

const VERUS_DRIVER_VERIFY: &str = "__VERUS_DRIVER_VERIFY_";

struct PackageSpec<'a> {
    name: &'a str,
    verify: Option<bool>,
    deps: &'a [&'a str],
}

fn temp_dir(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    std::env::temp_dir().join(format!(
        "cargo_trust_vc_verify_{label}_{}_{}",
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

fn write_package(package_root: &Path, name: &str, verify: Option<bool>, deps: &[&str]) {
    std::fs::create_dir_all(package_root.join("src")).expect("package src dir should exist");

    let mut manifest = format!(
        "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\npublish = false\n\n"
    );
    if !deps.is_empty() {
        manifest.push_str("[dependencies]\n");
        for dep in deps {
            manifest.push_str(&format!("{dep} = {{ path = \"../{dep}\" }}\n"));
        }
        manifest.push('\n');
    }
    if let Some(verify) = verify {
        manifest.push_str("[package.metadata.verus]\n");
        manifest.push_str(&format!("verify = {verify}\n"));
    }

    std::fs::write(package_root.join("Cargo.toml"), manifest)
        .expect("package manifest should be writable");
    std::fs::write(package_root.join("src/lib.rs"), "").expect("package lib should be writable");
}

fn write_workspace(root: &Path) {
    std::fs::create_dir_all(root).expect("workspace root should be creatable");
    std::fs::write(
        root.join("Cargo.toml"),
        r#"[workspace]
resolver = "2"
members = [
  "optin",
  "optout",
  "unset",
  "hasdeps",
]
"#,
    )
    .expect("workspace manifest should be writable");

    for package in [
        PackageSpec {
            name: "optin",
            verify: Some(true),
            deps: &[],
        },
        PackageSpec {
            name: "optout",
            verify: Some(false),
            deps: &[],
        },
        PackageSpec {
            name: "unset",
            verify: None,
            deps: &[],
        },
        PackageSpec {
            name: "hasdeps",
            verify: Some(true),
            deps: &["optin"],
        },
    ] {
        write_package(
            &root.join(package.name),
            package.name,
            package.verify,
            package.deps,
        );
    }
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
        .arg("-Ztrust-verify=off")
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

fn run_verify(current_dir: Option<&Path>, record_root: &Path, args: &[&str]) -> Value {
    let fake_cargo = build_fake_cargo_recorder(record_root);
    let record_path = record_root.join("cargo-record.json");
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());

    let mut command = Command::new(cargo_trust_vc_bin());
    if let Some(current_dir) = current_dir {
        command.current_dir(current_dir);
    }
    let output = command
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", real_cargo)
        .env("TRUST_VC_FAKE_CARGO_RECORD", &record_path)
        .arg("verify")
        .args(args)
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );

    serde_json::from_str(
        &std::fs::read_to_string(record_path).expect("fake cargo should write a record"),
    )
    .expect("fake cargo record should be valid JSON")
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

fn record_args(record: &Value) -> Vec<&str> {
    record
        .get("args")
        .and_then(Value::as_array)
        .expect("record args should be an array")
        .iter()
        .map(|arg| arg.as_str().expect("cargo arg should be a string"))
        .collect()
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

fn assert_env_has_no_key_prefix(record: &Value, key_prefix: &str) {
    assert!(
        !env_keys(record).any(|key| key.starts_with(key_prefix)),
        "fake cargo env should not contain {key_prefix}*: {record:#?}"
    );
}

fn assert_cargo_verus_env_contract(record: &Value) {
    assert_env_has(record, "RUSTC_WRAPPER");
    assert_env_sets(record, "__CARGO_DEFAULT_LIB_METADATA", "verus");
    assert_env_sets(record, "__VERUS_DRIVER_VIA_CARGO__", "1");
}

fn package_env_id(package_root: &Path, name: &str) -> String {
    let manifest_path = package_root.join("Cargo.toml");
    let digest = Sha256::digest(manifest_path.to_string_lossy().as_bytes());
    let mut manifest_path_hash = String::with_capacity(12);
    for byte in &digest[..6] {
        write!(&mut manifest_path_hash, "{byte:02x}").expect("write to string should succeed");
    }
    format!("{name}-0.1.0-{manifest_path_hash}")
}

fn single_package(label: &str, verify: Option<bool>) -> PathBuf {
    let package_dir = temp_dir(label);
    write_package(&package_dir, "foo", verify, &[]);
    package_dir
        .canonicalize()
        .expect("package path should canonicalize")
}

fn manifest_arg(root: &Path) -> String {
    root.join("Cargo.toml")
        .to_str()
        .expect("manifest path should be valid UTF-8")
        .to_string()
}

fn assert_single_verify_env(record: &Value, package_dir: &Path, should_verify: bool) {
    assert_cargo_verus_env_contract(record);
    if should_verify {
        let package_prefix = format!(
            "{VERUS_DRIVER_VERIFY}{}",
            package_env_id(package_dir, "foo")
        );
        assert_env_sets_key_prefix(record, &package_prefix, "1");
    } else {
        assert_env_has_no_key_prefix(record, VERUS_DRIVER_VERIFY);
    }
}

fn workspace_fixture(label: &str) -> PathBuf {
    let workspace = temp_dir(label);
    write_workspace(&workspace);
    workspace
        .canonicalize()
        .expect("workspace path should canonicalize")
}

fn assert_workspace_verify_env(record: &Value, workspace: &Path, optin: bool, hasdeps: bool) {
    assert_cargo_verus_env_contract(record);
    for (name, should_verify) in [("optin", optin), ("hasdeps", hasdeps)] {
        let package_prefix = format!(
            "{VERUS_DRIVER_VERIFY}{}",
            package_env_id(&workspace.join(name), name)
        );
        if should_verify {
            assert_env_sets_key_prefix(record, &package_prefix, "1");
        } else {
            assert_env_has_no_key_prefix(record, &package_prefix);
        }
    }
    for name in ["optout", "unset"] {
        let package_prefix = format!(
            "{VERUS_DRIVER_VERIFY}{}",
            package_env_id(&workspace.join(name), name)
        );
        assert_env_has_no_key_prefix(record, &package_prefix);
    }
}

#[test]
fn crate_optin_workdir() {
    let package_dir = single_package("crate_optin_workdir", Some(true));
    let record = run_verify(Some(&package_dir), &package_dir, &[]);

    assert_eq!(record_args(&record), vec!["check"]);
    assert_single_verify_env(&record, &package_dir, true);

    std::fs::remove_dir_all(package_dir).ok();
}

#[test]
fn crate_optin_manifest() {
    let package_dir = single_package("crate_optin_manifest", Some(true));
    let manifest_arg = manifest_arg(&package_dir);
    let record = run_verify(None, &package_dir, &["--manifest-path", &manifest_arg]);

    assert_eq!(
        record_args(&record),
        vec!["check", "--manifest-path", manifest_arg.as_str()]
    );
    assert_single_verify_env(&record, &package_dir, true);

    std::fs::remove_dir_all(package_dir).ok();
}

#[test]
fn crate_optout_workdir() {
    let package_dir = single_package("crate_optout_workdir", Some(false));
    let record = run_verify(Some(&package_dir), &package_dir, &[]);

    assert_eq!(record_args(&record), vec!["check"]);
    assert_single_verify_env(&record, &package_dir, false);

    std::fs::remove_dir_all(package_dir).ok();
}

#[test]
fn crate_optout_manifest() {
    let package_dir = single_package("crate_optout_manifest", Some(false));
    let manifest_arg = manifest_arg(&package_dir);
    let record = run_verify(None, &package_dir, &["--manifest-path", &manifest_arg]);

    assert_eq!(
        record_args(&record),
        vec!["check", "--manifest-path", manifest_arg.as_str()]
    );
    assert_single_verify_env(&record, &package_dir, false);

    std::fs::remove_dir_all(package_dir).ok();
}

#[test]
fn crate_unset_workdir() {
    let package_dir = single_package("crate_unset_workdir", None);
    let record = run_verify(Some(&package_dir), &package_dir, &[]);

    assert_eq!(record_args(&record), vec!["check"]);
    assert_single_verify_env(&record, &package_dir, false);

    std::fs::remove_dir_all(package_dir).ok();
}

#[test]
fn crate_unset_manifest() {
    let package_dir = single_package("crate_unset_manifest", None);
    let manifest_arg = manifest_arg(&package_dir);
    let record = run_verify(None, &package_dir, &["--manifest-path", &manifest_arg]);

    assert_eq!(
        record_args(&record),
        vec!["check", "--manifest-path", manifest_arg.as_str()]
    );
    assert_single_verify_env(&record, &package_dir, false);

    std::fs::remove_dir_all(package_dir).ok();
}

#[test]
fn workspace_workdir() {
    let workspace = workspace_fixture("workspace_workdir");
    let record = run_verify(Some(&workspace), &workspace, &[]);

    assert_eq!(record_args(&record), vec!["check"]);
    assert_workspace_verify_env(&record, &workspace, true, true);

    std::fs::remove_dir_all(workspace).ok();
}

#[test]
fn workspace_manifest() {
    let workspace = workspace_fixture("workspace_manifest");
    let manifest_arg = manifest_arg(&workspace);
    let record = run_verify(None, &workspace, &["--manifest-path", &manifest_arg]);

    assert_eq!(
        record_args(&record),
        vec!["check", "--manifest-path", manifest_arg.as_str()]
    );
    assert_workspace_verify_env(&record, &workspace, true, true);

    std::fs::remove_dir_all(workspace).ok();
}

#[test]
fn workspace_manifest_package_optin() {
    let workspace = workspace_fixture("workspace_manifest_package_optin");
    let manifest_arg = manifest_arg(&workspace);
    let record = run_verify(
        None,
        &workspace,
        &["--manifest-path", &manifest_arg, "--package", "optin"],
    );

    assert_eq!(
        record_args(&record),
        vec![
            "check",
            "--manifest-path",
            manifest_arg.as_str(),
            "--package",
            "optin"
        ]
    );
    assert_workspace_verify_env(&record, &workspace, true, false);

    std::fs::remove_dir_all(workspace).ok();
}

#[test]
fn workspace_manifest_package_hasdeps() {
    let workspace = workspace_fixture("workspace_manifest_package_hasdeps");
    let manifest_arg = manifest_arg(&workspace);
    let record = run_verify(
        None,
        &workspace,
        &["--manifest-path", &manifest_arg, "--package", "hasdeps"],
    );

    assert_eq!(
        record_args(&record),
        vec![
            "check",
            "--manifest-path",
            manifest_arg.as_str(),
            "--package",
            "hasdeps"
        ]
    );
    assert_workspace_verify_env(&record, &workspace, true, true);

    std::fs::remove_dir_all(workspace).ok();
}
