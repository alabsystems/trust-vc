// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use serde_json::Value;
use sha2::{Digest, Sha256};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

const VERUS_DRIVER_ARGS: &str = " __VERUS_DRIVER_ARGS__";
const VERUS_DRIVER_ARGS_FOR: &str = " __VERUS_DRIVER_ARGS_FOR_";
const VERUS_DRIVER_ARGS_SEP: &str = "__VERUS_DRIVER_ARGS_SEP__";
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
        "cargo_trust_vc_focus_{label}_{}_{}",
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

    panic!(
        "cargo-trust-vc binary not found; run `targo --unverified build -p targo-trust-vc` first"
    );
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

fn write_workspace(root: &Path, packages: &[PackageSpec<'_>]) {
    std::fs::create_dir_all(root).expect("workspace root should be creatable");
    let mut manifest = "[workspace]\nresolver = \"2\"\nmembers = [\n".to_string();
    for package in packages {
        manifest.push_str(&format!("  \"{}\",\n", package.name));
    }
    manifest.push_str("]\n");
    std::fs::write(root.join("Cargo.toml"), manifest)
        .expect("workspace manifest should be writable");

    for package in packages {
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

    // targo exports only `$CARGO` to test processes: `$RUSTC` when set, else the
    // Trust compiler, never a bare `rustc` from PATH.
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "trustc".to_string());
    let output = Command::new(rustc)
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

fn env_value<'a>(record: &'a Value, key: &str) -> Option<&'a str> {
    record.get("env")?.get(key)?.as_str()
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

fn env_keys(record: &Value) -> impl Iterator<Item = &str> {
    record
        .get("env")
        .and_then(Value::as_object)
        .expect("record env should be an object")
        .keys()
        .map(String::as_str)
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

fn packed_args_contain(value: Option<&str>, expected: &str) -> bool {
    value
        .unwrap_or("")
        .split(VERUS_DRIVER_ARGS_SEP)
        .any(|arg| arg == expected)
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

fn run_focus(root: &Path, args: &[&str]) -> Value {
    let fake_cargo = build_fake_cargo_recorder(root);
    let record_path = root.join("cargo-record.json");
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "targo".to_string());

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(root)
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", real_cargo)
        .env("TRUST_VC_FAKE_CARGO_RECORD", &record_path)
        .arg("focus")
        .args(args)
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );

    read_record(&record_path)
}

fn assert_cargo_verus_env_contract(record: &Value) {
    assert_env_has(record, "RUSTC_WRAPPER");
    assert_env_sets(record, "__CARGO_DEFAULT_LIB_METADATA", "verus");
    assert_env_sets(record, "__VERUS_DRIVER_VIA_CARGO__", "1");
}

#[test]
fn crate_optin_manifest() {
    let package_dir = temp_dir("crate_optin_manifest");
    write_package(&package_dir, "foo", Some(true), &[]);
    let package_dir = package_dir
        .canonicalize()
        .expect("package path should canonicalize");
    let manifest_path = package_dir.join("Cargo.toml");
    let manifest_arg = manifest_path
        .to_str()
        .expect("manifest path should be valid UTF-8");
    let record = run_focus(&package_dir, &["--manifest-path", manifest_arg]);

    let target_dir = package_dir.join("target").join("verus-partial");
    assert_eq!(
        record_args(&record),
        vec![
            "--unverified",
            "check",
            "--manifest-path",
            manifest_arg,
            "--target-dir",
            target_dir
                .to_str()
                .expect("target dir should be valid UTF-8")
        ]
    );

    let foo_prefix = format!(
        "__VERUS_DRIVER_VERIFY_{}",
        package_env_id(&package_dir, "foo")
    );
    let foo_args_prefix = format!(
        "{VERUS_DRIVER_ARGS_FOR}{}",
        package_env_id(&package_dir, "foo")
    );
    assert_cargo_verus_env_contract(&record);
    assert_env_sets_key_prefix(&record, &foo_prefix, "1");
    assert_env_has_no_key_prefix(&record, &foo_args_prefix);

    std::fs::remove_dir_all(package_dir).ok();
}

#[test]
fn workspace_manifest() {
    let workspace = temp_dir("workspace_manifest");
    write_workspace(
        &workspace,
        &[
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
        ],
    );
    let workspace = workspace
        .canonicalize()
        .expect("workspace path should canonicalize");
    let manifest_path = workspace.join("Cargo.toml");
    let manifest_arg = manifest_path
        .to_str()
        .expect("manifest path should be valid UTF-8");
    let record = run_focus(&workspace, &["--manifest-path", manifest_arg]);

    let target_dir = workspace.join("target").join("verus-partial");
    assert_eq!(
        record_args(&record),
        vec![
            "--unverified",
            "check",
            "--manifest-path",
            manifest_arg,
            "--target-dir",
            target_dir
                .to_str()
                .expect("target dir should be valid UTF-8")
        ]
    );

    assert_cargo_verus_env_contract(&record);
    let hasdeps_id = package_env_id(&workspace.join("hasdeps"), "hasdeps");
    let optin_id = package_env_id(&workspace.join("optin"), "optin");
    let optout_id = package_env_id(&workspace.join("optout"), "optout");
    let unset_id = package_env_id(&workspace.join("unset"), "unset");
    assert_env_sets_key_prefix(&record, &format!("{VERUS_DRIVER_VERIFY}{hasdeps_id}"), "1");
    assert!(
        !packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps_id}")),
            "--no-verify"
        ),
        "workspace root hasdeps should not receive --no-verify: {record:#?}"
    );
    assert_env_sets_key_prefix(&record, &format!("{VERUS_DRIVER_VERIFY}{optin_id}"), "1");
    assert!(
        !packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{optin_id}")),
            "--no-verify"
        ),
        "workspace root optin should not receive --no-verify: {record:#?}"
    );
    assert_env_has_no_key_prefix(&record, &format!("{VERUS_DRIVER_VERIFY}{optout_id}"));
    assert_env_has_no_key_prefix(&record, &format!("{VERUS_DRIVER_VERIFY}{unset_id}"));

    std::fs::remove_dir_all(workspace).ok();
}

#[test]
fn workspace_package_hasdeps() {
    let workspace = temp_dir("workspace_package_hasdeps");
    write_workspace(
        &workspace,
        &[
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
                deps: &["optin", "optout"],
            },
        ],
    );
    let workspace = workspace
        .canonicalize()
        .expect("workspace path should canonicalize");
    let record = run_focus(&workspace, &["--package", "hasdeps"]);

    let target_dir = workspace.join("target").join("verus-partial");
    assert_eq!(
        record_args(&record),
        vec![
            "--unverified",
            "check",
            "--target-dir",
            target_dir
                .to_str()
                .expect("target dir should be valid UTF-8"),
            "--package",
            "hasdeps"
        ]
    );

    assert_cargo_verus_env_contract(&record);
    let hasdeps_id = package_env_id(&workspace.join("hasdeps"), "hasdeps");
    let optin_id = package_env_id(&workspace.join("optin"), "optin");
    let optout_id = package_env_id(&workspace.join("optout"), "optout");
    let unset_id = package_env_id(&workspace.join("unset"), "unset");
    assert_env_sets_key_prefix(&record, &format!("{VERUS_DRIVER_VERIFY}{hasdeps_id}"), "1");
    assert!(
        !packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps_id}")),
            "--no-verify"
        ),
        "selected focus root should not receive --no-verify: {record:#?}"
    );
    assert_env_sets_key_prefix(&record, &format!("{VERUS_DRIVER_VERIFY}{optin_id}"), "1");
    assert!(
        packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{optin_id}")),
            "--no-verify"
        ),
        "verified dependency outside selected focus root should receive --no-verify: {record:#?}"
    );
    assert_env_has_no_key_prefix(&record, &format!("{VERUS_DRIVER_VERIFY}{optout_id}"));
    assert_env_has_no_key_prefix(&record, &format!("{VERUS_DRIVER_VERIFY}{unset_id}"));

    std::fs::remove_dir_all(workspace).ok();
}

#[test]
fn workspace_package_hasdeps_forwards_verus_args_only_to_roots() {
    let workspace = temp_dir("workspace_package_hasdeps_forwarding");
    write_workspace(
        &workspace,
        &[
            PackageSpec {
                name: "optin",
                verify: Some(true),
                deps: &[],
            },
            PackageSpec {
                name: "hasdeps",
                verify: Some(true),
                deps: &["optin"],
            },
        ],
    );
    let workspace = workspace
        .canonicalize()
        .expect("workspace path should canonicalize");
    let record = run_focus(
        &workspace,
        &["--package", "hasdeps", "--", "--verify-module=bar"],
    );

    assert!(
        !packed_args_contain(env_value(&record, VERUS_DRIVER_ARGS), "--verify-module=bar"),
        "forwarded Verus args should not be in common driver args: {record:#?}"
    );

    let hasdeps_id = package_env_id(&workspace.join("hasdeps"), "hasdeps");
    let optin_id = package_env_id(&workspace.join("optin"), "optin");
    assert!(
        packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps_id}")),
            "--verify-module=bar"
        ),
        "selected root crate should receive --verify-module=bar: {record:#?}"
    );
    assert!(
        !packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{optin_id}")),
            "--verify-module=bar"
        ),
        "dependency should not receive --verify-module=bar: {record:#?}"
    );

    std::fs::remove_dir_all(workspace).ok();
}
