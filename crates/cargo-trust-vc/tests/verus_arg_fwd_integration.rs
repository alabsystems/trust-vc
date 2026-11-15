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

fn temp_dir(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    std::env::temp_dir().join(format!(
        "cargo_trust_vc_verus_arg_fwd_{label}_{}_{}",
        std::process::id(),
        unique
    ))
}

/// The Trust compiler for helper binaries: `$RUSTC` when set, else `trustc`.
/// targo exports only `$CARGO` to test processes, so a bare `rustc` fallback
/// would resolve whatever `rustc` PATH carries.
fn trust_rustc() -> String {
    std::env::var("RUSTC").unwrap_or_else(|_| "trustc".to_string())
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

fn write_workspace(root: &Path) {
    write_workspace_with_default_members(root, None);
}

fn write_workspace_with_default_members(root: &Path, default_members: Option<&[&str]>) {
    std::fs::create_dir_all(root).expect("workspace root should be creatable");
    let mut workspace_manifest = r#"[workspace]
resolver = "2"
members = [
  "optin",
  "optout",
  "unset",
  "hasdeps",
  "sibling",
]
"#
    .to_string();
    if let Some(default_members) = default_members {
        workspace_manifest.push_str("default-members = [\n");
        for member in default_members {
            workspace_manifest.push_str(&format!("  \"{member}\",\n"));
        }
        workspace_manifest.push_str("]\n");
    }
    std::fs::write(root.join("Cargo.toml"), workspace_manifest)
        .expect("workspace manifest should be writable");

    write_package(root, "optin", Some(true), &[]);
    write_package(root, "optout", Some(false), &[]);
    write_package(root, "unset", None, &[]);
    write_package(root, "hasdeps", Some(true), &["optin", "optout", "unset"]);
    write_package(root, "sibling", Some(true), &[]);
}

fn write_package(root: &Path, name: &str, verify: Option<bool>, deps: &[&str]) {
    let package_root = root.join(name);
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

    let rustc = trust_rustc();
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

fn build_fake_metadata_recorder(root: &Path) -> PathBuf {
    let source = root.join("fake_metadata_cargo.rs");
    let binary = root.join(format!(
        "fake-metadata-cargo{}",
        std::env::consts::EXE_SUFFIX
    ));
    std::fs::write(
        &source,
        r#"
use std::{env, fs, path::Path};

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

fn package(workspace: &Path, id: &str, name: &str) -> String {
    let manifest_path = workspace.join(name).join("Cargo.toml");
    format!(
        "{{\"id\":{},\"name\":{},\"version\":\"0.1.0\",\"manifest_path\":{},\"metadata\":{{\"verus\":{{\"verify\":true}}}},\"targets\":[{{\"kind\":[\"lib\"]}}]}}",
        json_string(id),
        json_string(name),
        json_string(&manifest_path.to_string_lossy()),
    )
}

fn main() {
    let record_path = env::var("TRUST_VC_FAKE_METADATA_RECORD").expect("record path");
    let workspace = env::var("TRUST_VC_FAKE_METADATA_WORKSPACE").expect("workspace path");
    let workspace = Path::new(&workspace);
    let args: Vec<String> = env::args().skip(1).collect();

    let mut record = String::from("{\"args\":[");
    for (index, arg) in args.iter().enumerate() {
        if index > 0 {
            record.push(',');
        }
        record.push_str(&json_string(arg));
    }
    record.push_str("]}\n");
    fs::write(record_path, record).expect("write metadata record");

    let hasdeps = "hasdeps 0.1.0";
    let optin = "optin 0.1.0";
    let sibling = "sibling 0.1.0";
    println!(
        "{{\"packages\":[{},{},{}],\"resolve\":{{\"nodes\":[{{\"id\":{},\"dependencies\":[{}]}},{{\"id\":{},\"dependencies\":[]}},{{\"id\":{},\"dependencies\":[]}}]}},\"workspace_members\":[{},{},{}],\"workspace_default_members\":[{}],\"workspace_root\":{}}}",
        package(workspace, hasdeps, "hasdeps"),
        package(workspace, optin, "optin"),
        package(workspace, sibling, "sibling"),
        json_string(hasdeps),
        json_string(optin),
        json_string(optin),
        json_string(sibling),
        json_string(hasdeps),
        json_string(optin),
        json_string(sibling),
        json_string(hasdeps),
        json_string(&workspace.to_string_lossy()),
    );
}
"#,
    )
    .expect("fake metadata cargo source should be writable");

    let rustc = trust_rustc();
    let output = Command::new(rustc)
        .arg("-Ztrust-verify=off")
        .arg(&source)
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("rustc should execute");
    assert!(
        output.status.success(),
        "fake metadata cargo recorder should compile\nstdout={}\nstderr={}",
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

fn packed_args_contain(value: Option<&str>, expected: &str) -> bool {
    value
        .unwrap_or("")
        .split(VERUS_DRIVER_ARGS_SEP)
        .any(|arg| arg == expected)
}

fn package_env_id(workspace: &Path, name: &str) -> String {
    let manifest_path = workspace.join(name).join("Cargo.toml");
    let digest = Sha256::digest(manifest_path.to_string_lossy().as_bytes());
    let mut manifest_path_hash = String::with_capacity(12);
    for byte in &digest[..6] {
        write!(&mut manifest_path_hash, "{byte:02x}").expect("write to string should succeed");
    }
    format!("{name}-0.1.0-{manifest_path_hash}")
}

fn assert_forwarding_selector(
    subcommand: &str,
    selector: &str,
    hasdeps_receives_args: bool,
    optin_receives_args: bool,
    sibling_receives_args: bool,
) {
    let workspace = temp_dir(&format!("{subcommand}_{selector}"));
    let expected_cargo_subcommand = match subcommand {
        "build" => "build",
        _ => "check",
    };
    write_workspace(&workspace);
    let workspace = workspace
        .canonicalize()
        .expect("workspace path should canonicalize");
    let fake_cargo = build_fake_cargo_recorder(&workspace);
    let record_path = workspace.join("cargo-record.json");
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "targo".to_string());

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&workspace)
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", real_cargo)
        .env("TRUST_VC_FAKE_CARGO_RECORD", &record_path)
        .arg(subcommand)
        .arg("--package")
        .arg("hasdeps")
        .arg("--package")
        .arg("sibling")
        .args(if selector == "default" {
            Vec::<String>::new()
        } else {
            vec!["--fwd-verus-args-to".to_string(), selector.to_string()]
        })
        .arg("--")
        .arg("--verify-module=bar")
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );

    let record: Value = serde_json::from_str(
        &std::fs::read_to_string(&record_path).expect("fake cargo should write a record"),
    )
    .expect("fake cargo record should be valid JSON");
    let args: Vec<&str> = record
        .get("args")
        .and_then(Value::as_array)
        .expect("record args should be an array")
        .iter()
        .map(|arg| arg.as_str().expect("cargo arg should be a string"))
        .collect();
    let mut expected_args = vec![
        "--unverified".to_string(),
        expected_cargo_subcommand.to_string(),
    ];
    if subcommand == "focus" {
        expected_args.push("--target-dir".to_string());
        expected_args.push(
            workspace
                .join("target")
                .join("verus-partial")
                .to_string_lossy()
                .into_owned(),
        );
    }
    expected_args.extend(
        ["--package", "hasdeps", "--package", "sibling"]
            .into_iter()
            .map(str::to_string),
    );
    let actual_args: Vec<String> = args.iter().map(|arg| (*arg).to_string()).collect();
    assert_eq!(actual_args, expected_args);

    let forwarded = "--verify-module=bar";
    let hasdeps_id = package_env_id(&workspace, "hasdeps");
    let sibling_id = package_env_id(&workspace, "sibling");
    let optin_id = package_env_id(&workspace, "optin");
    let optout_id = package_env_id(&workspace, "optout");
    let unset_id = package_env_id(&workspace, "unset");
    assert!(
        !packed_args_contain(record["env"][VERUS_DRIVER_ARGS].as_str(), forwarded),
        "forwarded Verus args should not be placed in common driver args: {record:#?}"
    );
    assert_eq!(
        packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps_id}")),
            forwarded
        ),
        hasdeps_receives_args,
        "unexpected forwarding for root package hasdeps with selector {selector}: {record:#?}"
    );
    assert_eq!(
        packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{sibling_id}")),
            forwarded
        ),
        sibling_receives_args,
        "unexpected forwarding for root package sibling with selector {selector}: {record:#?}"
    );
    assert_eq!(
        packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{optin_id}")),
            forwarded
        ),
        optin_receives_args,
        "unexpected forwarding for dependency package optin with selector {selector}: {record:#?}"
    );
    assert!(
        env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{optout_id}")).is_none(),
        "optout package should not receive verifier args env: {record:#?}"
    );
    assert!(
        env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{unset_id}")).is_none(),
        "unset package should not receive verifier args env: {record:#?}"
    );

    std::fs::remove_dir_all(workspace).ok();
}

#[test]
fn fwd_verus_args_to_all_reaches_all_verify_packages_in_closure() {
    assert_forwarding_selector("verify", "all", true, true, true);
}

#[test]
fn fwd_verus_args_to_roots_only_reaches_root_package_invocations() {
    assert_forwarding_selector("verify", "roots", true, false, true);
}

#[test]
fn fwd_verus_args_to_deps_only_reaches_dependency_package_invocations() {
    assert_forwarding_selector("verify", "deps", false, true, false);
}

#[test]
fn fwd_verus_args_default_for_verify_is_all() {
    assert_forwarding_selector("verify", "default", true, true, true);
}

#[test]
fn fwd_verus_args_default_for_build_is_all() {
    assert_forwarding_selector("build", "default", true, true, true);
}

#[test]
fn fwd_verus_args_default_for_check_is_all() {
    assert_forwarding_selector("check", "default", true, true, true);
}

#[test]
fn fwd_verus_args_default_for_focus_is_roots() {
    assert_forwarding_selector("focus", "default", true, false, true);
}

#[test]
fn verify_short_equals_package_selector_preserves_dependency_closure() {
    let workspace = temp_dir("short_equals_package");
    write_workspace(&workspace);
    let workspace = workspace
        .canonicalize()
        .expect("workspace path should canonicalize");
    let fake_cargo = build_fake_cargo_recorder(&workspace);
    let record_path = workspace.join("cargo-record.json");
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "targo".to_string());

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&workspace)
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", real_cargo)
        .env("TRUST_VC_FAKE_CARGO_RECORD", &record_path)
        .arg("verify")
        .arg("-p=hasdeps")
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );

    let record = read_record(&record_path);
    assert_eq!(
        record_args(&record),
        vec!["--unverified", "check", "-p=hasdeps"]
    );

    let hasdeps_id = package_env_id(&workspace, "hasdeps");
    let optin_id = package_env_id(&workspace, "optin");
    let sibling_id = package_env_id(&workspace, "sibling");
    assert_eq!(
        env_value(&record, &format!("{VERUS_DRIVER_VERIFY}{hasdeps_id}")),
        Some("1"),
        "-p= package root should be verified: {record:#?}"
    );
    assert_eq!(
        env_value(&record, &format!("{VERUS_DRIVER_VERIFY}{optin_id}")),
        Some("1"),
        "-p= package dependency should stay in the closure: {record:#?}"
    );
    assert!(
        env_value(&record, &format!("{VERUS_DRIVER_VERIFY}{sibling_id}")).is_none(),
        "unselected sibling should not be verified for -p= package selector: {record:#?}"
    );

    std::fs::remove_dir_all(workspace).ok();
}

#[test]
fn verify_propagates_target_features_config_and_target_dir_to_cargo_layers() {
    let workspace = temp_dir("target_features_config_target_dir");
    write_workspace(&workspace);
    let workspace = workspace
        .canonicalize()
        .expect("workspace path should canonicalize");
    let fake_cargo = build_fake_cargo_recorder(&workspace);
    let fake_metadata_cargo = build_fake_metadata_recorder(&workspace);
    let record_path = workspace.join("cargo-record.json");
    let metadata_record_path = workspace.join("metadata-record.json");

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&workspace)
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", &fake_metadata_cargo)
        .env("TRUST_VC_FAKE_CARGO_RECORD", &record_path)
        .env("TRUST_VC_FAKE_METADATA_RECORD", &metadata_record_path)
        .env("TRUST_VC_FAKE_METADATA_WORKSPACE", &workspace)
        .arg("verify")
        .arg("--target")
        .arg("wasm32-unknown-unknown")
        .arg("-F")
        .arg("feature-a")
        .arg("--config")
        .arg("net.offline=true")
        .arg("--target-dir")
        .arg("custom-target")
        .arg("--package")
        .arg("hasdeps")
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );

    let record = read_record(&record_path);
    assert_eq!(
        record_args(&record),
        vec![
            "--unverified",
            "check",
            "--target",
            "wasm32-unknown-unknown",
            "-F",
            "feature-a",
            "--config",
            "net.offline=true",
            "--target-dir",
            "custom-target",
            "--package",
            "hasdeps"
        ]
    );

    let metadata_record = read_record(&metadata_record_path);
    assert_eq!(
        record_args(&metadata_record),
        vec![
            "metadata",
            "--format-version",
            "1",
            "--filter-platform",
            "wasm32-unknown-unknown",
            "-F",
            "feature-a",
            "--config",
            "net.offline=true"
        ],
        "target-dir and package selectors should stay out of cargo metadata, while target/features/config are propagated"
    );

    let hasdeps_id = package_env_id(&workspace, "hasdeps");
    let optin_id = package_env_id(&workspace, "optin");
    assert_eq!(
        env_value(&record, &format!("{VERUS_DRIVER_VERIFY}{hasdeps_id}")),
        Some("1"),
        "selected package should still be verified with propagated cargo options: {record:#?}"
    );
    assert_eq!(
        env_value(&record, &format!("{VERUS_DRIVER_VERIFY}{optin_id}")),
        Some("1"),
        "dependency closure from metadata should still be verified with propagated cargo options: {record:#?}"
    );

    std::fs::remove_dir_all(workspace).ok();
}

#[test]
fn verify_fake_cargo_record_contains_wrapper_env_contract() {
    let workspace = temp_dir("fake_cargo_env_contract");
    write_workspace(&workspace);
    let workspace = workspace
        .canonicalize()
        .expect("workspace path should canonicalize");
    let fake_cargo = build_fake_cargo_recorder(&workspace);
    let record_path = workspace.join("cargo-record.json");
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "targo".to_string());

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&workspace)
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", real_cargo)
        .env("TRUST_VC_FAKE_CARGO_RECORD", &record_path)
        .arg("verify")
        .arg("--package")
        .arg("hasdeps")
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );

    let record = read_record(&record_path);
    assert_eq!(
        record_args(&record),
        vec!["--unverified", "check", "--package", "hasdeps"]
    );
    assert!(
        env_value(&record, "RUSTC_WRAPPER").is_some(),
        "fake cargo should observe the wrapper executable env: {record:#?}"
    );
    assert_eq!(
        env_value(&record, "__CARGO_DEFAULT_LIB_METADATA"),
        Some("verus"),
        "fake cargo should observe cargo-verus-compatible lib metadata: {record:#?}"
    );
    assert_eq!(
        env_value(&record, "__VERUS_DRIVER_VIA_CARGO__"),
        Some("1"),
        "fake cargo should observe cargo-verus-compatible driver mode: {record:#?}"
    );

    std::fs::remove_dir_all(workspace).ok();
}

#[test]
fn build_adds_own_lib_import_driver_arg_for_verified_lib_package() {
    let workspace = temp_dir("build_own_lib_import");
    write_workspace(&workspace);
    let workspace = workspace
        .canonicalize()
        .expect("workspace path should canonicalize");
    let fake_cargo = build_fake_cargo_recorder(&workspace);
    let record_path = workspace.join("cargo-record.json");
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "targo".to_string());

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&workspace)
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", real_cargo)
        .env("TRUST_VC_FAKE_CARGO_RECORD", &record_path)
        .arg("build")
        .arg("--package")
        .arg("hasdeps")
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );

    let record = read_record(&record_path);
    assert_eq!(
        record_args(&record),
        vec!["--unverified", "build", "--package", "hasdeps"]
    );

    let hasdeps_id = package_env_id(&workspace, "hasdeps");
    assert!(
        packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps_id}")),
            "import-dep-if-present=hasdeps"
        ),
        "build should pass the package's own lib import hint to the verifier driver: {record:#?}"
    );
    assert!(
        packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps_id}")),
            "import-dep-if-present=optin"
        ),
        "build should pass verified direct dependency import hints to the verifier driver: {record:#?}"
    );
    assert!(
        !packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps_id}")),
            "import-dep-if-present=optout"
        ) && !packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps_id}")),
            "import-dep-if-present=unset"
        ),
        "build should not require artifacts from unverified dependencies: {record:#?}"
    );

    std::fs::remove_dir_all(workspace).ok();
}

#[test]
fn build_roots_forwarding_selector_preserves_dependency_import_hints() {
    let workspace = temp_dir("build_roots_forwarding_import_hints");
    write_workspace(&workspace);
    let workspace = workspace
        .canonicalize()
        .expect("workspace path should canonicalize");
    let fake_cargo = build_fake_cargo_recorder(&workspace);
    let record_path = workspace.join("cargo-record.json");
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "targo".to_string());

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&workspace)
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", real_cargo)
        .env("TRUST_VC_FAKE_CARGO_RECORD", &record_path)
        .arg("build")
        .arg("--package")
        .arg("hasdeps")
        .arg("--fwd-verus-args-to=roots")
        .arg("--")
        .arg("--verify-module=bar")
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );

    let record = read_record(&record_path);
    assert_eq!(
        record_args(&record),
        vec!["--unverified", "build", "--package", "hasdeps"]
    );

    let forwarded = "--verify-module=bar";
    let hasdeps_id = package_env_id(&workspace, "hasdeps");
    let optin_id = package_env_id(&workspace, "optin");
    assert!(
        packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps_id}")),
            forwarded
        ),
        "build root should receive root-only forwarded Verus args: {record:#?}"
    );
    assert!(
        !packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{optin_id}")),
            forwarded
        ),
        "verified dependency should not receive root-only forwarded Verus args: {record:#?}"
    );
    for import in [
        "import-dep-if-present=hasdeps",
        "import-dep-if-present=optin",
    ] {
        assert!(
            packed_args_contain(
                env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps_id}")),
                import
            ),
            "build root should keep semantic import hint {import}: {record:#?}"
        );
    }
    assert!(
        packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{optin_id}")),
            "import-dep-if-present=optin"
        ),
        "verified dependency should keep its own build semantic import hint despite root-only forwarded Verus args: {record:#?}"
    );

    std::fs::remove_dir_all(workspace).ok();
}

#[test]
fn focus_uses_partial_target_dir_and_disables_verification_for_selected_deps() {
    let workspace = temp_dir("focus_partial_target");
    write_workspace(&workspace);
    let workspace = workspace
        .canonicalize()
        .expect("workspace path should canonicalize");
    let fake_cargo = build_fake_cargo_recorder(&workspace);
    let record_path = workspace.join("cargo-record.json");
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "targo".to_string());

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&workspace)
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", real_cargo)
        .env("TRUST_VC_FAKE_CARGO_RECORD", &record_path)
        .arg("focus")
        .arg("--package")
        .arg("hasdeps")
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );

    let record: Value = serde_json::from_str(
        &std::fs::read_to_string(&record_path).expect("fake cargo should write a record"),
    )
    .expect("fake cargo record should be valid JSON");
    let args: Vec<&str> = record
        .get("args")
        .and_then(Value::as_array)
        .expect("record args should be an array")
        .iter()
        .map(|arg| arg.as_str().expect("cargo arg should be a string"))
        .collect();
    let target_dir = workspace.join("target").join("verus-partial");
    assert_eq!(
        args,
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

    let hasdeps_id = package_env_id(&workspace, "hasdeps");
    let optin_id = package_env_id(&workspace, "optin");
    assert!(
        !packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps_id}")),
            "--no-verify"
        ),
        "selected focus root should not receive --no-verify: {record:#?}"
    );
    assert!(
        packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{optin_id}")),
            "--no-verify"
        ),
        "verified dependency outside the selected focus root should receive --no-verify: {record:#?}"
    );

    std::fs::remove_dir_all(workspace).ok();
}

#[test]
fn focus_workspace_selection_covers_all_members_not_default_members() {
    let workspace = temp_dir("focus_workspace_selection");
    write_workspace_with_default_members(&workspace, Some(&["hasdeps"]));
    let workspace = workspace
        .canonicalize()
        .expect("workspace path should canonicalize");
    let fake_cargo = build_fake_cargo_recorder(&workspace);
    let record_path = workspace.join("cargo-record.json");
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "targo".to_string());

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&workspace)
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", real_cargo)
        .env("TRUST_VC_FAKE_CARGO_RECORD", &record_path)
        .arg("focus")
        .arg("--workspace")
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );

    let record: Value = serde_json::from_str(
        &std::fs::read_to_string(&record_path).expect("fake cargo should write a record"),
    )
    .expect("fake cargo record should be valid JSON");
    let args: Vec<&str> = record
        .get("args")
        .and_then(Value::as_array)
        .expect("record args should be an array")
        .iter()
        .map(|arg| arg.as_str().expect("cargo arg should be a string"))
        .collect();
    let target_dir = workspace.join("target").join("verus-partial");
    assert_eq!(
        args,
        vec![
            "--unverified",
            "check",
            "--workspace",
            "--target-dir",
            target_dir
                .to_str()
                .expect("target dir should be valid UTF-8")
        ]
    );

    for name in ["hasdeps", "optin", "sibling"] {
        let package_id = package_env_id(&workspace, name);
        let forwarded = env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{package_id}"));
        assert!(
            !packed_args_contain(forwarded, "--no-verify"),
            "workspace focus root {name} should not receive --no-verify: {record:#?}"
        );
    }

    std::fs::remove_dir_all(workspace).ok();
}

#[test]
fn verify_member_manifest_selects_that_package_and_dependency_closure() {
    let workspace = temp_dir("verify_member_manifest");
    write_workspace(&workspace);
    let workspace = workspace
        .canonicalize()
        .expect("workspace path should canonicalize");
    let fake_cargo = build_fake_cargo_recorder(&workspace);
    let record_path = workspace.join("cargo-record.json");
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "targo".to_string());

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&workspace)
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", real_cargo)
        .env("TRUST_VC_FAKE_CARGO_RECORD", &record_path)
        .arg("verify")
        .arg("--manifest-path")
        .arg("hasdeps/Cargo.toml")
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );

    let record = read_record(&record_path);
    assert_eq!(
        record_args(&record),
        vec![
            "--unverified",
            "check",
            "--manifest-path",
            "hasdeps/Cargo.toml"
        ]
    );

    let hasdeps_id = package_env_id(&workspace, "hasdeps");
    let optin_id = package_env_id(&workspace, "optin");
    let sibling_id = package_env_id(&workspace, "sibling");
    assert_eq!(
        env_value(&record, &format!("{VERUS_DRIVER_VERIFY}{hasdeps_id}")),
        Some("1"),
        "manifest-selected package should be verified: {record:#?}"
    );
    assert_eq!(
        env_value(&record, &format!("{VERUS_DRIVER_VERIFY}{optin_id}")),
        Some("1"),
        "manifest-selected package dependency should stay in the closure: {record:#?}"
    );
    assert!(
        env_value(&record, &format!("{VERUS_DRIVER_VERIFY}{sibling_id}")).is_none(),
        "sibling package should not be selected by a member manifest path: {record:#?}"
    );

    std::fs::remove_dir_all(workspace).ok();
}

#[test]
fn focus_member_manifest_uses_partial_target_and_disables_verified_deps() {
    let workspace = temp_dir("focus_member_manifest");
    write_workspace(&workspace);
    let workspace = workspace
        .canonicalize()
        .expect("workspace path should canonicalize");
    let fake_cargo = build_fake_cargo_recorder(&workspace);
    let record_path = workspace.join("cargo-record.json");
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "targo".to_string());
    let manifest_path = workspace.join("hasdeps").join("Cargo.toml");

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&workspace)
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", real_cargo)
        .env("TRUST_VC_FAKE_CARGO_RECORD", &record_path)
        .arg("focus")
        .arg("--manifest-path")
        .arg(&manifest_path)
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );

    let record = read_record(&record_path);
    let target_dir = workspace.join("target").join("verus-partial");
    assert_eq!(
        record_args(&record),
        vec![
            "--unverified",
            "check",
            "--manifest-path",
            manifest_path
                .to_str()
                .expect("manifest path should be valid UTF-8"),
            "--target-dir",
            target_dir
                .to_str()
                .expect("target dir should be valid UTF-8")
        ]
    );

    let hasdeps_id = package_env_id(&workspace, "hasdeps");
    let optin_id = package_env_id(&workspace, "optin");
    let sibling_id = package_env_id(&workspace, "sibling");
    assert_eq!(
        env_value(&record, &format!("{VERUS_DRIVER_VERIFY}{hasdeps_id}")),
        Some("1"),
        "manifest-selected focus root should be verified: {record:#?}"
    );
    assert!(
        !packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps_id}")),
            "--no-verify"
        ),
        "manifest-selected focus root should not receive --no-verify: {record:#?}"
    );
    assert!(
        packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{optin_id}")),
            "--no-verify"
        ),
        "verified dependency outside the manifest focus root should receive --no-verify: {record:#?}"
    );
    assert!(
        env_value(&record, &format!("{VERUS_DRIVER_VERIFY}{sibling_id}")).is_none(),
        "sibling package should not be selected by a focus member manifest path: {record:#?}"
    );

    std::fs::remove_dir_all(workspace).ok();
}

#[test]
fn workspace_exclude_removes_root_but_preserves_dependency_closure() {
    let workspace = temp_dir("workspace_exclude_closure");
    write_workspace(&workspace);
    let workspace = workspace
        .canonicalize()
        .expect("workspace path should canonicalize");
    let fake_cargo = build_fake_cargo_recorder(&workspace);
    let record_path = workspace.join("cargo-record.json");
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "targo".to_string());

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&workspace)
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", real_cargo)
        .env("TRUST_VC_FAKE_CARGO_RECORD", &record_path)
        .arg("verify")
        .arg("--workspace")
        .arg("--exclude")
        .arg("optin")
        .arg("--fwd-verus-args-to")
        .arg("roots")
        .arg("--")
        .arg("--verify-module=bar")
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "cargo-trust-vc should exit successfully\nstdout={stdout}\nstderr={stderr}"
    );

    let record = read_record(&record_path);
    assert_eq!(
        record_args(&record),
        vec!["--unverified", "check", "--workspace", "--exclude", "optin"]
    );

    let forwarded = "--verify-module=bar";
    let hasdeps_id = package_env_id(&workspace, "hasdeps");
    let optin_id = package_env_id(&workspace, "optin");
    let sibling_id = package_env_id(&workspace, "sibling");
    assert_eq!(
        env_value(&record, &format!("{VERUS_DRIVER_VERIFY}{optin_id}")),
        Some("1"),
        "excluded package should still be verified when reached as a dependency: {record:#?}"
    );
    assert!(
        packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps_id}")),
            forwarded
        ),
        "workspace root hasdeps should receive root-only forwarded args: {record:#?}"
    );
    assert!(
        packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{sibling_id}")),
            forwarded
        ),
        "workspace root sibling should receive root-only forwarded args: {record:#?}"
    );
    assert!(
        !packed_args_contain(
            env_value(&record, &format!("{VERUS_DRIVER_ARGS_FOR}{optin_id}")),
            forwarded
        ),
        "excluded package dependency should not receive root-only forwarded args: {record:#?}"
    );

    std::fs::remove_dir_all(workspace).ok();
}

/// Upstream cargo answers targo's lane flag with a usage error. Forwarding must
/// refuse before it spawns the build, name targo, and never fall back to a stock
/// build of its own.
#[cfg(unix)]
#[test]
fn verify_refuses_a_cargo_that_is_not_targo_before_forwarding() {
    use std::os::unix::fs::PermissionsExt;

    let workspace = temp_dir("not_targo");
    write_workspace(&workspace);
    let workspace = workspace
        .canonicalize()
        .expect("workspace path should canonicalize");
    let stock_cargo = workspace.join("cargo");
    std::fs::write(
        &stock_cargo,
        "#!/bin/sh\nif [ \"$1\" = --unverified ]; then echo \"error: unexpected argument '--unverified' found\" >&2; exit 1; fi\ntouch \"$(dirname \"$0\")/ran-a-build\"\n",
    )
    .expect("stock cargo stand-in should be writable");
    std::fs::set_permissions(&stock_cargo, std::fs::Permissions::from_mode(0o755))
        .expect("stock cargo stand-in should be executable");
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "targo".to_string());

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&workspace)
        .env("CARGO", &stock_cargo)
        .env("TRUST_VC_METADATA_CARGO", real_cargo)
        .arg("verify")
        .arg("--package")
        .arg("optin")
        .output()
        .expect("cargo-trust-vc should execute");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr={stderr}");
    assert!(
        stderr.contains("run it as `targo trust-vc verify`"),
        "the refusal must name targo: {stderr}"
    );
    assert!(
        stderr.contains("unexpected argument '--unverified'"),
        "the refusal must carry the discriminator's answer: {stderr}"
    );
    assert!(
        !workspace.join("ran-a-build").exists(),
        "a cargo that is not targo must not run the forwarded build"
    );

    std::fs::remove_dir_all(workspace).ok();
}

/// The one forwarding test that runs the real toolchain: `$CARGO` (targo, as
/// targo exports it to this test) takes `--unverified check`, runs this binary
/// as the RUSTC_WRAPPER, and trust-vc reports on the crate. Every other
/// forwarding test records the spawn with a fake cargo instead.
#[test]
fn verify_runs_the_real_targo_unverified_lane_through_the_trust_vc_wrapper() {
    let targo = std::env::var("CARGO").unwrap_or_else(|_| "targo".to_string());
    let probe = Command::new(&targo)
        .args(["--unverified", "--version"])
        .output()
        .expect("$CARGO (or targo) should launch");
    assert!(
        probe.status.success(),
        "`{targo} --unverified --version` failed: this test needs the Trust toolchain's \
         targo (run it under `targo --unverified test`)\nstderr={}",
        String::from_utf8_lossy(&probe.stderr)
    );

    let root = temp_dir("real_targo");
    std::fs::create_dir_all(root.join("src")).expect("crate src dir should exist");
    let root = root.canonicalize().expect("crate path should canonicalize");
    std::fs::write(
        root.join("Cargo.toml"),
        "[package]\nname = \"e2e_optin\"\nversion = \"0.1.0\"\nedition = \"2021\"\npublish = false\n\n[package.metadata.verus]\nverify = true\n\n[workspace]\n",
    )
    .expect("crate manifest should be writable");
    std::fs::write(
        root.join("src/lib.rs"),
        "pub fn add_one(x: u32) -> u32 {\n    if x < u32::MAX { x + 1 } else { x }\n}\n",
    )
    .expect("crate source should be writable");

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&root)
        .env("CARGO", &targo)
        .env_remove("TRUST_VC_METADATA_CARGO")
        // A private target dir: the outer test run holds the lock on its own.
        .env("CARGO_TARGET_DIR", root.join("target"))
        .arg("verify")
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "real targo forwarding should succeed\nstdout={stdout}\nstderr={stderr}"
    );
    let combined = format!("{stdout}{stderr}");
    assert!(
        combined.contains("UNVERIFIED: `targo check`"),
        "targo itself must have run the forwarded check in the unverified lane: {combined}"
    );
    assert!(
        combined.contains("trust_vc check: 1 function found") && combined.contains("add_one"),
        "the trust-vc wrapper must have analyzed the crate: {combined}"
    );

    std::fs::remove_dir_all(root).ok();
}
