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

    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let output = Command::new(rustc)
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

    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let output = Command::new(rustc)
        .arg("-Zno-trust-verify")
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
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());

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
    let mut expected_args = vec![expected_cargo_subcommand.to_string()];
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
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());

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
    assert_eq!(record_args(&record), vec!["check", "-p=hasdeps"]);

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
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());

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
    assert_eq!(record_args(&record), vec!["check", "--package", "hasdeps"]);
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
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());

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
    assert_eq!(record_args(&record), vec!["build", "--package", "hasdeps"]);

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
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());

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
    assert_eq!(record_args(&record), vec!["build", "--package", "hasdeps"]);

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
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());

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
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());

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
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());

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
        vec!["check", "--manifest-path", "hasdeps/Cargo.toml"]
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
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
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
    let real_cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());

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
        vec!["check", "--workspace", "--exclude", "optin"]
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
