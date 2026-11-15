// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn temp_dir(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    let sequence = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "cargo_trust_vc_late_args_{label}_{}_{}_{}",
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

    panic!(
        "cargo-trust-vc binary not found; run `targo --unverified build -p targo-trust-vc` first"
    );
}

fn write_package(root: &std::path::Path, name: &str) {
    write_package_with_extra_manifest(root, name, "");
}

fn write_package_with_extra_manifest(root: &std::path::Path, name: &str, extra_manifest: &str) {
    std::fs::create_dir_all(root.join("src")).expect("package src dir should be creatable");
    std::fs::write(
        root.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\npublish = false\n\n{extra_manifest}[package.metadata.verus]\nverify = true\n"
        ),
    )
    .expect("package manifest should be writable");
    std::fs::write(root.join("src/lib.rs"), "").expect("package lib should be writable");
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

fn build_fake_cargo_recorder(root: &std::path::Path) -> PathBuf {
    let source = root.join("fake_cargo.rs");
    let binary = root.join(format!("fake-cargo{}", std::env::consts::EXE_SUFFIX));
    std::fs::write(
        &source,
        r#"
use std::{env, fs};

fn main() {
    let record_path = env::var("TRUST_VC_LATE_ARGS_FAKE_CARGO_RECORD").expect("record path");
    let args: Vec<String> = env::args().skip(1).collect();
    fs::write(record_path, args.join("\n")).expect("write record");
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

fn build_fake_metadata_cargo(root: &std::path::Path) -> PathBuf {
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

fn package(root: &Path) -> String {
    let manifest_path = root.join("Cargo.toml");
    format!(
        "{{\"id\":\"foo 0.1.0\",\"name\":\"foo\",\"version\":\"0.1.0\",\"manifest_path\":{},\"metadata\":{{\"verus\":{{\"verify\":true}}}},\"targets\":[{{\"kind\":[\"lib\"]}}]}}",
        json_string(&manifest_path.to_string_lossy()),
    )
}

fn main() {
    if let Ok(record_path) = env::var("TRUST_VC_LATE_ARGS_FAKE_METADATA_RECORD") {
        let args: Vec<String> = env::args().skip(1).collect();
        fs::write(record_path, args.join("\n")).expect("write metadata record");
    }

    let root = env::current_dir().expect("current dir");
    println!(
        "{{\"packages\":[{}],\"resolve\":{{\"nodes\":[{{\"id\":\"foo 0.1.0\",\"dependencies\":[]}}]}},\"workspace_members\":[\"foo 0.1.0\"],\"workspace_default_members\":[\"foo 0.1.0\"],\"workspace_root\":{}}}",
        package(&root),
        json_string(&root.to_string_lossy()),
    );
}
"#,
    )
    .expect("fake metadata cargo source should be writable");

    let output = Command::new(rustc_command())
        .arg("-Ztrust-verify=off")
        .arg(&source)
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("rustc should execute");
    assert!(
        output.status.success(),
        "fake metadata cargo should compile\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    binary
}

fn read_recorded_args(record_path: &std::path::Path) -> Vec<String> {
    let record = std::fs::read_to_string(record_path).expect("fake cargo should write a record");
    if record.is_empty() {
        Vec::new()
    } else {
        record.lines().map(str::to_string).collect()
    }
}

fn assert_late_args_cli_error(subcommand: &str, late_args: &[&str], expected_message: &str) {
    let crate_root = temp_dir(&format!("{subcommand}_late_arg"));
    write_package(&crate_root, "foo");

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&crate_root)
        .arg(subcommand)
        .arg("--release")
        .args(late_args)
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert_eq!(
        output.status.code(),
        Some(2),
        "stdout={stdout}\nstderr={stderr}"
    );
    assert!(
        stderr.contains(expected_message),
        "stdout={stdout}\nstderr={stderr}"
    );

    std::fs::remove_dir_all(crate_root).ok();
}

fn assert_late_arg_cli_error(subcommand: &str, late_arg: &str) {
    assert_late_args_cli_error(
        subcommand,
        &[late_arg],
        "must appear before cargo-only passthrough arguments",
    );
}

fn assert_joined_z_cli_error(subcommand: &str) {
    let crate_root = temp_dir(&format!("{subcommand}_joined_z"));
    write_package(&crate_root, "foo");

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&crate_root)
        .arg(subcommand)
        .arg("-Zunstable-options")
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert_eq!(
        output.status.code(),
        Some(2),
        "stdout={stdout}\nstderr={stderr}"
    );
    assert!(
        stderr.contains("requires `-Z <flag>` with a space"),
        "stdout={stdout}\nstderr={stderr}"
    );

    std::fs::remove_dir_all(crate_root).ok();
}

fn assert_accepted_cargo_args(
    label: &str,
    manifest_extra: &str,
    cli_args: &[&str],
    expected_cargo_args: &[&str],
) {
    let crate_root = temp_dir(label);
    write_package_with_extra_manifest(&crate_root, "foo", manifest_extra);
    let fake_cargo = build_fake_cargo_recorder(&crate_root);
    let fake_metadata_cargo = build_fake_metadata_cargo(&crate_root);
    let record_path = crate_root.join("cargo-record.txt");

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&crate_root)
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", &fake_metadata_cargo)
        .env("TRUST_VC_LATE_ARGS_FAKE_CARGO_RECORD", &record_path)
        .arg("verify")
        .args(cli_args)
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert!(output.status.success(), "stdout={stdout}\nstderr={stderr}");
    assert_eq!(read_recorded_args(&record_path), expected_cargo_args);

    std::fs::remove_dir_all(crate_root).ok();
}

fn assert_accepted_cargo_and_metadata_args(
    label: &str,
    manifest_extra: &str,
    cli_args: &[&str],
    expected_cargo_args: &[&str],
    expected_metadata_args: &[&str],
) {
    let crate_root = temp_dir(label);
    write_package_with_extra_manifest(&crate_root, "foo", manifest_extra);
    let fake_cargo = build_fake_cargo_recorder(&crate_root);
    let fake_metadata_cargo = build_fake_metadata_cargo(&crate_root);
    let cargo_record_path = crate_root.join("cargo-record.txt");
    let metadata_record_path = crate_root.join("metadata-record.txt");

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&crate_root)
        .env("CARGO", &fake_cargo)
        .env("TRUST_VC_METADATA_CARGO", &fake_metadata_cargo)
        .env("TRUST_VC_LATE_ARGS_FAKE_CARGO_RECORD", &cargo_record_path)
        .env(
            "TRUST_VC_LATE_ARGS_FAKE_METADATA_RECORD",
            &metadata_record_path,
        )
        .arg("verify")
        .args(cli_args)
        .output()
        .expect("cargo-trust-vc should execute");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert!(output.status.success(), "stdout={stdout}\nstderr={stderr}");
    assert_eq!(read_recorded_args(&cargo_record_path), expected_cargo_args);
    assert_eq!(
        read_recorded_args(&metadata_record_path),
        expected_metadata_args
    );

    std::fs::remove_dir_all(crate_root).ok();
}

#[test]
fn joined_z_unstable_options_exits_with_cli_error() {
    let crate_root = temp_dir("joined");
    std::fs::create_dir_all(&crate_root).expect("temp dir should be creatable");

    let output = Command::new(cargo_trust_vc_bin())
        .arg("check")
        .arg(&crate_root)
        .arg("-Zunstable-options")
        .output()
        .expect("cargo-trust-vc check should execute");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert_eq!(
        output.status.code(),
        Some(2),
        "stdout={stdout}\nstderr={stderr}"
    );
    std::fs::remove_dir_all(crate_root).ok();
}

#[test]
fn late_package_arg_after_release() {
    assert_late_arg_cli_error("verify", "--package=foo");
}

#[test]
fn late_features_arg_after_release() {
    assert_late_arg_cli_error("verify", "--features=some-feature");
}

#[test]
fn late_all_features_arg_after_release() {
    assert_late_arg_cli_error("verify", "--all-features");
}

#[test]
fn late_no_default_features_arg_after_release() {
    assert_late_arg_cli_error("verify", "--no-default-features");
}

#[test]
fn late_workspace_arg_after_release() {
    assert_late_arg_cli_error("verify", "--workspace");
}

#[test]
fn late_frozen_arg_after_release() {
    assert_late_arg_cli_error("verify", "--frozen");
}

#[test]
fn late_locked_arg_after_release() {
    assert_late_arg_cli_error("verify", "--locked");
}

#[test]
fn late_offline_arg_after_release() {
    assert_late_arg_cli_error("verify", "--offline");
}

#[test]
fn late_target_dir_arg_after_release() {
    assert_late_arg_cli_error("verify", "--target-dir=/tmp/foo");
}

#[test]
fn late_config_arg_after_release() {
    assert_late_arg_cli_error("verify", "--config=build.jobs=1");
}

#[test]
fn late_z_flag_arg_after_release() {
    assert_late_args_cli_error(
        "verify",
        &["-Z", "unstable-options"],
        "must appear before cargo-only passthrough arguments",
    );
}

#[test]
fn z_flag_without_space_is_rejected() {
    assert_joined_z_cli_error("verify");
}

#[test]
fn z_flag_with_space_is_accepted() {
    assert_accepted_cargo_args(
        "z_flag_with_space",
        "",
        &["-Z", "unstable-options"],
        &["--unverified", "check", "-Z", "unstable-options"],
    );
}

#[test]
fn package_before_release_is_ok() {
    assert_accepted_cargo_args(
        "package_before_release",
        "",
        &["--package=foo", "--release"],
        &["--unverified", "check", "--package", "foo", "--release"],
    );
}

#[test]
fn features_before_release_is_ok() {
    assert_accepted_cargo_args(
        "features_before_release",
        "[features]\ndefault = []\n\n",
        &["--features=default", "--release"],
        &[
            "--unverified",
            "check",
            "--features",
            "default",
            "--release",
        ],
    );
}

#[test]
fn locked_offline_before_release_are_forwarded_to_metadata_and_cargo() {
    assert_accepted_cargo_and_metadata_args(
        "locked_offline_before_release",
        "",
        &["--locked", "--offline", "--release"],
        &[
            "--unverified",
            "check",
            "--locked",
            "--offline",
            "--release",
        ],
        &["metadata", "--format-version", "1", "--locked", "--offline"],
    );
}

#[test]
fn focus_late_package_arg_after_release() {
    assert_late_arg_cli_error("focus", "--package=foo");
}

#[test]
fn focus_z_flag_without_space_is_rejected() {
    assert_joined_z_cli_error("focus");
}

#[test]
fn build_late_package_arg_after_release() {
    assert_late_arg_cli_error("build", "--package=foo");
}

#[test]
fn build_z_flag_without_space_is_rejected() {
    assert_joined_z_cli_error("build");
}

#[test]
fn check_late_package_arg_after_release() {
    assert_late_arg_cli_error("check", "--package=foo");
}

#[test]
fn check_z_flag_without_space_is_rejected() {
    assert_joined_z_cli_error("check");
}

#[test]
fn split_z_unstable_options_reaches_check_handling() {
    let crate_root = temp_dir("split");
    std::fs::create_dir_all(&crate_root).expect("temp dir should be creatable");

    let output = Command::new(cargo_trust_vc_bin())
        .arg("check")
        .arg(&crate_root)
        .arg("-Z")
        .arg("unstable-options")
        .output()
        .expect("cargo-trust-vc check should execute");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert_eq!(
        output.status.code(),
        Some(0),
        "stdout={stdout}\nstderr={stderr}"
    );
    assert!(
        stdout.contains("trust_vc check: 0 functions found"),
        "stdout={stdout}\nstderr={stderr}"
    );

    std::fs::remove_dir_all(crate_root).ok();
}
