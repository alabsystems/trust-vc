// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integration coverage for the local `gate`, `fuzz`, `new`, and top-level
//! help commands exposed by `cargo-trust-vc`.

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
        "cargo_trust_vc_gate_{label}_{}_{}_{}",
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

fn run(args: &[&str]) -> (String, String, i32) {
    let output = Command::new(cargo_trust_vc_bin())
        .args(args)
        .output()
        .expect("cargo-trust-vc should execute");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let code = output.status.code().unwrap_or(-1);
    (stdout, stderr, code)
}

fn run_in(dir: &PathBuf, args: &[&str]) -> (String, String, i32) {
    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(dir)
        .args(args)
        .output()
        .expect("cargo-trust-vc should execute");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let code = output.status.code().unwrap_or(-1);
    (stdout, stderr, code)
}

#[test]
fn top_level_help_lists_every_subcommand() {
    let (stdout, _stderr, code) = run(&["trust-vc", "--help"]);
    assert_eq!(code, 0);
    for subcommand in [
        "check",
        "gate",
        "fuzz",
        "evidence",
        "suggest",
        "new",
        "verus-compat",
    ] {
        assert!(
            stdout.contains(subcommand),
            "top-level help should list `{subcommand}`: {stdout}"
        );
    }
}

#[test]
fn bare_invocation_prints_help_index() {
    let (stdout, _stderr, code) = run(&[]);
    assert_eq!(code, 0);
    assert!(stdout.contains("Subcommands:"), "{stdout}");
    assert!(stdout.contains("gate"), "{stdout}");
}

#[test]
fn check_help_is_not_swallowed_by_top_level_help() {
    // `check --help` must show the check-specific help, not the index.
    let (stdout, _stderr, _code) = run(&["trust-vc", "check", "--help"]);
    assert!(
        stdout.contains("[PATH]") || stdout.contains("--function"),
        "check --help should show check options: {stdout}"
    );
    assert!(
        !stdout.contains("Subcommands:"),
        "check --help should not show the top-level index: {stdout}"
    );
}

#[test]
fn gate_help_lists_stages_and_flags() {
    let (stdout, _stderr, code) = run(&["trust-vc", "gate", "--help"]);
    assert_eq!(code, 0);
    for needle in [
        "targo fmt --all --check",
        "targo tippy --locked --workspace --all-targets -- -D warnings",
        "targo --unverified test --locked --workspace",
        "test",
        "examples",
        "evidence",
        "--locked",
        "--quick",
        "--no-fuzz",
    ] {
        assert!(
            stdout.contains(needle),
            "gate help should mention `{needle}`: {stdout}"
        );
    }
}

#[test]
fn gate_rejects_unknown_flag() {
    let (_stdout, stderr, code) = run(&["trust-vc", "gate", "--bogus"]);
    assert_eq!(code, 2, "unknown gate flag should be a CLI error: {stderr}");
    assert!(stderr.contains("--bogus"), "{stderr}");
}

#[test]
fn gate_rejects_verus_path_with_checkout_evidence_guidance() {
    let (_stdout, stderr, code) = run(&["trust-vc", "gate", "--verus-path", "/tmp/verus"]);
    assert_eq!(code, 2, "checkout evidence is a separate command: {stderr}");
    assert!(stderr.contains("offline local-integrity gate"), "{stderr}");
    assert!(stderr.contains("--port-manifest-only"), "{stderr}");
}

#[cfg(unix)]
#[test]
fn gate_json_captures_every_child_stream_in_one_report() {
    use std::os::unix::fs::PermissionsExt;

    let temp = temp_dir("json_clean");
    std::fs::create_dir_all(&temp).expect("temp directory should be creatable");
    let fake_cargo = temp.join("cargo");
    std::fs::write(
        &fake_cargo,
        "#!/bin/sh\nprintf 'fake cargo stdout\\n'\nprintf 'fake cargo stderr\\n' >&2\nexit 0\n",
    )
    .expect("fake cargo should be writable");
    let mut permissions = std::fs::metadata(&fake_cargo)
        .expect("fake cargo metadata should be readable")
        .permissions();
    permissions.set_mode(0o755);
    std::fs::set_permissions(&fake_cargo, permissions).expect("fake cargo should be executable");

    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&temp)
        .env("CARGO", &fake_cargo)
        .args(["trust-vc", "gate", "--quick", "--no-fuzz", "--json"])
        .output()
        .expect("JSON gate should execute");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "the deliberately incomplete synthetic checkout should fail in-band: stdout={stdout} stderr={stderr}"
    );
    let report: serde_json::Value =
        serde_json::from_str(&stdout).expect("stdout must contain exactly one JSON value");
    assert_eq!(report["overall"], "fail", "{stdout}");
    let stages = report["stages"]
        .as_array()
        .expect("gate report should contain a stage array");
    for stage_name in ["fmt", "clippy", "examples"] {
        let stage = stages
            .iter()
            .find(|stage| stage["name"] == stage_name)
            .unwrap_or_else(|| panic!("missing `{stage_name}` stage: {stdout}"));
        assert_eq!(stage["status"], "pass", "{stage:?}");
    }
    let evidence = stages
        .iter()
        .find(|stage| stage["name"] == "evidence")
        .expect("synthetic checkout should report its evidence failure");
    assert_eq!(evidence["status"], "fail", "{evidence:?}");
    // fmt and tippy run through `$CARGO` (targo), never a repository script.
    let fake_cargo_display = fake_cargo.to_string_lossy().into_owned();
    for (stage_name, expected) in [
        ("fmt", format!("{fake_cargo_display} fmt --all --check")),
        (
            "clippy",
            format!("{fake_cargo_display} tippy --locked --workspace --all-targets -- -D warnings"),
        ),
        (
            "examples",
            format!("{fake_cargo_display} --unverified build --locked --examples --workspace"),
        ),
    ] {
        assert_eq!(
            stages
                .iter()
                .find(|stage| stage["name"] == stage_name)
                .and_then(|stage| stage["command"].as_str()),
            Some(expected.as_str()),
            "{stdout}"
        );
    }
    for leaked in ["fake cargo stdout", "fake cargo stderr"] {
        assert!(
            !stdout.contains(leaked),
            "stdout leaked `{leaked}`: {stdout}"
        );
        assert!(
            !stderr.contains(leaked),
            "stderr leaked `{leaked}`: {stderr}"
        );
    }

    std::fs::remove_dir_all(&temp).ok();
}

#[test]
fn fuzz_help_lists_targets() {
    let (stdout, _stderr, code) = run(&["trust-vc", "fuzz", "--help"]);
    assert_eq!(code, 0);
    for target in [
        "ensures_false",
        "strict_inequality",
        "mode_crossing",
        "collections_contradiction",
    ] {
        assert!(
            stdout.contains(target),
            "fuzz help should list `{target}`: {stdout}"
        );
    }
}

#[test]
fn fuzz_rejects_unknown_target() {
    let (_stdout, stderr, code) = run(&["trust-vc", "fuzz", "definitely_not_a_target"]);
    assert_eq!(code, 2);
    assert!(stderr.contains("definitely_not_a_target"), "{stderr}");
    assert!(stderr.contains("available targets"), "{stderr}");
}

#[test]
fn fuzz_without_cargo_fuzz_prints_install_instructions() {
    // Force cargo-fuzz to be unavailable by pointing CARGO at a missing binary.
    let output = Command::new(cargo_trust_vc_bin())
        .env("CARGO", "definitely-not-a-real-cargo-binary")
        .args(["trust-vc", "fuzz"])
        .output()
        .expect("cargo-trust-vc should execute");
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert_eq!(
        output.status.code().unwrap_or(-1),
        2,
        "missing cargo-fuzz must exit 2 (not pretend to run): {stderr}"
    );
    assert!(
        stderr.contains("targo trust-vc fuzz ensures_false --time 30"),
        "should name the Trust lane first: {stderr}"
    );
    assert!(
        stderr.contains("RUSTUP_AUTO_INSTALL=0 rustup run <nightly> cargo install cargo-fuzz"),
        "should print the exact install instruction, with rustup's auto-install off: {stderr}"
    );
}

/// A stand-in for the Trust toolchain's targo: it passes the discriminator
/// (`targo --unverified --version` exits 0), which upstream cargo fails.
#[cfg(unix)]
fn write_executable(path: &std::path::Path, body: &str) {
    use std::os::unix::fs::PermissionsExt;

    std::fs::write(path, body).expect("synthetic executable should be written");
    let mut permissions = std::fs::metadata(path)
        .expect("synthetic executable metadata should be readable")
        .permissions();
    permissions.set_mode(0o755);
    std::fs::set_permissions(path, permissions).expect("synthetic executable should be executable");
}

#[cfg(unix)]
#[test]
fn fuzz_under_targo_never_sends_the_user_to_cargo_fuzz() {
    // Under targo the runner is fuzz/run.sh (cargo-fuzz spawns a bare `cargo`
    // from PATH and leaves the Targo lanes). Outside a checkout it is missing:
    // exit 2 with the Trust repair, never a cargo-fuzz install line.
    let dir = temp_dir("fuzz_targo_missing");
    std::fs::create_dir_all(&dir).expect("temp dir should be creatable");
    let fake_targo = dir.join("targo");
    write_executable(&fake_targo, "#!/bin/sh\nexit 0\n");
    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&dir)
        .env("CARGO", &fake_targo)
        .args(["trust-vc", "fuzz", "mode_crossing", "--time", "4"])
        .output()
        .expect("cargo-trust-vc should execute");
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert_eq!(output.status.code().unwrap_or(-1), 2, "{stderr}");
    assert!(stderr.contains("fuzz/run.sh not found"), "{stderr}");
    assert!(
        stderr.contains("fuzz/run.sh mode_crossing -max_total_time=4"),
        "{stderr}"
    );
    assert!(!stderr.contains("cargo install"), "{stderr}");
    assert!(!stderr.contains("cargo fuzz"), "{stderr}");
    std::fs::remove_dir_all(&dir).ok();
}

#[cfg(unix)]
#[test]
fn fuzz_under_targo_runs_fuzz_run_sh_with_the_same_targo() {
    let dir = temp_dir("fuzz_targo_runs");
    std::fs::create_dir_all(dir.join("fuzz")).expect("temp checkout should be creatable");
    let fake_targo = dir.join("targo");
    write_executable(&fake_targo, "#!/bin/sh\nexit 0\n");
    // The runner is invoked as `bash fuzz/run.sh <target> <budget>` with
    // TARGO naming the frontend that passed the discriminator.
    std::fs::write(
        dir.join("fuzz/run.sh"),
        "printf '%s|%s\\n' \"$TARGO\" \"$*\" >> \"$(dirname \"$0\")/invocations.txt\"\n",
    )
    .expect("synthetic fuzz/run.sh should be written");
    let output = Command::new(cargo_trust_vc_bin())
        .current_dir(&dir)
        .env("CARGO", &fake_targo)
        .args(["trust-vc", "fuzz", "strict_inequality", "--time", "5"])
        .output()
        .expect("cargo-trust-vc should execute");
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert_eq!(output.status.code().unwrap_or(-1), 0, "{stderr}");
    let recorded = std::fs::read_to_string(dir.join("fuzz/invocations.txt"))
        .expect("fuzz/run.sh should have run");
    assert_eq!(
        recorded,
        format!(
            "{}|strict_inequality -max_total_time=5\n",
            fake_targo.display()
        )
    );
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn new_lib_scaffolds_verifiable_crate() {
    let parent = temp_dir("new_lib");
    std::fs::create_dir_all(&parent).expect("temp parent should be creatable");

    let (_stdout, stderr, code) = run_in(&parent, &["trust-vc", "new", "--lib", "demolib"]);
    assert_eq!(code, 0, "new --lib should succeed: {stderr}");

    let project = parent.join("demolib");
    let manifest = std::fs::read_to_string(project.join("Cargo.toml"))
        .expect("scaffold should write a Cargo.toml");
    assert!(
        manifest.contains("trust-vc") || manifest.contains("trust_vc"),
        "scaffolded manifest should depend on trust_vc: {manifest}"
    );

    let lib = std::fs::read_to_string(project.join("src/lib.rs"))
        .expect("scaffold should write src/lib.rs");
    assert!(
        lib.contains("trust_vc::contract") || lib.contains("requires"),
        "scaffolded lib should carry a verification contract: {lib}"
    );

    // `check` must now find and verify the scaffolded function (no dead end).
    let (stdout, stderr, code) = run_in(&parent, &["trust-vc", "check", "demolib"]);
    assert_eq!(
        code, 0,
        "check on scaffold should pass: stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.lines().any(|line| {
            line.contains("checked_add_one")
                && (line.contains("Verified") || line.contains("verified"))
        }),
        "the named scaffolded function should verify: {stdout}"
    );

    std::fs::remove_dir_all(&parent).ok();
}

#[test]
fn new_bin_scaffolds_verifiable_crate() {
    let parent = temp_dir("new_bin");
    std::fs::create_dir_all(&parent).expect("temp parent should be creatable");

    let (_stdout, stderr, code) = run_in(&parent, &["trust-vc", "new", "--bin", "demobin"]);
    assert_eq!(code, 0, "new --bin should succeed: {stderr}");

    let project = parent.join("demobin");
    let main = std::fs::read_to_string(project.join("src/main.rs"))
        .expect("scaffold should write src/main.rs");
    assert!(
        main.contains("trust_vc::contract"),
        "scaffolded main should carry a verification contract: {main}"
    );

    let (stdout, stderr, code) = run_in(&parent, &["trust-vc", "check", "demobin"]);
    assert_eq!(
        code, 0,
        "check on scaffold should pass: stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.lines().any(|line| {
            line.contains("increment") && (line.contains("Verified") || line.contains("verified"))
        }),
        "the named scaffolded function should verify: {stdout}"
    );

    std::fs::remove_dir_all(&parent).ok();
}
