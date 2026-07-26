// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Downstream build audit for `#[trust_vc::contract]` surface claims.
//!
//! The `trust_vc` crate's in-package `harness = false` fixtures compile under test
//! configuration, which can mask the normal-build surface seen by external
//! consumers. This test exercises the proc-macro crate through a real path
//! dependency so claim verification runs against downstream semantics.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

struct DownstreamFixture {
    cleanup_root: PathBuf,
    manifest_dir: PathBuf,
    target_dir: PathBuf,
}

impl DownstreamFixture {
    fn new(name: &str) -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time should be after unix epoch")
            .as_nanos();
        let cleanup_root = env::temp_dir().join(format!(
            "trust_vc_contract_downstream_surface_{name}_{nonce}"
        ));
        let manifest_dir = cleanup_root.join("consumer");
        let src_bin_dir = manifest_dir.join("src").join("bin");
        let target_dir = cleanup_root.join("target");
        fs::create_dir_all(&src_bin_dir).expect("should create downstream fixture source tree");

        let trust_vc_dir = trust_vc_manifest_dir();
        let manifest = format!(
            "[package]\n\
             name = \"contract-downstream-surface\"\n\
             version = \"0.1.0\"\n\
             edition = \"2021\"\n\
             \n\
             [dependencies]\n\
             trust_vc = {{ package = \"trust-vc\", path = \"{}\" }}\n",
            trust_vc_dir.display()
        );
        fs::write(manifest_dir.join("Cargo.toml"), manifest)
            .expect("should write downstream fixture manifest");

        Self {
            cleanup_root,
            manifest_dir,
            target_dir,
        }
    }

    fn write_bin(&self, name: &str, source: &str) {
        let path = self
            .manifest_dir
            .join("src")
            .join("bin")
            .join(format!("{name}.rs"));
        fs::write(path, source).expect("should write downstream fixture binary");
    }

    fn build_bin(&self, name: &str) -> Output {
        Command::new("cargo")
            .arg("build")
            .arg("--quiet")
            .arg("--bin")
            .arg(name)
            .current_dir(self.manifest_dir())
            .env("CARGO_TARGET_DIR", &self.target_dir)
            .env("CARGO_TERM_COLOR", "never")
            .output()
            .expect("downstream cargo build should launch")
    }

    fn run_bin(&self, name: &str) -> Output {
        Command::new(self.bin_path(name))
            .current_dir(self.manifest_dir())
            .env("CARGO_TERM_COLOR", "never")
            .output()
            .expect("downstream fixture binary should launch")
    }

    fn bin_path(&self, name: &str) -> PathBuf {
        self.target_dir
            .join("debug")
            .join(format!("{name}{}", env::consts::EXE_SUFFIX))
    }

    fn manifest_dir(&self) -> &Path {
        &self.manifest_dir
    }
}

impl Drop for DownstreamFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.cleanup_root);
    }
}

fn trust_vc_manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("trust-vc-core manifest should live under crates/")
        .join("trust-vc")
        .canonicalize()
        .expect("trust-vc crate path should resolve")
}

fn stdout_text(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr_text(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn assert_build_succeeds(output: &Output, name: &str) {
    assert!(
        output.status.success(),
        "{name} should build successfully\nstdout:\n{}\nstderr:\n{}",
        stdout_text(output),
        stderr_text(output)
    );
}

fn assert_build_fails_with_stderr(output: &Output, name: &str, needle: &str) {
    assert!(
        !output.status.success(),
        "{name} should fail to build\nstdout:\n{}\nstderr:\n{}",
        stdout_text(output),
        stderr_text(output)
    );
    assert!(
        stderr_text(output).contains(needle),
        "{name} should mention `{needle}` in stderr\nstdout:\n{}\nstderr:\n{}",
        stdout_text(output),
        stderr_text(output)
    );
}

fn assert_run_succeeds(output: &Output, name: &str) {
    assert!(
        output.status.success(),
        "{name} should run successfully\nstdout:\n{}\nstderr:\n{}",
        stdout_text(output),
        stderr_text(output)
    );
}

fn assert_run_fails_with_stderr(output: &Output, name: &str, needle: &str) {
    assert!(
        !output.status.success(),
        "{name} should fail at runtime\nstdout:\n{}\nstderr:\n{}",
        stdout_text(output),
        stderr_text(output)
    );
    assert!(
        stderr_text(output).contains(needle),
        "{name} runtime stderr should mention `{needle}`\nstdout:\n{}\nstderr:\n{}",
        stdout_text(output),
        stderr_text(output)
    );
}

#[test]
fn test_contract_downstream_surface_matches_current_audit() {
    let fixture = DownstreamFixture::new("current_audit");
    fixture.write_bin(
        "multiple",
        r#"
#[trust_vc::contract(requires(x > 0, x < 100))]
fn bounded(x: u32) -> u32 {
    x + 1
}

fn main() {
    let _ = bounded(50);
}
"#,
    );
    fixture.write_bin(
        "returns",
        r#"
#[trust_vc::contract(
    ensures(ret > x),
    returns(ret),
)]
fn increment(x: u32) -> u32 {
    x + 1
}

fn main() {
    let _ = increment(5);
}
"#,
    );
    fixture.write_bin(
        "old",
        r#"
#[trust_vc::contract(
    requires(x > 0),
    ensures(ret == old!(x) + 1),
    returns(ret),
)]
fn increment(x: u32) -> u32 {
    x + 1
}

fn main() {
    let _ = increment(5);
}
"#,
    );
    fixture.write_bin(
        "proof",
        r#"
#[trust_vc::contract(requires(n > 0))]
#[trust_vc::proof]
fn lemma_positive(n: u32) {}

fn main() {
    lemma_positive(1);
}
"#,
    );

    let requires_only = fixture.build_bin("multiple");
    assert_build_succeeds(&requires_only, "multiple");

    let named_return = fixture.build_bin("returns");
    assert_build_succeeds(&named_return, "returns");

    let old_in_ensures = fixture.build_bin("old");
    assert_build_succeeds(&old_in_ensures, "old");

    let proof = fixture.build_bin("proof");
    assert_build_fails_with_stderr(
        &proof,
        "proof",
        "empty #[trust_vc::proof] bodies cannot use #[trust_vc::contract(requires(...))] without ensures(...)",
    );

    fixture.write_bin(
        "early_return_pass",
        r#"
#[trust_vc::contract(
    ensures(ret > 0),
    returns(ret),
)]
fn early_return(x: i32) -> i32 {
    if x < 0 {
        return 1;
    }
    x + 1
}

fn main() {
    let _ = early_return(-1);
}
"#,
    );
    fixture.write_bin(
        "early_return_fail",
        r#"
#[trust_vc::contract(
    ensures(ret > 0),
    returns(ret),
)]
fn early_return(x: i32) -> i32 {
    if x < 0 {
        return -1;
    }
    x + 1
}

fn main() {
    let _ = early_return(-1);
}
"#,
    );

    let early_return_pass = fixture.build_bin("early_return_pass");
    assert_build_succeeds(&early_return_pass, "early_return_pass");
    let early_return_pass_run = fixture.run_bin("early_return_pass");
    assert_run_succeeds(&early_return_pass_run, "early_return_pass");

    let early_return_fail = fixture.build_bin("early_return_fail");
    assert_build_succeeds(&early_return_fail, "early_return_fail");
    let early_return_fail_run = fixture.run_bin("early_return_fail");
    assert_run_fails_with_stderr(
        &early_return_fail_run,
        "early_return_fail",
        "trust_vc postcondition failed",
    );
}
