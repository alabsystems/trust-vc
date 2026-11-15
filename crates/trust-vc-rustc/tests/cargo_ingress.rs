//! Real native wrapper executions. In addition to the existing builtins input,
//! TRUST_VC_CARGO_COMPILER names the actual Trust compiler Cargo would pass.
//! No substitute wrapper, Cargo recorder or solver stub participates.

// The production protocol module belongs to the native driver crate. Link
// its compiler dependencies using the compiler's single-std convention too.
#![feature(rustc_private)]

mod common;

use std::path::PathBuf;
use std::process::{Command, Output};

use trust_vc_rustc::cargo;

struct Case {
    directory: PathBuf,
    artifact: PathBuf,
    dep_info: PathBuf,
    output: Output,
    record: serde_json::Value,
}

impl Drop for Case {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.directory);
    }
}

fn command() -> Command {
    let compiler = std::env::var_os("TRUST_VC_CARGO_COMPILER")
        .expect("TRUST_VC_CARGO_COMPILER must name Cargo's real Trust compiler");
    assert!(
        std::path::Path::new(&compiler).is_file(),
        "Cargo compiler input must exist"
    );
    let mut command = Command::new(env!("CARGO_BIN_EXE_rust_verify"));
    for (key, _) in std::env::vars_os() {
        let key_text = key.to_string_lossy();
        if key_text.starts_with("__VERUS_DRIVER_") || key_text.starts_with(" __VERUS_DRIVER_") {
            command.env_remove(key);
        }
    }
    command
        .arg(compiler)
        .env(cargo::VIA_CARGO, "1")
        .env_remove("TRUST_VC_VERDICT_DIR")
        .env_remove("TRUST_VC_DUMP_VCIR")
        .env_remove("CARGO_PKG_NAME")
        .env_remove("CARGO_PKG_VERSION")
        .env_remove("CARGO_MANIFEST_DIR")
        .env_remove("CARGO_CRATE_NAME")
        .env_remove("CARGO_PRIMARY_PACKAGE");
    command
}

fn case_directory(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!("trust-vc-cargo-test-{}-{name}", std::process::id()))
}

fn run(name: &str, source: &str, compile: bool, options: &[&str]) -> Case {
    let directory = case_directory(name);
    std::fs::create_dir(&directory).expect("fresh case directory");
    let entry = directory.join("lib.rs");
    let artifact = directory.join("libnative_cargo_fixture.rmeta");
    let dep_info = directory.join("public.d");
    std::fs::write(&entry, format!("{}{source}", common::PRELUDE)).unwrap();
    std::fs::write(
        directory.join("Cargo.toml"),
        "[package]\nname='native-cargo-fixture'\nversion='1.0.0'\nedition='2021'\n",
    )
    .unwrap();
    let manifest = directory.join("Cargo.toml");
    let id = cargo::package_id("native-cargo-fixture", "1.0.0", manifest.to_str().unwrap());
    let builtins =
        PathBuf::from(std::env::var_os("TRUST_VC_VERUS_BUILTINS").expect("native builtins input"));
    let mut forwarded = vec!["--no-vstd"];
    forwarded.extend_from_slice(options);
    if compile {
        forwarded.extend(["--VIA-CARGO", "compile-when-primary-package"]);
    }
    let packed: String = forwarded
        .iter()
        .map(|option| format!("{}{option}", cargo::DRIVER_ARGS_SEP))
        .collect();
    let output = command()
        .env("CARGO_PKG_NAME", "native-cargo-fixture")
        .env("CARGO_PKG_VERSION", "1.0.0")
        .env("CARGO_MANIFEST_DIR", &directory)
        .env("CARGO_CRATE_NAME", "native_cargo_fixture")
        .env("CARGO_PRIMARY_PACKAGE", "")
        .env(format!("{}{id}", cargo::VERIFY), "1")
        .env(cargo::DRIVER_ARGS, packed)
        .args([
            "--edition=2021",
            "--crate-name",
            "native_cargo_fixture",
            "--crate-type=lib",
            "--error-format=json",
        ])
        .arg(format!("--emit=metadata,dep-info={}", dep_info.display()))
        .arg("--extern")
        .arg(format!(
            "verus_builtin={}",
            builtins.join("libverus_builtin.rlib").display()
        ))
        .arg("--extern")
        .arg(format!(
            "verus_builtin_macros={}",
            builtins.join("libverus_builtin_macros.dylib").display()
        ))
        .arg("--extern")
        .arg(format!(
            "verus_state_machines_macros={}",
            builtins
                .join("libverus_state_machines_macros.dylib")
                .display()
        ))
        .arg("-L")
        .arg(format!("dependency={}", builtins.display()))
        .args(["--cfg", "verus_no_vstd", "-o"])
        .arg(&artifact)
        .arg(&entry)
        .output()
        .expect("native Cargo wrapper");
    let record_text =
        std::fs::read_to_string(directory.join("trust-vc-verdict.jsonl")).unwrap_or_default();
    let record = record_text
        .lines()
        .next()
        .and_then(|line| serde_json::from_str(line).ok())
        .unwrap_or(serde_json::Value::Null);
    Case {
        directory,
        artifact,
        dep_info,
        output,
        record,
    }
}

#[test]
fn real_compiler_probe_has_no_verification_record() {
    let output = command()
        .arg("-vV")
        .output()
        .expect("native compiler probe");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("commit-hash:"));
    assert!(!String::from_utf8_lossy(&output.stdout).contains("\"outcome\":"));
}

#[test]
fn native_verification_and_primary_compilation_are_distinct() {
    for (name, compile) in [("verify_only", false), ("verify_compile", true)] {
        let case = run(
            name,
            "verus! { proof fn p() { assert(true); } }",
            compile,
            &[],
        );
        assert!(
            case.output.status.success(),
            "{}",
            String::from_utf8_lossy(&case.output.stderr)
        );
        assert_eq!(case.record["outcome"], "checked");
        assert_eq!(case.record["refused"], false);
        assert_eq!(
            case.artifact.is_file(),
            compile,
            "only requested post-verification compilation emits metadata"
        );
        assert_eq!(
            case.dep_info.is_file(),
            compile,
            "the verification frontend cannot emit public dep-info either"
        );
        if compile {
            let dependencies = std::fs::read_to_string(&case.dep_info).unwrap();
            assert!(dependencies.contains("env-dep:__VERUS_DRIVER_VIA_CARGO__=1"));
            assert!(dependencies.contains("env-dep:CARGO_PRIMARY_PACKAGE="));
        }
    }
}

#[test]
fn false_assertion_cannot_leave_a_cargo_artifact() {
    let case = run(
        "false_no_output",
        "verus! { proof fn p() { assert(false); } }",
        true,
        &[],
    );
    assert_eq!(case.output.status.code(), Some(1));
    assert_eq!(case.record["outcome"], "verification-failed");
    assert!(
        !case.artifact.exists(),
        "speculative erase compile must use private outputs"
    );
    assert!(
        !case.dep_info.exists(),
        "the failed verification frontend cannot emit public dep-info"
    );
}

#[test]
fn explicit_no_verify_compiles_but_cannot_claim_a_proof() {
    let case = run(
        "skip_truthful",
        "verus! { proof fn p() { assert(false); } }",
        true,
        &["--no-verify"],
    );
    assert!(
        case.output.status.success(),
        "{}",
        String::from_utf8_lossy(&case.output.stderr)
    );
    assert!(case.artifact.is_file());
    assert!(case.dep_info.is_file());
    assert_eq!(case.record["outcome"], "verification-skipped");
    assert_eq!(
        case.record["refused"], true,
        "strict verification evidence still sees skipped work"
    );
    let functions = case.record["functions"].as_array().unwrap();
    assert!(functions
        .iter()
        .any(|function| function["verdict"] == "skipped" && function["tag"] == "no-verify"));
    assert!(functions
        .iter()
        .all(|function| function["verdict"] != "verified"));
}

#[test]
fn no_verify_does_not_override_a_real_native_refusal() {
    let case = run(
        "skip_refuses",
        "verus! { proof fn p() { assert(true); } }",
        true,
        &["--no-verify", "--smt-option", "smt.random_seed=1"],
    );
    assert_eq!(case.output.status.code(), Some(1));
    assert_eq!(case.record["outcome"], "refused");
    assert!(case.record["crate_refusals"]
        .as_array()
        .unwrap()
        .iter()
        .any(|message| message
            .as_str()
            .unwrap()
            .starts_with("trust-vc refused: smt-option")));
    assert!(!case.artifact.exists());
    assert!(!case.dep_info.exists());
}

#[test]
fn requested_dependency_without_a_real_contract_is_not_silently_ignored() {
    let case = run(
        "import_missing",
        "verus! { proof fn p() { assert(true); } }",
        true,
        &[
            "--no-verify",
            "--VIA-CARGO",
            "import-dep-if-present=verus_builtin",
        ],
    );
    assert_eq!(case.output.status.code(), Some(1));
    assert_eq!(case.record["outcome"], "refused");
    assert!(String::from_utf8_lossy(&case.output.stderr)
        .contains("could not find .vir file for 'verus_builtin'"));
    assert!(!case.artifact.exists());
    assert!(!case.dep_info.exists());
}

#[test]
fn ordinary_dependency_does_not_gain_unstable_feature_permission() {
    let directory =
        std::env::temp_dir().join(format!("trust-vc-cargo-ordinary-{}", std::process::id()));
    std::fs::create_dir(&directory).expect("fresh ordinary case directory");
    for (name, source, accepted) in [
        ("ordinary", "pub fn p() {}", true),
        (
            "unstable",
            "#![feature(rustc_private)]\npub fn p() {}",
            false,
        ),
    ] {
        let entry = directory.join(format!("{name}.rs"));
        let output_file = directory.join(format!("{name}.rmeta"));
        std::fs::write(&entry, source).unwrap();
        let output = command()
            .env("RUSTC_BOOTSTRAP", "-1")
            .env("CARGO_PKG_NAME", "ordinary-dependency")
            .env("CARGO_PKG_VERSION", "1.0.0")
            .env("CARGO_MANIFEST_DIR", &directory)
            .env("CARGO_CRATE_NAME", name)
            .args([
                "--crate-type=lib",
                "--emit=metadata",
                "--error-format=json",
                "-o",
            ])
            .arg(&output_file)
            .arg(&entry)
            .output()
            .expect("ordinary native compiler");
        assert_eq!(
            output.status.success(),
            accepted,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output_file.is_file(), accepted);
        if !accepted {
            assert!(String::from_utf8_lossy(&output.stderr).contains("E0554"));
        }
        assert!(!directory.join("trust-vc-verdict.jsonl").exists());
    }
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn original_emit_arguments_are_still_validated_by_rustc() {
    let case = run(
        "invalid_emit",
        "verus! { proof fn p() { assert(true); } }",
        false,
        &["--emit=not-an-emission-kind"],
    );
    assert_eq!(case.output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&case.output.stderr).contains("unknown emission type"));
    assert!(!case.artifact.exists());
    assert!(!case.dep_info.exists());
}

#[test]
fn requested_mir_dump_is_private_until_final_compilation() {
    for (name, compile) in [("mir_verify_only", false), ("mir_compile", true)] {
        let public_mir = case_directory(name).join("public-mir");
        let dump = format!("dump-mir-dir={}", public_mir.display());
        let case = run(
            name,
            "pub fn ordinary_mir(x: u32) -> u32 { x }\nverus! { proof fn p() { assert(true); } }",
            compile,
            &["-Z", "dump-mir=all", "-Z", &dump],
        );
        assert!(
            case.output.status.success(),
            "{}",
            String::from_utf8_lossy(&case.output.stderr)
        );
        assert_eq!(case.record["outcome"], "checked");
        assert_eq!(public_mir.is_dir(), compile);
        if compile {
            assert!(std::fs::read_dir(public_mir).unwrap().next().is_some());
        }
    }
}
