// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Real native transactions in separate test processes; no successful Record
//! or caller-provided result can construct CheckedProducer.
use super::*;
use std::cell::Cell;
use std::io::{Read, Write};
use std::sync::atomic::{AtomicU64, Ordering};

thread_local! {
    static ERASE_DISPATCH: Cell<bool> = const { Cell::new(false) };
}

pub(super) struct NativeEraseDispatch;
impl NativeEraseDispatch {
    pub(super) fn enter() -> Self {
        ERASE_DISPATCH.with(|active| assert!(!active.replace(true)));
        Self
    }
}
impl Drop for NativeEraseDispatch {
    fn drop(&mut self) {
        ERASE_DISPATCH.with(|active| active.set(false));
    }
}

pub(in crate::shim) fn native_erase_dispatch() -> bool {
    ERASE_DISPATCH.with(Cell::get)
}

fn exact_child(name: &str, input: &[u8]) -> std::process::Output {
    let test = format!("{}::{name}", module_path!().split_once("::").unwrap().1);
    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args(["--ignored", "--exact", &test, "--nocapture"])
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::piped());
    let mut child = crate::child_process::RetainedChild::spawn(&mut command).unwrap();
    child.write_input(input).unwrap();
    let (status, stderr) = child.stderr_and_wait().unwrap();
    std::process::Output {
        status,
        stdout: Vec::new(),
        stderr,
    }
}

pub(in crate::shim) fn run_native_erase(
    args: &[String],
    inputs: &CargoInputs,
    private_output: Option<&std::path::Path>,
    compiler_environment: Option<&CompilerEnvironment>,
) -> Result<EraseChild, String> {
    if !inputs.0.is_empty() || private_output.is_some() || compiler_environment.is_some() {
        return Err(
            "the producer test erase route has unrepresented Cargo/environment inputs".into(),
        );
    }
    let mut argv = vec![
        "native-producer-erase".to_owned(),
        ERASE_RUN_FLAG.to_owned(),
    ];
    argv.extend(args.iter().skip(1).cloned());
    let input = serde_json::to_vec(&argv).map_err(|error| error.to_string())?;
    let output = exact_child("actual_native_erase_child", &input);
    Ok(erase_child_result(
        output.status.code().unwrap_or(101),
        &output.stderr,
    ))
}

fn input() -> Vec<u8> {
    let mut bytes = Vec::new();
    std::io::stdin()
        .take(1_048_577)
        .read_to_end(&mut bytes)
        .unwrap();
    assert!(!bytes.is_empty() && bytes.len() <= 1_048_576);
    bytes
}

#[test]
#[ignore = "private exact-process helper; stdin supplies real native erase argv only"]
fn actual_native_erase_child() {
    let argv: Vec<String> = serde_json::from_slice(&input()).unwrap();
    assert_eq!(argv.get(1).map(String::as_str), Some(ERASE_RUN_FLAG));
    // The same real compiler/impl observation/status code as the production
    // erase child. Test argv is data and never a producer verification result.
    std::process::exit(i32::from(erase_child_code(&argv)));
}

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Fixture {
    root: PathBuf,
    sources: Sources,
    file: PathBuf,
}
impl Fixture {
    fn new(case: &str) -> Self {
        let root = std::env::temp_dir().join(format!(
            "trust-vc-producer-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&root).unwrap();
        let root = root.canonicalize().unwrap();
        let source_root = root.join("source");
        std::fs::create_dir(&source_root).unwrap();
        let file = source_root.join("producer.rs");
        let post = if matches!(case, "negative" | "assumption") {
            "r == x + 1"
        } else {
            "r == x"
        };
        let attribute = if case == "external" {
            "#[verifier::external_body]"
        } else {
            ""
        };
        let body = if case == "assumption" {
            "proof { assume(false); } x"
        } else {
            "x"
        };
        let text = format!("#![feature(sized_hierarchy)]\n#![feature(proc_macro_hygiene)]\nuse verus_builtin::*;\nuse verus_builtin_macros::*;\nverus! {{\npub open spec fn domain(x: u64) -> bool {{ x < 8 }}\n{attribute} pub fn identity(x: u64) -> (r: u64) requires domain(x), ensures {post}, {{ {body} }}\n}}\n");
        std::fs::write(&file, text).unwrap();
        let hash = Sha256::digest(std::fs::read(&file).unwrap());
        let hash = hash
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        let manifest = root.join("source-manifest.json");
        std::fs::write(
            &manifest,
            serde_json::to_vec(
                &serde_json::json!({"files_sha256": {"producer.rs":hash}, "symlink_targets":{}}),
            )
            .unwrap(),
        )
        .unwrap();
        let pin = PinnedFile {
            path: manifest.clone(),
            sha256: Sha256::digest(std::fs::read(&manifest).unwrap()).into(),
        };
        let sources = Sources::load(&source_root, pin, None).unwrap();
        Self {
            root,
            sources,
            file,
        }
    }

    fn invocation(&self, disabled: &[&str], native: bool) -> NormalInvocation {
        let mut args = vec![
            "--internal-test-mode".to_owned(),
            "--no-external-by-default".into(),
            "--no-cheating".into(),
            "--crate-name=verified_producer".into(),
            "--crate-type=lib".into(),
            "--emit=metadata".into(),
            "--error-format=json".into(),
            "--sysroot".into(),
            env!("VC_SHIM_COMPILER_SYSROOT").into(),
            "--cfg".into(),
            "verus_no_vstd".into(),
            "-o".into(),
            self.root.join("producer.rmeta").display().to_string(),
            self.file.display().to_string(),
        ];
        if native {
            let builtins = PathBuf::from(std::env::var_os("TRUST_VC_VERUS_BUILTINS").expect("the real native producer controls require the existing trustc-built builtin/macro cohort"));
            for (name, image) in [
                ("verus_builtin", "libverus_builtin.rlib"),
                ("verus_builtin_macros", "libverus_builtin_macros.dylib"),
                (
                    "verus_state_machines_macros",
                    "libverus_state_machines_macros.dylib",
                ),
            ] {
                args.extend([
                    "--extern".into(),
                    format!("{name}={}", builtins.join(image).display()),
                ]);
            }
            args.extend(["-L".into(), format!("dependency={}", builtins.display())]);
        }
        args.extend(disabled.iter().map(|value| (*value).to_owned()));
        NormalInvocation::derive(
            "verified-producer-control".into(),
            args::split(&args).unwrap(),
        )
        .unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.root).unwrap();
    }
}

#[test]
fn producer_scope_refuses_disabled_checks_before_native_compilation() {
    let fixture = Fixture::new("positive");
    for options in [
        vec!["--no-verify"],
        vec!["--no-lifetime"],
        vec!["--no-erasure-check"],
        vec!["--no-auto-recommends-check"],
    ] {
        let request = fixture.invocation(&options, false);
        assert!(full_checks(&request).is_err());
    }
    let request = fixture.invocation(&[], false);
    assert!(full_checks(&request).is_ok());
}

#[test]
fn verified_primitive_producer_keeps_real_contracts_and_predicate_bodies() {
    let output = exact_child("actual_native_producer_control", b"positive");
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn false_producer_postcondition_cannot_form_contract_authority() {
    let output = exact_child("actual_native_producer_control", b"negative");
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn assumptions_and_external_bodies_cannot_form_producer_contract_authority() {
    for case in [b"assumption".as_slice(), b"external".as_slice()] {
        let output = exact_child("actual_native_producer_control", case);
        assert!(
            output.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
#[ignore = "private exact-process helper for real producer compiler and AY controls"]
fn actual_native_producer_control() {
    let action = input();
    assert!(matches!(
        action.as_slice(),
        b"positive" | b"negative" | b"assumption" | b"external"
    ));
    let case = std::str::from_utf8(&action).unwrap();
    let fixture = Fixture::new(case);
    let invocation = fixture.invocation(&[], true);
    let result = verify(&invocation, &fixture.sources);
    if case != "positive" {
        let reason = match result {
            Err(reason) => reason,
            Ok(_) => panic!("an unproven/assumed/external producer formed contract authority"),
        };
        if case == "negative" {
            assert!(
                reason.contains("real AY producer body verification failed"),
                "the false postcondition was not checked by AY: {reason}"
            );
        }
    } else {
        let checked =
            result.unwrap_or_else(|error| panic!("real producer verification failed: {error}"));
        let function = checked
            .functions()
            .find(|function| function.declaration().name.ends_with("identity"))
            .unwrap();
        assert_eq!(function.declaration().mode, Mode::Exec);
        assert!(matches!(function.declaration().body, Body::Stmts(_)));
        assert_eq!(function.declaration().requires.len(), 1);
        assert_eq!(function.declaration().ensures.len(), 1);
        assert!(checked.functions().any(|function| function
            .declaration()
            .name
            .ends_with("domain")
            && matches!(function.declaration().body, Body::Spec(_))));
        assert_eq!(checked.source(), fixture.sources.identity());
        checked.revalidate(&fixture.sources).unwrap();
        std::fs::write(&fixture.file, "fn changed() {}\n").unwrap();
        assert!(checked.revalidate(&fixture.sources).is_err());
    }
}
