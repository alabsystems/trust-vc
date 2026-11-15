//! Native header traversal controls for the unverified declaration observer.
//!
//! These are not verifier oracles. They require the genuine Trust-built
//! builtin cohort and never claim executable, ownership or import authority.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_span;

use std::path::Path;
use std::process::{Command, Output};

use rustc_span::{SourceFileHash, SourceFileHashAlgorithm};
use serde_json::{json, Value};

fn sha(path: &Path) -> String {
    SourceFileHash::new_in_memory(
        SourceFileHashAlgorithm::Sha256,
        std::fs::read(path).unwrap(),
    )
    .to_string()
    .trim_start_matches("sha256=")
    .to_owned()
}

fn observe_with_args(
    name: &str,
    body: &str,
    source_listed: bool,
    extra: &[&str],
) -> (Output, Option<Value>) {
    let builtins = std::path::PathBuf::from(
        std::env::var_os("TRUST_VC_VERUS_BUILTINS").expect("genuine Trust-built builtin cohort"),
    );
    let dir = std::env::temp_dir().join(format!(
        "trust-vc-declaration-headers-{}-{name}",
        std::process::id()
    ));
    std::fs::create_dir(&dir).expect("fresh control directory");
    let source = dir.join("control.rs");
    std::fs::write(
        &source,
        format!(
            r#"#![feature(register_tool)]
#![register_tool(verus)]
#![allow(dead_code)]
extern crate verus_builtin as builtin;
extern crate verus_builtin_macros;
extern crate verus_state_machines_macros;
mod prelude {{ pub use builtin::*; }}
{body}
"#
        ),
    )
    .unwrap();
    let approved = if source_listed {
        source.clone()
    } else {
        let other = dir.join("unrelated.rs");
        std::fs::write(
            &other,
            "// This approved file does not contain the compiled helper.\n",
        )
        .unwrap();
        other
    };
    let artifact = |name: &str| {
        let path = builtins.join(name).canonicalize().unwrap();
        json!({"path": path.display().to_string(), "sha256": sha(&path)})
    };
    let mut sources = serde_json::Map::new();
    sources.insert(
        approved.canonicalize().unwrap().display().to_string(),
        json!(sha(&approved)),
    );
    let manifest = dir.join("inputs.json");
    std::fs::write(&manifest, serde_json::to_vec(&json!({
        "schema": "trust-vc.unverified-function-identity-observer@1",
        "compiler_commit": env!("VC_SHIM_COMPILER_COMMIT"),
        "observation_only": true, "import_authorized": false, "verified_functions": null,
        "builtin_artifact": artifact("libverus_builtin.rlib"),
        "macro_artifacts": [artifact("libverus_builtin_macros.dylib"), artifact("libverus_state_machines_macros.dylib")],
        "source_files": sources,
    })).unwrap()).unwrap();
    let report = dir.join("observation.json");
    let mut command = Command::new(env!("CARGO_BIN_EXE_vstd_declaration_observe"));
    command
        .env("VSTD_KIND", "NoVstd")
        .env("TRUST_VC_UNVERIFIED_FUNCTION_IDENTITY_MANIFEST", manifest)
        .env(
            "VERUS_Z3_PATH",
            "/nonexistent/trust-vc-runs-no-solver-process",
        )
        .arg(&report)
        .arg("--")
        .args([
            "-Ztrust-verify=off",
            "--edition=2021",
            "--crate-type=lib",
            "--crate-name=identity_observer_control",
        ])
        .args([
            "--cfg",
            "verus_keep_ghost",
            "--cfg",
            "verus_keep_ghost_body",
        ])
        .arg("--out-dir")
        .arg(&dir)
        .arg("-L")
        .arg(format!("dependency={}", builtins.display()));
    for (name, file) in [
        ("verus_builtin", "libverus_builtin.rlib"),
        ("verus_builtin_macros", "libverus_builtin_macros.dylib"),
        (
            "verus_state_machines_macros",
            "libverus_state_machines_macros.dylib",
        ),
    ] {
        command
            .arg("--extern")
            .arg(format!("{name}={}", builtins.join(file).display()));
    }
    let output = command.args(extra).arg(source).output().unwrap();
    let observation = report
        .exists()
        .then(|| serde_json::from_slice(&std::fs::read(report).unwrap()).unwrap());
    (output, observation)
}

fn header(name: &str, source: &str) -> Value {
    let (output, report) = observe_with_args(
        name,
        source,
        true,
        &[
            "-Zcrate-attr=register_tool(verifier)",
            "-Zcrate-attr=feature(stmt_expr_attributes)",
        ],
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report = report.expect("actual native header observation");
    assert_eq!(report["import_authorized"], false);
    assert!(report["verified_functions"].is_null());
    assert_eq!(report["keep_body_ownership_checked"], false);
    let row = report["rows"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["definition"]["item_name_observation"] == "test")
        .expect("actual public test declaration");
    let header = &row["header_observation"];
    assert_eq!(header["header_authority"]["state"], "Unknown");
    assert_eq!(header["ordered_header_validation"]["state"], "Unknown");
    assert_eq!(header["owner"], row["definition"]);
    header.clone()
}

#[test]
fn unchanged_free_and_inherent_bodies_have_empty_observations() {
    for (label, source) in [
        ("free_empty", "verus_builtin_macros::verus! { pub closed spec fn test(x: bool) -> bool { x } }"),
        ("inherent_empty", "verus_builtin_macros::verus! { pub struct S {} impl S { pub closed spec fn test(self, x: bool) -> bool { x } } }"),
    ] {
        let report = header(label, source);
        assert_eq!(report["state"], "ObservedNoHeaderReference");
        assert!(report["expressions_visited"].as_u64().unwrap() > 0);
        assert_eq!(report["bodies_visited"], 1);
    }
}

#[test]
fn leading_late_and_reified_builtin_headers_are_nonempty() {
    for (label, statements) in [
        ("leading_header", "builtin::requires(true);"),
        ("late_header", "let _ = true; builtin::requires(true);"),
        (
            "reified_header",
            "let _marker: fn(bool) = builtin::requires::<bool>;",
        ),
    ] {
        let source =
            format!("verus_builtin_macros::verus! {{ pub proof fn test() {{ {statements} }} }}");
        let report = header(label, &source);
        assert_eq!(report["state"], "ObservedHeaderReferences");
        assert!(!report["references"].as_array().unwrap().is_empty());
    }
}

#[test]
fn closure_bodies_do_not_hide_header_references() {
    for (label, statement, expected) in [
        ("closure_empty", "", "ObservedNoHeaderReference"),
        (
            "closure_header",
            "builtin::requires(x);",
            "ObservedHeaderReferences",
        ),
    ] {
        let source = format!("verus_builtin_macros::verus! {{ pub proof fn test() {{ let _f = |x: bool| {{ {statement} x }}; }} }}");
        let report = header(label, &source);
        assert_eq!(report["state"], expected);
        assert_eq!(report["includes_closure_bodies"], true);
        assert!(report["bodies_visited"].as_u64().unwrap() >= 2);
    }
}

#[test]
fn nested_items_never_donate_an_empty_or_nonempty_result() {
    for (label, statement) in [
        ("nested_empty", ""),
        ("nested_header", "builtin::requires(true);"),
    ] {
        let source = format!("verus_builtin_macros::verus! {{ pub proof fn test() {{ fn nested() {{ {statement} }} }} }}");
        let report = header(label, &source);
        assert_eq!(report["state"], "Unknown");
        assert!(report["unknowns"]
            .as_array()
            .unwrap()
            .iter()
            .any(|reason| reason.as_str().unwrap().contains("nested item")));
    }
}

#[test]
fn resolved_builtin_methods_cannot_be_confused_with_user_methods() {
    let template = r#"verus_builtin_macros::verus! {
pub struct S {}
impl S { pub closed spec fn view(self) -> bool { true } }
pub closed spec fn test(s: TYPE) -> bool { s.view() }
}"#;
    for (label, ty, expected) in [
        ("ordinary_method", "S", "ObservedNoHeaderReference"),
        ("unknown_builtin_method", "builtin::Ghost<bool>", "Unknown"),
    ] {
        let report = header(label, &template.replace("TYPE", ty));
        assert_eq!(report["state"], expected);
        if ty != "S" {
            assert!(report["unknowns"]
                .as_array()
                .unwrap()
                .iter()
                .any(|reason| reason
                    .as_str()
                    .unwrap()
                    .contains("unclassified Verus builtin")));
        }
    }
}

#[test]
fn unsupported_item_directives_and_trait_origins_remain_unknown() {
    for (label, source) in [
        (
            "external_body_header",
            "verus_builtin_macros::verus! { #[verifier::external_body] pub proof fn test() {} }",
        ),
        (
            "trait_header",
            "verus_builtin_macros::verus! { pub trait T { spec fn test() -> bool { true } } }",
        ),
    ] {
        assert_eq!(header(label, source)["state"], "Unknown");
    }
}

#[test]
fn an_unclassified_expression_directive_is_not_an_empty_header_fact() {
    let report = header(
        "expression_directive",
        r#"verus_builtin_macros::verus! {
pub closed spec fn test(x: bool) -> bool { #[verifier::atomic] { x } }
}"#,
    );
    assert_eq!(report["state"], "Unknown");
    assert!(report["unknowns"]
        .as_array()
        .unwrap()
        .iter()
        .any(|reason| reason.as_str().unwrap().contains("expression directive")));
}

#[test]
fn first_class_native_contract_fields_cannot_be_skipped_as_empty() {
    let template = r#"
#[verus::internal(verus_macro)]
#[verus::internal(spec)]
pub fn test(x: bool) -> bool CLAUSE { x }
"#;
    for (label, clause, expected) in [
        ("native_empty", "", "ObservedNoHeaderReference"),
        ("native_requires", "requires x", "Unknown"),
    ] {
        let report = header(label, &template.replace("CLAUSE", clause));
        assert_eq!(report["state"], expected);
        if !clause.is_empty() {
            assert!(report["unknowns"]
                .as_array()
                .unwrap()
                .iter()
                .any(|reason| reason
                    .as_str()
                    .unwrap()
                    .contains("native first-class clauses")));
        }
    }
}

#[test]
fn an_ordinary_function_named_requires_has_no_builtin_authority() {
    let report = header(
        "ordinary_requires",
        r#"verus_builtin_macros::verus! {
spec fn requires(x: bool) -> bool { x }
pub closed spec fn test(x: bool) -> bool { requires(x) }
}"#,
    );
    assert_eq!(report["state"], "ObservedNoHeaderReference");
    assert!(report["references"].as_array().unwrap().is_empty());
}
