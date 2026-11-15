//! Real compiler controls for the unverified declaration observer.
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

fn observe(name: &str, body: &str, source_listed: bool) -> (Output, Option<Value>) {
    observe_with_args(name, body, source_listed, &[])
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
        "trust-vc-identity-observer-{}-{name}",
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
fn generic<T>() {{}}
fn plain() {{}}
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

fn mode_report(name: &str, source: &str) -> Value {
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
    let report = report.expect("ordinary native declaration observation");
    assert_eq!(report["import_authorized"], false);
    assert!(report["verified_functions"].is_null());
    assert_eq!(report["keep_body_ownership_checked"], false);
    let row = report["rows"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["definition"]["item_name_observation"] == "test")
        .expect("actual public test declaration")
        .clone();
    assert_eq!(row["body_input_view"]["state"], "OriginalUnprojectedBody");
    row
}

#[test]
fn spec_lambda_body_checks_real_callee_modes() {
    let template = r#"verus_builtin_macros::verus! {
MODE fn helper(x: bool) -> bool { x }
spec fn sink(_f: spec_fn(bool) -> bool) -> bool { true }
pub closed spec fn test() -> bool { sink(|x: bool| helper(x)) }
}"#;
    for (label, mode, expected) in [
        ("lambda_spec_callee", "spec", "CheckedLocalBodyModes"),
        ("lambda_exec_callee", "", "RejectedBodyModes"),
    ] {
        let row = mode_report(label, &template.replace("MODE", mode));
        assert_eq!(row["body_mode_observation"]["state"], expected);
        if mode.is_empty() {
            assert!(row["body_mode_observation"]["message"]
                .as_str()
                .unwrap()
                .contains("with mode exec"));
        }
    }
}

#[test]
fn spec_lambda_keeps_inline_proof_children_in_the_mode_walk() {
    let template = r#"use builtin::*;
verus_builtin_macros::verus! {
MODE fn helper() {}
spec fn sink(_f: spec_fn(bool) -> bool) -> bool { true }
pub closed spec fn test(n: builtin::nat) -> bool decreases n {
    if n == 0 { sink(|x: bool| { proof { helper(); } x }) }
    else { test((n - 1) as builtin::nat) }
}
}"#;
    for (label, mode, expected) in [
        ("lambda_proof_child", "proof", "CheckedLocalBodyModes"),
        ("lambda_exec_proof_child", "", "RejectedBodyModes"),
    ] {
        let row = mode_report(label, &template.replace("MODE", mode));
        assert_eq!(row["body_mode_observation"]["state"], expected);
        assert_eq!(
            row["header_observation"]["state"],
            "ObservedHeaderReferences"
        );
        assert_eq!(
            row["header_observation"]["header_authority"]["state"],
            "Unknown"
        );
    }
}

#[test]
fn unaffected_inherent_bodies_keep_original_mode_provenance() {
    let template = r#"verus_builtin_macros::verus! {
MODE fn helper(x: bool) -> bool { x }
spec fn sink(_f: spec_fn(bool) -> bool) -> bool { true }
pub struct S {}
impl S {
    pub closed spec fn test(self, x: bool) -> bool { sink(|y: bool| helper(x && y)) }
}
}"#;
    for (label, mode, expected) in [
        ("inherent_lambda", "spec", "CheckedLocalBodyModes"),
        ("inherent_lambda_exec", "", "RejectedBodyModes"),
    ] {
        let row = mode_report(label, &template.replace("MODE", mode));
        assert_eq!(row["body_mode_observation"]["state"], expected);
    }
}

#[test]
fn ordinary_function_named_like_spec_conversion_does_not_gain_a_lambda_rule() {
    let row = mode_report(
        "fake_lambda_conversion",
        r#"
#[verus::internal(verus_macro)]
#[verus::internal(spec)]
fn closure_to_fn_spec<F>(_f: F) -> bool { true }
#[verus::internal(verus_macro)]
#[verus::internal(spec)]
pub fn test() -> bool { closure_to_fn_spec(|x: bool| x) }
"#,
    );
    assert_eq!(row["body_mode_observation"]["state"], "Unknown");
}

#[test]
fn producer_field_modes_stay_unknown_without_private_representation_reads() {
    let row = mode_report(
        "producer_field_mode",
        r#"verus_builtin_macros::verus! {
pub struct S { value: bool }
pub closed spec fn test(s: S) -> bool { s.value }
}"#,
    );
    assert_eq!(row["body_mode_observation"]["state"], "Unknown");
    assert!(row["body_mode_observation"]["reason"]
        .as_str()
        .unwrap()
        .contains("field mode reads"));
}

fn accepted(name: &str, source: &str) -> Value {
    let (output, report) = observe(name, source, true);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report = report.expect("unverified observation");
    assert_eq!(report["import_authorized"], false);
    assert!(report["verified_functions"].is_null());
    assert_eq!(report["keep_body_ownership_checked"], false);
    assert_eq!(
        report["analysis_input_view"],
        "ExplicitUnverifiedIdentityHelperProjection"
    );
    let identities = report["function_identity_observations"]["identities"]
        .as_array()
        .unwrap();
    assert_eq!(identities.len(), 1);
    assert_eq!(
        identities[0]["original_body_mode_check"]["state"],
        "Unknown"
    );
    assert_eq!(
        identities[0]["original_body_header_check"]["state"],
        "Unknown"
    );
    assert_eq!(
        identities[0]["original_source_binding"]["state"],
        "ObservedApprovedOriginalCallerFile"
    );
    assert_eq!(
        identities[0]["original_source_binding"]["expanded_token_provenance"]["state"],
        "Unknown"
    );
    assert_eq!(
        identities[0]["identity"]["reveal_permission"]["state"],
        "Unknown"
    );
    report
}

fn refused(name: &str, source: &str, listed: bool, reason: &str) {
    let (output, report) = observe(name, source, listed);
    assert!(!output.status.success());
    assert!(report.is_none());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(reason),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn generic_identity_has_no_invented_type_arguments() {
    accepted("generic", "#[verus::internal(reveal_fn)] fn carrier() { builtin::reveal_hide_internal_path_(generic) }");
}

#[test]
fn user_macro_wrapper_does_not_define_identity_authority() {
    accepted(
        "user_macro",
        r#"
macro_rules! declare { () => { #[verus::internal(reveal_fn)] fn carrier() { builtin::reveal_hide_internal_path_(generic) } } }
declare!();
"#,
    );
}

#[test]
fn native_marker_alias_retains_the_same_definition() {
    accepted("alias", "use builtin::reveal_hide_internal_path_ as marker; #[verus::internal(reveal_fn)] fn carrier() { marker(generic) }");
}

#[test]
fn same_marker_spelling_on_another_definition_is_refused() {
    refused("wrong_marker", "mod impostor { pub fn reveal_hide_internal_path_<T>(_value: T) {} } #[verus::internal(reveal_fn)] fn carrier() { impostor::reveal_hide_internal_path_(plain) }", true,
        "the identity marker callee is not the approved foreign builtin definition");
}

#[test]
fn extra_computation_is_not_deleted() {
    refused("statement", "#[verus::internal(reveal_fn)] fn carrier() { let _value = (); builtin::reveal_hide_internal_path_(plain) }", true,
        "statements in a function-identity helper body");
    refused("operand", "#[verus::internal(reveal_fn)] fn carrier() { builtin::reveal_hide_internal_path_(generic::<u8>()) }", true,
        "computations cannot be function-identity operands");
}

#[test]
fn parameters_and_additional_directives_are_not_erased() {
    refused("parameter", "#[verus::internal(reveal_fn)] fn carrier(_value: bool) { builtin::reveal_hide_internal_path_(plain) }", true,
        "a function-identity helper must have no parameters or generics and implicit unit return");
    refused("directive", "#[verus::internal(spec)] #[verus::internal(reveal_fn)] fn carrier() { builtin::reveal_hide_internal_path_(plain) }", true,
        "unexpected Verus directives on a function-identity helper");
}

#[test]
fn a_real_but_unapproved_caller_file_is_not_authenticated() {
    refused("unapproved", "#[verus::internal(reveal_fn)] fn carrier() { builtin::reveal_hide_internal_path_(generic) }", false,
        "the original identity caller is outside the approved source manifest");
}

#[test]
fn ordinary_calls_gain_no_execution_or_ownership_authority() {
    let report = accepted("ordinary_call", "#[verus::internal(reveal_fn)] fn carrier() { builtin::reveal_hide_internal_path_(generic) } fn ordinary() { carrier(); }");
    assert_eq!(
        report["function_identity_observations"]["identities"][0]
            ["metadata_only_execution_context"],
        "Unknown; this observer grants no executable semantics"
    );
    assert!(report["original_keep_helper_type_analysis"]
        .as_str()
        .unwrap()
        .starts_with("Not claimed"));
}

#[test]
fn nominal_receiver_placeholder_keeps_its_original_native_binder() {
    let report = accepted(
        "receiver_placeholder",
        r#"
struct G<T>(std::marker::PhantomData<T>);
impl<T> G<T> { fn member() {} }
#[verus::internal(reveal_fn)] fn carrier() { builtin::reveal_hide_internal_path_(G::<_>::member) }
"#,
    );
    let receiver =
        &report["function_identity_observations"]["identities"][0]["identity"]["receiver"];
    assert_eq!(receiver["state"], "ObservedUninstantiatedNominalReceiver");
    assert_eq!(receiver["native_binder"]["parent_count"], 0);
    assert_eq!(
        receiver["native_binder"]["parameters"]
            .as_array()
            .unwrap()
            .len(),
        1
    );
    let slots = receiver["explicit_slot_bindings"].as_array().unwrap();
    assert_eq!(slots.len(), 1);
    assert_eq!(slots[0]["syntax_kind"], "TypeOrConstInferencePlaceholder");
    assert_eq!(slots[0]["native_parameter_kind"], "Type");
    assert_eq!(slots[0]["native_parameter_index"], 0);
    assert_eq!(
        slots[0]["native_parameter_definition"],
        receiver["native_binder"]["parameters"][0]["definition"]
    );
    assert_eq!(slots[0]["chosen_type"]["state"], "Unknown");
    assert_eq!(receiver["applicability"]["state"], "Unknown");
}

#[test]
fn receiver_placeholders_require_actual_native_type_slots() {
    refused(
        "receiver_nongeneric",
        r#"
struct S;
impl S { fn member() {} }
#[verus::internal(reveal_fn)] fn carrier() { builtin::reveal_hide_internal_path_(S::<_>::member) }
"#,
        true,
        "receiver placeholder count differs from the actual native declaration binder",
    );
    refused(
        "receiver_const_slot",
        r#"
struct C<const N: usize>;
impl<const N: usize> C<N> { fn member() {} }
#[verus::internal(reveal_fn)] fn carrier() { builtin::reveal_hide_internal_path_(C::<_>::member) }
"#,
        true,
        "a receiver placeholder is not bound to an actual native type-parameter slot",
    );
}

#[test]
fn other_receiver_arguments_are_preserved_as_unsupported() {
    refused(
        "receiver_concrete",
        r#"
struct G<T>(std::marker::PhantomData<T>);
impl<T> G<T> { fn member() {} }
#[verus::internal(reveal_fn)] fn carrier() { builtin::reveal_hide_internal_path_(G::<u8>::member) }
"#,
        true,
        "only pure inference placeholders are represented in receiver arguments",
    );
    refused(
        "receiver_computation",
        r#"
struct C<const N: usize>;
impl<const N: usize> C<N> { fn member() {} }
#[verus::internal(reveal_fn)] fn carrier() { builtin::reveal_hide_internal_path_(C::<{ 1 + 2 }>::member) }
"#,
        true,
        "nested owners or extra bodies in a function-identity helper",
    );
    refused(
        "receiver_constraint",
        r#"
struct G<T>(std::marker::PhantomData<T>);
impl<T> G<T> { fn member() {} }
#[verus::internal(reveal_fn)] fn carrier() { builtin::reveal_hide_internal_path_(G::<Item = u8>::member) }
"#,
        true,
        "receiver binding constraints or parenthesized arguments are not discarded",
    );
}

#[test]
fn receiver_lookup_requires_unique_and_visible_native_declarations() {
    refused(
        "receiver_ambiguous",
        r#"
struct G<T>(std::marker::PhantomData<T>);
impl G<u8> { fn member() {} }
impl G<u16> { fn member() {} }
#[verus::internal(reveal_fn)] fn carrier() { builtin::reveal_hide_internal_path_(G::<_>::member) }
"#,
        true,
        "the native receiver/member identity has multiple inherent declarations",
    );
    refused(
        "receiver_private",
        r#"
mod hidden {
    pub struct G<T>(std::marker::PhantomData<T>);
    impl<T> G<T> { fn member() {} }
}
#[verus::internal(reveal_fn)] fn carrier() { builtin::reveal_hide_internal_path_(hidden::G::<_>::member) }
"#,
        true,
        "the native declaration is not visible from the identity helper's scope",
    );
}
