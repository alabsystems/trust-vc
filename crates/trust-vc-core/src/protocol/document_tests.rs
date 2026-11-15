//! The run-to-verdict mapping over canned documents: each rule's case breaks
//! one field of a document as `ty` writes it, and no case needs a `ty`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use serde_json::{json, Value};
use sha2::{Digest, Sha256};

use super::{judge, Expected, REQUIRED_CAPABILITIES};
use crate::protocol::config::Request;
use crate::protocol::run::Run;
use crate::protocol::ProtocolShape;
use crate::{UnknownCategory, VerifyResult};

const SPEC: &str =
    "---- MODULE Spec ----\nVARIABLE x\nInit == x = 0\nNext == x' = x\nInv == x = 0\n====\n";

fn request() -> Request {
    Request::parse("INIT Init\nNEXT Next\nINVARIANT Inv\n").expect("a valid config")
}

/// A passing document for [`SPEC`], as `ty` writes it.
fn passing() -> Value {
    let digest: String = Sha256::digest(SPEC.as_bytes())
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    json!({
        "version": "1.6",
        "tool": "ty",
        "capabilities": REQUIRED_CAPABILITIES,
        "build": {"version": "0.15.0", "git_sha": "abc", "git_dirty": false},
        "source": {
            "sha256": digest,
            "bytes": SPEC.len(),
            "modules_in_file": ["Spec"],
            "root_module": "Spec",
            "root_module_bytes": {"start": 0, "end": SPEC.trim_end().len()},
            "loaded_modules": [{"name": "Spec", "kind": "root"}],
            "units": [
                {"kind": "variable", "name": "x", "arity": 0, "local": false},
                {"kind": "operator", "name": "Init", "arity": 0, "local": false},
                {"kind": "operator", "name": "Next", "arity": 0, "local": false},
                {"kind": "operator", "name": "Inv", "arity": 0, "local": false},
            ],
        },
        "specification": {
            "init": "Init", "next": "Next", "invariants": ["Inv"], "properties": [],
            "variables": ["x"],
        },
        "soundness": {"mode": "sound", "deviations": []},
        "completeness": "exhaustive",
        "result": {"status": "ok"},
        "statistics": {"states_initial": 1, "suppressed_guard_errors": 0},
    })
}

fn violated(error_type: &str, name: &str, length: usize, loop_start: Option<u64>) -> Value {
    let mut document = passing();
    document["result"] = json!({
        "status": "error",
        "error_type": error_type,
        "error_code": "TLC_INVARIANT_VIOLATED",
        "error_message": "violated",
        "violated_property": {"name": name},
    });
    let states: Vec<Value> = (1..=length).map(|i| json!({"index": i})).collect();
    document["counterexample"] = json!({"length": length, "states": states});
    if let Some(start) = loop_start {
        document["counterexample"]["loop_start"] = json!(start);
    }
    document
}

fn run(exit: Option<i32>, stdout: &str) -> Run {
    Run {
        bin: "/opt/ty/bin/ty".into(),
        exit,
        stdout: stdout.as_bytes().to_vec(),
        stderr: b"stderr text".to_vec(),
    }
}

fn verdict_with(
    request: &Request,
    shape: Option<&ProtocolShape>,
    exit: i32,
    document: &Value,
) -> VerifyResult {
    judge(
        &Expected {
            name: "P",
            spec: SPEC,
            request,
            shape,
        },
        &run(Some(exit), &document.to_string()),
    )
}

fn verdict(exit: i32, document: &Value) -> VerifyResult {
    verdict_with(&request(), None, exit, document)
}

#[track_caller]
fn refused(result: VerifyResult, what: &str, detail: &str) {
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.starts_with(&format!("ty {what} for protocol 'P': ")),
                "{what:?} not the rule in: {message}"
            );
            assert!(message.contains(detail), "{detail:?} not in: {message}");
        }
        other => panic!("expected `ty {what}`, got {other:?}"),
    }
}

#[test]
fn a_passing_document_is_verified_and_each_broken_field_is_refused() {
    assert_eq!(verdict(0, &passing()), VerifyResult::Verified);

    let broken: &[(&str, Value, &str, &str)] = &[
        ("/tool", json!("Ty"), "output refused", "`tool`"),
        ("/version", json!(1.5), "output refused", "`version`"),
        ("/source/sha256", json!("00"), "source refused", "not the"),
        ("/source/bytes", json!(1), "source refused", "not the"),
        (
            "/source/modules_in_file",
            json!(["A", "Spec"]),
            "source refused",
            "2 modules",
        ),
        (
            "/source/loaded_modules",
            json!([{"name": "Spec", "kind": "root"}, {"name": "Lib", "kind": "user"}]),
            "source refused",
            "module Lib from user source",
        ),
        (
            "/source/loaded_modules",
            json!([{"name": "Spec", "kind": "root"}, {"name": "TLC", "kind": "standard"}]),
            "source refused",
            "standard module TLC",
        ),
        (
            "/source/root_module_bytes/end",
            json!(SPEC.find("Inv ==").expect("fixture")),
            "source refused",
            "text outside the module",
        ),
        (
            "/source/root_module_bytes/start",
            json!(SPEC.len() + 1),
            "source refused",
            "text outside the module",
        ),
        (
            "/source/units/3/arity",
            json!(1),
            "config refused",
            "`Inv` is not an operator",
        ),
        (
            "/source/units/3/local",
            json!(true),
            "config refused",
            "`Inv` is not an operator",
        ),
        (
            "/source/units/3/name",
            json!("Init"),
            "source refused",
            "'Init' is declared",
        ),
        (
            "/specification/next",
            json!("Other"),
            "configuration mismatch",
            "NEXT \"Other\"",
        ),
        (
            "/specification/invariants",
            json!(["Inv", "Inv"]),
            "configuration mismatch",
            "",
        ),
        (
            "/specification/properties",
            json!(["Inv"]),
            "configuration mismatch",
            "",
        ),
        (
            "/soundness/mode",
            json!("experimental"),
            "soundness refused",
            "experimental",
        ),
        (
            "/soundness/deviations",
            json!(["por"]),
            "soundness refused",
            "por",
        ),
        (
            "/completeness",
            json!("bounded"),
            "result refused",
            "not exhaustive",
        ),
        (
            "/statistics/states_initial",
            json!(0),
            "found no initial state",
            "vacuously",
        ),
        (
            "/statistics/suppressed_guard_errors",
            json!(2),
            "read an action error as a disabled action",
            "2 action",
        ),
    ];
    for (pointer, value, what, detail) in broken {
        let mut document = passing();
        *document
            .pointer_mut(pointer)
            .unwrap_or_else(|| panic!("{pointer} is in the passing document")) = value.clone();
        refused(verdict(0, &document), what, detail);
    }

    // Absent fields fail closed too.
    for (key, what) in [
        ("/source", "source refused"),
        ("/source/root_module_bytes", "source refused"),
        ("/statistics/suppressed_guard_errors", "result refused"),
        ("/capabilities", "capabilities missing"),
    ] {
        let mut document = passing();
        let (parent, field) = key.rsplit_once('/').expect("a pointer");
        let parent = if parent.is_empty() {
            &mut document
        } else {
            document.pointer_mut(parent).expect("the parent exists")
        };
        parent.as_object_mut().expect("an object").remove(field);
        refused(verdict(0, &document), what, "");
    }
    let mut document = passing();
    document["mode"] = json!("portfolio");
    refused(verdict(0, &document), "output refused", "engine-specific");
    let mut document = passing();
    document["result"]["verdict"] = json!("bounded");
    refused(verdict(0, &document), "result refused", "verdict");
}

#[test]
fn each_missing_capability_is_named() {
    for missing in REQUIRED_CAPABILITIES {
        let mut document = passing();
        document["capabilities"] = json!(REQUIRED_CAPABILITIES
            .iter()
            .filter(|c| **c != missing)
            .collect::<Vec<_>>());
        refused(verdict(0, &document), "capabilities missing", missing);
    }
    // A build advertising a retired name broke its promise: refused even
    // with every required name present.
    for retired in super::RETIRED_CAPABILITIES {
        let mut document = passing();
        document["capabilities"]
            .as_array_mut()
            .expect("an array")
            .push(json!(retired));
        refused(verdict(0, &document), "capabilities refused", retired);
    }
    // TY main from the lane's landing until the -v2 names: the -v1 names
    // only.
    let mut document = passing();
    document["capabilities"] = json!([
        "check-json-contract-v1",
        "check-exact-source-v1",
        "check-enabled-contract-v1",
        "check-no-cache-v1",
        "check-exit-incomplete-v1",
    ]);
    refused(verdict(0, &document), "capabilities refused", "retired");
    // ty 0.15.0 before the ENABLED rework advertised the other capabilities
    // under the same version string.
    let mut document = passing();
    document["capabilities"] = json!(["check-exit-incomplete-v1", "check-no-cache-v1"]);
    refused(
        verdict(0, &document),
        "capabilities missing",
        "ty 0.15.0, /opt/ty/bin/ty",
    );
}

#[test]
fn status_and_exit_must_agree() {
    refused(verdict(1, &passing()), "result refused", "exit 1");
    refused(
        verdict(0, &violated("invariant_violation", "Inv", 2, None)),
        "check error",
        "invariant_violation",
    );
    let mut stopped = passing();
    stopped["result"] =
        json!({"status": "limit_reached", "verdict": "bounded", "error_type": "state_limit"});
    refused(verdict(0, &stopped), "result refused", "bounded");
}

#[test]
fn violations_are_counterexamples_named_by_the_violated_property() {
    match verdict(1, &violated("invariant_violation", "Inv", 3, None)) {
        VerifyResult::Counterexample {
            obligation_name,
            location,
            model,
            bindings,
        } => {
            assert_eq!(obligation_name, "Inv");
            assert_eq!(location, None);
            assert_eq!(model.as_deref(), Some("3 state(s) in trace"));
            assert!(bindings.is_empty());
        }
        other => panic!("{other:?}"),
    }
    // A name the config does not check is not a counterexample to it.
    refused(
        verdict(1, &violated("invariant_violation", "Other", 3, None)),
        "result refused",
        "`Other` violated",
    );
    // A trace whose length disagrees with its states.
    let mut short = violated("invariant_violation", "Inv", 3, None);
    short["counterexample"]["length"] = json!(4);
    refused(verdict(1, &short), "result refused", "trace");

    let live = Request::parse("INIT Init\nNEXT Next\nPROPERTY Inv\n").expect("valid");
    let mut document = violated("liveness_violation", "Inv", 4, Some(3));
    document["specification"]["invariants"] = json!([]);
    document["specification"]["properties"] = json!(["Inv"]);
    match verdict_with(&live, None, 1, &document) {
        VerifyResult::Counterexample { model, .. } => assert_eq!(
            model.as_deref(),
            Some("liveness: 2 prefix state(s), cycle from state 3 to state 4")
        ),
        other => panic!("{other:?}"),
    }
    document["counterexample"]["loop_start"] = json!(5);
    refused(
        verdict_with(&live, None, 1, &document),
        "result refused",
        "loop_start",
    );
}

#[test]
fn deadlock_is_a_counterexample_only_while_deadlock_is_checked() {
    let mut document = violated("deadlock", "", 2, None);
    document["result"]["violated_property"] = Value::Null;
    match verdict(1, &document) {
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => {
            assert_eq!(obligation_name, "deadlock_freedom");
            assert_eq!(model.as_deref(), Some("2 state(s) in trace"));
        }
        other => panic!("{other:?}"),
    }
    let off = Request::parse("INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n")
        .expect("valid");
    refused(
        verdict_with(&off, None, 1, &document),
        "result refused",
        "CHECK_DEADLOCK FALSE",
    );
}

#[test]
fn an_incomplete_search_is_unknown_and_ty_errors_are_errors() {
    let mut document = passing();
    document["result"] =
        json!({"status": "limit_reached", "verdict": "incomplete", "error_type": "memory_limit"});
    document["completeness"] = json!("bounded");
    match verdict(5, &document) {
        VerifyResult::Unknown { reason, category } => {
            assert!(reason.contains("memory_limit"), "{reason}");
            assert_eq!(category, UnknownCategory::SolverUnknown);
        }
        other => panic!("{other:?}"),
    }
    let mut raised = passing();
    raised["result"] = json!({
        "status": "error", "error_type": "runtime_error", "error_code": "TLC_EVAL_ERROR",
        "error_message": "x' is not assigned",
    });
    refused(
        verdict(1, &raised),
        "check error",
        "TLC_EVAL_ERROR: x' is not assigned",
    );
    let mut vacuous = passing();
    vacuous["result"] =
        json!({"status": "vacuous", "error_type": "vacuous", "error_code": "TLC_VACUOUS"});
    refused(
        verdict(3, &vacuous),
        "found no initial state",
        "TLC_VACUOUS",
    );
}

#[test]
fn a_spec_ty_did_not_read_is_refused_before_its_source_is_read() {
    let document = json!({
        "version": "1.5",
        "tool": "ty",
        "capabilities": REQUIRED_CAPABILITIES,
        "result": {
            "status": "error", "error_type": "cli_error", "error_code": "TLA_PARSE_ERROR",
            "error_message": "TLA+ parse failed with 1 error(s)",
        },
        "diagnostics": {"errors": [{"message": "79..81: unrecognized input `¬`"}]},
    });
    refused(
        verdict(2, &document),
        "refused the spec",
        "TLA_PARSE_ERROR: TLA+ parse failed with 1 error(s) (first diagnostic: 79..81: \
         unrecognized input `¬`)",
    );
}

#[test]
fn output_that_is_not_one_document_is_refused() {
    let request = request();
    let expected = Expected {
        name: "P",
        spec: SPEC,
        request: &request,
        shape: None,
    };
    let one = passing().to_string();
    for (stdout, detail) in [
        ("", "stdout is empty"),
        (
            "error: unrecognized subcommand 'capabilities'",
            "not one JSON document",
        ),
        ("[1, 2]", "not an object"),
        (&format!("{one}\n{one}") as &str, "not one JSON document"),
    ] {
        refused(
            judge(&expected, &run(Some(2), stdout)),
            "output refused",
            detail,
        );
    }
    refused(judge(&expected, &run(None, &one)), "run failed", "signal");
    let mut bytes = run(Some(0), "");
    bytes.stdout = vec![0xff, 0xfe];
    refused(judge(&expected, &bytes), "output refused", "UTF-8");
}

#[test]
fn a_generated_module_must_be_exactly_what_was_emitted() {
    let shape = ProtocolShape {
        variables: vec!["x".into()],
        operators: vec!["Next".into(), "Inv".into(), "Init".into()],
    };
    assert_eq!(
        verdict_with(&request(), Some(&shape), 0, &passing()),
        VerifyResult::Verified
    );
    let mut extra = passing();
    extra["source"]["units"]
        .as_array_mut()
        .expect("units")
        .push(json!({"kind": "operator", "name": "Extra", "arity": 0, "local": false}));
    refused(
        verdict_with(&request(), Some(&shape), 0, &extra),
        "source refused",
        "not what was emitted",
    );
    let mut assumed = passing();
    assumed["source"]["units"]
        .as_array_mut()
        .expect("units")
        .push(json!({"kind": "assume", "name": null, "arity": 0, "local": false}));
    refused(
        verdict_with(&request(), Some(&shape), 0, &assumed),
        "source refused",
        "a unit it did not emit",
    );
    let mut extended = passing();
    extended["source"]["loaded_modules"]
        .as_array_mut()
        .expect("loaded")
        .push(json!({"name": "Naturals", "kind": "standard"}));
    refused(
        verdict_with(&request(), Some(&shape), 0, &extended),
        "source refused",
        "2 module(s) loaded",
    );
    // A raw obligation may extend an admitted standard module.
    assert_eq!(verdict(0, &extended), VerifyResult::Verified);
    // Text outside the module may be whitespace only.
    let mut padded = passing();
    padded["source"]["root_module_bytes"]["start"] = json!(0);
    padded["source"]["root_module_bytes"]["end"] = json!(SPEC.len() - 1);
    assert_eq!(verdict(0, &padded), VerifyResult::Verified);
}
