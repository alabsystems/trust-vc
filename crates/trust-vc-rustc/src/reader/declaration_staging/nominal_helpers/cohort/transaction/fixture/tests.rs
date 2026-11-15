// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Each slow case requires its own explicitly filtered standalone process.

use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};

use super::*;

fn standalone(name: &str) {
    let module = module_path!().split_once("::").unwrap().1;
    let expected = format!("{module}::{name}");
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    for required in [
        expected.as_str(),
        "--exact",
        "--ignored",
        "--test-threads=1",
    ] {
        assert_eq!(
            args.iter().filter(|arg| arg.as_str() == required).count(),
            1,
            "each genuine transaction control requires a single exact standalone invocation"
        );
    }
    assert!(
        args.iter().all(|arg| [
            expected.as_str(),
            "--exact",
            "--ignored",
            "--test-threads=1",
            "--nocapture"
        ]
        .contains(&arg.as_str())),
        "the transaction control does not run beside other unit controls"
    );
}

fn run(case: Case, name: &str) {
    standalone(name);
    let fixture = Fixture::load(case).unwrap();
    fixture.revalidate().unwrap();
    let alternate = fixture
        .alternate
        .as_ref()
        .map(|request| Inputs::load(&request.path).map(Box::new))
        .transpose()
        .unwrap();
    fixture.revalidate().unwrap();
    let sink = Arc::new(Mutex::new(Report::default()));
    let probe = Probe {
        case,
        output: fixture.output.clone(),
        alternate,
        sink: Arc::clone(&sink),
    };
    let attempt = catch_unwind(AssertUnwindSafe(|| {
        crate::reader::declaration_staging::produce_inner(&fixture.request.path, Some(probe))
    }));
    let result = match attempt {
        Err(payload) if case == Case::Unwind && payload.is::<UnwindTag>() => {
            // The compiler and its worker pool have unwound. No native query
            // or subsequent compiler invocation is allowed in this process.
            fixture.revalidate().unwrap();
            fixture
                .write(case, &sink, "ExactPrivateUnwindPayload")
                .unwrap();
            let state = sink.lock().unwrap();
            assert!(state.entered && state.finished_owned.is_none() && !state.rollback_failed);
            assert!(state
                .cases
                .iter()
                .any(|row| row["case"] == "unwind_before_finish"));
            return;
        }
        Err(payload) => {
            let _ = fixture.write(case, &sink, "UnexpectedPanic");
            resume_unwind(payload);
        }
        Ok(result) => result,
    };
    let outcome = match &result {
        Ok(_) => "ReturnedStagedLibrary",
        Err(reason) => reason.as_str(),
    };
    // Persist the actual producer result before any test assertion can fail.
    fixture.write(case, &sink, outcome).unwrap();
    fixture.revalidate().unwrap();
    let state = sink.lock().unwrap();
    assert!(
        state.entered,
        "the actual native pending-map finalizer was not reached"
    );
    assert!(
        !state.rollback_failed,
        "an owned mutation target failed to roll back"
    );
    match case {
        Case::Reversible => {
            let library = result.as_ref().unwrap();
            let count = library.prepared.nominal_helpers.len();
            assert!(count > 0);
            assert_eq!(state.finished_owned, Some(count));
            for name in [
                "different_inputs",
                "different_metadata_object",
                "cross_scope_pending",
                "mixed_pending",
                "wrong_pending_map_owner",
                "mixed_owned",
                "owned_script_bytes",
                "owned_archive_copy_bytes",
                "restored_original_scope",
            ] {
                assert_eq!(
                    state.cases.iter().filter(|row| row["case"] == name).count(),
                    1,
                    "the genuine case {name} was not completed exactly once"
                );
            }
            drop(state);
            library.write_observation().unwrap();
        }
        Case::Drop => {
            assert!(matches!(result, Err(ref error) if error == DROPPED));
            assert!(state.finished_owned.is_none());
            assert!(state
                .cases
                .iter()
                .any(|row| row["case"] == "drop_without_finish"));
        }
        Case::Diagnostics => {
            assert!(result.is_err());
            assert!(state.finished_owned.is_none());
            assert!(state
                .cases
                .iter()
                .any(|row| row["case"] == "diagnostics_revoke"));
            assert!(std::fs::read_to_string(fixture.output.join("phases.jsonl"))
                .unwrap()
                .lines()
                .any(|line| {
                    let row: Value = serde_json::from_str(line).unwrap();
                    row["phase"] == "ConsumeInActualKeepCallback"
                        && row["compiler_result"] == "FatalError"
                        && row["callback"]["state"] == "Rejected"
                }));
        }
        Case::Unwind => panic!("the exact private unwind payload did not propagate"),
    }
}

#[test]
#[ignore = "requires exact fresh staging fixtures and a dedicated admitted native process"]
fn genuine_helper_transaction_associations_and_owned_bytes() {
    run(
        Case::Reversible,
        "genuine_helper_transaction_associations_and_owned_bytes",
    );
}

#[test]
#[ignore = "requires exact fresh staging fixtures and a dedicated admitted native process"]
fn genuine_helper_transaction_drop_without_commit() {
    run(Case::Drop, "genuine_helper_transaction_drop_without_commit");
}

#[test]
#[ignore = "emits a real native diagnostic in a dedicated fresh staging process"]
fn genuine_helper_transaction_diagnostics_revoke_commit() {
    run(
        Case::Diagnostics,
        "genuine_helper_transaction_diagnostics_revoke_commit",
    );
}

#[test]
#[ignore = "unwinds a dedicated fresh staging process using an exact private payload"]
fn genuine_helper_transaction_unwind_without_commit() {
    run(
        Case::Unwind,
        "genuine_helper_transaction_unwind_without_commit",
    );
}
