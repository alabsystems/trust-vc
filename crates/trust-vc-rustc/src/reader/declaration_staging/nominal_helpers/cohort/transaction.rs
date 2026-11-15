// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Explicit, ignored-test-only controls over an actual producer transaction.
//! No observation or fixture can construct a native scope or pending fact.

use std::path::PathBuf;
use std::sync::Mutex;

use super::*;

mod cases;
mod fixture;
mod genuine;
mod mutation;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Case {
    Reversible,
    Drop,
    Diagnostics,
    Unwind,
}

impl Case {
    fn name(self) -> &'static str {
        match self {
            Self::Reversible => "reversible",
            Self::Drop => "drop",
            Self::Diagnostics => "diagnostics",
            Self::Unwind => "unwind",
        }
    }
}

#[derive(Default)]
struct Report {
    entered: bool,
    finished_owned: Option<usize>,
    rollback_failed: bool,
    cases: Vec<Value>,
}

type Sink = Arc<Mutex<Report>>;

fn record(sink: &Sink, name: &str, detail: Value) -> Result<(), String> {
    let mut state = sink
        .lock()
        .map_err(|_| "the test outcome lock is poisoned")?;
    state.cases.push(json!({"case": name, "detail": detail}));
    Ok(())
}

fn rejected<T>(result: Result<T, String>, expected: &str) -> Result<(), String> {
    match result {
        Err(reason) if reason == expected => Ok(()),
        Err(reason) => Err(format!("expected {expected:?}, observed {reason:?}")),
        Ok(_) => Err(format!(
            "a test mismatch escaped as an owned result: {expected}"
        )),
    }
}

/// Only the ignored native tests below can create this fixed case runner.
/// Its owned alternate Inputs also come from the real fresh constructor.
pub(in crate::reader::declaration_staging) struct Probe {
    case: Case,
    output: PathBuf,
    alternate: Option<Box<Inputs>>,
    sink: Sink,
}

struct UnwindTag;

const DROPPED: &str = "the explicit transaction control dropped its uncommitted scope";
const DIAGNOSTIC: &str = "explicit helper transaction diagnostic revocation control";

impl Probe {
    pub(super) fn finish<'tcx>(
        self,
        scope: Cohort<'_, 'tcx>,
        pending: BTreeMap<NativeKey, PendingHelpers>,
    ) -> Result<BTreeMap<NativeKey, OwnedHelpers>, String> {
        if scope.inputs.output != self.output {
            return Err("the transaction control reached another actual producer output".into());
        }
        scope.current(scope.tcx, scope.inputs, scope.metadata)?;
        if pending.is_empty() || (self.case == Case::Reversible && pending.len() < 2) {
            return Err(
                "the genuine transaction control needs actual pending nominal facts".into(),
            );
        }
        {
            let mut state = self
                .sink
                .lock()
                .map_err(|_| "the test outcome lock is poisoned")?;
            if state.entered {
                return Err("the owned transaction probe was entered twice".into());
            }
            state.entered = true;
        }
        record(
            &self.sink,
            "genuine_pending_setup",
            json!({
            "pending_nominals": pending.len(),
            "generated_helpers": pending.values().map(|fact| fact.helpers.len()).sum::<usize>(),
            "scope": "transaction ownership, not generated-helper language qualification"}),
        )?;
        match self.case {
            Case::Reversible => {
                let alternate = self
                    .alternate
                    .as_deref()
                    .ok_or("the reversible control lacks separately constructed Inputs")?;
                cases::reversible(&scope, &pending, alternate, &self.sink)?;
                let result = scope.finish(pending);
                if let Ok(owned) = &result {
                    let mut state = self
                        .sink
                        .lock()
                        .map_err(|_| "the test outcome lock is poisoned")?;
                    state.finished_owned = Some(owned.len());
                }
                result
            }
            Case::Drop => {
                drop(pending);
                drop(scope);
                record(
                    &self.sink,
                    "drop_without_finish",
                    json!({"owned_result": false}),
                )?;
                Err(DROPPED.into())
            }
            Case::Diagnostics => {
                // No compiler query follows this diagnostic except finish's
                // error gate; reporting below only reads owned Rust data.
                let _ = scope.tcx.dcx().err(DIAGNOSTIC);
                let result = scope.finish(pending);
                rejected(
                    result,
                    "native compiler diagnostics reject this staging phase",
                )?;
                record(
                    &self.sink,
                    "diagnostics_revoke",
                    json!({"owned_result": false}),
                )?;
                Err("the explicit transaction diagnostic control was rejected".into())
            }
            Case::Unwind => {
                record(
                    &self.sink,
                    "unwind_before_finish",
                    json!({"owned_result": false}),
                )?;
                // This is outside every native query and lock. The dedicated
                // test catches only this payload after compiler teardown.
                std::panic::panic_any(UnwindTag)
            }
        }
    }
}
