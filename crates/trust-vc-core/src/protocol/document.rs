//! What a `ty check` run answered, as a [`VerifyResult`].
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! The run's JSON document is read by the fields `ty` freezes under
//! `check-json-contract-v2` (ty's `docs/check-consumer-contract.md`). Every
//! rule below fails closed: a run that breaks one is an `Error`, never
//! `Verified` and never a counterexample.
//!
//! 1. The process exited (no signal) and wrote exactly one JSON object on
//!    stdout.
//! 2. `tool` is `ty`, `mode` is absent (an engine-specific document), and
//!    `version` is a string, recorded and never compared.
//! 3. The document's own `capabilities` hold every one of
//!    [`REQUIRED_CAPABILITIES`] and none of [`RETIRED_CAPABILITIES`]: a
//!    separate probe could describe another binary or another environment,
//!    and `ty --version` does not tell a build with them from one without.
//! 4. A `cli_error` means `ty` did not read the spec (a lexical, syntax,
//!    lowering or semantic error, a name declared twice); the spec is
//!    refused.
//! 5. `source`: `ty` read exactly these bytes (`sha256`), nothing but
//!    whitespace lies outside the checked module (`root_module_bytes`), the
//!    file holds one module, every module loaded beside it is one of the
//!    standard modules [`source`] admits,
//!    no unit name repeats, every name the config gives is an operator the
//!    module defines without parameters, and a `#[protocol]` module declares
//!    and defines exactly what was emitted ([`ProtocolShape`]).
//! 6. `specification` checks what was asked: the same `INIT` and `NEXT`, and
//!    the same invariants and properties.
//! 7. `soundness` is `sound`, with no deviation.
//! 8. Status and exit agree, as below.

use std::collections::BTreeMap;

use serde_json::Value;

use super::config::Request;
use super::run::Run;
use super::ProtocolShape;
use crate::{UnknownCategory, VerifyResult};

#[path = "document_source.rs"]
mod source;
use source::source;

/// What the document of a run must advertise: its fields, flags and exit
/// table (`check-json-contract-v2`), that `ty` refuses a spec it did not read
/// as written (`check-exact-source-v2`), that it decides `ENABLED` by its
/// contract (`check-enabled-contract-v1`), that `--no-cache` neither reads
/// nor writes the result cache (`check-no-cache-v1`), and that a search that
/// stopped before it proved anything exits 5 (`check-exit-incomplete-v1`).
pub(crate) const REQUIRED_CAPABILITIES: [&str; 5] = [
    "check-json-contract-v2",
    "check-exact-source-v2",
    "check-enabled-contract-v1",
    "check-no-cache-v1",
    "check-exit-incomplete-v1",
];

/// Names `ty` builds advertised with promises they did not keep (ty's
/// contract, "Retired names"): a document carrying one is refused whatever
/// else it carries.
pub(crate) const RETIRED_CAPABILITIES: [&str; 2] =
    ["check-json-contract-v1", "check-exact-source-v1"];

/// What the run was asked.
pub(super) struct Expected<'a> {
    pub(super) name: &'a str,
    pub(super) spec: &'a str,
    pub(super) request: &'a Request,
    pub(super) shape: Option<&'a ProtocolShape>,
}

/// A run that yields no verdict: `ty <what> for protocol '<name>': <detail>`.
#[derive(Debug)]
struct Refusal {
    what: &'static str,
    detail: String,
}

fn refuse(what: &'static str, detail: impl Into<String>) -> Refusal {
    Refusal {
        what,
        detail: detail.into(),
    }
}

/// The verdict of `run`, or an `Error` naming the first rule it broke.
pub(super) fn judge(expected: &Expected<'_>, run: &Run) -> VerifyResult {
    verdict(expected, run).unwrap_or_else(|Refusal { what, detail }| VerifyResult::Error {
        message: format!("ty {what} for protocol '{}': {detail}", expected.name),
    })
}

fn verdict(expected: &Expected<'_>, run: &Run) -> Result<VerifyResult, Refusal> {
    let bin = run.bin.display();
    let Some(exit) = run.exit else {
        return Err(refuse(
            "run failed",
            format!("{bin} was ended by a signal{}", stderr_tail(run)),
        ));
    };
    let document = one_document(&run.stdout).map_err(|detail| {
        refuse(
            "output refused",
            format!("{detail} ({bin}, exit {exit}){}", stderr_tail(run)),
        )
    })?;
    envelope(&document)?;
    capabilities(&document, run)?;
    let result = &document["result"];
    if result["error_type"] == "cli_error" {
        return Err(refuse("refused the spec", error_text(&document)));
    }
    source(&document, expected)?;
    specification(&document, expected.request)?;
    soundness(&document)?;
    outcome(&document, exit, expected)
}

/// Exactly one JSON object.
fn one_document(stdout: &[u8]) -> Result<Value, String> {
    let text = std::str::from_utf8(stdout).map_err(|_| "stdout is not UTF-8".to_string())?;
    if text.trim().is_empty() {
        return Err("stdout is empty".to_string());
    }
    // `from_str` refuses anything after the first value: two documents too.
    let value: Value = serde_json::from_str(text)
        .map_err(|error| format!("stdout is not one JSON document: {error}"))?;
    if !value.is_object() {
        return Err("stdout is JSON but not an object".to_string());
    }
    Ok(value)
}

fn envelope(document: &Value) -> Result<(), Refusal> {
    if document["tool"] != "ty" {
        return Err(refuse(
            "output refused",
            format!("`tool` is {}, not \"ty\"", document["tool"]),
        ));
    }
    if let Some(mode) = document.get("mode") {
        return Err(refuse(
            "output refused",
            format!("`mode` is {mode}: an engine-specific document, not the default engine's"),
        ));
    }
    if !document["version"].is_string() {
        return Err(refuse("output refused", "`version` is not a string"));
    }
    if !document["result"].is_object() {
        return Err(refuse("output refused", "the document has no `result`"));
    }
    Ok(())
}

fn capabilities(document: &Value, run: &Run) -> Result<(), Refusal> {
    let advertised: Vec<&str> = document["capabilities"]
        .as_array()
        .map(|list| list.iter().filter_map(Value::as_str).collect())
        .unwrap_or_default();
    let retired: Vec<&str> = RETIRED_CAPABILITIES
        .into_iter()
        .filter(|name| advertised.contains(name))
        .collect();
    if !retired.is_empty() {
        return Err(refuse(
            "capabilities refused",
            format!(
                "the run's document advertises the retired {} (ty {}, {}): its promises did not \
                 hold; build TY main and set {}",
                retired.join(", "),
                document["build"]["version"]
                    .as_str()
                    .unwrap_or("of unknown version"),
                run.bin.display(),
                super::binary::BIN_VAR,
            ),
        ));
    }
    let missing: Vec<&str> = REQUIRED_CAPABILITIES
        .into_iter()
        .filter(|required| !advertised.contains(required))
        .collect();
    if missing.is_empty() {
        return Ok(());
    }
    Err(refuse(
        "capabilities missing",
        format!(
            "the run's document lacks {} (it advertises [{}]; ty {}, {}): build TY main and set \
             {}",
            missing.join(", "),
            advertised.join(", "),
            document["build"]["version"]
                .as_str()
                .unwrap_or("of unknown version"),
            run.bin.display(),
            super::binary::BIN_VAR,
        ),
    ))
}

fn specification(document: &Value, request: &Request) -> Result<(), Refusal> {
    let spec = &document["specification"];
    let multiset = |names: Vec<&str>| {
        names.into_iter().fold(BTreeMap::new(), |mut counts, name| {
            *counts.entry(name.to_string()).or_insert(0_u32) += 1;
            counts
        })
    };
    let asked = |names: &[String]| multiset(names.iter().map(String::as_str).collect());
    if spec["init"] != request.init.as_str()
        || spec["next"] != request.next.as_str()
        || multiset(strings(&spec["invariants"])) != asked(&request.invariants)
        || multiset(strings(&spec["properties"])) != asked(&request.properties)
    {
        return Err(refuse(
            "configuration mismatch",
            format!(
                "ty checked INIT {} NEXT {} INVARIANT {} PROPERTY {}, not the configuration \
                 written",
                spec["init"], spec["next"], spec["invariants"], spec["properties"]
            ),
        ));
    }
    Ok(())
}

fn soundness(document: &Value) -> Result<(), Refusal> {
    let soundness = &document["soundness"];
    let deviations = strings(&soundness["deviations"]);
    if soundness["mode"] != "sound" || !soundness["deviations"].is_array() || !deviations.is_empty()
    {
        return Err(refuse(
            "soundness refused",
            format!(
                "mode {}, deviations [{}]",
                soundness["mode"],
                deviations.join("; ")
            ),
        ));
    }
    Ok(())
}

fn outcome(document: &Value, exit: i32, expected: &Expected<'_>) -> Result<VerifyResult, Refusal> {
    let result = &document["result"];
    let status = result["status"].as_str().unwrap_or("");
    let verdict = result.get("verdict");
    let error_type = result["error_type"].as_str();
    match (status, exit, error_type) {
        ("ok", 0, None) => {
            if let Some(verdict) = verdict {
                return Err(refuse(
                    "result refused",
                    format!("an `ok` result with verdict {verdict}"),
                ));
            }
            if document["completeness"] != "exhaustive" {
                return Err(refuse(
                    "result refused",
                    format!(
                        "the search was not exhaustive: completeness {}",
                        document["completeness"]
                    ),
                ));
            }
            let statistics = &document["statistics"];
            let (Some(initial), Some(suppressed)) = (
                statistics["states_initial"].as_u64(),
                statistics["suppressed_guard_errors"].as_u64(),
            ) else {
                return Err(refuse(
                    "result refused",
                    "`statistics` lacks `states_initial` or `suppressed_guard_errors`",
                ));
            };
            // Under check-json-contract-v2 an `ok` counts the initial states
            // its search or inductive proof started from, and a model with
            // none is `vacuous`: an `ok` with none proves nothing.
            if initial == 0 {
                return Err(refuse(
                    "found no initial state",
                    "every property holds vacuously",
                ));
            }
            if suppressed > 0 {
                return Err(refuse(
                    "read an action error as a disabled action",
                    format!(
                        "{suppressed} action evaluation error(s) were treated as a disabled \
                         action: the states past them were not explored"
                    ),
                ));
            }
            Ok(VerifyResult::Verified)
        }
        (
            "error",
            1,
            Some(kind @ ("invariant_violation" | "property_violation" | "liveness_violation")),
        ) => {
            let name = result["violated_property"]["name"].as_str().unwrap_or("");
            let request = expected.request;
            let requested = request.invariants.iter().chain(&request.properties);
            if !requested.into_iter().any(|asked| asked == name) {
                return Err(refuse(
                    "result refused",
                    format!("ty reports `{name}` violated, which the config does not check"),
                ));
            }
            let length = trace_length(document)?;
            let model = if kind == "liveness_violation" {
                let loop_start = document["counterexample"]["loop_start"]
                    .as_u64()
                    .filter(|start| (1..=length).contains(start))
                    .ok_or_else(|| {
                        refuse(
                            "result refused",
                            "a liveness counterexample without a `loop_start` in its trace",
                        )
                    })?;
                // The listing may end with a repeat of the `loop_start`
                // state that closes the cycle, so its length over-counts it.
                format!(
                    "liveness: {} prefix state(s), cycle from state {loop_start} to state {length}",
                    loop_start - 1,
                )
            } else {
                format!("{length} state(s) in trace")
            };
            Ok(VerifyResult::Counterexample {
                obligation_name: name.to_string(),
                location: None,
                model: Some(model),
                bindings: Vec::new(),
            })
        }
        ("error", 1, Some("deadlock")) => {
            if expected.request.check_deadlock == Some(false) {
                return Err(refuse(
                    "result refused",
                    "a deadlock reported with CHECK_DEADLOCK FALSE",
                ));
            }
            Ok(VerifyResult::Counterexample {
                obligation_name: "deadlock_freedom".into(),
                location: None,
                model: Some(format!("{} state(s) in trace", trace_length(document)?)),
                bindings: Vec::new(),
            })
        }
        ("limit_reached", 5, Some(reason)) if verdict == Some(&Value::from("incomplete")) => {
            Ok(VerifyResult::unknown(
                format!(
                    "ty stopped before it proved anything for protocol '{}': {reason}",
                    expected.name
                ),
                Some(UnknownCategory::SolverUnknown),
            ))
        }
        ("vacuous", _, _) => Err(refuse("found no initial state", error_text(document))),
        ("error", _, _) => Err(refuse("check error", error_text(document))),
        _ => Err(refuse(
            "result refused",
            format!(
                "status {status:?} with error_type {error_type:?}, verdict {} and exit {exit}",
                verdict.unwrap_or(&Value::Null)
            ),
        )),
    }
}

/// The 1-based length of the run's counterexample.
fn trace_length(document: &Value) -> Result<u64, Refusal> {
    let counterexample = &document["counterexample"];
    let length = counterexample["length"]
        .as_u64()
        .filter(|length| *length >= 1);
    let states = counterexample["states"].as_array().map(Vec::len);
    match (length, states) {
        (Some(length), Some(states)) if states as u64 == length => Ok(length),
        _ => Err(refuse(
            "result refused",
            "a violation without a counterexample trace",
        )),
    }
}

/// `<error_type>: <error_code>: <error_message>`, and the first diagnostic.
fn error_text(document: &Value) -> String {
    let result = &document["result"];
    let mut text = format!(
        "{}: {}: {}",
        result["error_type"].as_str().unwrap_or("?"),
        result["error_code"].as_str().unwrap_or("?"),
        result["error_message"].as_str().unwrap_or("")
    );
    if let Some(first) = document["diagnostics"]["errors"][0]["message"].as_str() {
        text.push_str(&format!(" (first diagnostic: {first})"));
    }
    text
}

fn strings(value: &Value) -> Vec<&str> {
    value
        .as_array()
        .map(|list| list.iter().filter_map(Value::as_str).collect())
        .unwrap_or_default()
}

fn stderr_tail(run: &Run) -> String {
    let stderr = String::from_utf8_lossy(&run.stderr);
    let stderr = stderr.trim();
    if stderr.is_empty() {
        return String::new();
    }
    let tail: String = stderr
        .chars()
        .rev()
        .take(400)
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .collect();
    format!("; stderr: {tail}")
}

#[cfg(test)]
#[path = "document_tests.rs"]
mod tests;
