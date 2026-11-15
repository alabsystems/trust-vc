//! The ty protocol lane agrees with an explicit-state oracle on random raw
//! protocol obligations.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Each case is a spec over `x, y \in Int`, `b \in BOOLEAN` and
//! `c \subseteq 0..3` with a finite reachable state space: actions with
//! guards, `\E` binders, floor division and modulus on negative operands,
//! variables drawn from set filters (over an interval, over SUBSET, or over
//! `\X` through a tuple pattern `<<p, q>>`; walked lazily or, over a `\cup`,
//! built whole; inline, from a module operator with a parameter, or, for `c`,
//! read in the successor: `c' \in Q'`, `c' \in ({s \in SUBSET S : P})'`),
//! module operators with parameters, LET, and invariants and properties that
//! use ENABLED, `[]`, `<>`, `[]<>`, `~>`, action properties and
//! `WF_vars(Next)`. The oracle (`protocol_oracle/`)
//! shares no code with ty. A case must come back as the oracle says: no
//! `Verified` where it finds a violation, no counterexample where it finds
//! none or naming an obligation that holds, including where ENABLED meets a
//! filter whose predicate reads a bound name (which the in-process lane
//! refused; the run's `check-enabled-contract-v1` now carries it). Other
//! errors from ty are fail-closed and only counted; a run with no qualifying
//! `ty` fails the test.
//!
//! Moving to another `ty` build runs it at scale on both and compares the
//! per-case verdicts:
//!
//! ```text
//! TRUST_VC_TY_BIN=<build>/ty TRUST_VC_TY_ORACLE_CASES=20000 \
//! TRUST_VC_TY_ORACLE_SEED=<seed> TRUST_VC_TY_ORACLE_VERDICTS=<build>.tsv \
//!   targo --unverified test --locked -p trust-vc-core --features ty \
//!   --test protocol_lane_oracle -- --nocapture
//! ```
//!
//! Requires the `ty` feature and a `ty` advertising every required
//! capability (`TRUST_VC_TY_BIN`, else `ty` on `PATH`):
//! `targo --unverified test -p trust-vc-core --features ty`

#![cfg(feature = "ty")]

mod common;
mod protocol_oracle;

use std::collections::BTreeMap;
use std::fmt::Write as _;

use protocol_oracle::case::{gen_case, Case};
use protocol_oracle::expr::Rng;
use trust_vc_core::protocol::ProtocolObligation;
use trust_vc_core::verification_bridge::{register_protocol, VerificationPipeline};
use trust_vc_core::VerifyResult;

/// Cases per run unless `TRUST_VC_TY_ORACLE_CASES` says otherwise.
const DEFAULT_CASES: u64 = 2000;

fn run(case: &Case) -> VerifyResult {
    common::with_clean_verification(|| {
        register_protocol(ProtocolObligation {
            name: "F".into(),
            spec: case.spec.clone(),
            config: case.config.clone(),
            shape: None,
        });
        VerificationPipeline::collect_from_macros().verify()
    })
}

fn setting(name: &str, default: u64) -> u64 {
    match std::env::var(name) {
        Ok(value) => value
            .parse()
            .unwrap_or_else(|_| panic!("{name}={value} is not a number")),
        Err(_) => default,
    }
}

fn class(result: &VerifyResult) -> String {
    match result {
        VerifyResult::Verified => "Verified".to_string(),
        VerifyResult::Counterexample {
            obligation_name, ..
        } => format!("Counterexample:{obligation_name}"),
        VerifyResult::Error { message } => {
            let head: String = message.chars().take(72).collect();
            format!("Error:{head}")
        }
        other => {
            let head: String = format!("{other:?}").chars().take(72).collect();
            format!("Other:{head}")
        }
    }
}

/// What the case's result is, or why it disagrees with the oracle.
fn judge(case: &Case, result: &VerifyResult) -> Result<&'static str, String> {
    let outcome = against_oracle(case, result).map_err(str::to_string)?;
    Ok(match (case.enabled_open_filter, outcome) {
        (true, "Verified") => "Verified: ENABLED over an open filter",
        (true, "Counterexample") => "Counterexample: ENABLED over an open filter",
        (_, outcome) => outcome,
    })
}

/// `result` against the oracle's verdict alone.
fn against_oracle(case: &Case, result: &VerifyResult) -> Result<&'static str, &'static str> {
    match result {
        VerifyResult::Verified if case.violated.is_empty() => Ok("Verified"),
        VerifyResult::Verified => Err("UNSOUND: Verified, the oracle finds a violation"),
        VerifyResult::Counterexample { .. } if case.violated.is_empty() => {
            Err("a counterexample to a spec the oracle verifies")
        }
        VerifyResult::Counterexample {
            obligation_name, ..
        } if case.violated.contains(obligation_name.as_str()) => Ok("Counterexample"),
        VerifyResult::Counterexample { .. } => {
            Err("the counterexample names an obligation that holds")
        }
        VerifyResult::Error { message } if common::no_qualifying_ty(message) => {
            Err("no qualifying ty ran")
        }
        VerifyResult::Error { message }
            if message.contains("refused the spec") || message.contains("config refused") =>
        {
            Err("the lane did not read the generated spec")
        }
        VerifyResult::Error { message } if !common::ty_declined(message) => {
            Err("the lane and ty disagree about the run's document")
        }
        _ => Ok("fail-closed error or unknown"),
    }
}

#[test]
fn the_ty_lane_agrees_with_an_explicit_state_oracle() {
    let cases = setting("TRUST_VC_TY_ORACLE_CASES", DEFAULT_CASES);
    let seed = setting("TRUST_VC_TY_ORACLE_SEED", 0x5eed);
    let mut rng = Rng(seed);
    let mut verdicts = String::new();
    let mut outcomes: BTreeMap<&str, u64> = BTreeMap::new();
    let mut kinds: BTreeMap<String, u64> = BTreeMap::new();
    let mut failures = Vec::new();
    let mut reasons: BTreeMap<String, u64> = BTreeMap::new();
    let mut largest = 0;
    for index in 0..cases {
        let case = gen_case(&mut rng);
        largest = largest.max(case.reachable);
        *kinds.entry(case.kind.clone()).or_default() += 1;
        let result = run(&case);
        let _ = writeln!(verdicts, "{index}\t{}", class(&result));
        match judge(&case, &result) {
            Ok(outcome) => *outcomes.entry(outcome).or_default() += 1,
            Err(reason) => {
                failures.push(format!(
                    "case {index} (seed {seed}): {reason}\noracle: violated {:?}, {} reachable \
                     state(s)\nlane: {result:?}\n{}{}",
                    case.violated, case.reachable, case.spec, case.config
                ));
                *reasons.entry(reason).or_default() += 1;
            }
        }
    }
    if let Ok(path) = std::env::var("TRUST_VC_TY_ORACLE_VERDICTS") {
        std::fs::write(&path, &verdicts).unwrap_or_else(|error| panic!("write {path}: {error}"));
    }
    eprintln!(
        "ty lane vs oracle, seed {seed}, {cases} case(s), up to {largest} reachable state(s): \
         {outcomes:?}, disagreements {reasons:?}"
    );
    for (kind, count) in &kinds {
        eprintln!("  {kind}: {count}");
    }
    assert!(
        failures.is_empty(),
        "{} disagreement(s); the first:\n{}",
        failures.len(),
        failures
            .iter()
            .take(3)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n---\n")
    );
}
