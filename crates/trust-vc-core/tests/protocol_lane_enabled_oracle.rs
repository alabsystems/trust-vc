//! The ty protocol lane never answers `Verified` (nor refutes) against the
//! meaning of ENABLED, on the shapes ty's ENABLED review cited and on
//! generated modules.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! ty decides `ENABLED A` by a witness search. Two reviews of that search
//! found it wrong in both directions: a prime read before the witness
//! assigns it (read from the current state), `~ENABLED B` as a conjunct of an
//! action (read the action's own successor), a LET definition or operator
//! argument read under a prime (read in the current state), a filter built
//! under a prime. The lane used to refuse those shapes on ty's AST; across
//! the process boundary it requires `check-enabled-contract-v1` of every run
//! instead, and this test holds that capability to the meaning of ENABLED.
//! The cases come from `protocol_enabled_oracle/`, ty's own semantic oracle
//! carried unchanged: modules over `x \in 0..3`, `y \in SUBSET (1..3)`,
//! `z \in (1..2) \X (1..2)`, judged against a model that brute-forces every
//! successor (no ty code).
//!
//! * `Verified` must be the model's verdict, and a counterexample must name
//!   `Inv` where the model finds `Inv` violated;
//! * an error from ty (a prime read before its ENABLED witness assigns it,
//!   where TLC raises too) is fail-closed and counted, except on a reviewed
//!   shape TLC answers, which ty must answer;
//! * a run with no qualifying `ty`, or that did not read the module, fails.
//!
//! `TRUST_VC_ENABLED_ORACLE_CASES` (default 300) and
//! `TRUST_VC_ENABLED_ORACLE_SEED` (default 1) choose the generated cases;
//! `TRUST_VC_ENABLED_ORACLE_VERDICTS=<file>` writes one verdict line per
//! case, to compare two `ty` builds case by case.
//!
//! Requires the `ty` feature and a `ty` advertising every required
//! capability (`TRUST_VC_TY_BIN`, else `ty` on `PATH`):
//! `targo --unverified test -p trust-vc-core --features ty`

#![cfg(feature = "ty")]

mod common;
mod protocol_enabled_oracle;

use std::collections::BTreeMap;
use std::fmt::Write as _;

use protocol_enabled_oracle::ast::{Module, St};
use protocol_enabled_oracle::model::{explore, Exploration, Model};
use protocol_enabled_oracle::{cases, gen, model, print, shapes};
use trust_vc_core::protocol::ProtocolObligation;
use trust_vc_core::verification_bridge::{register_protocol, VerificationPipeline};
use trust_vc_core::VerifyResult;

const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";

fn run(src: &str) -> VerifyResult {
    common::with_clean_verification(|| {
        register_protocol(ProtocolObligation {
            name: "E".into(),
            spec: src.to_string(),
            config: CFG.into(),
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

#[derive(Debug, Clone, PartialEq, Eq)]
enum Judged {
    Agree,
    /// An error or unknown from ty: no verdict.
    FailClosed(String),
    Unsound(&'static str),
    /// No qualifying `ty` ran, or it did not read the generated module: a
    /// defect of this test's setup, never an answer.
    NotRun(String),
}

fn judge(ex: &Exploration, result: &VerifyResult) -> Judged {
    match result {
        VerifyResult::Verified if ex.violating.is_empty() => Judged::Agree,
        VerifyResult::Verified => Judged::Unsound("Verified, the model finds Inv violated"),
        VerifyResult::Counterexample { .. } if ex.violating.is_empty() => {
            Judged::Unsound("a counterexample to an Inv that holds")
        }
        VerifyResult::Counterexample {
            obligation_name, ..
        } if obligation_name == "Inv" => Judged::Agree,
        VerifyResult::Counterexample { .. } => {
            Judged::Unsound("the counterexample names an obligation other than Inv")
        }
        VerifyResult::Error { message }
            if common::no_qualifying_ty(message)
                || message.contains("refused the spec")
                || message.contains("config refused") =>
        {
            Judged::NotRun(message.clone())
        }
        VerifyResult::Error { message } if common::ty_declined(message) => {
            // `ty check error for protocol 'E': <error_type>: <error_code>: ...`
            let code = message
                .split(": ")
                .nth(2)
                .unwrap_or_default()
                .chars()
                .take(40)
                .collect::<String>();
            Judged::FailClosed(format!("{} {code}", common::lane_rule(message)))
        }
        VerifyResult::Error { message } => Judged::NotRun(message.clone()),
        other => Judged::FailClosed(format!("{other:?}").chars().take(60).collect()),
    }
}

fn model_answer(m: &Module, universe: &[St]) -> Exploration {
    let model = Model::new(&m.defs, universe);
    explore(&model, &m.init, &m.next, &m.inv).unwrap_or_else(|e| {
        panic!(
            "the model cannot evaluate a generated module: {e:?}\n{}",
            print::module_text(m, "O")
        )
    })
}

/// Every reviewed shape and its twin: never a wrong answer, and an answer
/// wherever TLC gives one.
#[test]
fn reviewed_shapes_agree_with_the_semantics() {
    let universe = model::universe();
    let mut report = String::new();
    let mut wrong = Vec::new();
    for case in cases::all() {
        let ex = model_answer(&case.module, &universe);
        let src = print::module_text(&case.module, "O");
        let judged = judge(&ex, &run(&src));
        let _ = writeln!(
            report,
            "{:<22} model={:<8} tlc-answers={:<5} lane={judged:?}",
            case.name,
            if ex.violating.is_empty() {
                "holds"
            } else {
                "violated"
            },
            case.must_answer
        );
        if let Judged::NotRun(why) = &judged {
            panic!("{}: {why}\n{src}", case.name);
        }
        let answered = judged == Judged::Agree;
        if matches!(judged, Judged::Unsound(_)) || (case.must_answer && !answered) {
            wrong.push(case.name);
        }
    }
    eprintln!("{report}");
    assert!(
        wrong.is_empty(),
        "wrong, or no answer where TLC answers: {wrong:?}\n{report}"
    );
}

/// Seeded generated modules: no wrong answer.
#[test]
fn generated_modules_agree_with_the_model() {
    let cases = setting("TRUST_VC_ENABLED_ORACLE_CASES", 300);
    let seed = setting("TRUST_VC_ENABLED_ORACLE_SEED", 1);
    let universe = model::universe();
    let mut counts: BTreeMap<String, u64> = BTreeMap::new();
    let mut by_shape: BTreeMap<&'static str, u64> = BTreeMap::new();
    let mut verdicts = String::new();
    let mut first_wrong = Vec::new();
    for index in 0..cases {
        let mut rng = gen::Rng::new(seed.wrapping_mul(1_000_003).wrapping_add(index));
        let m = gen::Gen::module(&mut rng);
        let ex = model_answer(&m, &universe);
        let src = print::module_text(&m, "O");
        let judged = judge(&ex, &run(&src));
        let class = match &judged {
            Judged::Agree => "agree".to_string(),
            Judged::FailClosed(rule) => format!("fail-closed: {rule}"),
            Judged::Unsound(why) => format!("UNSOUND: {why}"),
            Judged::NotRun(why) => panic!("case {index} did not run: {why}\n{src}"),
        };
        let _ = writeln!(verdicts, "s{seed}c{index}\t{class}");
        *counts.entry(class).or_default() += 1;
        if let Judged::Unsound(why) = judged {
            for shape in shapes::features(&m) {
                *by_shape.entry(shape).or_default() += 1;
            }
            if first_wrong.len() < 3 {
                first_wrong.push(format!("case {index}: {why}\n{src}"));
            }
        }
    }
    if let Ok(path) = std::env::var("TRUST_VC_ENABLED_ORACLE_VERDICTS") {
        std::fs::write(&path, &verdicts).unwrap_or_else(|error| panic!("write {path}: {error}"));
    }
    let wrong: u64 = counts
        .iter()
        .filter(|(class, _)| class.starts_with("UNSOUND"))
        .map(|(_, n)| n)
        .sum();
    eprintln!(
        "ty lane vs ENABLED model, seed {seed}, {cases} case(s): {counts:?}; wrong answers by \
         shape {by_shape:?}"
    );
    assert_eq!(
        wrong,
        0,
        "wrong answers; the first:\n{}",
        first_wrong.join("\n---\n")
    );
}
