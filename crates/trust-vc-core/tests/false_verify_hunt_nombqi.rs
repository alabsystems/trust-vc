// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! FALSE-VERIFY HUNT for the ay `work/nombqi` lift (the `no_mbqi` admission in
//! `const_interp_cert_inner`).
//!
//! Every program here is one whose correct verdict is NOT `Verified`. Each test
//! PRINTS the verdict tag it actually got (run with `--nocapture` and diff the
//! two ay revisions) and asserts only the soundness half: never `Verified`.
//!
//! The real ported corpus files are driven directly, so the cases the lift was
//! commissioned for are measured as programs, not as replicas.

use trust_vc_core::{verify_function_from_file, VerifyResult};

/// Repo root, derived from this crate's manifest dir so the file is not tied to
/// one machine's checkout path.
fn repo_root() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
}

fn tag(r: &Result<VerifyResult, impl std::fmt::Debug>) -> String {
    match r {
        Ok(VerifyResult::Verified) => "VERIFIED".to_string(),
        Ok(VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        }) => format!(
            "counterexample[obligation={obligation_name}, model={}]",
            if model.is_some() { "yes" } else { "none" }
        ),
        Ok(other) => format!("{other:?}")
            .split_whitespace()
            .next()
            .unwrap_or("other")
            .to_string(),
        Err(e) => format!("ERR({e:?})").chars().take(60).collect(),
    }
}

fn is_verified(r: &Result<VerifyResult, impl std::fmt::Debug>) -> bool {
    matches!(r, Ok(VerifyResult::Verified))
}

fn port(file: &str, func: &str) -> Result<VerifyResult, String> {
    let path = repo_root().join("evals/verus/ported").join(file);
    verify_function_from_file(path.to_str().expect("utf8 path"), func).map_err(|e| e.to_string())
}

fn src(tmp_id: &str, func: &str, code: &str) -> Result<VerifyResult, String> {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_fvh_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, code).expect("write fixture");
    let r = verify_function_from_file(p.to_str().expect("utf8"), func).map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&p);
    r
}

// ---------------------------------------------------------------------------
// 1. THE SIX CASES, from the real ported files. Upstream verdict: FAILS.
// ---------------------------------------------------------------------------

#[test]
fn ported_choose_fails_cases_never_verify() {
    let cases: &[(&str, &str)] = &[
        ("choose.rs", "test1_fails1"),
        ("choose.rs", "test1_fails2"),
        ("choose.rs", "test1_fails3"),
        ("choose.rs", "test_refine_fail1"),
        ("choose_tuple.rs", "test1_fails1_tuple"),
        ("choose_tuple.rs", "test1_fails2_tuple"),
        ("choose_tuple.rs", "test1_fails3_tuple"),
        ("choose_tuple.rs", "test_refine_fail1_tuple"),
    ];
    let mut bad = Vec::new();
    for (file, func) in cases {
        let r = port(file, func);
        println!("PORT-FAILS {file}::{func} => {}", tag(&r));
        if is_verified(&r) {
            bad.push(format!("{file}::{func}"));
        }
    }
    assert!(
        bad.is_empty(),
        "FALSE VERIFIED on upstream-FAILS cases: {bad:?}"
    );
}

#[test]
fn ported_choose_ok_cases_report() {
    // Not a soundness assertion — a completeness readout, printed for the diff.
    let cases: &[(&str, &str)] = &[
        ("choose.rs", "test1_choose"),
        ("choose.rs", "test1_choose_inference"),
        ("choose.rs", "test1_choose_eq"),
        ("choose.rs", "test_refine"),
        ("choose.rs", "test_refine2"),
        ("choose_tuple.rs", "test1_tuple_choose"),
        ("choose_tuple.rs", "test1_tuple_choose_eq"),
        ("choose_tuple.rs", "test_refine_tuple"),
        ("choose_tuple.rs", "test_refine2_tuple"),
    ];
    for (file, func) in cases {
        let r = port(file, func);
        println!("PORT-OK {file}::{func} => {}", tag(&r));
    }
}

// ---------------------------------------------------------------------------
// 2. HYPOTHESIS-SIDE ATTACKS. Facts that make the negated goal UNSAT only if a
//    witness is ASSUMED to exist. Every one must stay non-`Verified`.
// ---------------------------------------------------------------------------

const PRELUDE: &str = r#"
#![allow(dead_code)]
use trust_vc_types::{int, nat};

#[trust_vc::spec]
fn f(i: int) -> bool { 5 <= i }

#[trust_vc::spec]
fn f2(i: int, j: int) -> bool { i <= j }

#[trust_vc::spec]
fn p(i: int) -> bool { i == 3 }

#[trust_vc::spec]
fn rel(i: int, j: int) -> bool { i <= j }
"#;

fn prog(body: &str) -> String {
    format!("{PRELUDE}\n#[trust_vc::ensures(true)]\nfn test() {{\n{body}\n}}\n")
}

/// Each case: (id, body, why it must not verify).
fn attack_cases() -> Vec<(&'static str, String)> {
    vec![
        // The witness axiom itself, witnessless: `f(i)` on the chosen `i`.
        (
            "a_witnessless_predicate",
            prog("    let i: int = trust_vc::choose!(|i: int| f(i));\n    trust_vc::assert!(f(i));"),
        ),
        // Same, multi-binder (the documented flip's shape).
        (
            "b_witnessless_predicate_tuple",
            prog("    let (i, j): (int, int) = trust_vc::choose!(|i: int, j: int| f2(i, j));\n    trust_vc::assert!(f2(i, j));"),
        ),
        // A disjunction that is valid ONLY under the witness: `5 <= i` or `i < 0`
        // leaves `i == 2` open when the witness is withheld.
        (
            "c_disjunctive_consequence",
            prog("    let i: int = trust_vc::choose!(|i: int| f(i));\n    trust_vc::assert!(f(i) || i < 0);"),
        ),
        // Singleton-witness predicate: `p(i)` forces `i == 3` only if the witness
        // fires; without it `i` is arbitrary.
        (
            "d_singleton_witness_pins_value",
            prog("    let i: int = trust_vc::choose!(|i: int| p(i));\n    trust_vc::assert!(i == 3);"),
        ),
        // Contrapositive shape: the negated goal is UNSAT only with the witness.
        (
            "e_negated_goal_needs_witness",
            prog("    let i: int = trust_vc::choose!(|i: int| p(i));\n    trust_vc::assert!(i != 4);"),
        ),
        // Assumed existence, but the claim does NOT follow from the witness.
        (
            "f_assumed_existence_wrong_claim",
            prog("    trust_vc::assume!(exists|i: int, j: int| rel(i, j));\n    let (a, b): (int, int) = trust_vc::choose!(|i: int, j: int| rel(i, j));\n    trust_vc::assert!(rel(b, a));"),
        ),
        // Assumed existence, arbitrary value pinned (choose.rs test1_fails2).
        (
            "g_assumed_existence_arbitrary_value",
            prog("    trust_vc::assume!(exists|i: int, j: int| rel(i, j));\n    let (a, _b): (int, int) = trust_vc::choose!(|i: int, j: int| rel(i, j));\n    trust_vc::assert!(a == 7);"),
        ),
        // Two witnessless chooses over EXTENSIONALLY equal predicates are not the
        // same value (choose.rs test1_fails3 shape).
        (
            "h_extensional_equality_of_two_chooses",
            prog("    let i1: int = trust_vc::choose!(|i: int| f(i) && (2 + 2 == 4));\n    let i2: int = trust_vc::choose!(|i: int| (2 + 2 == 4) && f(i));\n    trust_vc::assert!(i1 == i2);"),
        ),
        // nat refinement: the chosen nat is NOT negative (test_refine_fail1).
        (
            "i_nat_refinement_negative_claim",
            prog("    let n: nat = trust_vc::choose!(|n: nat| p(n as int) && n < 0);\n    trust_vc::assert!((n as int) < 0);"),
        ),
    ]
}

#[test]
fn hypothesis_side_attacks_never_verify() {
    let mut bad = Vec::new();
    for (id, code) in attack_cases() {
        let r = src(id, "test", &code);
        println!("ATTACK {id} => {}", tag(&r));
        if is_verified(&r) {
            bad.push(id);
        }
    }
    assert!(
        bad.is_empty(),
        "FALSE VERIFIED on hypothesis-side attacks: {bad:?}"
    );
}
