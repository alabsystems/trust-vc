// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CONCRETE GROUND FILTER: `seq![intlit, ..].filter(SpecFn::new(|x| PRED))` where
//! every element is an integer literal and `PRED` folds to a definite bool per
//! element now renders the concrete kept `seq![..]` at extraction, so downstream
//! `.contains`/`.len`/`.index` hit the WORKING fixed-array path instead of the
//! Skolemized filter-result quantifier (which non-terminates on positive
//! membership — the pre-existing `seqs.rs` `filter_lemmas` red, recovered here;
//! the harness went red→green AND 91s→5s).
//!
//! SOUND BY CONSTRUCTION: a literal-vs-literal comparison folds EXACTLY to the
//! spec (mathematical) truth, so every TRUE claim verifies and every FALSE claim
//! (a dropped element, a wrong length) must COUNTEREXAMPLE — the cardinal
//! never-false-verify property. Anything not exactly evaluable — a non-ground
//! receiver, a non-literal element, arithmetic in the predicate, an unsuffixed
//! all-dropped result — DECLINES to the opaque filter (→ NotProved, fail-closed),
//! never guesses.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(name: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_seqfilter_{}_{}.rs", std::process::id(), name));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), "t").unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

// --- TRUE claims: must VERIFY ---------------------------------------------

const KEEP_PRESENT: &str = r#"
#[trust_vc::ensures(true)]
fn t() { trust_vc::assert!(trust_vc_types::seq![10i32, 45i32].filter(trust_vc_types::SpecFn::new(|x: i32| x < 40i32)).contains(10i32)); }
"#;
const KEPT_LEN: &str = r#"
#[trust_vc::ensures(true)]
fn t() { trust_vc::assert!(trust_vc_types::seq![10i32, 45i32].filter(trust_vc_types::SpecFn::new(|x: i32| x < 40i32)).len() == 1int); }
"#;
const DROP_THEN_PACK_INDEX: &str = r#"
#[trust_vc::ensures(true)]
fn t() { trust_vc::assert!(trust_vc_types::seq![45i32, 10i32].filter(trust_vc_types::SpecFn::new(|x: i32| x < 40i32)).index(0usize) == 10i32); }
"#;
const AND_PREDICATE_KEEP: &str = r#"
#[trust_vc::ensures(true)]
fn t() { trust_vc::assert!(trust_vc_types::seq![10i32, 45i32, 5i32].filter(trust_vc_types::SpecFn::new(|x: i32| x < 40i32 && x > 7i32)).contains(10i32)); }
"#;
const ALL_EXCLUDED_LEN_ZERO: &str = r#"
#[trust_vc::ensures(true)]
fn t() { trust_vc::assert!(trust_vc_types::seq![45i32, 55i32].filter(trust_vc_types::SpecFn::new(|x: i32| x < 40i32)).len() == 0usize); }
"#;

// --- FALSE claims: must COUNTEREXAMPLE (cardinal never-false-verify) -------

const DROPPED_ABSENT: &str = r#"
#[trust_vc::ensures(true)]
fn t() { trust_vc::assert!(trust_vc_types::seq![10i32, 45i32].filter(trust_vc_types::SpecFn::new(|x: i32| x < 40i32)).contains(45i32)); }
"#;
const WRONG_LEN: &str = r#"
#[trust_vc::ensures(true)]
fn t() { trust_vc::assert!(trust_vc_types::seq![10i32, 45i32].filter(trust_vc_types::SpecFn::new(|x: i32| x < 40i32)).len() == 2int); }
"#;
const AND_DROPPED: &str = r#"
#[trust_vc::ensures(true)]
fn t() { trust_vc::assert!(trust_vc_types::seq![10i32, 45i32, 5i32].filter(trust_vc_types::SpecFn::new(|x: i32| x < 40i32 && x > 7i32)).contains(5i32)); }
"#;
const EMPTY_CONTAINS: &str = r#"
#[trust_vc::ensures(true)]
fn t() { trust_vc::assert!(trust_vc_types::seq![45i32, 55i32].filter(trust_vc_types::SpecFn::new(|x: i32| x < 40i32)).contains(45i32)); }
"#;

// --- DECLINE cases: not exactly foldable -> opaque filter -> NotProved -----

const ARITH_PREDICATE_DECLINES: &str = r#"
#[trust_vc::ensures(true)]
fn t() { trust_vc::assert!(trust_vc_types::seq![10i32, 45i32].filter(trust_vc_types::SpecFn::new(|x: i32| x * 2i32 < 40i32)).contains(10i32)); }
"#;
const UNSUFFIXED_EMPTY_DECLINES: &str = r#"
#[trust_vc::ensures(true)]
fn t() { trust_vc::assert!(trust_vc_types::seq![45, 55].filter(trust_vc_types::SpecFn::new(|x: i32| x < 40i32)).len() == 0usize); }
"#;

#[test]
fn kept_element_membership_verifies() {
    assert!(matches!(
        verify("keep", KEEP_PRESENT),
        VerifyResult::Verified
    ));
}
#[test]
fn kept_length_verifies() {
    assert!(matches!(verify("len", KEPT_LEN), VerifyResult::Verified));
}
#[test]
fn drop_then_pack_index_verifies() {
    assert!(matches!(
        verify("pack", DROP_THEN_PACK_INDEX),
        VerifyResult::Verified
    ));
}
#[test]
fn and_predicate_kept_verifies() {
    assert!(matches!(
        verify("and", AND_PREDICATE_KEEP),
        VerifyResult::Verified
    ));
}
#[test]
fn all_excluded_empty_len_zero_verifies() {
    assert!(matches!(
        verify("empty0", ALL_EXCLUDED_LEN_ZERO),
        VerifyResult::Verified
    ));
}

#[test]
fn dropped_element_membership_counterexamples() {
    assert!(
        matches!(
            verify("dropped", DROPPED_ABSENT),
            VerifyResult::Counterexample { .. }
        ),
        "CARDINAL: a dropped element's membership must COUNTEREXAMPLE, never verify"
    );
}
#[test]
fn wrong_length_counterexamples() {
    assert!(
        matches!(
            verify("wlen", WRONG_LEN),
            VerifyResult::Counterexample { .. }
        ),
        "CARDINAL: a wrong filtered length must COUNTEREXAMPLE"
    );
}
#[test]
fn and_predicate_dropped_counterexamples() {
    assert!(
        matches!(
            verify("anddrop", AND_DROPPED),
            VerifyResult::Counterexample { .. }
        ),
        "CARDINAL: an AND-predicate-dropped element must COUNTEREXAMPLE"
    );
}
#[test]
fn empty_result_membership_counterexamples() {
    assert!(
        matches!(
            verify("emptyc", EMPTY_CONTAINS),
            VerifyResult::Counterexample { .. }
        ),
        "CARDINAL: an all-dropped (empty) result contains nothing — must COUNTEREXAMPLE"
    );
}

#[test]
fn arithmetic_predicate_declines_to_notproved() {
    // Arithmetic in the predicate is not exactly folded -> opaque filter ->
    // fail-closed (NotProved), never a false-verify.
    assert!(
        !matches!(
            verify("arith", ARITH_PREDICATE_DECLINES),
            VerifyResult::Verified
        ),
        "an arithmetic predicate must NOT verify via concrete eval (declines, fail-closed)"
    );
}
#[test]
fn unsuffixed_empty_declines_to_notproved() {
    assert!(
        !matches!(
            verify("unsuf", UNSUFFIXED_EMPTY_DECLINES),
            VerifyResult::Verified
        ),
        "an unsuffixed all-dropped result cannot infer an element type -> declines, fail-closed"
    );
}
