// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (sets.rs `test_set_fold_singleton` / `test_set_fold_two_insert_sum`,
//! 2026-09-13): `Set::fold` over a CONCRETE `Set::empty().insert(e_1)…insert(e_n)`
//! chain is encoded by finite instantiation — the literal cardinality `n` as the
//! fold range when the `e_i` are pairwise-distinct BV literals, membership as the
//! literal disjunction over the `e_i`, no surjection witness for `n <= 4`, and the
//! ground step instances in place of the quantified step axiom when `n <= 4`.
//! Before, the singleton fold timed out at the 30 s wall in every retry (724 s for
//! the sets suite) and the two-insert sum hit the same wall behind it.
//!
//! The liars pin that the finite form still refutes a wrong sum, that a DUPLICATE
//! insert is not double-counted (the pairwise-distinct guard: `insert(9).insert(9)`
//! keeps the tracked cardinality instead of the literal `2`), that the fold is not
//! order-sensitive, and that a five-element chain (past the ground depth of four)
//! never verifies a wrong sum — it fails closed as `unknown (incomplete)` today.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_sffc_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, SRC).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

const SRC: &str = r#"
use trust_vc_types::{Set, SpecFn};

#[trust_vc::ensures(true)]
fn singleton_sum_verifies() {
    trust_vc::assert!(
        Set::<usize>::empty()
            .insert(9usize)
            .fold(0usize, SpecFn::new(|p: usize, a: usize| p + a))
            == 9usize
    );
}

#[trust_vc::ensures(true)]
fn singleton_wrong_sum_liar() {
    trust_vc::assert!(
        Set::<usize>::empty()
            .insert(9usize)
            .fold(0usize, SpecFn::new(|p: usize, a: usize| p + a))
            == 10usize
    );
}

#[trust_vc::ensures(true)]
fn two_insert_sum_reversed_order_verifies() {
    trust_vc::assert!(
        Set::<usize>::empty()
            .insert(7usize)
            .insert(4usize)
            .fold(0usize, SpecFn::new(|p: usize, a: usize| p + a))
            == 11usize
    );
}

#[trust_vc::ensures(true)]
fn two_insert_wrong_sum_liar() {
    trust_vc::assert!(
        Set::<usize>::empty()
            .insert(4usize)
            .insert(7usize)
            .fold(0usize, SpecFn::new(|p: usize, a: usize| p + a))
            == 12usize
    );
}

#[trust_vc::ensures(true)]
fn three_insert_count_verifies() {
    trust_vc::assert!(
        Set::<usize>::empty()
            .insert(1usize)
            .insert(2usize)
            .insert(3usize)
            .fold(0usize, SpecFn::new(|p: usize, a: usize| p + 1usize))
            == 3usize
    );
}

#[trust_vc::ensures(true)]
fn three_insert_wrong_count_liar() {
    trust_vc::assert!(
        Set::<usize>::empty()
            .insert(1usize)
            .insert(2usize)
            .insert(3usize)
            .fold(0usize, SpecFn::new(|p: usize, a: usize| p + 1usize))
            == 4usize
    );
}

// SOUNDNESS: a duplicate insert is one element. The literal cardinality `2` would
// double-count it; the pairwise-distinct guard must keep the tracked length.
#[trust_vc::ensures(true)]
fn duplicate_insert_double_count_liar() {
    trust_vc::assert!(
        Set::<usize>::empty()
            .insert(9usize)
            .insert(9usize)
            .fold(0usize, SpecFn::new(|p: usize, a: usize| p + a))
            == 18usize
    );
}

// SOUNDNESS: past the ground depth (five elements) a wrong sum never verifies.
#[trust_vc::ensures(true)]
fn five_insert_wrong_sum_liar() {
    trust_vc::assert!(
        Set::<usize>::empty()
            .insert(1usize)
            .insert(2usize)
            .insert(3usize)
            .insert(4usize)
            .insert(5usize)
            .fold(0usize, SpecFn::new(|p: usize, a: usize| p + a))
            == 16usize
    );
}
"#;

#[test]
fn singleton_sum_verifies() {
    let r = verify("c1", "singleton_sum_verifies");
    assert!(
        matches!(r, VerifyResult::Verified),
        "`{{9}}.fold(0, +) == 9` must verify; got {r:?}"
    );
}

#[test]
fn singleton_wrong_sum_liar_is_refuted() {
    let r = verify("l1", "singleton_wrong_sum_liar");
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "CARDINAL: `{{9}}.fold(0, +) == 10` must be refuted; got {r:?}"
    );
}

#[test]
fn two_insert_sum_reversed_order_verifies() {
    let r = verify("c2", "two_insert_sum_reversed_order_verifies");
    assert!(
        matches!(r, VerifyResult::Verified),
        "`{{7, 4}}.fold(0, +) == 11` must verify; got {r:?}"
    );
}

#[test]
fn two_insert_wrong_sum_liar_is_refuted() {
    let r = verify("l2", "two_insert_wrong_sum_liar");
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "CARDINAL: `{{4, 7}}.fold(0, +) == 12` must be refuted; got {r:?}"
    );
}

#[test]
fn three_insert_count_verifies() {
    let r = verify("c3", "three_insert_count_verifies");
    assert!(
        matches!(r, VerifyResult::Verified),
        "`{{1, 2, 3}}.fold(0, |p, _| p + 1) == 3` must verify; got {r:?}"
    );
}

#[test]
fn three_insert_wrong_count_liar_is_refuted() {
    let r = verify("l3", "three_insert_wrong_count_liar");
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "CARDINAL: `{{1, 2, 3}}.fold(0, |p, _| p + 1) == 4` must be refuted; got {r:?}"
    );
}

#[test]
fn duplicate_insert_double_count_liar_is_refuted() {
    let r = verify("l4", "duplicate_insert_double_count_liar");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL (soundness): `{{9, 9}}.fold(0, +) == 18` double-counts a duplicate insert and must never verify; got {r:?}"
    );
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "`{{9, 9}}.fold(0, +) == 18` should be refuted; got {r:?}"
    );
}

#[test]
fn five_insert_wrong_sum_liar_fails_closed_or_is_refuted() {
    let r = verify("l5", "five_insert_wrong_sum_liar");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL (soundness): `{{1..5}}.fold(0, +) == 16` must never verify; got {r:?}"
    );
    // Target: a Counterexample. Today: past the ground depth of four the
    // ordering cells `4..` are unconstrained and ay answers `unknown
    // (incomplete)` — pinned so a change is visible.
    match &r {
        VerifyResult::Counterexample { .. } => {}
        VerifyResult::NotProved { reason, .. } | VerifyResult::Unknown { reason, .. } => assert!(
            reason.contains("unknown (incomplete)"),
            "`{{1..5}}.fold(0, +) == 16` should fail closed as ay's `unknown (incomplete)` (or be refuted); got {r:?}"
        ),
        other => panic!("`{{1..5}}.fold(0, +) == 16` should fail closed or be refuted; got {other:?}"),
    }
}
