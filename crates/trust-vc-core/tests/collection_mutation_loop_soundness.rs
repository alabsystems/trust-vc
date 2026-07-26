// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness guards for in-place collection mutation that the positive
//! `is_known_mutating_method` allow-list omitted (`retain`/`drain`/`dedup`/
//! `extend`/`sort`/`reverse`/`rotate_*`/`fill`/`split_off`).
//!
//! Two catastrophic false-`Verified` shapes are pinned here:
//!
//! 1. LOOP frame: a `while` loop whose body mutates a `Vec` via an omitted
//!    method left the receiver OUT of `modified_vars`, so the frame condition
//!    pinned `v == v_pre` and ANY invariant about `v` was trivially "preserved"
//!    even when the body broke it — escalating to a proven-false post-loop
//!    `assert`. The conservative collection-mutation default now records the
//!    receiver as modified, so the false invariant is no longer inductive.
//!
//! 2. STRAIGHT-LINE `&mut` collection postcondition: a `&mut Vec` parameter is
//!    not a `supported_mut_ref` scalar, so a bare occurrence in an `ensures`
//!    resolved to the ENTRY snapshot. A method mutation (`clear`/`push`/…) was
//!    not threaded into that snapshot, so the postcondition was checked against
//!    the pre-call state. This shape now fails closed.
//!
//! Both directions are asserted: the false shapes must NOT verify, and the
//! legitimate shapes (recognized mutators unchanged, pure reads, true loops,
//! owned-param entry-value postconditions, unmutated `&mut` params) must be
//! unaffected.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
// ---------- (1) LOOP frame: omitted mutators must NOT be wrongly framed ----------
// Guard is an independent counter so the inductive step actually exercises the
// body's mutation of `v` (not vacuous under invariant && guard).

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn loop_retain_false_invariant(v: &mut Vec<u64>, n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(v.len() == 5usize);
        v.retain(|_x| false);
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 5usize);
}

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn loop_drain_false_invariant(v: &mut Vec<u64>, n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(v.len() == 5usize);
        v.drain(0usize..1usize);
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 5usize);
}

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn loop_dedup_false_invariant(v: &mut Vec<u64>, n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(v.len() == 5usize);
        v.dedup();
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 5usize);
}

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn loop_extend_false_invariant(v: &mut Vec<u64>, w: Vec<u64>, n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(v.len() == 5usize);
        v.extend(w.iter());
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 5usize);
}

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn loop_sort_false_invariant(v: &mut Vec<u64>, n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(v.len() == 5usize && v.index(0usize) == 7u64);
        v.sort();
        i = i + 1usize;
    }
    trust_vc::assert!(v.index(0usize) == 7u64);
}

// CONTROL: recognized mutators were already correctly framed; still NOT verified.
#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn loop_push_false_invariant(v: &mut Vec<u64>, n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(v.len() == 5usize);
        v.push(1u64);
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 5usize);
}

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn loop_clear_false_invariant(v: &mut Vec<u64>, n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(v.len() == 5usize);
        v.clear();
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 5usize);
}

// ---------- (1) NO OVER-REJECTION: legitimate loops must still verify ----------

// A pure `&self` read (`len`) in the body must NOT invalidate the receiver, so a
// true invariant about it is still framed and verifies.
#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn loop_pure_read_true_invariant(v: &mut Vec<u64>, n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(v.len() == 5usize);
        let _l = v.len();
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 5usize);
}

// A plain true scalar loop is unaffected.
#[trust_vc::requires(n == 10u64)]
#[trust_vc::ensures(true)]
fn loop_plain_true_scalar(mut i: u64, n: u64) {
    while i < n {
        trust_vc::invariant!(n == 10u64);
        i = i + 1u64;
    }
    trust_vc::assert!(i >= 10u64);
}

// A loop that DOES mutate the collection (push) but whose invariant is a true
// fact about an unrelated scalar still verifies — havocking `v` must not break
// invariants that do not depend on `v`.
#[trust_vc::requires(n == 3u64)]
#[trust_vc::ensures(true)]
fn loop_push_true_scalar_invariant(v: &mut Vec<u64>, mut i: u64, n: u64) {
    while i < n {
        trust_vc::invariant!(n == 3u64);
        v.push(1u64);
        i = i + 1u64;
    }
    trust_vc::assert!(i >= 3u64);
}

// ---------- (1b) EXPLICIT-DEREF receiver `(*v).m(..)` in a loop body ----------
// The loop modified-var collector resolved the receiver via `expr_path_ident`,
// which strips paren/group but NOT the deref `*`, so `(*v).<mutator>()` was
// never recorded as modifying `v`. The frame then pinned `v == v_pre` and a
// false invariant about `v` was trivially "preserved" — a false Verified even
// for a RECOGNIZED mutator like `(*v).clear()`. Now resolved to `v`.

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn deref_loop_retain_false_invariant(v: &mut Vec<u64>, n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(v.len() == 5usize);
        (*v).retain(|_x| false);
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 5usize);
}

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn deref_loop_clear_false_invariant(v: &mut Vec<u64>, n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(v.len() == 5usize);
        (*v).clear();
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 5usize);
}

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn deref_loop_drain_false_invariant(v: &mut Vec<u64>, n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(v.len() == 5usize);
        (*v).drain(0usize..1usize);
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 5usize);
}

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn deref_loop_push_false_invariant(v: &mut Vec<u64>, n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(v.len() == 5usize);
        (*v).push(1u64);
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 5usize);
}

// ---------- (1b) NO OVER-REJECTION: pure reads through a deref ----------

// `(*v).len()` is a pure `&self` read through the deref; a true invariant about
// `v` must still be framed and verify (receiver NOT havoced).
#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn deref_loop_pure_len_true_invariant(v: &mut Vec<u64>, n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(v.len() == 5usize);
        let _l = (*v).len();
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 5usize);
}

// `(*v).get(i)` is a pure `&self` read through the deref; a true invariant must
// still verify.
#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn deref_loop_pure_get_true_invariant(v: &mut Vec<u64>, n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(v.len() == 5usize);
        let _g = (*v).get(0usize);
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 5usize);
}

// ---------- (2) STRAIGHT-LINE `&mut` collection postcondition ----------
// A bare `&mut` collection param mutated by a method call must fail closed.

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(v.len() == 5usize)]
fn straight_mut_clear_false_ensures(v: &mut Vec<u64>) {
    v.clear();
}

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(v.len() == 5usize)]
fn straight_mut_push_false_ensures(v: &mut Vec<u64>) {
    v.push(1u64);
}

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(v.len() == 5usize)]
fn straight_mut_truncate_false_ensures(v: &mut Vec<u64>) {
    v.truncate(0usize);
}

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(v.len() == 5usize)]
fn straight_mut_retain_false_ensures(v: &mut Vec<u64>) {
    v.retain(|_x| false);
}

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(v.len() == 5usize)]
fn straight_mut_extend_false_ensures(v: &mut Vec<u64>, w: Vec<u64>) {
    v.extend(w.iter());
}

// ---------- (2) NO OVER-REJECTION ----------

// Owned (by-value) param: the entry-value postcondition is Verus-faithful for an
// owned parameter and must stay verified.
#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(v.len() == 5usize)]
fn straight_owned_clear_entry_value(mut v: Vec<u64>) {
    v.clear();
}

// `&mut` collection param that is NOT mutated: entry == final, so the
// postcondition is sound and must stay verified.
#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(v.len() == 5usize)]
fn straight_mut_not_mutated_ok(v: &mut Vec<u64>) {
    let _l = v.len();
}

// REGRESSION: a `&mut [T; N]` const-generic-length array is modeled
// symbolically; the `&mut` collection postcondition guard must extract its NAME
// (not run the type-rejecting pattern extractor) so it never spuriously errors.
#[trust_vc::requires(ar.len() == 3usize)]
#[trust_vc::ensures(true)]
fn mut_const_generic_array_pure_read_ok<const N: usize>(ar: &mut [u64; N]) {
    let _l = ar.len();
}
"####;

fn run(func: &str) -> VerifyResult {
    let dir = std::env::temp_dir().join("trust_vc_collection_mutation_soundness");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{func}.rs"));
    let mut f = std::fs::File::create(&path).unwrap();
    f.write_all(SRC.as_bytes()).unwrap();
    drop(f);
    verify_function_from_file(path.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    })
}

fn assert_not_verified(func: &str) {
    let r = run(func);
    assert!(
        !r.is_verified(),
        "{func} must NOT verify (false postcondition / invariant), got Verified"
    );
}

fn assert_verified(func: &str) {
    let r = run(func);
    assert!(
        r.is_verified(),
        "{func} must verify (legitimate, no over-rejection), got: {r:?}"
    );
}

// ---- (1) Catastrophic loop direction: omitted mutators must NOT verify ----

#[test]
fn loop_retain_false_invariant_is_not_verified() {
    assert_not_verified("loop_retain_false_invariant");
}

#[test]
fn loop_drain_false_invariant_is_not_verified() {
    assert_not_verified("loop_drain_false_invariant");
}

#[test]
fn loop_dedup_false_invariant_is_not_verified() {
    assert_not_verified("loop_dedup_false_invariant");
}

#[test]
fn loop_extend_false_invariant_is_not_verified() {
    assert_not_verified("loop_extend_false_invariant");
}

#[test]
fn loop_sort_false_invariant_is_not_verified() {
    assert_not_verified("loop_sort_false_invariant");
}

#[test]
fn loop_push_false_invariant_is_not_verified() {
    assert_not_verified("loop_push_false_invariant");
}

#[test]
fn loop_clear_false_invariant_is_not_verified() {
    assert_not_verified("loop_clear_false_invariant");
}

// ---- (1) No over-rejection ----

#[test]
fn loop_pure_read_true_invariant_verifies() {
    assert_verified("loop_pure_read_true_invariant");
}

#[test]
fn loop_plain_true_scalar_verifies() {
    assert_verified("loop_plain_true_scalar");
}

#[test]
fn loop_push_true_scalar_invariant_verifies() {
    assert_verified("loop_push_true_scalar_invariant");
}

// ---- (1b) Explicit-deref receiver `(*v).m(..)` loop: must NOT verify ----

#[test]
fn deref_loop_retain_false_invariant_is_not_verified() {
    assert_not_verified("deref_loop_retain_false_invariant");
}

#[test]
fn deref_loop_clear_false_invariant_is_not_verified() {
    assert_not_verified("deref_loop_clear_false_invariant");
}

#[test]
fn deref_loop_drain_false_invariant_is_not_verified() {
    assert_not_verified("deref_loop_drain_false_invariant");
}

#[test]
fn deref_loop_push_false_invariant_is_not_verified() {
    assert_not_verified("deref_loop_push_false_invariant");
}

// ---- (1b) No over-rejection: pure reads through a deref ----

#[test]
fn deref_loop_pure_len_true_invariant_verifies() {
    assert_verified("deref_loop_pure_len_true_invariant");
}

#[test]
fn deref_loop_pure_get_true_invariant_verifies() {
    assert_verified("deref_loop_pure_get_true_invariant");
}

// ---- (2) Straight-line `&mut` collection postcondition: must NOT verify ----

#[test]
fn straight_mut_clear_false_ensures_is_not_verified() {
    assert_not_verified("straight_mut_clear_false_ensures");
}

#[test]
fn straight_mut_push_false_ensures_is_not_verified() {
    assert_not_verified("straight_mut_push_false_ensures");
}

#[test]
fn straight_mut_truncate_false_ensures_is_not_verified() {
    assert_not_verified("straight_mut_truncate_false_ensures");
}

#[test]
fn straight_mut_retain_false_ensures_is_not_verified() {
    assert_not_verified("straight_mut_retain_false_ensures");
}

#[test]
fn straight_mut_extend_false_ensures_is_not_verified() {
    assert_not_verified("straight_mut_extend_false_ensures");
}

// ---- (2) No over-rejection ----

#[test]
fn straight_owned_clear_entry_value_verifies() {
    assert_verified("straight_owned_clear_entry_value");
}

#[test]
fn straight_mut_not_mutated_ok_verifies() {
    assert_verified("straight_mut_not_mutated_ok");
}

#[test]
fn mut_const_generic_array_pure_read_does_not_spuriously_error() {
    // The guard must not raise a `&mut`-collection two-state error here, and the
    // symbolic-length array param must not trip a pattern-extraction error.
    let r = run("mut_const_generic_array_pure_read_ok");
    assert!(
        !matches!(&r, VerifyResult::Error { message } if message.contains("two-state postcondition")),
        "const-generic &mut array must not trip the collection postcondition guard, got: {r:?}"
    );
    assert!(
        r.is_verified(),
        "const-generic &mut array pure read with ensures(true) should verify, got: {r:?}"
    );
}
