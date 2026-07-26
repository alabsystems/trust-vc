// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Fixture for the Set/Map extensional-equality precondition-consumption
// soundness regression. Parsed/verified through `verify_function_from_file`,
// exactly like the upstream `maps.rs`/`sets.rs` ports — NOT compiled as a test
// target.

use trust_vc_types::Map;
use trust_vc_types::Set;

// ── VALID precondition-dependent ext-eq lemmas (must Verify) ────────────────

// remove-after-insert identity (=~=): given !s.contains(x).
#[trust_vc::requires(!s.contains(x))]
#[trust_vc::ensures(true)]
fn set_insert_remove_exteq(s: Set<i32>, x: i32) {
    trust_vc::assert!(trust_vc::ext_eq!(s.insert(x).remove(x), s));
}

// remove-after-insert identity (==): given !s.contains(x).
#[trust_vc::requires(!s.contains(x))]
#[trust_vc::ensures(true)]
fn set_insert_remove_eq(s: Set<i32>, x: i32) {
    trust_vc::assert!(s.insert(x).remove(x) == s);
}

// remove no-op (=~=): given !s.contains(x).
#[trust_vc::requires(!s.contains(x))]
#[trust_vc::ensures(true)]
fn set_remove_noop_exteq(s: Set<i32>, x: i32) {
    trust_vc::assert!(trust_vc::ext_eq!(s.remove(x), s));
}

// insert no-op (=~=): given s.contains(x).
#[trust_vc::requires(s.contains(x))]
#[trust_vc::ensures(true)]
fn set_insert_noop_exteq(s: Set<i32>, x: i32) {
    trust_vc::assert!(trust_vc::ext_eq!(s.insert(x), s));
}

// Map generalization (=~=): given m.contains_key(k) && m.get(k)==v.
#[trust_vc::requires(m.contains_key(k))]
#[trust_vc::requires(m.get(k) == v)]
#[trust_vc::ensures(true)]
fn map_insert_noop_exteq(m: Map<i32, i32>, k: i32, v: i32) {
    trust_vc::assert!(trust_vc::ext_eq!(m.insert(k, v), m));
}

// ── Membership-DECOMPOSED form + control (already Verify; establishes the bug
//    is precondition-non-consumption, not incompleteness) ───────────────────

// Decomposed: contains at the differing element, same requires. Verifies.
#[trust_vc::requires(!s.contains(x))]
#[trust_vc::ensures(true)]
fn set_insert_remove_decomposed(s: Set<i32>, x: i32) {
    trust_vc::assert!(s.insert(x).remove(x).contains(x) == s.contains(x));
}

// Control: needs no precondition. Verifies.
#[trust_vc::ensures(true)]
fn set_insert_remove_eq_remove(s: Set<i32>, x: i32) {
    trust_vc::assert!(s.insert(x).remove(x) == s.remove(x));
}

// ── GENUINELY-DIFFERENT (must Counterexample) ──────────────────────────────

// insert no-op WITHOUT the contains precondition: x may not be in s.
#[trust_vc::ensures(true)]
fn set_insert_noop_no_precond(s: Set<i32>, x: i32) {
    trust_vc::assert!(trust_vc::ext_eq!(s.insert(x), s));
}

// Map insert no-op WITHOUT the contains_key&&get==v precondition.
#[trust_vc::ensures(true)]
fn map_insert_noop_no_precond(m: Map<i32, i32>, k: i32, v: i32) {
    trust_vc::assert!(trust_vc::ext_eq!(m.insert(k, v), m));
}

// Variable-rooted remove no-op WITHOUT precondition: x may be in s, so remove
// changes it. Exercises the remove-expansion's refutation on a symbolic base.
#[trust_vc::ensures(true)]
fn set_remove_noop_no_precond(s: Set<i32>, x: i32) {
    trust_vc::assert!(trust_vc::ext_eq!(s.remove(x), s));
}

// Two concretely-different sets.
#[trust_vc::ensures(true)]
fn set_concrete_different() {
    trust_vc::assert!(trust_vc::ext_eq!(
        Set::<i32>::empty().insert(1i32),
        Set::<i32>::empty().insert(2i32)
    ));
}

// Two concretely-different maps.
#[trust_vc::ensures(true)]
fn map_concrete_different() {
    trust_vc::assert!(trust_vc::ext_eq!(
        Map::<i32, i32>::empty().insert(1i32, 1i32),
        Map::<i32, i32>::empty().insert(1i32, 2i32)
    ));
}

// ── WRONG precondition (must Counterexample) ───────────────────────────────
// requires s.contains(x), claim s.insert(x).remove(x) =~= s. False: remove
// drops x, so the result lacks x while s has it.
#[trust_vc::requires(s.contains(x))]
#[trust_vc::ensures(true)]
fn set_insert_remove_wrong_precond(s: Set<i32>, x: i32) {
    trust_vc::assert!(trust_vc::ext_eq!(s.insert(x).remove(x), s));
}
