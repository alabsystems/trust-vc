// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness guards for USER-STRUCT receiver mutation — the struct analog of the
//! #62/#63 collection loop-mutation false-`Verified` gap.
//!
//! A struct mutated by a `&mut self` method (`s.bump()`) is neither a recognized
//! collection mutator nor a collection-typed receiver, so the loop modified-var
//! collector left it OUT of `modified_vars` and the straight-line scoped model
//! treated the call as a no-op. The frame then pinned `s == s_pre` (loop) / `s`
//! kept its constrained ENTRY value (straight-line), so a stale read of the
//! receiver was trivially "preserved" — a catastrophic false `Verified`.
//!
//! The fix resolves each impl method's `self` receiver kind (`&mut self` /
//! `&self` / by-value `self`) from the file's impls and:
//!   - records a possibly-mutating struct receiver in the loop modified set
//!     (`loop_modified_vars`), and
//!   - havocs it in the straight-line scoped model (fresh unconstrained symbol),
//!
//! while leaving a pure `&self`/by-value reader untouched (NO over-rejection).
//! An UNKNOWN-signature method on a struct receiver is conservatively treated as
//! mutating (fail-closed) unless it is a universally-pure read.
//!
//! Both directions are pinned: the false shapes must NOT verify, and the
//! legitimate shapes (pure `&self` getter, a universally-pure `clone`, a
//! pre-mutation read, a no-call read) must still verify.

use std::io::Write;
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

const SRC: &str = r####"
struct S { x: u64 }
impl S {
    fn bump(&mut self) { self.x = self.x + 1u64; }
    fn get(&self) -> u64 { self.x }
}

// ---------- STRAIGHT-LINE: &mut self mutation must NOT preserve a stale read ----------

#[trust_vc::requires(s.x == 5u64)]
fn sl_bump_field_false(s: &mut S) {
    s.bump();
    trust_vc::assert!(s.x == 5u64);
}

#[trust_vc::requires(s.x == 5u64)]
fn sl_bump_getter_false(s: &mut S) {
    s.bump();
    trust_vc::assert!(s.get() == 5u64);
}

// Owned receiver: `s.bump()` autorefs `&mut s` and mutates it in place.
#[trust_vc::requires(s.x == 5u64)]
fn sl_owned_bump_field_false(mut s: S) {
    s.bump();
    trust_vc::assert!(s.x == 5u64);
}

// UNKNOWN-signature method (no in-scope impl): conservatively havoc, fail closed.
#[trust_vc::requires(s.x == 5u64)]
fn sl_unknown_field_false(s: &mut S) {
    s.mystery();
    trust_vc::assert!(s.x == 5u64);
}

// ---------- STRAIGHT-LINE: NO over-rejection ----------

// A pure `&self` getter does not mutate the receiver; the true read still verifies.
#[trust_vc::requires(s.x == 5u64)]
fn sl_getter_field_true(s: &mut S) {
    let _g = s.get();
    trust_vc::assert!(s.x == 5u64);
}

// `clone` is a universally-pure read (unknown to the in-file impls): NOT havocked.
#[trust_vc::requires(s.x == 5u64)]
fn sl_clone_then_read_true(s: &mut S) {
    let _c = s.clone();
    trust_vc::assert!(s.x == 5u64);
}

// The read BEFORE the mutation is at the pre-call state and must still verify
// (the havoc is position-aware — it only affects reads AFTER the mutating call).
#[trust_vc::requires(s.x == 5u64)]
fn sl_pre_mutation_assert_true(s: &mut S) {
    trust_vc::assert!(s.x == 5u64);
    s.bump();
}

// No mutating call at all: the entry read verifies.
#[trust_vc::requires(s.x == 5u64)]
fn sl_no_call_true(s: &mut S) {
    trust_vc::assert!(s.x == 5u64);
}

// ---------- POSTCONDITION (ensures): &mut S mutated by a method ----------
// A bare `&mut S` param in `ensures` denotes its FINAL value; the method's
// effect is not threaded, so checking against the entry snapshot is unsound.

#[trust_vc::requires(s.x == 5u64)]
#[trust_vc::ensures(s.x == 5u64)]
fn ens_bump_false(s: &mut S) {
    s.bump();
}

#[trust_vc::requires(s.x == 5u64)]
#[trust_vc::ensures(s.x == 5u64)]
fn ens_unknown_false(s: &mut S) {
    s.mystery();
}

// NO over-rejection: a pure `&self` getter does not mutate, so the ensures holds.
#[trust_vc::requires(s.x == 5u64)]
#[trust_vc::ensures(s.x == 5u64)]
fn ens_getter_true(s: &mut S) {
    let _g = s.get();
}

#[trust_vc::requires(s.x == 5u64)]
#[trust_vc::ensures(s.x == 5u64)]
fn ens_no_call_true(s: &mut S) {}

// ---------- LOOP: a possibly-mutating receiver must NOT be frame-pinned ----------
// (The invariant is a true fact about a parameter so the inductive step is not
// vacuous; the post-loop read of the mutated struct is the false claim.)

#[trust_vc::requires(s.x == 5u64)]
#[trust_vc::requires(n == 3u64)]
fn loop_bump_post_false(s: &mut S, mut i: u64, n: u64) {
    while i < n {
        trust_vc::invariant!(n == 3u64);
        s.bump();
        i = i + 1u64;
    }
    trust_vc::assert!(s.x == 5u64);
}

#[trust_vc::requires(s.x == 5u64)]
#[trust_vc::requires(n == 3u64)]
fn loop_unknown_post_false(s: &mut S, mut i: u64, n: u64) {
    while i < n {
        trust_vc::invariant!(n == 3u64);
        s.mystery();
        i = i + 1u64;
    }
    trust_vc::assert!(s.x == 5u64);
}

#[trust_vc::requires(s.x == 5u64)]
#[trust_vc::requires(n == 3u64)]
fn loop_field_inv_bump_false(s: &mut S, mut i: u64, n: u64) {
    while i < n {
        trust_vc::invariant!(s.x == 5u64);
        s.bump();
        i = i + 1u64;
    }
    trust_vc::assert!(s.x == 5u64);
}

// ---------- LOOP collector modified-var fixtures (inspected directly) ----------
// A &mut self call must put the receiver into the loop modified set; a &self
// getter must NOT (so a true invariant about an only-read struct stays framed).

#[trust_vc::requires(n == 3u64)]
fn loop_modset_bump(s: &mut S, mut i: u64, n: u64) {
    while i < n {
        trust_vc::invariant!(n == 3u64);
        s.bump();
        i = i + 1u64;
    }
}

#[trust_vc::requires(n == 3u64)]
fn loop_modset_getter(s: &mut S, mut i: u64, n: u64) {
    while i < n {
        trust_vc::invariant!(n == 3u64);
        let _g = s.get();
        i = i + 1u64;
    }
}

#[trust_vc::requires(n == 3u64)]
fn loop_modset_unknown(s: &mut S, mut i: u64, n: u64) {
    while i < n {
        trust_vc::invariant!(n == 3u64);
        s.mystery();
        i = i + 1u64;
    }
}
"####;

fn run(func: &str) -> VerifyResult {
    let dir = std::env::temp_dir().join("trust_vc_struct_mutation_loop_soundness");
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
        "{func} must NOT verify (struct receiver mutated; stale read), got Verified"
    );
}

fn assert_verified(func: &str) {
    let r = run(func);
    assert!(
        r.is_verified(),
        "{func} must verify (legitimate, no over-rejection), got: {r:?}"
    );
}

/// Whether `var` is in SOME loop's modified set in `func`'s extracted context.
fn struct_in_loop_modified_set(func_name: &str, var: &str) -> bool {
    let file = syn::parse_file(SRC).expect("source parses");
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(f) if f.sig.ident == func_name => Some(f.clone()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{func_name} should exist"));
    let vc = extract_verification_conditions_with_file_context(&file, &func)
        .unwrap_or_else(|e| panic!("{func_name} should extract: {e}"));
    vc.loop_modified_vars()
        .values()
        .any(|vars| vars.iter().any(|v| v == var))
}

// ---- STRAIGHT-LINE false shapes: must NOT verify ----

#[test]
fn sl_bump_field_false_is_not_verified() {
    assert_not_verified("sl_bump_field_false");
}

#[test]
fn sl_bump_getter_false_is_not_verified() {
    assert_not_verified("sl_bump_getter_false");
}

#[test]
fn sl_owned_bump_field_false_is_not_verified() {
    assert_not_verified("sl_owned_bump_field_false");
}

#[test]
fn sl_unknown_field_false_is_not_verified() {
    assert_not_verified("sl_unknown_field_false");
}

// ---- STRAIGHT-LINE legitimate shapes: NO over-rejection ----

#[test]
fn sl_getter_field_true_verifies() {
    assert_verified("sl_getter_field_true");
}

#[test]
fn sl_clone_then_read_true_verifies() {
    assert_verified("sl_clone_then_read_true");
}

#[test]
fn sl_pre_mutation_assert_true_verifies() {
    assert_verified("sl_pre_mutation_assert_true");
}

#[test]
fn sl_no_call_true_verifies() {
    assert_verified("sl_no_call_true");
}

// ---- POSTCONDITION (ensures) shapes ----

#[test]
fn ens_bump_false_is_not_verified() {
    assert_not_verified("ens_bump_false");
}

#[test]
fn ens_unknown_false_is_not_verified() {
    assert_not_verified("ens_unknown_false");
}

#[test]
fn ens_getter_true_verifies() {
    assert_verified("ens_getter_true");
}

#[test]
fn ens_no_call_true_verifies() {
    assert_verified("ens_no_call_true");
}

// ---- LOOP false shapes: must NOT verify ----

#[test]
fn loop_bump_post_false_is_not_verified() {
    assert_not_verified("loop_bump_post_false");
}

#[test]
fn loop_unknown_post_false_is_not_verified() {
    assert_not_verified("loop_unknown_post_false");
}

#[test]
fn loop_field_inv_bump_false_is_not_verified() {
    assert_not_verified("loop_field_inv_bump_false");
}

// ---- LOOP collector modified-var recording (direct, mask-independent) ----

#[test]
fn loop_collector_records_mut_self_receiver() {
    assert!(
        struct_in_loop_modified_set("loop_modset_bump", "s"),
        "a &mut self method call must put the struct receiver in the loop modified set"
    );
}

#[test]
fn loop_collector_records_unknown_method_receiver() {
    assert!(
        struct_in_loop_modified_set("loop_modset_unknown", "s"),
        "an unknown-signature method on a struct receiver must be conservatively recorded (havoc)"
    );
}

#[test]
fn loop_collector_does_not_record_ref_self_getter() {
    assert!(
        !struct_in_loop_modified_set("loop_modset_getter", "s"),
        "a pure &self getter must NOT havoc the struct receiver (no over-rejection)"
    );
}
