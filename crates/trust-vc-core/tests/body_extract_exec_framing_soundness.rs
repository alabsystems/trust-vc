// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Round-3 exec-framing soundness guards for `body_extract` — the
//! mutation-framing / contract-scope cluster of false-`Verified`s, plus a
//! cardinal NO-OVER-REJECTION pin for the field-projection method path.
//!
//! The closed holes (each a stale read that was trivially "preserved" because the
//! body model never threaded a laundered mutation):
//!   - `core::mem::take`/`replace`/`swap` (and any `f(P)`) passing a `&mut`
//!     parameter's referent out where the mutation is invisible to the body;
//!   - a `&mut self` method laundered through a FIELD projection of a `&mut`
//!     struct parameter (`o.sub.raise()`) — straight-line assert AND postcondition;
//!   - a `&mut` struct sub-place REBORROW alias (`let a = &mut o.sub; a.raise();`);
//!   - a NO-invariant `while`/`for` loop mutating a `requires`/`assume`-pinned
//!     parameter (scalar or struct), with a post-loop read of the stale value;
//!   - a `&mut self` method with a pure-LOOKING name (`len`) that the file's impl
//!     declares `&mut self` — the receiver-kind registry wins over the allow-list.
//!
//! CARDINAL no-over-rejection direction: a FIELD-PROJECTION receiver
//! `o.sub.method()` must be classified by the projected sub-field's RESOLVED
//! struct type (its declared `Datatype`), NOT by a method-NAME allow-list. So a
//! pure `&self` getter on the sub-field with a CUSTOM name (`peek`/`value`/
//! `current`/`data`) — including a 2-level-deep projection — must STILL verify in
//! both the `assert!` and `ensures` forms. (A prior fix classified these by name
//! and wrongly havocked the root struct, regressing every custom-named getter
//! Verified -> Unknown/Error.)

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
struct Inner { x: u64 }
impl Inner {
    fn raise(&mut self) { self.x = self.x + 1u64; }
    // PURE &self getters with CUSTOM names (NOT in the universal allow-list).
    fn peek(&self) -> u64 { self.x }
    fn value(&self) -> u64 { self.x }
    fn current(&self) -> u64 { self.x }
    fn data(&self) -> u64 { self.x }
    // A &mut self method with a pure-LOOKING name: the registry must win.
    fn len(&mut self) -> u64 { self.x = self.x + 1u64; self.x }
    // A pure &self getter (used in loop / direct receiver checks).
    fn get(&self) -> u64 { self.x }
}
struct Outer { sub: Inner }
struct Deep { mid: Outer }

// ===== FIELD-PROJECTION &mut self launder (FALSE) =====

#[trust_vc::requires(o.sub.x == 5u64)]
fn fp_raise_assert_false(o: &mut Outer) {
    o.sub.raise();
    trust_vc::assert!(o.sub.x == 5u64);
}

#[trust_vc::requires(o.sub.x == 5u64)]
#[trust_vc::ensures(o.sub.x == 5u64)]
fn fp_raise_ensures_false(o: &mut Outer) {
    o.sub.raise();
}

// Pure-name spoof through a projection: len() is &mut self despite the name.
#[trust_vc::requires(o.sub.x == 5u64)]
fn fp_spoof_len_assert_false(o: &mut Outer) {
    let _ = o.sub.len();
    trust_vc::assert!(o.sub.x == 5u64);
}

// ===== FIELD-PROJECTION custom-named PURE getters (VERIFY — no over-rejection) =====

#[trust_vc::requires(o.sub.x == 5u64)]
fn fp_peek_assert_true(o: &mut Outer) {
    let _v = o.sub.peek();
    trust_vc::assert!(o.sub.x == 5u64);
}

#[trust_vc::requires(o.sub.x == 5u64)]
fn fp_value_assert_true(o: &mut Outer) {
    let _v = o.sub.value();
    trust_vc::assert!(o.sub.x == 5u64);
}

#[trust_vc::requires(o.sub.x == 5u64)]
fn fp_current_assert_true(o: &mut Outer) {
    let _v = o.sub.current();
    trust_vc::assert!(o.sub.x == 5u64);
}

#[trust_vc::requires(o.sub.x == 5u64)]
fn fp_data_assert_true(o: &mut Outer) {
    let _v = o.sub.data();
    trust_vc::assert!(o.sub.x == 5u64);
}

#[trust_vc::requires(o.sub.x == 5u64)]
#[trust_vc::ensures(o.sub.x == 5u64)]
fn fp_peek_ensures_true(o: &mut Outer) {
    let _v = o.sub.peek();
}

#[trust_vc::requires(o.sub.x == 5u64)]
#[trust_vc::ensures(o.sub.x == 5u64)]
fn fp_value_ensures_true(o: &mut Outer) {
    let _v = o.sub.value();
}

// 2-level-deep projection, custom-named pure getter.
#[trust_vc::requires(d.mid.sub.x == 5u64)]
fn fp_deep_peek_assert_true(d: &mut Deep) {
    let _v = d.mid.sub.peek();
    trust_vc::assert!(d.mid.sub.x == 5u64);
}

// A non-mutated &mut struct param: the ensures about the entry value holds.
#[trust_vc::requires(o.sub.x == 5u64)]
#[trust_vc::ensures(o.sub.x == 5u64)]
fn fp_no_call_true(o: &mut Outer) {}

// ===== core::mem::take / replace / swap (FALSE) =====

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(v.len() == 5usize)]
fn mem_take_false(v: &mut Vec<u64>) {
    let _g = core::mem::take(v);
}

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(v.len() == 5usize)]
fn mem_replace_false(v: &mut Vec<u64>) {
    let _g = core::mem::replace(v, Vec::new());
}

#[trust_vc::requires(a.len() == 5usize)]
#[trust_vc::ensures(a.len() == 5usize)]
fn mem_swap_false(a: &mut Vec<u64>, b: &mut Vec<u64>) {
    core::mem::swap(a, b);
}

// ===== reborrow-alias of a struct sub-place (FALSE) =====

#[trust_vc::requires(o.sub.x == 5u64)]
fn reborrow_alias_false(o: &mut Outer) {
    let a = &mut o.sub;
    a.raise();
    trust_vc::assert!(o.sub.x == 5u64);
}

// ===== no-invariant loop mutating a requires-pinned PARAMETER (FALSE) =====

#[trust_vc::requires(x == 7u64)]
fn loop_noinv_param_false(mut x: u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        x = x + 1u64;
        i = i + 1u64;
    }
    trust_vc::assert!(x == 7u64);
}

// for-loop variant of the same no-invariant parameter frame leak.
#[trust_vc::requires(x == 7u64)]
fn loop_for_noinv_param_false(mut x: u64, n: u64) {
    for _k in 0u64..n {
        x = x + 1u64;
    }
    trust_vc::assert!(x == 7u64);
}

// ===== struct PARAMETER mutated by a method in a no-invariant loop (FALSE) =====

#[trust_vc::requires(s.x == 5u64)]
fn loop_noinv_struct_false(s: &mut Inner, n: u64) {
    let mut i = 0u64;
    while i < n {
        s.raise();
        i = i + 1u64;
    }
    trust_vc::assert!(s.x == 5u64);
}

// ===== pure-name method spoof in a loop: len() is &mut self (FALSE) =====

#[trust_vc::requires(s.x == 5u64)]
fn loop_spoof_len_false(s: &mut Inner, n: u64) {
    let mut i = 0u64;
    while i < n {
        let _ = s.len();
        i = i + 1u64;
    }
    trust_vc::assert!(s.x == 5u64);
}

// ===== legitimate shapes that must STILL verify =====

// A loop WITH a correct (true, inductive) invariant.
#[trust_vc::requires(n == 3u64)]
fn loop_with_inv_true(mut i: u64, n: u64) {
    while i < n {
        trust_vc::invariant!(n == 3u64);
        i = i + 1u64;
    }
    trust_vc::assert!(n == 3u64);
}

// A by-value parameter is never mutated, so the ensures about it holds.
#[trust_vc::requires(x == 7u64)]
#[trust_vc::ensures(x == 7u64)]
fn byval_ensures_true(x: u64) -> u64 { x }

// A direct &self getter call does not mutate the receiver (no over-rejection).
#[trust_vc::requires(s.x == 5u64)]
fn sl_direct_getter_true(s: &mut Inner) {
    let _g = s.get();
    trust_vc::assert!(s.x == 5u64);
}
"####;

fn run(func: &str) -> VerifyResult {
    let dir = std::env::temp_dir().join("trust_vc_body_extract_exec_framing_soundness");
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
        "{func} must NOT verify (laundered/loop-framed mutation; stale read), got Verified"
    );
}

fn assert_verified(func: &str) {
    let r = run(func);
    assert!(
        r.is_verified(),
        "{func} must verify (legitimate; no over-rejection), got: {r:?}"
    );
}

// ---- FALSE: field-projection &mut self launder ----

#[test]
fn fp_raise_assert_false_is_not_verified() {
    assert_not_verified("fp_raise_assert_false");
}

#[test]
fn fp_raise_ensures_false_is_not_verified() {
    assert_not_verified("fp_raise_ensures_false");
}

#[test]
fn fp_spoof_len_assert_false_is_not_verified() {
    assert_not_verified("fp_spoof_len_assert_false");
}

// ---- CARDINAL: field-projection custom-named PURE getters must STILL verify ----

#[test]
fn fp_peek_assert_true_verifies() {
    assert_verified("fp_peek_assert_true");
}

#[test]
fn fp_value_assert_true_verifies() {
    assert_verified("fp_value_assert_true");
}

#[test]
fn fp_current_assert_true_verifies() {
    assert_verified("fp_current_assert_true");
}

#[test]
fn fp_data_assert_true_verifies() {
    assert_verified("fp_data_assert_true");
}

#[test]
fn fp_peek_ensures_true_verifies() {
    assert_verified("fp_peek_ensures_true");
}

#[test]
fn fp_value_ensures_true_verifies() {
    assert_verified("fp_value_ensures_true");
}

#[test]
fn fp_deep_peek_assert_true_verifies() {
    assert_verified("fp_deep_peek_assert_true");
}

#[test]
fn fp_no_call_true_verifies() {
    assert_verified("fp_no_call_true");
}

// ---- FALSE: core::mem::take / replace / swap ----

#[test]
fn mem_take_false_is_not_verified() {
    assert_not_verified("mem_take_false");
}

#[test]
fn mem_replace_false_is_not_verified() {
    assert_not_verified("mem_replace_false");
}

#[test]
fn mem_swap_false_is_not_verified() {
    assert_not_verified("mem_swap_false");
}

// ---- FALSE: reborrow-alias of a struct sub-place ----

#[test]
fn reborrow_alias_false_is_not_verified() {
    assert_not_verified("reborrow_alias_false");
}

// ---- FALSE: no-invariant loop parameter frame leak ----

#[test]
fn loop_noinv_param_false_is_not_verified() {
    assert_not_verified("loop_noinv_param_false");
}

#[test]
fn loop_for_noinv_param_false_is_not_verified() {
    assert_not_verified("loop_for_noinv_param_false");
}

#[test]
fn loop_noinv_struct_false_is_not_verified() {
    assert_not_verified("loop_noinv_struct_false");
}

#[test]
fn loop_spoof_len_false_is_not_verified() {
    assert_not_verified("loop_spoof_len_false");
}

// ---- legitimate shapes: NO over-rejection ----

#[test]
fn loop_with_inv_true_verifies() {
    assert_verified("loop_with_inv_true");
}

#[test]
fn byval_ensures_true_verifies() {
    assert_verified("byval_ensures_true");
}

#[test]
fn sl_direct_getter_true_verifies() {
    assert_verified("sl_direct_getter_true");
}
