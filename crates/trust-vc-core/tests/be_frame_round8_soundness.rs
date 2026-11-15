// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Round-8 cluster "be-frame" (`body_extract`) soundness guards — three
//! sub-areas of false-`Verified`s plus their cardinal NO-OVER-REJECTION duals.
//!
//!  (A) UFCS associated-fn mutation framing was DROPPED. A UFCS call
//!      `S::bump(s)` / `<S>::bump(s)` / `<S as Tr>::traise(s)` / `Tr::traise(s)`
//!      / `S::bump(&mut s)` (owned) / `Vec::push(v, ..)` is the desugaring of
//!      `recv.method(..)`, but the call path did not havoc the `&mut self`
//!      struct receiver / non-pure collection receiver the way the method-call
//!      path does, so the receiver kept its `requires`-pinned ENTRY value and a
//!      post-call `assert!` read it (false `Verified`). A pure UFCS read
//!      (`S::read(s)`) and a no-call baseline must STILL verify.
//!
//!  (B) A call-site `requires` was discharged by a strictly-LATER `assume!` or a
//!      later call's `ensures` (backward-leak): `need(x); assume!(x == 7)` and
//!      `need(x); mk(x)` (with `mk` ensuring `x == 7`) wrongly verified. An
//!      EARLIER `assume!`/call-`ensures` that legitimately establishes the
//!      precondition must STILL discharge it.
//!
//!  (C) A `let mut`-bound exec closure REASSIGNED to a new closure literal inside
//!      a nested block / if-else branch, then CALLED after the block, dropped the
//!      invoked-exec-closure arith-safety obligation (a div-by-zero `g(a, 0)`
//!      false `Verified`). A straight-line single closure — and a cross-scope
//!      rebind to a SAFE body — must STILL verify (correct modeling).

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn run(src: &str, func: &str) -> VerifyResult {
    let dir = std::env::temp_dir().join("trust_vc_be_frame_round8_soundness");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{func}.rs"));
    let mut f = std::fs::File::create(&path).unwrap();
    f.write_all(src.as_bytes()).unwrap();
    drop(f);
    // CACHE DISCIPLINE (mandatory, round-4 correction): the on-disk verification
    // cache stores only `Verified` results and survives `cargo clean`, and this
    // helper called `verify_function_from_file` directly — so whether an
    // `assert_verified` pin here was recomputed depended on the CALLER's
    // environment, which is exactly what the sibling suite
    // `closure_escape_body_soundness.rs` mandates against. MEASURED: it costs
    // this suite nothing — 20 tests in 0.33-0.56 s with the cache off — so the
    // suite's SPEED was never evidence of cache-serving; these fixtures are
    // simply cheap.
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(path.to_str().unwrap(), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        })
    })
}

fn assert_not_verified(src: &str, func: &str) {
    let r = run(src, func);
    assert!(
        !r.is_verified(),
        "{func} must NOT verify (genuinely false goal), got Verified"
    );
}

fn assert_verified(src: &str, func: &str) {
    let r = run(src, func);
    assert!(
        matches!(r, VerifyResult::Verified),
        "{func} must verify (sound, no over-rejection), got {r:?}"
    );
}

// =====================================================================
// (A) UFCS associated-fn mutation framing
// =====================================================================

const SRC_A: &str = r####"
struct S { x: u64 }
impl S {
    fn bump(&mut self) { self.x = self.x + 1u64; }
    fn read(&self) -> u64 { self.x }          // pure &self read — must not havoc
    fn make(input: u64) -> S { S { x: input } } // associated ctor — no self recv
}

trait Tr { fn traise(&mut self); }
impl Tr for S { fn traise(&mut self) { self.x = self.x + 1u64; } }

// ---- FALSE: plain inherent UFCS `S::bump(s)` ----
#[trust_vc::requires(s.x == 5u64)]
fn ufcs_bump_false(s: &mut S) {
    S::bump(s);
    trust_vc::assert!(s.x == 5u64);
}

// ---- FALSE: fully-qualified `<S>::bump(s)` ----
#[trust_vc::requires(s.x == 5u64)]
fn ufcs_qself_bump_false(s: &mut S) {
    <S>::bump(s);
    trust_vc::assert!(s.x == 5u64);
}

// ---- FALSE: qualified trait UFCS `<S as Tr>::traise(s)` ----
#[trust_vc::requires(s.x == 5u64)]
fn ufcs_trait_qual_false(s: &mut S) {
    <S as Tr>::traise(s);
    trust_vc::assert!(s.x == 5u64);
}

// ---- FALSE: plain trait UFCS `Tr::traise(s)` ----
#[trust_vc::requires(s.x == 5u64)]
fn ufcs_trait_plain_false(s: &mut S) {
    Tr::traise(s);
    trust_vc::assert!(s.x == 5u64);
}

// ---- FALSE: owned receiver `S::bump(&mut s)` ----
#[trust_vc::requires(s.x == 5u64)]
fn ufcs_owned_bump_false(mut s: S) {
    S::bump(&mut s);
    trust_vc::assert!(s.x == 5u64);
}

// ---- FALSE: collection mutator UFCS `Vec::push(v, 9)` ----
#[trust_vc::requires(v.len() == 5usize)]
fn ufcs_push_false(v: &mut Vec<u64>) {
    Vec::push(v, 9u64);
    trust_vc::assert!(v.len() == 5usize);
}

// ---- FALSE: collection mutator UFCS `Vec::clear(v)` ----
#[trust_vc::requires(v.len() == 5usize)]
fn ufcs_clear_false(v: &mut Vec<u64>) {
    Vec::clear(v);
    trust_vc::assert!(v.len() == 5usize);
}

// ---- TRUE (no over-rejection): pure `&self` UFCS read does NOT havoc ----
#[trust_vc::requires(s.x == 5u64)]
fn ufcs_pure_read_true(s: &mut S) {
    let _r = S::read(s);
    trust_vc::assert!(s.x == 5u64);
}

// ---- TRUE (no over-rejection): associated ctor with a struct-typed result
//      argument does NOT havoc an unrelated read ----
#[trust_vc::requires(s.x == 5u64)]
fn ufcs_ctor_no_havoc_true(s: &mut S) {
    let _other = S::make(99u64);
    trust_vc::assert!(s.x == 5u64);
}

// ---- TRUE (no over-rejection): no call, requires honored ----
#[trust_vc::requires(s.x == 5u64)]
fn no_call_true(s: &mut S) {
    trust_vc::assert!(s.x == 5u64);
}
"####;

#[test]
fn a_ufcs_bump_false_not_verified() {
    assert_not_verified(SRC_A, "ufcs_bump_false");
}
#[test]
fn a_ufcs_qself_bump_false_not_verified() {
    assert_not_verified(SRC_A, "ufcs_qself_bump_false");
}
#[test]
fn a_ufcs_trait_qual_false_not_verified() {
    assert_not_verified(SRC_A, "ufcs_trait_qual_false");
}
#[test]
fn a_ufcs_trait_plain_false_not_verified() {
    assert_not_verified(SRC_A, "ufcs_trait_plain_false");
}
#[test]
fn a_ufcs_owned_bump_false_not_verified() {
    assert_not_verified(SRC_A, "ufcs_owned_bump_false");
}
#[test]
fn a_ufcs_push_false_not_verified() {
    assert_not_verified(SRC_A, "ufcs_push_false");
}
#[test]
fn a_ufcs_clear_false_not_verified() {
    assert_not_verified(SRC_A, "ufcs_clear_false");
}
#[test]
fn a_ufcs_pure_read_true_verifies() {
    assert_verified(SRC_A, "ufcs_pure_read_true");
}
#[test]
fn a_ufcs_ctor_no_havoc_true_verifies() {
    assert_verified(SRC_A, "ufcs_ctor_no_havoc_true");
}
#[test]
fn a_no_call_true_verifies() {
    assert_verified(SRC_A, "no_call_true");
}

// =====================================================================
// (B) call-site requires backward-leak
// =====================================================================

const SRC_B: &str = r####"
#[trust_vc::requires(x == 7u64)]
fn need(x: u64) -> u64 { x }

// `mk`'s ensures constrains its INPUT parameter `x`.
#[trust_vc::ensures(x == 7u64)]
fn mk(x: u64) {}

// ---- FALSE: later `assume!` must NOT discharge an earlier requires ----
#[trust_vc::ensures(true)]
fn later_assume_false(x: u64) {
    let _ = need(x);
    trust_vc::assume!(x == 7u64);
    trust_vc::assert!(true);
}

// ---- FALSE: later call `ensures` must NOT discharge an earlier requires ----
#[trust_vc::ensures(true)]
fn later_ensures_false(x: u64) {
    let _ = need(x);
    let _ = mk(x);
    trust_vc::assert!(true);
}

// ---- FALSE: a nested-block later assume must NOT discharge it either ----
#[trust_vc::ensures(true)]
fn later_assume_block_false(x: u64) {
    let _ = need(x);
    { trust_vc::assume!(x == 7u64); }
    trust_vc::assert!(true);
}

// ---- TRUE (no over-rejection): EARLIER assume establishes the requires ----
#[trust_vc::ensures(true)]
fn earlier_assume_true(x: u64) {
    trust_vc::assume!(x == 7u64);
    let _ = need(x);
    trust_vc::assert!(true);
}

// ---- TRUE (no over-rejection): EARLIER call ensures establishes the requires ----
#[trust_vc::ensures(true)]
fn earlier_ensures_true(x: u64) {
    let _ = mk(x);
    let _ = need(x);
    trust_vc::assert!(true);
}
"####;

#[test]
fn b_later_assume_false_not_verified() {
    assert_not_verified(SRC_B, "later_assume_false");
}
#[test]
fn b_later_ensures_false_not_verified() {
    assert_not_verified(SRC_B, "later_ensures_false");
}
#[test]
fn b_later_assume_block_false_not_verified() {
    assert_not_verified(SRC_B, "later_assume_block_false");
}
#[test]
fn b_earlier_assume_true_verifies() {
    assert_verified(SRC_B, "earlier_assume_true");
}
#[test]
fn b_earlier_ensures_true_verifies() {
    assert_verified(SRC_B, "earlier_ensures_true");
}

// =====================================================================
// (C) cross-scope exec-closure rebind
// =====================================================================

const SRC_C: &str = r####"
// ---- FALSE: rebind in a nested block, then call (div-by-zero body) ----
#[trust_vc::ensures(true)]
fn closure_rebind_block_false(a: u64) {
    let mut g = |x: u64, y: u64| x / y;
    { g = |x: u64, y: u64| x / y; }
    let _ = g(a, 0u64);
    trust_vc::assert!(true);
}

// ---- FALSE: rebind on both if/else arms, then call (div-by-zero body) ----
#[trust_vc::ensures(true)]
fn closure_rebind_if_false(a: u64, c: bool) {
    let mut g = |x: u64, y: u64| x / y;
    if c { g = |x: u64, y: u64| x / y; } else { g = |x: u64, y: u64| x / y; }
    let _ = g(a, 0u64);
    trust_vc::assert!(true);
}

// ---- TRUE (no over-rejection): straight-line single closure, safe call ----
#[trust_vc::ensures(true)]
fn closure_straightline_true(a: u64) {
    let g = |x: u64, _y: u64| x / 2u64;
    let _ = g(a, 1u64);
    trust_vc::assert!(true);
}

// ---- TRUE (correct modeling): block rebind to a SAFE body still verifies ----
#[trust_vc::ensures(true)]
fn closure_rebind_block_safe_true(a: u64) {
    let mut g = |x: u64, y: u64| x / y;
    { g = |x: u64, _y: u64| x / 2u64; }
    let _ = g(a, 0u64);
    trust_vc::assert!(true);
}

// ---- TRUE (correct modeling): both if/else arms rebind to a SAFE body ----
#[trust_vc::ensures(true)]
fn closure_rebind_if_safe_true(a: u64, c: bool) {
    let mut g = |x: u64, y: u64| x / y;
    if c { g = |x: u64, _y: u64| x / 2u64; } else { g = |x: u64, _y: u64| x / 2u64; }
    let _ = g(a, 0u64);
    trust_vc::assert!(true);
}
"####;

#[test]
fn c_closure_rebind_block_false_not_verified() {
    assert_not_verified(SRC_C, "closure_rebind_block_false");
}
#[test]
fn c_closure_rebind_if_false_not_verified() {
    assert_not_verified(SRC_C, "closure_rebind_if_false");
}
#[test]
fn c_closure_straightline_true_verifies() {
    assert_verified(SRC_C, "closure_straightline_true");
}
#[test]
fn c_closure_rebind_block_safe_true_verifies() {
    assert_verified(SRC_C, "closure_rebind_block_safe_true");
}
#[test]
fn c_closure_rebind_if_safe_true_verifies() {
    assert_verified(SRC_C, "closure_rebind_if_safe_true");
}
