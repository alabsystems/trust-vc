// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Round-6/8 cluster `be` (`body_extract.rs`) soundness guards.
//!
//! Two false-`Verified` classes are pinned here:
//!
//! (A) STRAIGHT-LINE in-place COLLECTION mutation read by an IN-BODY `assert!`.
//!     A `&mut Vec`/`&mut HashSet`/`&mut HashMap` parameter (modeled as a ghost
//!     `Seq`/`Set`/`Map`) mutated by an unmodeled in-place method
//!     (`clear`/`pop`/`truncate`/`drain`/`retain`/`extend`/`sort`/`dedup`/
//!     `reverse`/…) left the bare parameter resolving to its precondition-pinned
//!     ENTRY symbol, so a later `v.len()`/`v[i]`/`s.contains(..)` in an in-body
//!     `assert!` was checked against the PRE-mutation state — a false `Verified`.
//!     The postcondition path was already guarded; the in-body `assert!` path was
//!     not. The receiver is now havoced to a fresh, unconstrained collection
//!     symbol. Both the auto-deref `v.clear()` and explicit-deref `(*v).clear()`
//!     receiver forms are covered.
//!
//! (B) A DEFERRED closure body that calls a CONTRACTED free function whose
//!     `ensures` constrains a CAPTURED free variable PASSED AS AN ARGUMENT. The
//!     call-`ensures` hypothesis was injected as a flat global `assume` that
//!     survived the closure's isolated-scope visit and discharged a
//!     sibling/enclosing `assert!` over the same capture — even though the closure
//!     was never invoked. The #74 capture-freshening, previously gated only on a
//!     literal `assume!` token, now also fires when the body contains a contracted
//!     helper call — but ONLY freshens the captures that actually appear in such a
//!     call's ARGUMENT list, so a contracted call on a LITERAL (`checked(3u64)`)
//!     freshens nothing and an UNRELATED outer fact about a capture is preserved
//!     (the round-7 over-rejection, fixed here).
//!
//! Both directions are asserted: the false shapes must NOT verify, and the
//! legitimate shapes (pure reads, the already-modeled `push`/`set` re-binds, a
//! closure's own sound reasoning, a closure relying on an outer fact through a
//! contract-less helper OR a literal-arg contracted helper) must stay verified
//! (NO over-rejection).

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
// ---------- (A) straight-line collection mutation + in-body assert ----------

#[trust_vc::requires(v.len() == 2usize)]
#[trust_vc::ensures(true)]
fn vec_clear_stale_len(v: &mut Vec<u64>) {
    v.clear();
    trust_vc::assert!(v.len() == 2usize);
}

#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn vec_pop_stale_len(v: &mut Vec<u64>) {
    v.pop();
    trust_vc::assert!(v.len() == 5usize);
}

#[trust_vc::requires(v.len() == 3usize)]
#[trust_vc::ensures(true)]
fn vec_truncate_stale_len(v: &mut Vec<u64>) {
    v.truncate(1usize);
    trust_vc::assert!(v.len() == 3usize);
}

#[trust_vc::requires(v.len() == 3usize)]
#[trust_vc::ensures(true)]
fn vec_drain_stale_len(v: &mut Vec<u64>) {
    v.drain(0usize..2usize);
    trust_vc::assert!(v.len() == 3usize);
}

#[trust_vc::requires(v.len() == 4usize)]
#[trust_vc::ensures(true)]
fn vec_retain_stale_len(v: &mut Vec<u64>) {
    v.retain(|x| *x > 0u64);
    trust_vc::assert!(v.len() == 4usize);
}

#[trust_vc::requires(v.len() == 1usize)]
#[trust_vc::ensures(true)]
fn vec_extend_stale_len(v: &mut Vec<u64>) {
    v.extend(vec![1u64, 2u64]);
    trust_vc::assert!(v.len() == 1usize);
}

#[trust_vc::requires(v.len() == 3usize && v[0usize] == 9u64)]
#[trust_vc::ensures(true)]
fn vec_sort_stale_elem(v: &mut Vec<u64>) {
    v.sort();
    trust_vc::assert!(v[0usize] == 9u64);
}

#[trust_vc::requires(v.len() == 3usize)]
#[trust_vc::ensures(true)]
fn vec_dedup_stale_len(v: &mut Vec<u64>) {
    v.dedup();
    trust_vc::assert!(v.len() == 3usize);
}

#[trust_vc::requires(v.len() == 3usize && v[0usize] == 9u64)]
#[trust_vc::ensures(true)]
fn vec_reverse_stale_elem(v: &mut Vec<u64>) {
    v.reverse();
    trust_vc::assert!(v[0usize] == 9u64);
}

// explicit-deref receiver form
#[trust_vc::requires(v.len() == 2usize)]
#[trust_vc::ensures(true)]
fn vec_deref_clear_stale_len(v: &mut Vec<u64>) {
    (*v).clear();
    trust_vc::assert!(v.len() == 2usize);
}

// HashSet len + membership
#[trust_vc::requires(s.len() == 2usize)]
#[trust_vc::ensures(true)]
fn set_clear_stale_len(s: &mut std::collections::HashSet<u64>) {
    s.clear();
    trust_vc::assert!(s.len() == 2usize);
}

#[trust_vc::requires(s.contains(&7u64))]
#[trust_vc::ensures(true)]
fn set_clear_stale_member(s: &mut std::collections::HashSet<u64>) {
    s.clear();
    trust_vc::assert!(s.contains(&7u64));
}

#[trust_vc::requires(s.len() == 2usize)]
#[trust_vc::ensures(true)]
fn btreeset_clear_stale_len(s: &mut std::collections::BTreeSet<u64>) {
    s.clear();
    trust_vc::assert!(s.len() == 2usize);
}

// HashMap len
#[trust_vc::requires(m.len() == 2usize)]
#[trust_vc::ensures(true)]
fn map_clear_stale_len(m: &mut std::collections::HashMap<u64, u64>) {
    m.clear();
    trust_vc::assert!(m.len() == 2usize);
}

#[trust_vc::requires(m.len() == 2usize)]
#[trust_vc::ensures(true)]
fn btreemap_clear_stale_len(m: &mut std::collections::BTreeMap<u64, u64>) {
    m.clear();
    trust_vc::assert!(m.len() == 2usize);
}

// owned (by-value) param: an IN-BODY assert sees the mutated value (after clear,
// len == 0), so the stale len == 2 claim is genuinely false and must NOT verify.
#[trust_vc::requires(v.len() == 2usize)]
#[trust_vc::ensures(true)]
fn owned_vec_clear_stale_inbody(mut v: Vec<u64>) {
    v.clear();
    trust_vc::assert!(v.len() == 2usize);
}

// ---------- (A) NO over-rejection ----------

// pure `len` read, no mutation: a TRUE in-body claim still verifies.
#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn vec_pure_len_read_ok(v: &mut Vec<u64>) {
    let _l = v.len();
    trust_vc::assert!(v.len() == 5usize);
}

// pure `index` read, no mutation.
#[trust_vc::requires(v.len() == 3usize)]
#[trust_vc::ensures(true)]
fn vec_pure_index_read_ok(v: &mut Vec<u64>) {
    let _x = v.index(0usize);
    trust_vc::assert!(v.len() == 3usize);
}

// pure membership read, no mutation.
#[trust_vc::requires(s.contains(&7u64))]
#[trust_vc::ensures(true)]
fn set_pure_contains_read_ok(s: &mut std::collections::HashSet<u64>) {
    trust_vc::assert!(s.contains(&7u64));
}

// pure map len read.
#[trust_vc::requires(m.len() == 2usize)]
#[trust_vc::ensures(true)]
fn map_pure_len_read_ok(m: &mut std::collections::HashMap<u64, u64>) {
    let _l = m.len();
    trust_vc::assert!(m.len() == 2usize);
}

// push re-bind still MODELS the post-state: the TRUE post-push len verifies.
#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(true)]
fn vec_push_rebind_ok(v: &mut Vec<u64>) {
    v.push(1u64);
    trust_vc::assert!(v.len() == 6usize);
}

// `.set` re-bind still MODELS the post-state: the length is preserved.
#[trust_vc::requires(v.len() == 3usize)]
#[trust_vc::ensures(true)]
fn vec_set_rebind_ok(v: &mut Vec<u64>) {
    v.set(0usize, 42u64);
    trust_vc::assert!(v.len() == 3usize);
}

// owned (by-value) param entry-value POSTCONDITION must stay Verus-faithful: an
// `ensures` over an owned param reads the entry value, unaffected by the in-body
// havoc (regression guard for the owned-param exclusion).
#[trust_vc::requires(v.len() == 5usize)]
#[trust_vc::ensures(v.len() == 5usize)]
fn owned_vec_clear_entry_value_ensures(mut v: Vec<u64>) {
    v.clear();
}

// ---------- (B) closure free-call ensures leak ----------

#[trust_vc::ensures(x == 7u64)]
fn mk7(x: u64) -> u64 { 0u64 }

#[trust_vc::ensures(x == 5u64)]
fn mk5(x: u64) -> u64 { 0u64 }

// a CONTRACTED helper (non-empty `ensures`) whose contract is satisfiable and
// UNINFORMATIVE about any caller capture: `checked(3u64)` injects `3 == 3`.
#[trust_vc::ensures(x == 3u64)]
fn checked(x: u64) -> u64 { 0u64 }

fn pure_helper(x: u64) -> u64 { x }

// enclosing-fn leak: closure never invoked, n unconstrained; n == 7 is false.
#[trust_vc::ensures(true)]
fn closure_call_ensures_enclosing_leak(n: u64) {
    let _a = |t: u64| { let _ = mk7(n); t };
    trust_vc::assert!(n == 7u64);
}

// sibling-closure leak.
#[trust_vc::ensures(true)]
fn closure_call_ensures_sibling_leak(n: u64) {
    let _a = |t: u64| { let _ = mk7(n); t };
    let _b = |t: u64| { trust_vc::assert!(n == 7u64); t };
    trust_vc::assert!(true);
}

// the leaked fact is mk7's substituted post (n == 7); a false n == 5 claim must
// NOT verify off the (now-scoped) hypothesis.
#[trust_vc::ensures(true)]
fn closure_call_ensures_leak_mk7(n: u64) {
    let _a = |t: u64| { let _ = mk7(n); t };
    trust_vc::assert!(n == 5u64);
}

#[trust_vc::ensures(true)]
fn closure_call_ensures_leak_mk5(n: u64) {
    let _a = |t: u64| { let _ = mk5(n); t };
    trust_vc::assert!(n == 7u64);
}

// SOUNDNESS guard for the narrowing: a closure with BOTH a literal-arg contracted
// call (`checked(3u64)`, freshens nothing) AND a capture-arg contracted call
// (`mk7(n)`, freshens `n`). The capture-arg call still scopes its hypothesis, so
// the sibling read of the unconstrained outer `n` must NOT verify.
#[trust_vc::ensures(true)]
fn closure_literal_and_capture_contracted_call_sibling_leak(n: u64) {
    let _a = |t: u64| { let _ = checked(3u64); let _ = mk7(n); t };
    let _b = |t: u64| { trust_vc::assert!(n == 7u64); t };
    trust_vc::assert!(true);
}

// ---------- (B) NO over-rejection ----------

// real (non-closure) call site: sound modular semantics; mk7(n) assumes n == 7.
#[trust_vc::ensures(true)]
fn straightline_call_ensures_ok(n: u64) {
    let _ = mk7(n);
    trust_vc::assert!(n == 7u64);
}

// an INVOKED closure whose OWN body uses mk7(n) then asserts n == 7 stays sound:
// the injected hypothesis and the assert resolve to the same freshened symbol.
#[trust_vc::ensures(true)]
fn closure_own_reasoning_ok(n: u64) {
    let a = |t: u64| { let _ = mk7(n); trust_vc::assert!(n == 7u64); t };
    let _r = a(1u64);
    trust_vc::assert!(true);
}

// a closure that calls a CONTRACT-LESS helper and relies on an OUTER fact about a
// capture is NOT freshened (the helper injects no hypothesis) — outer fact holds.
#[trust_vc::requires(n == 7u64)]
#[trust_vc::ensures(true)]
fn closure_contractless_outer_fact_ok(n: u64) {
    let a = |t: u64| { let _ = pure_helper(n); trust_vc::assert!(n == 7u64); t };
    let _r = a(1u64);
    trust_vc::assert!(true);
}

// a closure with NO contracted call and NO assume! relying on an outer fact: the
// existing #74 path leaves it untouched.
#[trust_vc::requires(n == 7u64)]
#[trust_vc::ensures(true)]
fn closure_plain_outer_fact_ok(n: u64) {
    let _a = |t: u64| { trust_vc::assert!(n == 7u64); t };
    trust_vc::assert!(true);
}

// THE round-7 over-rejection regression (fixed here): a closure that calls a
// CONTRACTED helper on a LITERAL (`checked(3u64)`, constrains no capture) while
// relying on an UNRELATED outer fact about a capture (`n == 7` from `requires`).
// The broad freshening freshened `n` and broke this; the narrowed freshening
// freshens nothing here (the contracted call's arg is a literal), so it verifies.
#[trust_vc::requires(n == 7u64)]
#[trust_vc::ensures(true)]
fn closure_literal_contracted_call_outer_fact_ok(n: u64) {
    let a = |t: u64| { let _ = checked(3u64); trust_vc::assert!(n == 7u64); t };
    let _r = a(1u64);
    trust_vc::assert!(true);
}

// the never-invoked, sibling-read variant of the same over-rejection: closure `_a`
// calls the literal-arg contracted helper, sibling `_b` reads the outer-pinned
// capture; with the narrowing, `n` is not freshened, so the outer fact survives.
#[trust_vc::requires(n == 7u64)]
#[trust_vc::ensures(true)]
fn closure_literal_contracted_call_sibling_outer_fact_ok(n: u64) {
    let _a = |t: u64| { let _ = checked(3u64); t };
    let _b = |t: u64| { trust_vc::assert!(n == 7u64); t };
    trust_vc::assert!(true);
}
"####;

fn run(func: &str) -> VerifyResult {
    let dir = std::env::temp_dir().join("trust_vc_be_collection_inbody_closure");
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
        "{func} must NOT verify (false in-body claim / leaked hypothesis), got Verified"
    );
}

fn assert_verified(func: &str) {
    let r = run(func);
    assert!(
        r.is_verified(),
        "{func} must verify (legitimate, no over-rejection), got: {r:?}"
    );
}

// ---- (A) false shapes must NOT verify ----

#[test]
fn vec_clear_stale_len_is_not_verified() {
    assert_not_verified("vec_clear_stale_len");
}

#[test]
fn vec_pop_stale_len_is_not_verified() {
    assert_not_verified("vec_pop_stale_len");
}

#[test]
fn vec_truncate_stale_len_is_not_verified() {
    assert_not_verified("vec_truncate_stale_len");
}

#[test]
fn vec_drain_stale_len_is_not_verified() {
    assert_not_verified("vec_drain_stale_len");
}

#[test]
fn vec_retain_stale_len_is_not_verified() {
    assert_not_verified("vec_retain_stale_len");
}

#[test]
fn vec_extend_stale_len_is_not_verified() {
    assert_not_verified("vec_extend_stale_len");
}

#[test]
fn vec_sort_stale_elem_is_not_verified() {
    assert_not_verified("vec_sort_stale_elem");
}

#[test]
fn vec_dedup_stale_len_is_not_verified() {
    assert_not_verified("vec_dedup_stale_len");
}

#[test]
fn vec_reverse_stale_elem_is_not_verified() {
    assert_not_verified("vec_reverse_stale_elem");
}

#[test]
fn vec_deref_clear_stale_len_is_not_verified() {
    assert_not_verified("vec_deref_clear_stale_len");
}

#[test]
fn set_clear_stale_len_is_not_verified() {
    assert_not_verified("set_clear_stale_len");
}

#[test]
fn set_clear_stale_member_is_not_verified() {
    assert_not_verified("set_clear_stale_member");
}

#[test]
fn btreeset_clear_stale_len_is_not_verified() {
    assert_not_verified("btreeset_clear_stale_len");
}

#[test]
fn map_clear_stale_len_is_not_verified() {
    assert_not_verified("map_clear_stale_len");
}

#[test]
fn btreemap_clear_stale_len_is_not_verified() {
    assert_not_verified("btreemap_clear_stale_len");
}

#[test]
fn owned_vec_clear_stale_inbody_is_not_verified() {
    assert_not_verified("owned_vec_clear_stale_inbody");
}

// ---- (A) no over-rejection ----

#[test]
fn vec_pure_len_read_ok_verifies() {
    assert_verified("vec_pure_len_read_ok");
}

#[test]
fn vec_pure_index_read_ok_verifies() {
    assert_verified("vec_pure_index_read_ok");
}

#[test]
fn set_pure_contains_read_ok_verifies() {
    assert_verified("set_pure_contains_read_ok");
}

#[test]
fn map_pure_len_read_ok_verifies() {
    assert_verified("map_pure_len_read_ok");
}

#[test]
fn vec_push_rebind_ok_verifies() {
    assert_verified("vec_push_rebind_ok");
}

#[test]
fn vec_set_rebind_ok_verifies() {
    assert_verified("vec_set_rebind_ok");
}

#[test]
fn owned_vec_clear_entry_value_ensures_verifies() {
    assert_verified("owned_vec_clear_entry_value_ensures");
}

// ---- (B) leaks must NOT verify ----

#[test]
fn closure_call_ensures_enclosing_leak_is_not_verified() {
    assert_not_verified("closure_call_ensures_enclosing_leak");
}

#[test]
fn closure_call_ensures_sibling_leak_is_not_verified() {
    assert_not_verified("closure_call_ensures_sibling_leak");
}

#[test]
fn closure_call_ensures_leak_mk7_is_not_verified() {
    assert_not_verified("closure_call_ensures_leak_mk7");
}

#[test]
fn closure_call_ensures_leak_mk5_is_not_verified() {
    assert_not_verified("closure_call_ensures_leak_mk5");
}

#[test]
fn closure_literal_and_capture_contracted_call_sibling_leak_is_not_verified() {
    assert_not_verified("closure_literal_and_capture_contracted_call_sibling_leak");
}

// ---- (B) no over-rejection ----

#[test]
fn straightline_call_ensures_ok_verifies() {
    assert_verified("straightline_call_ensures_ok");
}

#[test]
fn closure_own_reasoning_ok_verifies() {
    assert_verified("closure_own_reasoning_ok");
}

#[test]
fn closure_contractless_outer_fact_ok_verifies() {
    assert_verified("closure_contractless_outer_fact_ok");
}

#[test]
fn closure_plain_outer_fact_ok_verifies() {
    assert_verified("closure_plain_outer_fact_ok");
}

// THE round-7 over-rejection regression: must VERIFY again with the narrowing.
#[test]
fn closure_literal_contracted_call_outer_fact_ok_verifies() {
    assert_verified("closure_literal_contracted_call_outer_fact_ok");
}

#[test]
fn closure_literal_contracted_call_sibling_outer_fact_ok_verifies() {
    assert_verified("closure_literal_contracted_call_sibling_outer_fact_ok");
}
