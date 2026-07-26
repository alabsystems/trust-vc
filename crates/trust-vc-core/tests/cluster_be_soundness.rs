// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Round-4 cluster "be" (`body_extract`) soundness guards — three sub-areas of
//! false-`Verified`s plus their cardinal NO-OVER-REJECTION duals:
//!
//!  (A) FREE-FUNCTION CALL with a `&mut` argument is not havoced. A contract-less
//!      `fn push_helper(v: &mut Vec<u64>) { v.push(1) }` (or scalar
//!      `bump_scalar(x: &mut u64)`) mutates its referent, but the caller dropped
//!      the effect — a post-call `assert!(v.len() == 5)` read the pre-call entry
//!      snapshot. Closed on the straight-line, loop-frame, and branch-join paths,
//!      for collection AND scalar `&mut` referents. A free call WITH a sound
//!      `ensures` that pins the value must STILL verify; a `&`-shared (non-mut)
//!      argument must NOT havoc; a pure read still verifies.
//!
//!  (B) BARE UNARY NEG exec arithmetic-safety. `let x = -a;` with
//!      `requires(a == i32::MIN)` overflows (`-i32::MIN` is unrepresentable) yet
//!      verified, at every value position. `-5i32` / a non-MIN-constrained signed
//!      value still verifies where safe.
//!
//!  (C) OWNED-LOCAL field write returned as the result. `let mut s = S { a: 0 };
//!      s.a = 5; s.a` with `ensures(result == 0)` verified because the returned
//!      field projection read the construction value, not the post-write state.
//!      `ensures(result == 5)` (the true post-write value) must STILL verify.

use std::io::Write;
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn run(src: &str, func: &str) -> VerifyResult {
    let dir = std::env::temp_dir().join("trust_vc_cluster_be_soundness");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{func}.rs"));
    let mut f = std::fs::File::create(&path).unwrap();
    f.write_all(src.as_bytes()).unwrap();
    drop(f);
    verify_function_from_file(path.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
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

fn in_loop_modified_set(src: &str, func_name: &str, var: &str) -> bool {
    let file = syn::parse_file(src).expect("source parses");
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == func_name => Some(func.clone()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{func_name} should exist"));
    let vc = extract_verification_conditions_with_file_context(&file, &func)
        .unwrap_or_else(|error| panic!("{func_name} should extract: {error}"));
    vc.loop_modified_vars()
        .values()
        .any(|vars| vars.iter().any(|name| name == var))
}

// =====================================================================
// (A) free-call &mut argument not havoced
// =====================================================================

const SRC_A: &str = r####"
fn push_helper(v: &mut Vec<u64>) { v.push(1u64); }
fn clear_helper(v: &mut Vec<u64>) { v.clear(); }
fn read_helper(v: &Vec<u64>) -> usize { v.len() }
fn bump_scalar(x: &mut u64) { *x = *x + 1u64; }
fn flip_bool(x: &mut bool) { *x = !*x; }
fn read_scalar(x: &u64) -> u64 { *x }

// helper WITH a sound &mut-param ensures pinning the length (no over-rejection)
#[trust_vc::ensures(v.len() == 5usize)]
fn pin_len_helper(v: &mut Vec<u64>) {}

// ---- FALSE: straight-line collection ----
#[trust_vc::requires(v.len() == 5usize)]
fn straight_push_false(v: &mut Vec<u64>) {
    push_helper(v);
    trust_vc::assert!(v.len() == 5usize);
}

#[trust_vc::requires(v.len() == 5usize)]
fn straight_clear_false(v: &mut Vec<u64>) {
    clear_helper(v);
    trust_vc::assert!(v.len() == 5usize);
}

// ---- FALSE: branch-join collection ----
#[trust_vc::requires(v.len() == 5usize)]
fn branch_push_false(v: &mut Vec<u64>, b: bool) {
    if b { push_helper(v); }
    trust_vc::assert!(v.len() == 5usize);
}

// ---- FALSE: loop-frame collection ----
#[trust_vc::requires(v.len() == 5usize)]
fn loop_push_false(v: &mut Vec<u64>, n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(v.len() == 5usize);
        push_helper(v);
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 5usize);
}

#[trust_vc::requires(v.len() == 5usize)]
fn loop_clear_false(v: &mut Vec<u64>, n: usize) {
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(v.len() == 5usize);
        clear_helper(v);
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 5usize);
}

// ---- FALSE: straight-line scalar (snapshot pattern; `*x` in requires
//      fails-closed, so the hole is exercised via a body snapshot) ----
fn straight_scalar_false(x: &mut u64) {
    let start = *x;
    bump_scalar(x);
    trust_vc::assert!(*x == start);
}

// ---- FALSE: loop-frame scalar ----
fn loop_scalar_false(x: &mut u64, n: u64) {
    let start = *x;
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(*x == start);
        bump_scalar(x);
        i = i + 1u64;
    }
    trust_vc::assert!(*x == start);
}

fn loop_bool_snapshot_false(x: &mut bool, n: u64) {
    let start = *x;
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(*x == start);
        flip_bool(x);
        i = i + 1u64;
    }
    trust_vc::assert!(*x == start);
}

// Same invariant violation without a helper call. This pins the direct
// deref-write root in the loop-modified set independently of callee-signature
// analysis.
fn loop_scalar_inline_false(x: &mut u64, n: u64) {
    let start = *x;
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(*x == start);
        *x = *x + 1u64;
        i = i + 1u64;
    }
    trust_vc::assert!(*x == start);
}

#[trust_vc::requires(n == 0u64)]
fn loop_scalar_unreachable_true(x: &mut u64, n: u64) {
    let start = *x;
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(*x == start);
        bump_scalar(x);
        i = i + 1u64;
    }
    trust_vc::assert!(*x == start);
}

// ---- NO OVER-REJECTION ----

// a free call WITH a sound ensures pinning len==5: assert len==5 still verifies
#[trust_vc::requires(v.len() == 5usize)]
fn pinned_ensures_true(v: &mut Vec<u64>) {
    pin_len_helper(v);
    trust_vc::assert!(v.len() == 5usize);
}

// a &-shared (non-mut) argument must NOT havoc the caller's value
#[trust_vc::requires(v.len() == 5usize)]
fn shared_read_true(v: &mut Vec<u64>) {
    let _n = read_helper(v);
    trust_vc::assert!(v.len() == 5usize);
}

fn shared_scalar_read_true(x: &mut u64) {
    let start = *x;
    let _n = read_scalar(x);
    trust_vc::assert!(*x == start);
}

fn loop_shared_scalar_read_true(x: &mut u64, n: u64) {
    let start = *x;
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(*x == start);
        let _n = read_scalar(x);
        i = i + 1u64;
    }
    trust_vc::assert!(*x == start);
}

// assert BEFORE the mutating call still verifies
#[trust_vc::requires(v.len() == 5usize)]
fn before_push_true(v: &mut Vec<u64>) {
    trust_vc::assert!(v.len() == 5usize);
    push_helper(v);
}

// no call at all: entry value holds
#[trust_vc::requires(v.len() == 5usize)]
fn no_call_true(v: &mut Vec<u64>) {
    trust_vc::assert!(v.len() == 5usize);
}
"####;

#[test]
fn a_straight_push_false_rejected() {
    assert_not_verified(SRC_A, "straight_push_false");
}
#[test]
fn a_straight_clear_false_rejected() {
    assert_not_verified(SRC_A, "straight_clear_false");
}
#[test]
fn a_branch_push_false_rejected() {
    assert_not_verified(SRC_A, "branch_push_false");
}
#[test]
fn a_loop_push_false_rejected() {
    assert_not_verified(SRC_A, "loop_push_false");
}
#[test]
fn a_loop_clear_false_rejected() {
    assert_not_verified(SRC_A, "loop_clear_false");
}
#[test]
fn a_straight_scalar_false_rejected() {
    assert_not_verified(SRC_A, "straight_scalar_false");
}
#[test]
fn a_loop_scalar_false_rejected() {
    assert_not_verified(SRC_A, "loop_scalar_false");
}
#[test]
fn a_loop_bool_snapshot_false_rejected() {
    assert_not_verified(SRC_A, "loop_bool_snapshot_false");
}
#[test]
fn a_loop_scalar_free_call_is_in_modified_set() {
    assert!(
        in_loop_modified_set(SRC_A, "loop_scalar_false", "x"),
        "a free call's scalar &mut argument must be loop-modified"
    );
}
#[test]
fn a_loop_scalar_inline_false_rejected() {
    assert_not_verified(SRC_A, "loop_scalar_inline_false");
}
#[test]
fn a_loop_scalar_unreachable_true_verifies() {
    assert_verified(SRC_A, "loop_scalar_unreachable_true");
}
#[test]
fn a_pinned_ensures_true_verifies() {
    assert_verified(SRC_A, "pinned_ensures_true");
}
#[test]
fn a_shared_read_true_verifies() {
    assert_verified(SRC_A, "shared_read_true");
}
#[test]
fn a_shared_scalar_read_true_verifies() {
    assert_verified(SRC_A, "shared_scalar_read_true");
}
#[test]
fn a_loop_shared_scalar_read_true_verifies() {
    assert_verified(SRC_A, "loop_shared_scalar_read_true");
}
#[test]
fn a_before_push_true_verifies() {
    assert_verified(SRC_A, "before_push_true");
}
#[test]
fn a_no_call_true_verifies() {
    assert_verified(SRC_A, "no_call_true");
}

// =====================================================================
// (B) bare unary neg exec arithmetic-safety
// =====================================================================

const SRC_B: &str = r####"
// ---- FALSE: -i32::MIN overflows, at every value position ----
#[trust_vc::requires(a == -2147483648i32)]
fn neg_let_false(a: i32) {
    let _x = -a;
    trust_vc::assert!(true);
}

#[trust_vc::requires(a == -2147483648i32)]
fn neg_stmt_false(a: i32) {
    let _ = -a;
    trust_vc::assert!(true);
}

#[trust_vc::requires(a == -2147483648i32)]
fn neg_tuple_false(a: i32) {
    let _t = (-a, 0i32);
    trust_vc::assert!(true);
}

#[trust_vc::requires(a == -9223372036854775808i64)]
fn neg_i64_false(a: i64) {
    let _x = -a;
    trust_vc::assert!(true);
}

// ---- NO OVER-REJECTION ----

// a negation that is provably safe (a > i32::MIN) verifies
#[trust_vc::requires(a > -2147483648i32)]
fn neg_safe_true(a: i32) {
    let _x = -a;
    trust_vc::assert!(true);
}

// a literal negation is always safe
fn neg_literal_true() {
    let _x = -5i32;
    trust_vc::assert!(true);
}

// negation nested in a safe value position verifies
#[trust_vc::requires(a > -2147483648i32)]
fn neg_tuple_safe_true(a: i32) {
    let _t = (-a, 0i32);
    trust_vc::assert!(true);
}
"####;

#[test]
fn b_neg_let_false_rejected() {
    assert_not_verified(SRC_B, "neg_let_false");
}
#[test]
fn b_neg_stmt_false_rejected() {
    assert_not_verified(SRC_B, "neg_stmt_false");
}
#[test]
fn b_neg_tuple_false_rejected() {
    assert_not_verified(SRC_B, "neg_tuple_false");
}
#[test]
fn b_neg_i64_false_rejected() {
    assert_not_verified(SRC_B, "neg_i64_false");
}
#[test]
fn b_neg_safe_true_verifies() {
    assert_verified(SRC_B, "neg_safe_true");
}
#[test]
fn b_neg_literal_true_verifies() {
    assert_verified(SRC_B, "neg_literal_true");
}
#[test]
fn b_neg_tuple_safe_true_verifies() {
    assert_verified(SRC_B, "neg_tuple_safe_true");
}

// =====================================================================
// (C) owned-local field write returned as result
// =====================================================================

const SRC_C: &str = r####"
struct S { a: u64 }
struct Pair(u64, u64);
struct Inner { v: u64 }
struct Outer { inner: Inner }

// ---- FALSE: returned field reads construction value, dropping the write ----
#[trust_vc::ensures(result == 0u64)]
fn s_named_false() -> u64 {
    let mut s = S { a: 0u64 };
    s.a = 5u64;
    s.a
}

#[trust_vc::ensures(result == 0u64)]
fn s_tuple_false() -> u64 {
    let mut p = Pair(0u64, 0u64);
    p.0 = 5u64;
    p.0
}

#[trust_vc::ensures(result == 0u64)]
fn s_nested_false() -> u64 {
    let mut o = Outer { inner: Inner { v: 0u64 } };
    o.inner.v = 5u64;
    o.inner.v
}

// ---- NO OVER-REJECTION: the true post-write value verifies ----
#[trust_vc::ensures(result == 5u64)]
fn s_named_true() -> u64 {
    let mut s = S { a: 0u64 };
    s.a = 5u64;
    s.a
}

#[trust_vc::ensures(result == 5u64)]
fn s_tuple_true() -> u64 {
    let mut p = Pair(0u64, 0u64);
    p.0 = 5u64;
    p.0
}

#[trust_vc::ensures(result == 5u64)]
fn s_nested_true() -> u64 {
    let mut o = Outer { inner: Inner { v: 0u64 } };
    o.inner.v = 5u64;
    o.inner.v
}

// no write: the construction value verifies
#[trust_vc::ensures(result == 0u64)]
fn s_named_nowrite_true() -> u64 {
    let s = S { a: 0u64 };
    s.a
}
"####;

#[test]
fn c_s_named_false_rejected() {
    assert_not_verified(SRC_C, "s_named_false");
}
#[test]
fn c_s_tuple_false_rejected() {
    assert_not_verified(SRC_C, "s_tuple_false");
}
#[test]
fn c_s_nested_false_rejected() {
    assert_not_verified(SRC_C, "s_nested_false");
}
#[test]
fn c_s_named_true_verifies() {
    assert_verified(SRC_C, "s_named_true");
}
#[test]
fn c_s_tuple_true_verifies() {
    assert_verified(SRC_C, "s_tuple_true");
}
#[test]
fn c_s_nested_true_verifies() {
    assert_verified(SRC_C, "s_nested_true");
}
#[test]
fn c_s_named_nowrite_true_verifies() {
    assert_verified(SRC_C, "s_named_nowrite_true");
}

// =====================================================================
// (D) cross-cutting NO-OVER-REJECTION sanity: the cluster-be changes
//     (free-call havoc / unary-neg arith / return-field threading) must not
//     perturb adjacent verification paths.
// =====================================================================

const SRC_D: &str = r####"
#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { 7u32 }   // CONFORMING default body
}
struct Z;
impl DT for Z {}

#[trust_vc::ensures(true)]
fn conforming_trait_default<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r == 7u32);
}

#[trust_vc::ensures(true)]
fn true_forall() {
    trust_vc::assert!(forall|i: int| i == i);
}
"####;

#[test]
fn d_conforming_trait_default_verifies() {
    assert_verified(SRC_D, "conforming_trait_default");
}
#[test]
fn d_true_forall_verifies() {
    assert_verified(SRC_D, "true_forall");
}
