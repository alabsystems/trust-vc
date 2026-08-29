// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Round-10 cluster `be-2` (`body_extract.rs`) soundness guards.
//!
//! Two residual false-`Verified` classes are pinned here, both the LET-LOCAL
//! siblings of already-closed `&mut`-PARAMETER shapes:
//!
//! (A) LET-LOCAL loop-mutation framing. A `let`-bound user-struct or `Vec`
//!     mutated INSIDE a `while`/`for` loop by a `&mut self` method
//!     (`c.bump()`) or an in-place collection mutator
//!     (`retain`/`drain`/`dedup`/`extend`/`sort`/`reverse`/…) was NOT recorded
//!     in the loop's modified-var set, so the loop frame pinned `recv ==
//!     recv_pre` and a post-loop `assert!` reading the (frozen) entry value of
//!     the receiver was trivially "preserved" — a false `Verified`. The
//!     modified-set collector only consulted `vc.variables()` (params/declared
//!     vars), never the scoped let-local bindings. It is now seeded with the
//!     in-scope let-local struct/collection bindings, so its conservative typed
//!     receiver rule catches even unlisted mutators without classifying a pure
//!     user method by spelling alone.
//!
//! (B) CAPTURED-LOCAL closure assume! leak. A closure capturing a `let`-bound
//!     local (`let n = p;`) whose body carries `assume!(n == 7)` leaked that
//!     hypothesis into the enclosing function body / a sibling closure / a
//!     postcondition / a div-by-zero panic-freedom check — even when the
//!     closure was NEVER called. The `#74` capture-freshening only freshened
//!     captures that were DECLARED `vc` variables (params); a scoped-only alias
//!     local (`let n = p`) was skipped, so its in-closure `assume!` resolved
//!     through the alias to the underlying parameter symbol and survived the
//!     isolated-scope visit as a flat global hypothesis. The freshening now also
//!     re-points a captured scoped-local to a fresh, unconstrained symbol for
//!     the closure visit, so the hypothesis is scoped to the closure.
//!
//! Both directions are asserted: the false shapes must NOT verify, and the
//! legitimate shapes (read-only let-local in a loop, straight-line true
//! post-mutation, a read-only capture, an assume-bearing closure that does NOT
//! defeat an outer TRUE fact, a top-level assume that legitimately discharges)
//! must stay verified (NO over-rejection).

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
struct Counter { val: u64 }
impl Counter {
    fn bump(&mut self) { self.val = self.val + 1u64; }
    fn get(&self) -> u64 { self.val }
    fn sort(&self) -> u64 { self.val }
}

// ===================== (A) LET-LOCAL loop-mutation framing =====================

// ---- (A) false shapes: must NOT verify ----

// finding 5 (1-based 6): let-local struct + &mut self method in a WHILE loop.
#[trust_vc::ensures(true)]
fn struct_while_local_bump_false(n: u64) {
    let mut c = Counter { val: 0u64 };
    let mut i = 0u64;
    while i < n {
        c.bump();
        i = i + 1u64;
    }
    trust_vc::assert!(c.val == 0u64);
}

// finding 6 (1-based 7): let-local struct + &mut self method in a FOR loop.
#[trust_vc::ensures(true)]
fn struct_for_local_bump_false(n: u64) {
    let mut c = Counter { val: 0u64 };
    for _x in 0u64..n {
        c.bump();
    }
    trust_vc::assert!(c.val == 0u64);
}

// finding 7 (1-based 8): let-local Vec + `retain` (omitted mutator) in a loop.
#[trust_vc::ensures(true)]
fn vec_while_local_retain_false(n: usize) {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    v.push(2u64);
    v.push(3u64);
    let mut i = 0usize;
    while i < n {
        v.retain(|x| *x > 1u64);
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 3usize);
}

// finding 8 (1-based 9): let-local Vec + `sort` (omitted mutator) in a loop.
#[trust_vc::ensures(true)]
fn vec_while_local_sort_false(n: usize) {
    let mut v: Vec<u32> = Vec::new();
    v.push(3u32);
    v.push(1u32);
    v.push(2u32);
    let mut i = 0usize;
    while i < n {
        v.sort();
        i = i + 1usize;
    }
    trust_vc::assert!(v.index(0) == 3u32);
}

// finding 9 (1-based 10): let-local Vec + `extend` (omitted mutator) in a loop.
#[trust_vc::ensures(true)]
fn vec_while_local_extend_false(n: usize) {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    v.push(2u64);
    let mut i = 0usize;
    while i < n {
        let mut w: Vec<u64> = Vec::new();
        w.push(9u64);
        v.extend(w.iter());
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 2usize);
}

// finding 10 (1-based 11): let-local Vec + `dedup` (omitted mutator) in a loop.
#[trust_vc::ensures(true)]
fn vec_while_local_dedup_false(n: usize) {
    let mut v: Vec<u32> = Vec::new();
    v.push(1u32);
    v.push(1u32);
    v.push(2u32);
    let mut i = 0usize;
    while i < n {
        v.dedup();
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 3usize);
}

// for-loop variant of an omitted mutator on a let-local Vec.
#[trust_vc::ensures(true)]
fn vec_for_local_truncate_false(n: usize) {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    v.push(2u64);
    v.push(3u64);
    for _x in 0usize..n {
        v.truncate(1usize);
    }
    trust_vc::assert!(v.len() == 3usize);
}

// let-local fixed array + unlisted in-place slice mutator.
#[trust_vc::ensures(true)]
fn array_while_local_reverse_false(n: usize) {
    let mut a = [1u64, 2u64];
    let mut i = 0usize;
    while i < n {
        a.reverse();
        i = i + 1usize;
    }
    trust_vc::assert!(a[0] == 1u64);
}

// ---- (A) no over-rejection: legitimate shapes must verify ----

// read-only let-local Vec in a loop (only a pure `len` read) -> true post-loop.
#[trust_vc::ensures(true)]
fn vec_while_local_read_only_ok(n: usize) {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    v.push(2u64);
    let mut i = 0usize;
    while i < n {
        let _len = v.len();
        i = i + 1usize;
    }
    trust_vc::assert!(v.len() == 2usize);
}

// read-only let-local struct in a loop (pure `&self` getter) -> true post-loop.
#[trust_vc::ensures(true)]
fn struct_while_local_read_only_ok(n: u64) {
    let mut c = Counter { val: 5u64 };
    let mut i = 0u64;
    while i < n {
        let _g = c.get();
        i = i + 1u64;
    }
    trust_vc::assert!(c.val == 5u64);
}

// let-local struct in a loop with NO method call -> true post-loop (untouched).
#[trust_vc::ensures(true)]
fn struct_while_local_no_call_ok(n: u64) {
    let mut c = Counter { val: 0u64 };
    let mut i = 0u64;
    while i < n {
        i = i + 1u64;
    }
    trust_vc::assert!(c.val == 0u64);
}

// A user-defined pure `&self` method may share a std mutator name. Receiver-kind
// classification, not the spelling alone, must keep this read-only local framed.
#[trust_vc::ensures(true)]
fn struct_while_local_pure_sort_name_ok(n: u64) {
    let c = Counter { val: 5u64 };
    let mut i = 0u64;
    while i < n {
        let _g = c.sort();
        i = i + 1u64;
    }
    trust_vc::assert!(c.val == 5u64);
}

// A nearer struct local shadows the same-named collection parameter. The stale
// declaration-table type must not make the pure user `sort` look mutating.
#[trust_vc::ensures(true)]
fn collection_param_shadowed_by_struct_pure_sort_ok(v: Vec<u64>, n: u64) {
    let v = Counter { val: 5u64 };
    let mut i = 0u64;
    while i < n {
        let _g = v.sort();
        i = i + 1u64;
    }
    trust_vc::assert!(v.val == 5u64);
}

// straight-line (no loop) let-local Vec + pushes -> true `len` claim.
#[trust_vc::ensures(true)]
fn vec_local_push_true_no_loop() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    v.push(2u64);
    trust_vc::assert!(v.len() == 2usize);
}

#[trust_vc::ensures(true)]
fn array_while_local_read_only_ok(n: usize) {
    let a = [1u64, 2u64];
    let mut i = 0usize;
    while i < n {
        let _len = a.len();
        i = i + 1usize;
    }
    trust_vc::assert!(a[0] == 1u64);
}

// ===================== (B) CAPTURED-LOCAL closure assume! leak =====================

// ---- (B) false shapes: must NOT verify ----

// finding 12 (1-based 13): captured-local assume leak into the OUTER body.
#[trust_vc::ensures(true)]
fn capture_assume_leak_outer_false(p: u64) {
    let n = p;
    let _a = |x: u64| { trust_vc::assume!(n == 7u64); x };
    trust_vc::assert!(n == 7u64);
}

// finding 11 (1-based 12): cross-closure assume leak (sibling closure assert).
#[trust_vc::ensures(true)]
fn capture_cross_closure_leak_false(p: u64) {
    let n = p;
    let _a = |x: u64| { trust_vc::assume!(n == 7u64); x };
    let _b = |y: u64| { trust_vc::assert!(n == 7u64); y };
}

// finding 11 two-hop alias chain (`let m = p; let n = m;`).
#[trust_vc::ensures(true)]
fn capture_assume_leak_twohop_false(p: u64) {
    let m = p;
    let n = m;
    let _a = |x: u64| { trust_vc::assume!(n == 7u64); x };
    trust_vc::assert!(n == 7u64);
}

// finding 13 (1-based 14): uncalled closure discharging a FALSE postcondition.
#[trust_vc::ensures(result == 7u64)]
fn capture_assume_leak_post_false(p: u64) -> u64 {
    let n = p;
    let _a = |x: u64| { trust_vc::assume!(n == 7u64); x };
    n
}

// finding 14 (1-based 15): captured-local assume leak discharging div-by-zero.
#[trust_vc::ensures(true)]
fn capture_assume_leak_divzero_false(p: u64, q: u64) {
    let d = q;
    let _a = |x: u64| { trust_vc::assume!(d != 0u64); x };
    let _z = p / d;
}

// finding 15 (1-based 16): two let-aliased locals coupled by an in-closure assume.
#[trust_vc::ensures(true)]
fn capture_assume_leak_couple_false(p: u64, q: u64) {
    let m = p;
    let k = q;
    let _a = |x: u64| { trust_vc::assume!(m == k); x };
    trust_vc::assert!(m == k);
}

// A later same-named local does not bind an earlier macro use. The assumption
// still references the captured outer `n` and must not escape the closure.
#[trust_vc::ensures(true)]
fn capture_assume_before_shadow_false(p: u64) {
    let n = p;
    let _a = |x: u64| {
        trust_vc::assume!(n == 7u64);
        let n = 0u64;
        let _z = n;
        x
    };
    trust_vc::assert!(n == 7u64);
}

// ---- (B) no over-rejection: legitimate shapes must verify ----

// read-only capture in a NON-assume closure; outer TRUE fact about the local.
#[trust_vc::ensures(true)]
fn capture_read_only_ok(p: u64) {
    let n = p;
    let _a = |_x: u64| -> u64 { n };
    trust_vc::assert!(n == p);
}

// assume-bearing closure capturing a local, but the OUTER fact is TRUE (n == p):
// the leak must neither help nor hurt — the straight-line truth must still hold.
#[trust_vc::ensures(true)]
fn capture_assume_closure_outer_true_ok(p: u64) {
    let n = p;
    let _a = |x: u64| { trust_vc::assume!(n == 7u64); x };
    trust_vc::assert!(n == p);
}

// top-level assume legitimately discharges the div-by-zero (no closure).
#[trust_vc::ensures(true)]
fn divzero_toplevel_assume_ok(p: u64, q: u64) {
    let d = q;
    trust_vc::assume!(d != 0u64);
    let _z = p / d;
}

// captured-PARAM direct assume (no alias local) — already sound under #74; must
// stay not-verified (regression guard that the param path is unchanged).
#[trust_vc::ensures(true)]
fn capture_param_direct_assume_false(n: u64) {
    let _a = |x: u64| { trust_vc::assume!(n == 7u64); x };
    trust_vc::assert!(n == 7u64);
}
"####;

fn run(func: &str) -> VerifyResult {
    let dir = std::env::temp_dir().join("trust_vc_be2_local_loop_capture");
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
        "{func} must NOT verify (false post-loop claim / leaked closure hypothesis), got Verified"
    );
}

fn assert_verified(func: &str) {
    let r = run(func);
    assert!(
        r.is_verified(),
        "{func} must verify (legitimate, no over-rejection), got: {r:?}"
    );
}

// ---- (A) false shapes ----

#[test]
fn struct_while_local_bump_false_is_not_verified() {
    assert_not_verified("struct_while_local_bump_false");
}

#[test]
fn struct_for_local_bump_false_is_not_verified() {
    assert_not_verified("struct_for_local_bump_false");
}

#[test]
fn vec_while_local_retain_false_is_not_verified() {
    assert_not_verified("vec_while_local_retain_false");
}

#[test]
fn vec_while_local_sort_false_is_not_verified() {
    assert_not_verified("vec_while_local_sort_false");
}

#[test]
fn vec_while_local_extend_false_is_not_verified() {
    assert_not_verified("vec_while_local_extend_false");
}

#[test]
fn vec_while_local_dedup_false_is_not_verified() {
    assert_not_verified("vec_while_local_dedup_false");
}

#[test]
fn vec_for_local_truncate_false_is_not_verified() {
    assert_not_verified("vec_for_local_truncate_false");
}

#[test]
fn array_while_local_reverse_false_is_not_verified() {
    assert_not_verified("array_while_local_reverse_false");
}

// ---- (A) no over-rejection ----

#[test]
fn vec_while_local_read_only_ok_verifies() {
    assert_verified("vec_while_local_read_only_ok");
}

#[test]
fn struct_while_local_read_only_ok_verifies() {
    assert_verified("struct_while_local_read_only_ok");
}

#[test]
fn struct_while_local_no_call_ok_verifies() {
    assert_verified("struct_while_local_no_call_ok");
}

#[test]
fn struct_while_local_pure_sort_name_ok_verifies() {
    assert_verified("struct_while_local_pure_sort_name_ok");
}

#[test]
fn collection_param_shadowed_by_struct_pure_sort_ok_verifies() {
    assert_verified("collection_param_shadowed_by_struct_pure_sort_ok");
}

#[test]
fn vec_local_push_true_no_loop_verifies() {
    assert_verified("vec_local_push_true_no_loop");
}

#[test]
fn array_while_local_read_only_ok_verifies() {
    assert_verified("array_while_local_read_only_ok");
}

// ---- (B) false shapes ----

#[test]
fn capture_assume_leak_outer_false_is_not_verified() {
    assert_not_verified("capture_assume_leak_outer_false");
}

#[test]
fn capture_cross_closure_leak_false_is_not_verified() {
    assert_not_verified("capture_cross_closure_leak_false");
}

#[test]
fn capture_assume_leak_twohop_false_is_not_verified() {
    assert_not_verified("capture_assume_leak_twohop_false");
}

#[test]
fn capture_assume_leak_post_false_is_not_verified() {
    assert_not_verified("capture_assume_leak_post_false");
}

#[test]
fn capture_assume_leak_divzero_false_is_not_verified() {
    assert_not_verified("capture_assume_leak_divzero_false");
}

#[test]
fn capture_assume_leak_couple_false_is_not_verified() {
    assert_not_verified("capture_assume_leak_couple_false");
}

#[test]
fn capture_assume_before_shadow_false_is_not_verified() {
    assert_not_verified("capture_assume_before_shadow_false");
}

// ---- (B) no over-rejection ----

#[test]
fn capture_read_only_ok_verifies() {
    assert_verified("capture_read_only_ok");
}

#[test]
fn capture_assume_closure_outer_true_ok_verifies() {
    assert_verified("capture_assume_closure_outer_true_ok");
}

#[test]
fn divzero_toplevel_assume_ok_verifies() {
    assert_verified("divzero_toplevel_assume_ok");
}

// regression guard: the captured-PARAM path remains sound (still not verified).
#[test]
fn capture_param_direct_assume_false_is_not_verified() {
    assert_not_verified("capture_param_direct_assume_false");
}
