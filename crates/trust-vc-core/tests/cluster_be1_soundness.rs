// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Round-10 cluster "be1" (`body_extract`) soundness guards — two sub-areas of
//! false-`Verified`s plus their cardinal NO-OVER-REJECTION duals.
//!
//!  (A) FOR-LOOP RANGE-BOUND / bare-`Range`-value arithmetic & index
//!      panic-freedom. The iterator expression of a `for` loop — and any `Range`
//!      / `RangeInclusive` value in an unconditionally-evaluated value position —
//!      EAGERLY evaluates each present bound at construction (before the first
//!      iteration), exactly like a `while` guard. A checked-arith / shift /
//!      negation site or an OOB index in a range bound (`0..(a / b)`,
//!      `(a / b)..n`, `0..(a + b)`, `0..=(a + b)`, `let _ = 0..(a / b)`) therefore
//!      carries a real exec panic obligation that `visit_expr_for_loop` and the
//!      value-position collectors never emitted — a silent false `Verified`. A
//!      SAFE range (`0..n`, a guarded `(a / b)..n` / `0..(a + b)`, a constant
//!      bound) must STILL verify; the loop BODY's own obligations are unchanged.
//!
//!  (B) NON-SCALAR `&mut` PARAMETER let-move alias. A bare `let q = p;` MOVES a
//!      `&mut S` / `&mut [T; N]` parameter, so `q` denotes the SAME referent; a
//!      place write through the alias (`q.f = ..`, `q[i] = ..`, `*q = ..`), a
//!      reborrow, or an escape mutates `p`'s referent, but is rooted at `q` — so
//!      the param was never flagged and a postcondition reading `p` resolved to
//!      its frozen ENTRY snapshot (a false `Verified`). The let-move-alias of a
//!      non-scalar `&mut` param is now tracked and fails closed on a postcondition
//!      reading the param. A read-only capture (`let q = p; let _ = q.f;`), a
//!      bare move with NO mutation, and a by-value scalar copy must STILL verify.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn run(src: &str, func: &str) -> VerifyResult {
    let dir = std::env::temp_dir().join("trust_vc_cluster_be1_soundness");
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
        "{func} must NOT verify (genuinely false / panicking goal), got Verified"
    );
}

fn assert_verified(src: &str, func: &str) {
    let r = run(src, func);
    assert!(
        r.is_verified(),
        "{func} must verify (legitimate, no over-rejection), got: {r:?}"
    );
}

// =====================================================================
// (A) for-loop range-bound + bare-Range-value arith / index
// =====================================================================

const SRC_A: &str = r####"
// ---- FALSE: div-by-zero in a range bound (upper, lower, both ends) ----
#[trust_vc::ensures(true)]
fn for_div_upper(a: u64, b: u64) { for _i in 0u64..(a / b) { trust_vc::assert!(true); } }

#[trust_vc::ensures(true)]
fn for_div_lower(a: u64, b: u64, n: u64) { for _i in (a / b)..n { trust_vc::assert!(true); } }

#[trust_vc::ensures(true)]
fn for_rem_zero(a: u64, b: u64) { for _i in 0u64..(a % b) { trust_vc::assert!(true); } }

// ---- FALSE: +/-/* overflow in a range bound ----
#[trust_vc::ensures(true)]
fn for_add_overflow(a: u64, b: u64) { for _i in 0u64..(a + b) { trust_vc::assert!(true); } }

#[trust_vc::ensures(true)]
fn for_sub_overflow(a: u64, b: u64) { for _i in 0u64..(a - b) { trust_vc::assert!(true); } }

#[trust_vc::ensures(true)]
fn for_mul_overflow(a: u64, b: u64) { for _i in 0u64..(a * b) { trust_vc::assert!(true); } }

// ---- FALSE: shift overflow in a range bound ----
#[trust_vc::ensures(true)]
fn for_shift_overflow(s: u32) { for _i in 0u64..(1u64 << s) { trust_vc::assert!(true); } }

// ---- FALSE: inclusive RangeInclusive upper bound ----
#[trust_vc::ensures(true)]
fn for_incl_add(a: u64, b: u64) { for _i in 0u64..=(a + b) { trust_vc::assert!(true); } }

// ---- FALSE: OOB index eagerly evaluated in a range bound ----
#[trust_vc::ensures(true)]
fn for_index_upper(ar: [u64; 2], i: usize) { for _x in 0u64..ar[i] { trust_vc::assert!(true); } }

// ---- FALSE: bare Range value (let-init) and bare Range statement ----
#[trust_vc::ensures(true)]
fn bare_range_let_div(a: u64, b: u64) { let _ = 0u64..(a / b); trust_vc::assert!(true); }

#[trust_vc::ensures(true)]
fn bare_range_stmt_div(a: u64, b: u64) { 0u64..(a / b); trust_vc::assert!(true); }

#[trust_vc::ensures(true)]
fn bare_range_let_index(ar: [u64; 2], i: usize) { let _ = 0u64..ar[i]; trust_vc::assert!(true); }

// ---- NO OVER-REJECTION: safe ranges must STILL verify ----
#[trust_vc::requires(b != 0u64)]
#[trust_vc::ensures(true)]
fn for_div_guarded(a: u64, b: u64) { for _i in 0u64..(a / b) { trust_vc::assert!(true); } }

#[trust_vc::requires(a < 100u64)]
#[trust_vc::requires(b < 100u64)]
#[trust_vc::ensures(true)]
fn for_add_guarded(a: u64, b: u64) { for _i in 0u64..(a + b) { trust_vc::assert!(true); } }

#[trust_vc::requires(a >= b)]
#[trust_vc::ensures(true)]
fn for_sub_guarded(a: u64, b: u64) { for _i in 0u64..(a - b) { trust_vc::assert!(true); } }

#[trust_vc::ensures(true)]
fn for_plain(n: u64) { for _i in 0u64..n { trust_vc::assert!(true); } }

#[trust_vc::ensures(true)]
fn for_const_bound(n: u64) { for _i in 0u64..(2u64 + 3u64) { trust_vc::assert!(true); } }

#[trust_vc::requires(b != 0u64)]
#[trust_vc::ensures(true)]
fn bare_range_let_safe(a: u64, b: u64) { let _ = 0u64..(a / b); trust_vc::assert!(true); }

#[trust_vc::requires(i < 2usize)]
#[trust_vc::ensures(true)]
fn for_index_guarded(ar: [u64; 2], i: usize) { for _x in 0u64..ar[i] { trust_vc::assert!(true); } }
"####;

#[test]
fn for_div_upper_bound_div_by_zero_not_verified() {
    assert_not_verified(SRC_A, "for_div_upper");
}
#[test]
fn for_div_lower_bound_div_by_zero_not_verified() {
    assert_not_verified(SRC_A, "for_div_lower");
}
#[test]
fn for_rem_zero_bound_not_verified() {
    assert_not_verified(SRC_A, "for_rem_zero");
}
#[test]
fn for_add_overflow_bound_not_verified() {
    assert_not_verified(SRC_A, "for_add_overflow");
}
#[test]
fn for_sub_overflow_bound_not_verified() {
    assert_not_verified(SRC_A, "for_sub_overflow");
}
#[test]
fn for_mul_overflow_bound_not_verified() {
    assert_not_verified(SRC_A, "for_mul_overflow");
}
#[test]
fn for_shift_overflow_bound_not_verified() {
    assert_not_verified(SRC_A, "for_shift_overflow");
}
#[test]
fn for_inclusive_add_overflow_bound_not_verified() {
    assert_not_verified(SRC_A, "for_incl_add");
}
#[test]
fn for_index_upper_bound_oob_not_verified() {
    assert_not_verified(SRC_A, "for_index_upper");
}
#[test]
fn bare_range_let_div_by_zero_not_verified() {
    assert_not_verified(SRC_A, "bare_range_let_div");
}
#[test]
fn bare_range_stmt_div_by_zero_not_verified() {
    assert_not_verified(SRC_A, "bare_range_stmt_div");
}
#[test]
fn bare_range_let_index_oob_not_verified() {
    assert_not_verified(SRC_A, "bare_range_let_index");
}

#[test]
fn for_div_guarded_verifies() {
    assert_verified(SRC_A, "for_div_guarded");
}
#[test]
fn for_add_guarded_verifies() {
    assert_verified(SRC_A, "for_add_guarded");
}
#[test]
fn for_sub_guarded_verifies() {
    assert_verified(SRC_A, "for_sub_guarded");
}
#[test]
fn for_plain_range_verifies() {
    assert_verified(SRC_A, "for_plain");
}
#[test]
fn for_const_bound_verifies() {
    assert_verified(SRC_A, "for_const_bound");
}
#[test]
fn bare_range_let_safe_verifies() {
    assert_verified(SRC_A, "bare_range_let_safe");
}
#[test]
fn for_index_guarded_verifies() {
    assert_verified(SRC_A, "for_index_guarded");
}

// =====================================================================
// (B) non-scalar &mut parameter let-move alias
// =====================================================================

const SRC_B: &str = r####"
struct S { f: u64, g: u64 }
impl S {
    fn bump(&mut self) { self.f = self.f + 1u64; }
    fn get(&self) -> u64 { self.f }
}
fn clobber(p: &mut S) { p.f = 99u64; }

// ---- FALSE: struct field write through a let-move alias ----
#[trust_vc::requires(p.f == 0u64)]
#[trust_vc::ensures(p.f == 0u64)]
fn struct_letmove_field_false(p: &mut S) { let q = p; q.f = 5u64; }

// ---- FALSE: chained let-move alias ----
#[trust_vc::requires(p.f == 0u64)]
#[trust_vc::ensures(p.f == 0u64)]
fn struct_letmove_chain_false(p: &mut S) { let q = p; let r = q; r.f = 5u64; }

// ---- FALSE: whole-referent write through `*q` ----
#[trust_vc::requires(p.f == 0u64)]
#[trust_vc::ensures(p.f == 0u64)]
fn struct_letmove_deref_false(p: &mut S) { let q = p; *q = S { f: 5u64, g: 6u64 }; }

// ---- FALSE: alias escapes into a free call that mutates ----
#[trust_vc::requires(p.f == 0u64)]
#[trust_vc::ensures(p.f == 0u64)]
fn struct_letmove_escape_false(p: &mut S) { let q = p; clobber(q); }

// ---- FALSE: &mut [T; N] array index write through a let-move alias ----
#[trust_vc::requires(a[0] == 0u64)]
#[trust_vc::ensures(a[0] == 0u64)]
fn array_letmove_index_false(a: &mut [u64; 3]) { let b = a; b[0] = 5u64; }

// ---- FALSE: method mutation through a let-move alias ----
#[trust_vc::requires(p.f == 0u64)]
#[trust_vc::ensures(p.f == 0u64)]
fn struct_letmove_method_false(p: &mut S) { let q = p; q.bump(); }

#[trust_vc::requires(v.len() == 2usize)]
#[trust_vc::ensures(v.len() == 2usize)]
fn vec_letmove_method_false(v: &mut Vec<u64>) { let q = v; q.clear(); }

#[trust_vc::requires(a[0] == 0u64)]
#[trust_vc::requires(a[1] == 1u64)]
#[trust_vc::ensures(a[0] == 0u64)]
fn array_letmove_method_false(a: &mut [u64; 2]) { let q = a; q.reverse(); }

// ---- NO OVER-REJECTION ----
// read-only capture: alias never mutated, postcondition on p stays sound
#[trust_vc::requires(p.f == 0u64)]
#[trust_vc::ensures(p.f == 0u64)]
fn struct_letmove_readonly_ok(p: &mut S) { let q = p; let _x = q.f; }

// bare move with NO mutation at all
#[trust_vc::requires(p.f == 0u64)]
#[trust_vc::ensures(p.f == 0u64)]
fn struct_letmove_nomut_ok(p: &mut S) { let _q = p; }

// pure method reads through aliases do not mutate the referent
#[trust_vc::requires(p.f == 0u64)]
#[trust_vc::ensures(p.f == 0u64)]
fn struct_letmove_method_read_ok(p: &mut S) { let q = p; let _x = q.get(); }

#[trust_vc::requires(v.len() == 2usize)]
#[trust_vc::ensures(v.len() == 2usize)]
fn vec_letmove_method_read_ok(v: &mut Vec<u64>) { let q = v; let _x = q.len(); }

// a same-named local shadows the parameter and must not be mistaken for it
#[trust_vc::requires(p.f == 0u64)]
#[trust_vc::ensures(p.f == 0u64)]
fn struct_param_shadow_method_ok(p: &mut S) {
    let mut p = S { f: 10u64, g: 11u64 };
    p.bump();
}

// the parameter remains visible while a same-named shadow's initializer runs
#[trust_vc::requires(p.f == 0u64)]
#[trust_vc::ensures(p.f == 0u64)]
fn struct_param_shadow_initializer_false(p: &mut S) {
    let p = { p.bump(); S { f: 10u64, g: 11u64 } };
    let _x = p.f;
}

// by-value scalar copy is unaffected by the non-scalar &mut path
#[trust_vc::requires(c == 3u64)]
#[trust_vc::ensures(c == 3u64)]
fn scalar_copy_ok(c: u64) { let _n = c; }
"####;

#[test]
fn struct_letmove_field_write_not_verified() {
    assert_not_verified(SRC_B, "struct_letmove_field_false");
}
#[test]
fn struct_letmove_chain_write_not_verified() {
    assert_not_verified(SRC_B, "struct_letmove_chain_false");
}
#[test]
fn struct_letmove_deref_write_not_verified() {
    assert_not_verified(SRC_B, "struct_letmove_deref_false");
}
#[test]
fn struct_letmove_escape_call_not_verified() {
    assert_not_verified(SRC_B, "struct_letmove_escape_false");
}
#[test]
fn array_letmove_index_write_not_verified() {
    assert_not_verified(SRC_B, "array_letmove_index_false");
}
#[test]
fn struct_letmove_method_mutation_not_verified() {
    assert_not_verified(SRC_B, "struct_letmove_method_false");
}
#[test]
fn vec_letmove_method_mutation_not_verified() {
    assert_not_verified(SRC_B, "vec_letmove_method_false");
}
#[test]
fn array_letmove_method_mutation_not_verified() {
    assert_not_verified(SRC_B, "array_letmove_method_false");
}

#[test]
fn struct_letmove_readonly_capture_verifies() {
    assert_verified(SRC_B, "struct_letmove_readonly_ok");
}
#[test]
fn struct_letmove_no_mutation_verifies() {
    assert_verified(SRC_B, "struct_letmove_nomut_ok");
}
#[test]
fn struct_letmove_method_read_verifies() {
    assert_verified(SRC_B, "struct_letmove_method_read_ok");
}
#[test]
fn vec_letmove_method_read_verifies() {
    assert_verified(SRC_B, "vec_letmove_method_read_ok");
}
#[test]
fn struct_param_shadow_method_verifies() {
    assert_verified(SRC_B, "struct_param_shadow_method_ok");
}
#[test]
fn struct_param_shadow_initializer_mutation_not_verified() {
    assert_not_verified(SRC_B, "struct_param_shadow_initializer_false");
}
#[test]
fn scalar_copy_unaffected_verifies() {
    assert_verified(SRC_B, "scalar_copy_ok");
}
