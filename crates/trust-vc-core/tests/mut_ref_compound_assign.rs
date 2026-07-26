// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Slice C of the mut-ref two-state keystone: COMPOUND assignment through a
//! dereference (`*P op= rhs`) and SEQUENTIAL deref writes (`*P = a; *P = b;`)
//! on supported scalar `&mut` params.
//!
//! Semantics: `*P op= rhs` desugars AT THE AST LEVEL to the already-modeled
//! single-write funnel `*P = (*P) op (rhs)` — read the CURRENT scoped value
//! (the entry symbol when untouched), apply the operator, rebind — so the SSA
//! chain, `old()` entry semantics (slices A+B), `clean_finals` contract
//! resolution and the deref-write RHS panic-safety obligations are inherited
//! from the plain-write path by construction. Sequential writes rebind in
//! order: the once-only guard (the alias→target mapping shadowed by the first
//! write's value binding) is lifted by re-pinning the mapping at the binding's
//! frame; plain rebinds of the name and `let` shadows still clear/shadow it.
//!
//! THE WRONG-VERIFY LANDMINE this suite pins in BOTH directions: SSA-chain
//! staleness. A compound op reading a STALE value (entry instead of current
//! after a prior write) proves wrong facts — `*x = 10; *x += 1;` must make
//! `*x == 11` Verified AND `*x == 6` (entry 5 + 1) a Counterexample. The
//! chain `*x += 1; *x *= 2;` from 5 must make `12` Verified and BOTH `7`
//! (precedence-loss `5 + 1*2`) and `10` (stale-entry `5*2`) Counterexamples.
//!
//! OVERFLOW PARITY (probed FIRST, then pinned): before slice C the deref-write
//! branches emitted NO panic-safety obligation at all — the EXPLICIT spelling
//! `*x = *x + 1` at `u64::MAX` silently Verified (empty context) while the
//! same RHS on a local carried an overflow Counterexample. Slice C closes that
//! hole for the explicit spelling and the desugared compound TOGETHER (both
//! route through the same `assign_expr` deref branches), so both spellings now
//! CE identically on unbounded `+= / -= / /= 0 / <<= width` — pinned here in
//! both spellings, plus the bounded Verified companions.
//!
//! Fail-closed boundaries pinned: compound through a NON-`Local` target
//! (field-projected alias, on a param-rooted or local struct), through a
//! non-scalar `&mut` param (`String`), or with an RHS containing an embedded
//! assignment (real compound assignment evaluates the RHS BEFORE reading the
//! place; the desugar reads the place first, so an embedded same-place write
//! would be silently reordered) all keep the PRE-EXISTING hard error
//! ("assignment through a dereferenced reference is unsupported") VERBATIM.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
// ---------- (a) upstream basic.rs test_compound_assign faithful shapes ----------

// The deref slice of upstream test1 (`*y /= 2; assert(*y == *old(y)/2);`),
// same u32 width, no contracts. (Upstream test1 also has a LOCAL compound
// `x += 2; assert(x == 3)` — that is a separate pre-existing gap: the scalar
// local compound path invalidates the binding, so the assert fails closed
// with "unresolved variable"; out of slice C's deref scope.)
fn upstream_test1_deref_slice(y: &mut u32) {
    *y /= 2u32;
    trust_vc::assert!(*y == *old(y) / 2u32);
}

// The contract form of the same shape.
#[trust_vc::requires(*old(y) < 100u64)]
#[trust_vc::ensures(*y == *old(y) / 2u64)]
fn compound_div_contract_verified(y: &mut u64) {
    *y /= 2u64;
}

// Wrong-relation twin (non-vacuity): /3 instead of /2 must CE.
#[trust_vc::requires(*old(y) < 100u64)]
#[trust_vc::requires(*old(y) >= 10u64)]
#[trust_vc::ensures(*y == *old(y) / 3u64)]
fn compound_div_contract_wrong_relation(y: &mut u64) {
    *y /= 2u64;
}

// Upstream test_compound_assign_fail test1: `*x /= y` with unbounded divisor
// must fail (possible division by zero).
fn upstream_fail_test1_div_by_zero(x: &mut u64, y: u64) {
    *x /= y;
}

// ---------- (b) per-operator smokes: correct assert Verified, wrong assert CE ----------
// The wrong assert is always the ENTRY value — a stale-read tripwire per op.

#[trust_vc::requires(x == 5u64)]
fn op_add(x: &mut u64) { *x += 3u64; trust_vc::assert!(*x == 8u64); }
#[trust_vc::requires(x == 5u64)]
fn op_add_stale(x: &mut u64) { *x += 3u64; trust_vc::assert!(*x == 5u64); }

#[trust_vc::requires(x == 10u64)]
fn op_sub(x: &mut u64) { *x -= 4u64; trust_vc::assert!(*x == 6u64); }
#[trust_vc::requires(x == 10u64)]
fn op_sub_stale(x: &mut u64) { *x -= 4u64; trust_vc::assert!(*x == 10u64); }

#[trust_vc::requires(x == 7u64)]
fn op_mul(x: &mut u64) { *x *= 3u64; trust_vc::assert!(*x == 21u64); }
#[trust_vc::requires(x == 7u64)]
fn op_mul_stale(x: &mut u64) { *x *= 3u64; trust_vc::assert!(*x == 7u64); }

#[trust_vc::requires(x == 20u64)]
fn op_div(x: &mut u64) { *x /= 4u64; trust_vc::assert!(*x == 5u64); }
#[trust_vc::requires(x == 20u64)]
fn op_div_stale(x: &mut u64) { *x /= 4u64; trust_vc::assert!(*x == 20u64); }

#[trust_vc::requires(x == 23u64)]
fn op_rem(x: &mut u64) { *x %= 5u64; trust_vc::assert!(*x == 3u64); }
#[trust_vc::requires(x == 23u64)]
fn op_rem_stale(x: &mut u64) { *x %= 5u64; trust_vc::assert!(*x == 23u64); }

#[trust_vc::requires(x == 12u64)]
fn op_bitand(x: &mut u64) { *x &= 10u64; trust_vc::assert!(*x == 8u64); }
#[trust_vc::requires(x == 12u64)]
fn op_bitand_stale(x: &mut u64) { *x &= 10u64; trust_vc::assert!(*x == 12u64); }

#[trust_vc::requires(x == 12u64)]
fn op_bitor(x: &mut u64) { *x |= 3u64; trust_vc::assert!(*x == 15u64); }
#[trust_vc::requires(x == 12u64)]
fn op_bitor_stale(x: &mut u64) { *x |= 3u64; trust_vc::assert!(*x == 12u64); }

#[trust_vc::requires(x == 12u64)]
fn op_bitxor(x: &mut u64) { *x ^= 10u64; trust_vc::assert!(*x == 6u64); }
#[trust_vc::requires(x == 12u64)]
fn op_bitxor_stale(x: &mut u64) { *x ^= 10u64; trust_vc::assert!(*x == 12u64); }

#[trust_vc::requires(x == 3u64)]
fn op_shl(x: &mut u64) { *x <<= 2u64; trust_vc::assert!(*x == 12u64); }
#[trust_vc::requires(x == 3u64)]
fn op_shl_stale(x: &mut u64) { *x <<= 2u64; trust_vc::assert!(*x == 3u64); }

#[trust_vc::requires(x == 12u64)]
fn op_shr(x: &mut u64) { *x >>= 2u64; trust_vc::assert!(*x == 3u64); }
#[trust_vc::requires(x == 12u64)]
fn op_shr_stale(x: &mut u64) { *x >>= 2u64; trust_vc::assert!(*x == 12u64); }

// ---------- (c) SSA chain: value tracking in order, both directions ----------

// write-then-compound: 10 + 1 = 11; the stale read would be entry 5 + 1 = 6.
#[trust_vc::requires(x == 5u64)]
fn chain_write_then_compound(x: &mut u64) {
    *x = 10u64;
    *x += 1u64;
    trust_vc::assert!(*x == 11u64);
}
#[trust_vc::requires(x == 5u64)]
fn chain_write_then_compound_stale(x: &mut u64) {
    *x = 10u64;
    *x += 1u64;
    trust_vc::assert!(*x == 6u64);
}

// compound-then-compound: (5+1)*2 = 12; precedence-loss would be 5+1*2 = 7;
// stale-entry second op would be 5*2 = 10.
#[trust_vc::requires(x == 5u64)]
fn chain_compound_compound(x: &mut u64) {
    *x += 1u64;
    *x *= 2u64;
    trust_vc::assert!(*x == 12u64);
}
#[trust_vc::requires(x == 5u64)]
fn chain_compound_compound_precedence_tripwire(x: &mut u64) {
    *x += 1u64;
    *x *= 2u64;
    trust_vc::assert!(*x == 7u64);
}
#[trust_vc::requires(x == 5u64)]
fn chain_compound_compound_stale(x: &mut u64) {
    *x += 1u64;
    *x *= 2u64;
    trust_vc::assert!(*x == 10u64);
}

// sequential plain writes (the slice-B once-only reject, now lifted).
#[trust_vc::requires(x == 5u64)]
fn chain_sequential_plain(x: &mut u64) {
    *x = 10u64;
    *x = 20u64;
    trust_vc::assert!(*x == 20u64);
}
#[trust_vc::requires(x == 5u64)]
fn chain_sequential_plain_stale(x: &mut u64) {
    *x = 10u64;
    *x = 20u64;
    trust_vc::assert!(*x == 10u64);
}

// compound-then-plain: the final plain write wins.
#[trust_vc::requires(x == 5u64)]
fn chain_compound_then_plain(x: &mut u64) {
    *x += 1u64;
    *x = 3u64;
    trust_vc::assert!(*x == 3u64);
}
#[trust_vc::requires(x == 5u64)]
fn chain_compound_then_plain_stale(x: &mut u64) {
    *x += 1u64;
    *x = 3u64;
    trust_vc::assert!(*x == 6u64);
}

// compound chain through a reborrow alias, observed through the param.
#[trust_vc::requires(x == 5u64)]
fn chain_alias_compound(x: &mut u64) {
    let r: &mut u64 = &mut *x;
    *r += 1u64;
    *r *= 2u64;
    trust_vc::assert!(*x == 12u64);
}

// reborrow-of-reborrow still resolves to the same Local target (parity with
// the plain-write alias support).
#[trust_vc::requires(x == 5u64)]
fn chain_reborrow_chain_compound(x: &mut u64) {
    let r: &mut u64 = &mut *x;
    let rr: &mut u64 = &mut *r;
    *rr += 1u64;
    trust_vc::assert!(*x == 6u64);
}

// ---------- (d) old() across compound/sequential writes (A+B preserved) ----------

#[trust_vc::requires(x == 5u64)]
fn old_across_compound_entry(x: &mut u64) {
    *x = 10u64;
    *x += 4u64;
    trust_vc::assert!(old(x) == 5u64);
    trust_vc::assert!(*x == 14u64);
}
// If old() ever read the post state after the chain — catastrophic direction.
#[trust_vc::requires(x == 5u64)]
fn old_across_compound_post_tripwire(x: &mut u64) {
    *x = 10u64;
    *x += 4u64;
    trust_vc::assert!(old(x) == 14u64);
}

// Callee-side ensures resolver sees the FINAL value after the chain.
#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(*x == old(x) * 2u64 + 1u64)]
fn ensures_final_after_chain(x: &mut u64) {
    *x *= 2u64;
    *x += 1u64;
}
#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(*x == old(x))]
fn ensures_final_after_chain_wrong(x: &mut u64) {
    *x *= 2u64;
    *x += 1u64;
}

// ---------- (e) overflow / panic-safety parity (probed first, then pinned) ----------
// PROBED BASELINE: before slice C the explicit spelling `*x = *x + 1` emitted
// NO obligation at all ("Cannot verify empty context") — a silent hole. Both
// spellings now carry the same obligation class and CE together.

// explicit spelling, unbounded: must CE on possible addition overflow.
fn overflow_explicit_add_unbounded(x: &mut u64) {
    *x = *x + 1u64;
}
// compound spelling, unbounded: same class.
fn overflow_compound_add_unbounded(x: &mut u64) {
    *x += 1u64;
}
// compound at pinned MAX: must CE, never silently verify.
#[trust_vc::requires(x == 18446744073709551615u64)]
fn overflow_compound_add_at_max(x: &mut u64) {
    *x += 1u64;
}
// bounded companion verifies (the check must not over-reject).
#[trust_vc::requires(x < 100u64)]
fn overflow_compound_add_bounded(x: &mut u64) {
    *x += 1u64;
    trust_vc::assert!(*x < 101u64);
}
// subtraction underflow, unbounded.
fn overflow_compound_sub_unbounded(x: &mut u64) {
    *x -= 1u64;
}
// division by an unbounded divisor (upstream _fail twin lives in (a)).
fn overflow_compound_div_unbounded(x: &mut u64, d: u64) {
    *x /= d;
}
// left shift by an unbounded amount.
fn overflow_compound_shl_unbounded(x: &mut u64, d: u64) {
    *x <<= d;
}

// ---------- (f) fail-closed boundaries (pre-existing error kept verbatim) ----------

struct S {
    f: u64,
}

// field-projected alias on a `&mut` struct param.
#[trust_vc::requires(s.f == 5u64)]
fn reject_field_alias_compound_param(s: &mut S) {
    let r: &mut u64 = &mut s.f;
    *r += 1u64;
}

// field-projected alias on a LOCAL struct (a `Field` target, not `Local`).
fn reject_field_alias_compound_local() {
    let mut s = S { f: 5u64 };
    let r: &mut u64 = &mut s.f;
    *r += 1u64;
}

// non-scalar `&mut` param (String is not a supported scalar target).
fn reject_nonscalar_compound(s: &mut String) {
    *s += "a";
}

// RHS with an embedded same-place write: real compound assignment evaluates
// the RHS BEFORE reading the place; the desugar reads the place first — must
// stay rejected, never silently reordered.
#[trust_vc::requires(x == 5u64)]
fn reject_side_effecting_rhs(x: &mut u64) {
    *x += { *x = 3u64; 1u64 };
}
"####;

fn run(func: &str) -> VerifyResult {
    // The on-disk VC-result cache stores only `verified` verdicts and replays
    // them without re-encoding — it MUST be disabled for true verdicts.
    // Serialized behind the process-wide env lock and restored on scope exit
    // (guards drop before the lock releases) via the workspace env choke point.
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir = std::env::temp_dir().join("trust_vc_mut_ref_compound_assign");
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

fn assert_verified(func: &str) {
    let r = run(func);
    assert!(
        r.is_verified(),
        "{func} must verify (no over-rejection), got: {r:?}"
    );
}

fn assert_counterexample(func: &str) {
    let r = run(func);
    assert!(
        r.is_counterexample(),
        "{func} must be a Counterexample (never Verified — directionality), got: {r:?}"
    );
}

/// Counterexample whose obligation name carries the expected panic class —
/// pins that the CE is the SAFETY obligation, not an incidental assert.
fn assert_counterexample_named(func: &str, fragment: &str) {
    let r = run(func);
    let VerifyResult::Counterexample {
        obligation_name, ..
    } = &r
    else {
        panic!("{func} must be a Counterexample, got: {r:?}");
    };
    assert!(
        obligation_name.contains(fragment),
        "{func} counterexample must be the `{fragment}` obligation, got: {obligation_name}"
    );
}

fn assert_error_contains(func: &str, fragment: &str) {
    let r = run(func);
    let VerifyResult::Error { message } = &r else {
        panic!("{func} must fail closed with Error, got: {r:?}");
    };
    assert!(
        message.contains(fragment),
        "{func} error must contain `{fragment}`, got: {message}"
    );
}

// The pre-existing deref-write rejection, kept verbatim for unsupported shapes.
const DEREF_HARD_ERROR: &str = "assignment through a dereferenced reference is unsupported";

// ---- (a) upstream faithful shapes ----

#[test]
fn battery_a_upstream_test1_deref_slice_verified() {
    assert_verified("upstream_test1_deref_slice");
}

#[test]
fn battery_a_compound_div_contract_verified() {
    assert_verified("compound_div_contract_verified");
}

#[test]
fn battery_a_compound_div_contract_wrong_relation_counterexample() {
    assert_counterexample("compound_div_contract_wrong_relation");
}

#[test]
fn battery_a_upstream_fail_test1_div_by_zero_counterexample() {
    assert_counterexample_named("upstream_fail_test1_div_by_zero", "division by zero");
}

// ---- (b) per-operator smokes ----

#[test]
fn battery_b_op_add() {
    assert_verified("op_add");
    assert_counterexample("op_add_stale");
}

#[test]
fn battery_b_op_sub() {
    assert_verified("op_sub");
    assert_counterexample("op_sub_stale");
}

#[test]
fn battery_b_op_mul() {
    assert_verified("op_mul");
    assert_counterexample("op_mul_stale");
}

#[test]
fn battery_b_op_div() {
    assert_verified("op_div");
    assert_counterexample("op_div_stale");
}

#[test]
fn battery_b_op_rem() {
    assert_verified("op_rem");
    assert_counterexample("op_rem_stale");
}

#[test]
fn battery_b_op_bitand() {
    assert_verified("op_bitand");
    assert_counterexample("op_bitand_stale");
}

#[test]
fn battery_b_op_bitor() {
    assert_verified("op_bitor");
    assert_counterexample("op_bitor_stale");
}

#[test]
fn battery_b_op_bitxor() {
    assert_verified("op_bitxor");
    assert_counterexample("op_bitxor_stale");
}

#[test]
fn battery_b_op_shl() {
    assert_verified("op_shl");
    assert_counterexample("op_shl_stale");
}

#[test]
fn battery_b_op_shr() {
    assert_verified("op_shr");
    assert_counterexample("op_shr_stale");
}

// ---- (c) SSA chain, both directions ----

#[test]
fn battery_c_chain_write_then_compound() {
    assert_verified("chain_write_then_compound");
    assert_counterexample("chain_write_then_compound_stale");
}

#[test]
fn battery_c_chain_compound_compound() {
    assert_verified("chain_compound_compound");
    assert_counterexample("chain_compound_compound_precedence_tripwire");
    assert_counterexample("chain_compound_compound_stale");
}

#[test]
fn battery_c_chain_sequential_plain() {
    assert_verified("chain_sequential_plain");
    assert_counterexample("chain_sequential_plain_stale");
}

#[test]
fn battery_c_chain_compound_then_plain() {
    assert_verified("chain_compound_then_plain");
    assert_counterexample("chain_compound_then_plain_stale");
}

#[test]
fn battery_c_chain_alias_compound() {
    assert_verified("chain_alias_compound");
}

#[test]
fn battery_c_chain_reborrow_chain_compound() {
    assert_verified("chain_reborrow_chain_compound");
}

// ---- (d) old() interaction ----

#[test]
fn battery_d_old_across_compound_entry() {
    assert_verified("old_across_compound_entry");
}

#[test]
fn battery_d_old_across_compound_post_tripwire_counterexample() {
    assert_counterexample("old_across_compound_post_tripwire");
}

#[test]
fn battery_d_ensures_final_after_chain() {
    assert_verified("ensures_final_after_chain");
    assert_counterexample("ensures_final_after_chain_wrong");
}

// ---- (e) overflow / panic-safety parity ----

#[test]
fn battery_e_overflow_explicit_add_unbounded_counterexample() {
    assert_counterexample_named("overflow_explicit_add_unbounded", "addition overflow");
}

#[test]
fn battery_e_overflow_compound_add_unbounded_counterexample() {
    assert_counterexample_named("overflow_compound_add_unbounded", "addition overflow");
}

#[test]
fn battery_e_overflow_compound_add_at_max_counterexample() {
    assert_counterexample_named("overflow_compound_add_at_max", "addition overflow");
}

#[test]
fn battery_e_overflow_compound_add_bounded_verified() {
    assert_verified("overflow_compound_add_bounded");
}

#[test]
fn battery_e_overflow_compound_sub_unbounded_counterexample() {
    assert_counterexample_named("overflow_compound_sub_unbounded", "subtraction overflow");
}

#[test]
fn battery_e_overflow_compound_div_unbounded_counterexample() {
    assert_counterexample_named("overflow_compound_div_unbounded", "division by zero");
}

#[test]
fn battery_e_overflow_compound_shl_unbounded_counterexample() {
    assert_counterexample_named("overflow_compound_shl_unbounded", "shift overflow");
}

// ---- (f) fail-closed boundaries ----

#[test]
fn battery_f_reject_field_alias_compound_param() {
    assert_error_contains("reject_field_alias_compound_param", DEREF_HARD_ERROR);
}

#[test]
fn battery_f_reject_field_alias_compound_local() {
    assert_error_contains("reject_field_alias_compound_local", DEREF_HARD_ERROR);
}

#[test]
fn battery_f_reject_nonscalar_compound() {
    assert_error_contains("reject_nonscalar_compound", DEREF_HARD_ERROR);
}

#[test]
fn battery_f_reject_side_effecting_rhs() {
    assert_error_contains("reject_side_effecting_rhs", DEREF_HARD_ERROR);
}
