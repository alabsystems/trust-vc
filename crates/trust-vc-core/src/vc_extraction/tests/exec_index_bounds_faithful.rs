// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness + parity regressions for exec array/slice index-bounds obligations
//! (#81).
//!
//! Before this fix, trust-vc emitted an array index-bounds obligation ONLY by
//! re-encoding an ASSERTION expression that mentioned the access; an exec access
//! whose value was discarded or never observed carried NO obligation and silently
//! `Verified` despite a runtime out-of-bounds panic — UNLIKE the per-site scalar
//! arithmetic path. The fix pins a reflexive `(a[i]) == (a[i])` obligation at each
//! exec index ACCESS (read, bare statement, scalar-assign RHS, index-write, and
//! compound-write — the last also routing the element through the overflow check),
//! gated on `check_overflow()` and DEFERRED inside loop bodies exactly like the
//! arithmetic path.
//!
//! These tests pin BOTH directions:
//! * SOUNDNESS — an unobserved access with an unbounded / out-of-bounds index (or
//!   an unbounded `+=` element) is rejected (Counterexample or fail-closed
//!   Unknown), NEVER `Verified`.
//! * NO OVER-REJECTION — a literal in-bounds index, a `requires`-bounded index,
//!   the #77 dependent fixed-array case, and a concrete-element compound write all
//!   still `Verified`; a loop-body access stays deferred (no spurious
//!   counterexample).

use super::*;
use crate::encoder::VerifyResult;

fn verdict(code: &str, name: &str) -> VerifyResult {
    let file = parse_file(code).expect("fixture should parse");
    let func =
        find_function(&file, name).unwrap_or_else(|| panic!("fixture should define fn {name}"));
    let vc = extract_verification_conditions(func)
        .unwrap_or_else(|err| panic!("fn {name} should extract: {err}"));
    vc.verify()
}

/// Fail-closed: the access is rejected as a model-bearing counterexample, a
/// model-less non-proof, or an inconclusive Unknown — never `Verified` (and
/// never a silent extraction `Error`).
///
/// `NotProved` is the incompleteness FAILURE of
/// `docs/design-unknown-as-failure.md`; for these bounds checks it is a
/// strictly STRONGER rejection than the `Unknown` this list originally
/// enumerated, so accepting it preserves the fail-closed intent exactly.
fn assert_not_verified(code: &str, name: &str, what: &str) {
    match verdict(code, name) {
        VerifyResult::Counterexample { .. }
        | VerifyResult::NotProved { .. }
        | VerifyResult::Unknown { .. } => {}
        other => {
            panic!("{what}: expected Counterexample/NotProved/Unknown (fail closed), got {other:?}")
        }
    }
}

/// Fail-closed across the WHOLE pipeline: either extraction REJECTS the function
/// (an `Err`, the soundest fail-closed outcome) or it extracts to a non-`Verified`
/// verdict. Only a `Verified` is the catastrophic false positive. Used for inputs
/// trust-vc refuses to model rather than verify (e.g. a compound write whose
/// side-effecting index does not fold to a re-usable pure value).
fn assert_extract_or_verify_fails_closed(code: &str, name: &str, what: &str) {
    let file = parse_file(code).expect("fixture should parse");
    let func =
        find_function(&file, name).unwrap_or_else(|| panic!("fixture should define fn {name}"));
    match extract_verification_conditions(func) {
        Err(_) => {}
        Ok(vc) => {
            if let VerifyResult::Verified = vc.verify() {
                panic!("{what}: expected a fail-closed (non-Verified) verdict, got Verified");
            }
        }
    }
}

/// Fail-closed in the broad sense: any non-`Verified` verdict (Counterexample,
/// Unknown, or an extraction/lowering Error) is acceptable — only `Verified`
/// would be the catastrophic false positive.
fn assert_fails_closed(code: &str, name: &str, what: &str) {
    if let VerifyResult::Verified = verdict(code, name) {
        panic!("{what}: expected a fail-closed (non-Verified) verdict, got Verified");
    }
}

fn assert_counterexample(code: &str, name: &str, what: &str) {
    match verdict(code, name) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("{what}: expected Counterexample, got {other:?}"),
    }
}

fn assert_verified(code: &str, name: &str, what: &str) {
    match verdict(code, name) {
        VerifyResult::Verified => {}
        other => panic!("{what}: expected Verified, got {other:?}"),
    }
}

fn assert_not_counterexample(code: &str, name: &str, what: &str) {
    if let VerifyResult::Counterexample { model, .. } = verdict(code, name) {
        panic!("{what}: expected no spurious counterexample, got Counterexample {model:?}")
    }
}

// ========================================================================
// SOUNDNESS direction: unobserved / unbounded accesses must fail closed.
// ========================================================================

#[test]
fn unobserved_unbounded_read_let_is_rejected() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let _ = ar[i];
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = ar[i] (unbounded i)",
    );
}

#[test]
fn unobserved_unbounded_bare_read_is_rejected() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            ar[i];
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "ar[i]; (unbounded i)",
    );
}

#[test]
fn unobserved_unbounded_scalar_assign_rhs_is_rejected() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let mut x: usize = 0;
            x = ar[i];
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "x = ar[i] (unbounded i)",
    );
}

#[test]
fn unobserved_unbounded_index_write_is_rejected() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize, v: usize) {
            ar[i] = v;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "ar[i] = v (unbounded i)",
    );
}

#[test]
fn unobserved_unbounded_compound_write_is_rejected() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            ar[i] += 1usize;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "ar[i] += 1 (unbounded i)",
    );
}

#[test]
fn unobserved_nested_unbounded_read_is_rejected() {
    // The outer index `ar[0]` is unconstrained, so `ar[ar[0]]` can be OOB.
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20]) {
            let _ = ar[ar[0usize]];
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = ar[ar[0]] (unbounded outer index)",
    );
}

#[test]
fn compound_write_element_overflow_is_caught() {
    // The index `3` is in bounds, but `ar[3]: usize` is unconstrained, so the
    // element arithmetic `ar[3] + usize::MAX` overflows — a genuine Verus error
    // that the routed element-overflow check must catch.
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20]) {
            ar[3usize] += 18446744073709551615usize;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "ar[3] += usize::MAX (element overflow)",
    );
}

// ========================================================================
// NO-OVER-REJECTION direction: provably-bounded accesses still Verify.
// ========================================================================

#[test]
fn literal_in_bounds_read_verifies() {
    assert_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20]) {
            let _ = ar[3usize];
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = ar[3] on [_; 20]",
    );
}

#[test]
fn requires_bounded_index_read_verifies() {
    assert_verified(
        r#"
        #[trust_vc::requires(i < 20)]
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let _ = ar[i];
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "requires(i < 20); let _ = ar[i]",
    );
}

#[test]
fn requires_bounded_index_write_verifies() {
    assert_verified(
        r#"
        #[trust_vc::requires(i < 20)]
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize, v: usize) {
            ar[i] = v;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "requires(i < 20); ar[i] = v",
    );
}

#[test]
fn concrete_element_literal_compound_write_verifies() {
    // `a[1]` is concretely 0 from the array literal, so `a[1] + 1 = 1` cannot
    // overflow and the literal index `1 < 3` is in bounds.
    assert_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f() {
            let mut a = [0u8; 3];
            a[1usize] += 1u8;
            trust_vc::assert!(a[1usize] == 1u8);
        }
        "#,
        "f",
        "let mut a = [0u8;3]; a[1] += 1",
    );
}

#[test]
fn dependent_fixed_array_compound_write_verifies() {
    // The #77 dependent fixed-array case: the symbolic index `ar[0]` is
    // discharged in pure BV against the static length `20`, and the `requires`
    // bound the elements so neither element arithmetic overflows.
    assert_verified(
        r#"
        #[trust_vc::requires(ar[0usize] == 1usize)]
        #[trust_vc::requires(ar[2usize] == 2usize)]
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20]) {
            ar[0usize] += 1usize;
            ar[ar[0usize]] += 1usize;
            trust_vc::assert!(ar[0usize] == 2usize);
            trust_vc::assert!(ar[2usize] == 3usize);
        }
        "#,
        "f",
        "requires(ar[0]==1, ar[2]==2); ar[0]+=1; ar[ar[0]]+=1",
    );
}

#[test]
fn loop_body_access_is_deferred_not_spurious_counterexample() {
    // The body access `ar[i]` is deferred exactly like the arithmetic path, so it
    // must NOT produce a spurious counterexample (the loop guard/invariant are not
    // routed into body-site obligations). The accepted, sound incompleteness is an
    // Unknown / Verified, never a body-site OOB counterexample.
    assert_not_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20]) {
            let mut i: usize = 0;
            while i < 20 {
                let _ = ar[i];
                i = i + 1;
            }
        }
        "#,
        "f",
        "while i < 20 { let _ = ar[i]; }",
    );
}

#[test]
fn scalar_arithmetic_discarded_still_counterexample() {
    // Regression guard: the pre-existing scalar arithmetic-safety path is
    // unaffected — a discarded `x + y` is still a counterexample at the overflow.
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(x: usize, y: usize) {
            let _ = x + y;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = x + y (scalar overflow)",
    );
}

// ========================================================================
// Unsupported features still fail closed WITHOUT a spurious synthetic
// obligation (the index instrumentation skips un-modelable receivers and
// side-effecting compound writes, so it does not perturb the blocked outcome).
// ========================================================================

#[test]
fn unmodelable_split_at_mut_receiver_is_not_falsely_verified() {
    // `left`/`right` come from an unsupported `split_at_mut`; the write bound is
    // skipped (un-modelable receiver) so the function still fails closed on its
    // own, never `Verified`.
    assert_fails_closed(
        r#"
        #[trust_vc::ensures(true)]
        fn f() {
            let mut v: Vec<u64> = Vec::new();
            v.push(1u64);
            v.push(2u64);
            v.push(3u64);
            let (left, right) = v.as_mut_slice().split_at_mut(2usize);
            left[1usize] = 20u64;
            right[0usize] = 30u64;
            trust_vc::assert!(v[1usize] == 20u64);
        }
        "#,
        "f",
        "split_at_mut writes to left/right",
    );
}

// ========================================================================
// NESTED value-position accesses (the narrower residual of #81): an index
// access nested in a tuple / array / struct literal or a call/method argument
// is evaluated — and can panic OOB — just like a top-level access. The
// value-position collector now recurses into those unconditionally-evaluated
// sub-positions, so an unbounded nested access fails closed and a
// provably-bounded one still verifies.
// ========================================================================

#[test]
fn nested_tuple_unbounded_read_is_rejected() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let _ = (ar[i], 0usize);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = (ar[i], 0) (unbounded i)",
    );
}

#[test]
fn nested_array_repeat_unbounded_read_is_rejected() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let _ = [ar[i]; 1];
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = [ar[i]; 1] (unbounded i)",
    );
}

#[test]
fn nested_array_list_unbounded_read_is_rejected() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let _ = [ar[i], 0usize];
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = [ar[i], 0] (unbounded i)",
    );
}

#[test]
fn nested_binary_operand_unbounded_read_is_rejected() {
    // `ar[i] + 0` routes through the arithmetic-safety path (its reflexive fires
    // the bound on the whole RHS), but the collector also descends into binary
    // operands directly — either way an unbounded operand index must fail closed.
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let _ = ar[i] + 0usize;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = ar[i] + 0 (unbounded i)",
    );
}

#[test]
fn nested_struct_literal_unbounded_read_is_rejected() {
    assert_not_verified(
        r#"
        struct S { x: usize }
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let _ = S { x: ar[i] };
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = S { x: ar[i] } (unbounded i)",
    );
}

#[test]
fn nested_call_argument_unbounded_read_is_rejected() {
    assert_not_verified(
        r#"
        fn g(_x: usize) {}
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            g(ar[i]);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "g(ar[i]) (unbounded i)",
    );
}

#[test]
fn nested_method_argument_unbounded_read_is_rejected() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize, v: &mut Vec<usize>) {
            v.push(ar[i]);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "v.push(ar[i]) (unbounded i)",
    );
}

#[test]
fn nested_in_nested_tuple_unbounded_read_is_rejected() {
    // The OUTER index `ar[i]` (unbounded `i`) makes `ar[ar[i]]` OOB; nesting it in
    // a tuple must not hide that — resolving the outermost access fires both bounds.
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let _ = (ar[ar[i]], 0usize);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = (ar[ar[i]], 0) (unbounded inner index)",
    );
}

#[test]
fn nested_bare_tuple_statement_unbounded_read_is_rejected() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            (ar[i], 0usize);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "(ar[i], 0); (unbounded i)",
    );
}

#[test]
fn nested_side_effecting_index_unbounded_read_is_rejected() {
    // A side-effecting index (`{ j = i; j }`) is NOT exempt on the read path: the
    // throwaway reflexive bound pins nothing into scope, so an unbounded
    // side-effecting index correctly fails closed (it would be a silent OOB
    // otherwise). This is the deliberate divergence from the compound-write
    // side-effect gate.
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let mut j: usize = 0;
            let _ = (ar[{ j = i; j }], 0usize);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = (ar[{ j = i; j }], 0) (unbounded side-effecting index)",
    );
}

#[test]
fn nested_tuple_literal_in_bounds_read_verifies() {
    assert_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20]) {
            let _ = (ar[3usize], 0usize);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = (ar[3], 0) on [_; 20]",
    );
}

#[test]
fn nested_tuple_requires_bounded_read_verifies() {
    assert_verified(
        r#"
        #[trust_vc::requires(i < 20)]
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let _ = (ar[i], 0usize);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "requires(i < 20); let _ = (ar[i], 0)",
    );
}

#[test]
fn nested_struct_literal_requires_bounded_read_verifies() {
    assert_verified(
        r#"
        struct S { x: usize }
        #[trust_vc::requires(i < 20)]
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let _ = S { x: ar[i] };
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "requires(i < 20); let _ = S { x: ar[i] }",
    );
}

#[test]
fn nested_side_effecting_index_bounded_read_verifies() {
    // No over-rejection: a provably-bounded side-effecting nested index verifies.
    assert_verified(
        r#"
        #[trust_vc::requires(i < 20)]
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let mut j: usize = 0;
            let _ = (ar[{ j = i; j }], 0usize);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "requires(i < 20); let _ = (ar[{ j = i; j }], 0)",
    );
}

#[test]
fn nested_loop_body_access_is_deferred_not_spurious_counterexample() {
    // A nested body access is deferred exactly like a top-level body access (the
    // collector early-returns inside a loop context), so it must NOT produce a
    // spurious counterexample.
    assert_not_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20]) {
            let mut i: usize = 0;
            while i < 20 {
                let _ = (ar[i], 0usize);
                i = i + 1;
            }
        }
        "#,
        "f",
        "while i < 20 { let _ = (ar[i], 0); }",
    );
}

#[test]
fn nested_unmodelable_split_at_mut_receiver_is_not_falsely_verified() {
    // A nested read on the un-modelable `left` receiver is skipped (no un-lowerable
    // obligation), so recursion does not perturb the (independently fail-closed)
    // split_at_mut outcome — the function still fails closed, never `Verified`.
    assert_fails_closed(
        r#"
        #[trust_vc::ensures(true)]
        fn f() {
            let mut v: Vec<u64> = Vec::new();
            v.push(1u64);
            v.push(2u64);
            v.push(3u64);
            let (left, right) = v.as_mut_slice().split_at_mut(2usize);
            let _ = (left[5usize], 0u64);
            left[1usize] = 20u64;
            right[0usize] = 30u64;
            trust_vc::assert!(v[1usize] == 20u64);
        }
        "#,
        "f",
        "split_at_mut with nested read of left[5]",
    );
}

// ========================================================================
// #83 — SIDE-EFFECTING-INDEX compound writes. A compound assignment whose
// INDEX (or RHS) has a side effect was previously EXEMPTED from the write-index
// bound + element-overflow check (to avoid re-executing the effect across the
// `update(idx, a[idx] OP rhs)` rewrite), so an unbounded resulting index
// silently `Verified` despite a runtime OOB panic. The fix folds a
// block-embedded effect into a pure value (evaluated EXACTLY ONCE) and pins the
// obligation just like a side-effect-free write; an effect that does not fold
// to a re-usable pure value fails closed instead of `Verified`.
// ========================================================================

#[test]
fn side_effecting_index_unbounded_compound_write_is_rejected() {
    // The index block `{ j = i; j }` folds to the unbounded value `i`; the
    // write-index bound `i < 20` is no longer skipped, so a genuine OOB is
    // rejected (was a false `Verified` before #83).
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let mut j: usize = 0;
            ar[{ j = i; j }] += 1usize;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "ar[{ j = i; j }] += 1 (unbounded folded index)",
    );
}

#[test]
fn side_effecting_index_compound_write_element_overflow_is_caught() {
    // The index `{ j = 3; j }` folds to the in-bounds literal `3`, but the
    // routed element check sees `ar[3] + usize::MAX` overflow — caught as a
    // counterexample exactly like the side-effect-free `ar[3] += usize::MAX`.
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20]) {
            let mut j: usize = 0;
            ar[{ j = 3usize; j }] += 18446744073709551615usize;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "ar[{ j = 3; j }] += usize::MAX (element overflow)",
    );
}

#[test]
fn side_effecting_rhs_unbounded_element_compound_write_is_rejected() {
    // The RHS block `{ j = n; j }` folds to the unbounded value `n`; the routed
    // element check `ar[i] + n` can overflow, so it is rejected (was exempted —
    // and thus a false `Verified` — before #83). The index `i` is bounded so the
    // ONLY residual obligation is the element arithmetic.
    assert_not_verified(
        r#"
        #[trust_vc::requires(i < 20)]
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize, n: usize) {
            let mut j: usize = 0;
            ar[i] += { j = n; j };
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "ar[i] += { j = n; j } (unbounded folded element)",
    );
}

#[test]
fn bounded_safe_side_effecting_index_compound_write_verifies() {
    // NO OVER-REJECTION: a side-effecting index that folds to a provably
    // in-bounds value (`i < 20`) over a provably non-overflowing element
    // (`ar[i] == 5`) still `Verified` — and the increment lands as `5 + 1 == 6`,
    // proving the `+=` op + index are modeled EXACTLY ONCE (not doubled).
    assert_verified(
        r#"
        #[trust_vc::requires(i < 20)]
        #[trust_vc::requires(ar[i] == 5usize)]
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let mut j: usize = 0;
            ar[{ j = i; j }] += 1usize;
            trust_vc::assert!(ar[i] == 6usize);
        }
        "#,
        "f",
        "requires(i<20, ar[i]==5); ar[{ j = i; j }] += 1; assert ar[i]==6",
    );
}

#[test]
fn side_effecting_index_compound_write_op_is_applied_exactly_once() {
    // Exactly-once guard (the dual of the case above): if the `+=` (or the index)
    // were re-executed across the `update` rewrite, `ar[i]` would land on `5 + 2
    // == 7`. Asserting `ar[i] == 7` must therefore FAIL closed — the effect is
    // modeled once, not twice.
    assert_not_verified(
        r#"
        #[trust_vc::requires(i < 20)]
        #[trust_vc::requires(ar[i] == 5usize)]
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let mut j: usize = 0;
            ar[{ j = i; j }] += 1usize;
            trust_vc::assert!(ar[i] == 7usize);
        }
        "#,
        "f",
        "ar[{ j = i; j }] += 1 then assert ar[i]==7 (double-eval would pass)",
    );
}

#[test]
fn impure_side_effecting_index_compound_write_fails_closed() {
    // A bare-assignment index `ar[(j = i)] += 1` does NOT fold to a pure value —
    // the raw `j = i` would be textually re-embedded by the element read and the
    // `update` chain (re-executing the effect). trust-vc refuses to model it, so
    // it fails closed (extraction `Err`), never silently `Verified`, even though
    // the index is provably in bounds.
    assert_extract_or_verify_fails_closed(
        r#"
        #[trust_vc::requires(i < 20)]
        #[trust_vc::ensures(true)]
        fn f(ar: &mut [usize; 20], i: usize) {
            let mut j: usize = 0;
            ar[(j = i)] += 1usize;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "ar[(j = i)] += 1 (non-folding side-effecting index)",
    );
}

#[test]
fn bounded_deref_aliasing_side_effecting_index_compound_write_fails_closed() {
    // SCOPE BOUNDARY (#83): a side effect that writes THROUGH A DEREFERENCE
    // (`*a_ref = …`, the mut-ref aliasing-evaluation-order case) keeps the
    // conservative boundary: faithful aliasing for a deref write inside the
    // throwaway scoped evaluation is tracked separately from #83. The extractor
    // now rejects this shape explicitly instead of silently reverting the write
    // and reasoning from stale state. Even though the folded index is the
    // in-bounds literal `0`, unsupported mutable aliasing must fail closed.
    // SLICE-C REMEDIATION UPDATE: the reverted write's root `a` is HAVOCKED (and
    // its aliases invalidated) at the region exit, so the OBSERVED variants
    // fail closed for BOTH spellings — reading `a` after was already
    // "unresolved", and reading `*a_ref` after (previously false-`Verified`
    // against the reverted pre-write value — probed firsthand on 2fdd181) is
    // now fail-closed too (see the sibling test below).
    let code = r#"
        #[trust_vc::ensures(true)]
        fn f() {
            let mut a: u64 = 0u64;
            let a_ref = &mut a;
            let mut x = [0u64, 1u64];
            x[{
                *a_ref = 1u64;
                0usize
            }] += 1u64;
            trust_vc::assert!(x[0usize] == 1u64);
        }
        "#;
    let file = parse_file(code).expect("fixture should parse");
    let func = find_function(&file, "f").expect("fixture should define fn f");
    let err = extract_verification_conditions(func)
        .expect_err("deref-aliasing index evaluation must fail closed at extraction");
    let message = err.to_string();
    assert!(
        message.contains("assignment through a dereferenced reference is unsupported")
            && message.contains("* a_ref"),
        "unexpected fail-closed diagnostic: {message}"
    );
}

#[test]
fn deref_aliasing_side_effecting_index_write_alias_read_never_verifies_stale() {
    // The firsthand base false-`Verified` closed by the slice-C remediation:
    // the in-index-block deref write is reverted by the throwaway evaluation,
    // and the post-write alias read `*a_ref == 0` proved the STALE pre-write
    // value — false on every execution (`a == 1`; the compiled assert
    // panics). The region-exit havoc + alias invalidation now make any
    // post-region observation of the reverted write unconstrained or
    // unresolved. Must never verify.
    assert_extract_or_verify_fails_closed(
        r#"
        #[trust_vc::ensures(true)]
        fn f() {
            let mut a: u64 = 0u64;
            let a_ref = &mut a;
            let mut x = [0u64, 1u64];
            x[{
                *a_ref = 1u64;
                0usize
            }] += 1u64;
            trust_vc::assert!(*a_ref == 0u64);
        }
        "#,
        "f",
        "x[{ *a_ref = 1; 0 }] += 1; assert *a_ref==0 (stale alias read of a reverted write)",
    );
}
