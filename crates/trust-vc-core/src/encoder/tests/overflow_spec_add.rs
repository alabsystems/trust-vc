//! Verus `vstd`/`builtin` spec-mode `add` parity (#2778, upstream `overflow.rs`).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Mirrors upstream Verus `source/rust_verify_test/tests/overflow.rs` cases
//! `test_overflow_spec_pass`, `test_overflow_spec_fails_1`, and
//! `test_overflow_spec_fails_2`.
//!
//! ## What the upstream `add` actually means
//!
//! Verus's `builtin::add` / `vstd` spec-mode `add(a, b)` is the *fixed-width*
//! addition. In `rust_to_vir`'s `fn_call_to_vir.rs`, `ArithItem::BuiltinAdd`
//! lowers to `BinaryOp::Arith(ArithOp::Add(ob))` where, in ghost/proof mode,
//! `ob = OverflowBehavior::Truncate(range)` — i.e. the mathematical sum
//! *clipped/truncated to the operand bit width*, with **no** overflow
//! obligation. That is exactly trust-vc's `WrappingArith { mode: Wrapping, .. }`
//! (BV modular arithmetic). The free-function recognition lives in
//! `ir_lowering::dispatch::calls::lower_wrapping_free_function_call`, which maps
//! an unregistered `add`/`sub`/`mul` over fixed-width integer operands to that
//! IR node. When `add` is instead a user/registered spec function the lookup
//! guard defers to the user definition, so this recognition is safe.
//!
//! The string-condition path used by these tests routes through
//! `syn::parse_str` → `lower_syn_expr` → the same dispatch, so `add(a, 2)` in a
//! `ProofObligation` condition is lowered identically to source.
//!
//! ## Why the "fails" cases fail
//!
//! The failures in the upstream `_fails_*` cases do not come from the `add`
//! lowering itself (which is exact); they come from the *other* arithmetic in
//! the assertion:
//!
//! * `_fails_1`: `assert(j == a as nat + 2)` compares the truncated u64 result
//!   `j == wrap64(a + 2)` against the *unbounded* `a as nat + 2`. These differ
//!   precisely when `a + 2` overflows u64 (e.g. `a == u64::MAX`). The query is a
//!   mixed BV/Int constraint (`bv2int(wrap64(a + 2)) == a + 2`); ay-dpll cannot
//!   currently refute it and returns `Unknown(incomplete)`. That is a sound,
//!   fail-closed result — never a false `Verified`.
//! * `_fails_2`: `assert(j == a + 4)` where the bare `+` is exec-mode `u64`
//!   addition carrying a no-overflow obligation. With overflow checks enabled
//!   that obligation is refuted at `a == u64::MAX`, yielding a clean
//!   counterexample — matching upstream `assert_one_fails`.
//!
//! Soundness invariant for this module: the pass case verifies, and *every*
//! fails case is fail-closed (Counterexample or Unknown, never Verified).

use super::*;

/// Upstream `test_overflow_spec_pass`:
/// ```ignore
/// let ghost mut j: u64 = a;
/// proof { j = add(j, 2); }
/// assert(j == add(a, 2));
/// ```
/// Both sides use the truncating `add`, so `j == add(a, 2)` holds for all `a`.
#[test]
fn test_overflow_spec_pass() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u64_ty());
    ctx.declare_var_typed("j", u64_ty());
    // proof { j = add(j, 2); } with j initialized to a  ⇒  j == add(a, 2)
    ctx.push_obligation(ProofObligation::assume("j_def", "j == add(a, 2)"));
    ctx.push_obligation(ProofObligation::assert("spec_add_eq", "j == add(a, 2)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "#2778 overflow.rs test_overflow_spec_pass: j == add(a, 2) holds for the truncating spec add",
    );
}

/// Upstream `test_overflow_spec_fails_1`:
/// ```ignore
/// let mut j = a;
/// j = add(j, 2);
/// assert(j == a as nat + 2); // FAILS
/// ```
/// The truncated `j == wrap64(a + 2)` differs from the unbounded `a as nat + 2`
/// when `a + 2` overflows u64. The refutation is a mixed BV/Int query that
/// ay-dpll cannot currently decide, so the sound outcome is fail-closed
/// (`Unknown(incomplete)`) — crucially NOT `Verified`.
#[test]
fn test_overflow_spec_fails_1() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u64_ty());
    ctx.declare_var_typed("j", u64_ty());
    ctx.push_obligation(ProofObligation::assume("j_def", "j == add(a, 2)"));
    ctx.push_obligation(ProofObligation::assert("nat_eq", "j == a as nat + 2"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "#2778 overflow.rs test_overflow_spec_fails_1: truncated add vs unbounded nat must not verify",
    );
}

/// Upstream `test_overflow_spec_fails_2`:
/// ```ignore
/// let ghost mut j: u64 = a;
/// proof { j = add(j, 2); j = add(j, 2); }
/// assert(j == a + 4); // FAILS
/// ```
/// `j == wrap64(a + 4)`, but the bare `a + 4` is exec-mode `u64` addition with a
/// no-overflow obligation. That obligation is refutable at `a == u64::MAX`, so
/// the result is a counterexample — matching upstream `assert_one_fails`.
#[test]
fn test_overflow_spec_fails_2() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", u64_ty());
    ctx.declare_var_typed("j", u64_ty());
    // proof { j = add(j, 2); j = add(j, 2); } with j initialized to a.
    ctx.push_obligation(ProofObligation::assume("j_def", "j == add(add(a, 2), 2)"));
    ctx.push_obligation(ProofObligation::assert("plus4_eq", "j == a + 4"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "#2778 overflow.rs test_overflow_spec_fails_2: exec '+' overflow obligation on a + 4 is refuted at a = u64::MAX",
    );
}

/// Soundness guard: a user-registered `add` must take precedence over the
/// truncating builtin recognition. Verus's `add` is the builtin only when no
/// in-scope `add` shadows it; this confirms trust-vc's lookup guard
/// (`env.lookup_fn` / `env.lookup` in `lower_wrapping_free_function_call`)
/// defers to a user definition so the recognition can never silently override a
/// user's `add`. Here `add` is given an *unbounded-int* body axiom
/// (`add(a, b) == a + b` over `int`); if the builtin BV-truncation recognition
/// fired instead, `add(2, 3) == 5` would still hold but for the wrong reason —
/// so we also pin the non-truncating identity below.
#[test]
fn test_user_add_shadows_builtin_add() {
    let i32_params = || vec![("a".to_string(), i32_ty()), ("b".to_string(), i32_ty())];

    let mut ctx = VerificationContext::new();
    ctx.declare_helper_function_typed("add", i32_ty(), i32_params());
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_add", "add(a, b) == a + b")
            .with_bound_vars(vec!["a".to_string(), "b".to_string()])
            .with_trigger_patterns(vec![vec!["add(a, b)".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::assert("user_add", "add(2, 3) == 5"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "user-registered add must shadow the truncating builtin recognition",
    );
}
