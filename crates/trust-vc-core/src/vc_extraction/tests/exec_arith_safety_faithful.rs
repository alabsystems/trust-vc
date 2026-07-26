// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness + parity regressions for exec scalar arithmetic-safety obligations
//! (the exec-arithmetic sibling of the array-OOB index-bounds work, #81/#82/#83).
//!
//! The encoder ALREADY carries the exec arithmetic-safety prechecks (overflow /
//! divide-by-zero / signed `MIN / -1` / shift-bounds) for every `+ - * / % << >>`
//! site, fired while it lowers an obligation expression. The bug was in the
//! EXTRACTOR: it pinned the reflexive `(v) == (v)` arithmetic obligation (which
//! makes the encoder run those prechecks) ONLY when the TOP-LEVEL right-hand side
//! of a `let` / scalar-assignment was itself a checked-arith/shift expression, and
//! NEVER for a scalar compound assignment (`a OP= b`). So three classes of exec
//! arithmetic silently `Verified` a guaranteed runtime panic:
//!
//! 1. scalar compound assignment `a OP= b` — the implicit `a OP b` (and its panic
//!    obligation) vanished; only `invalidate_scoped(a)` ran.
//! 2. arithmetic nested in a tuple / array / struct literal or a call argument
//!    (`let _ = (a / b, 0);`, `let _ = [a / b];`, `let _ = Some(a / b);`) — the
//!    top-level RHS was the aggregate / call, not the arithmetic.
//! 3. a bare arithmetic statement (`a / b;`, `a % b;`).
//!
//! The fix adds a recursive `emit_exec_arith_safety_checks_in_expr` (the
//! `collect_value_position_arith_exprs` analog of the index-bounds collector) that
//! descends the UNCONDITIONALLY-evaluated value sub-positions and pins a reflexive
//! obligation at each checked-arith/shift site, plus a synthesized
//! `(old_a) OP (b)` element-safety pin for the scalar compound. It is wired into
//! the scalar-compound branch, the bare-statement arm, and the `let` / scalar-
//! assignment / const-static initializer paths, with the SAME gates as the index
//! path: `check_overflow()` (exec only), loop-body deferral, and a seen-dedup.
//!
//! Both directions are pinned:
//! * SOUNDNESS — an unguarded compound / bare / nested arithmetic site with
//!   unbounded operands is rejected (Counterexample, or a fail-closed Unknown for
//!   the `*` case the ay multiplication encoding currently solver-panics on),
//!   NEVER `Verified`.
//! * NO OVER-REJECTION — a `requires`-guarded compound, bounded operands, a
//!   short-circuit-guarded `&&` right operand, and a loop-body compound all still
//!   `Verified`.

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

/// Number of auto-emitted arithmetic-safety obligations (`overflow_check_*`)
/// collected for the named function. Used to assert the scalar compound emits the
/// implicit-`a OP b` check EXACTLY ONCE (operands evaluated once, not duplicated).
fn arith_obligation_count(code: &str, name: &str) -> usize {
    let file = parse_file(code).expect("fixture should parse");
    let func =
        find_function(&file, name).unwrap_or_else(|| panic!("fixture should define fn {name}"));
    let vc = extract_verification_conditions(func)
        .unwrap_or_else(|err| panic!("fn {name} should extract: {err}"));
    vc.obligations
        .iter()
        .filter(|o| o.name.starts_with("overflow_check"))
        .count()
}

/// Fail-closed: rejected as a Counterexample or an Unknown, never `Verified` (and
/// never a silent extraction `Error`). Mirrors the index-bounds suite helper.
fn assert_not_verified(code: &str, name: &str, what: &str) {
    match verdict(code, name) {
        VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. } => {}
        other => panic!("{what}: expected Counterexample/Unknown (fail closed), got {other:?}"),
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

// ========================================================================
// GAP 1 — scalar compound assignment `a OP= b`.
// ========================================================================

/// `a /= b` with unbounded `b`: divide-by-zero. The pre-fix path only
/// `invalidate_scoped`d `a` and emitted nothing, so this falsely `Verified`.
#[test]
fn compound_div_by_zero_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let mut a = a;
            a /= b;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "a /= b (unbounded b)",
    );
}

/// `a %= b` with unbounded `b`: remainder-by-zero.
#[test]
fn compound_rem_by_zero_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let mut a = a;
            a %= b;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "a %= b (unbounded b)",
    );
}

/// `a += b` with unbounded operands: addition overflow.
#[test]
fn compound_add_overflow_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let mut a = a;
            a += b;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "a += b (unbounded operands)",
    );
}

/// `a *= b` with unbounded operands: multiplication overflow. The ay
/// multiplication encoding currently solver-panics on this goal (a known TCB
/// issue), which surfaces as a fail-closed `Unknown` — still NOT `Verified`, so
/// the panic-freedom guarantee holds. Asserted with `assert_not_verified`.
#[test]
fn compound_mul_overflow_is_rejected() {
    assert_not_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let mut a = a;
            a *= b;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "a *= b (unbounded operands)",
    );
}

/// Signed `i32` compound `a /= b` guarded `b != 0`: the residual `MIN / -1`
/// signed-division overflow is still caught (no over-rejection of the div-by-zero,
/// but the signed-overflow precheck fires on `(old_a) / (b)`).
#[test]
fn signed_compound_div_min_over_neg1_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::requires(b != 0)]
        #[trust_vc::ensures(true)]
        fn f(a: i32, b: i32) {
            let mut a = a;
            a /= b;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "i32 a /= b guarded b != 0 (MIN / -1)",
    );
}

/// The compound applied DIRECTLY to a `mut` parameter (no `let mut` shadow)
/// is instrumented the same way — `lookup_scoped` resolves the parameter.
#[test]
fn compound_on_mut_parameter_div_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(mut a: u64, b: u64) {
            a /= b;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "mut param a /= b (unbounded b)",
    );
}

/// A bitwise compound (`a ^= b / c`) needs no check on the `^` itself, but the
/// arithmetic in its RHS (`b / c`) must still be checked.
#[test]
fn bitwise_compound_with_nested_div_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64, c: u64) {
            let mut a = a;
            a ^= b / c;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "a ^= b / c (unbounded c)",
    );
}

// ========================================================================
// GAP 2 — arithmetic nested in an aggregate / call argument / comparison.
// ========================================================================

#[test]
fn nested_tuple_div_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let _ = (a / b, 0u64);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = (a / b, 0)",
    );
}

#[test]
fn nested_array_div_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let _ = [a / b];
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = [a / b]",
    );
}

#[test]
fn nested_call_arg_div_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let _ = Some(a / b);
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = Some(a / b)",
    );
}

#[test]
fn nested_comparison_operand_div_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let _ = a / b > 0;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = a / b > 0",
    );
}

/// The scalar-assignment initializer path (a re-assignment whose RHS nests the
/// arithmetic in a non-arith expression) is wired through the same walker.
#[test]
fn scalar_assign_nested_comparison_div_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let mut t = false;
            t = a / b > 0;
            trust_vc::assert!(t || true);
        }
        "#,
        "f",
        "t = a / b > 0",
    );
}

// ========================================================================
// GAP 3 — bare arithmetic statement.
// ========================================================================

#[test]
fn bare_div_statement_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            a / b;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "a / b;",
    );
}

#[test]
fn bare_rem_statement_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            a % b;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "a % b;",
    );
}

// ========================================================================
// Value-once: the implicit `a OP b` is pinned EXACTLY ONCE.
// ========================================================================

/// A plain-operand compound `a += b` emits a SINGLE arithmetic-safety obligation
/// (the synthesized `(old_a) + (b)` element-safety pin); the RHS walk finds no
/// further arithmetic, so `b` is not duplicated into a second obligation.
#[test]
fn compound_emits_single_arith_obligation() {
    let n = arith_obligation_count(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let mut a = a;
            a += b;
            trust_vc::assert!(true);
        }
        "#,
        "f",
    );
    assert_eq!(
        n, 1,
        "a += b should emit exactly one arithmetic-safety obligation, got {n}"
    );
}

/// A guarded compound over a KNOWN value verifies — the synthesized value is
/// resolved consistently (single evaluation); a double-applied `a / b / b` would
/// not change this Verified outcome, but the guard plus single evaluation cleanly
/// discharges with no spurious counterexample.
#[test]
fn guarded_known_value_compound_div_verifies() {
    assert_verified(
        r#"
        #[trust_vc::requires(b != 0 && a == 10)]
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let mut a = a;
            a /= b;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "requires(b != 0 && a == 10); a /= b",
    );
}

// ========================================================================
// NO over-rejection: guarded / bounded / deferred sites still Verify.
// ========================================================================

#[test]
fn guarded_compound_div_verifies() {
    assert_verified(
        r#"
        #[trust_vc::requires(b != 0)]
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let mut a = a;
            a /= b;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "requires(b != 0); a /= b",
    );
}

#[test]
fn bounded_compound_add_verifies() {
    assert_verified(
        r#"
        #[trust_vc::requires(a < 10 && b < 10)]
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let mut a = a;
            a += b;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "requires(a < 10 && b < 10); a += b",
    );
}

#[test]
fn signed_guarded_compound_div_verifies() {
    assert_verified(
        r#"
        #[trust_vc::requires(b >= 1)]
        #[trust_vc::ensures(true)]
        fn f(a: i32, b: i32) {
            let mut a = a;
            a /= b;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "i32 requires(b >= 1); a /= b (no div0, no MIN/-1)",
    );
}

/// A short-circuit `&&` whose RIGHT operand holds the arithmetic
/// (`b != 0 && a / b > 0`) is guarded at runtime — the division only executes when
/// `b != 0` — so the right operand is NOT descended into and no spurious
/// divide-by-zero obligation is pinned.
#[test]
fn shortcircuit_guarded_right_operand_div_verifies() {
    assert_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64, b: u64) {
            let _ = b != 0 && a / b > 0;
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "let _ = b != 0 && a / b > 0",
    );
}

// ========================================================================
// LOOP-BODY exec arithmetic safety (the closed round-3 deferral).
//
// A boolean-guard `while` loop body's arithmetic is checked against the
// HAVOC'd loop-body-entry state (each modified scalar is a fresh, unconstrained
// symbol — its arbitrary value after any number of iterations), weakened by the
// loop GUARD + INVARIANTS over those same fresh symbols (the Verus "panic-free
// GIVEN the guard and invariant hold at body entry" rule). Both directions are
// pinned: an unbounded modified scalar is a Counterexample, while a
// guard-bounded counter, a wider-type non-overflowing site, and an
// invariant-bounded var still Verify.
// ========================================================================

/// A loop-body compound on a LOCAL `u8` (`x += 100`) overflows once `x` reaches
/// 200 after enough iterations — the modified scalar is arbitrary at body entry,
/// so this is a Counterexample (NOT the pre-fix false `Verified`).
#[test]
fn loop_body_local_u8_compound_overflow_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(n: u64) {
            let mut x: u8 = 200u8;
            let mut i: u64 = 0;
            while i < n {
                x += 100u8;
                i += 1u64;
            }
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "while-loop body local x += 100 (u8 overflow)",
    );
}

/// Same overflow when the modified scalar is a `mut` PARAMETER — checked against
/// the havoc'd entry value, NOT the (possibly-`requires`-constrained) function
/// entry value.
#[test]
fn loop_body_param_u8_compound_overflow_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(mut x: u8, n: u64) {
            let mut i: u64 = 0;
            while i < n {
                x += 100u8;
                i += 1u64;
            }
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "while-loop body param x += 100 (u8 overflow)",
    );
}

/// The previously-pinned `seen += 1` case: an UNBOUNDED `u64` accumulator (no
/// invariant relates `seen` to the guard counter `i`) overflows at `u64::MAX`.
/// This was the false-`Verified` the deferral pinned; closing the hole flips it
/// to a Counterexample (Verus likewise requires an `invariant seen <= i`). The
/// guard counter `i += 1` in the SAME body is safe (bounded by `i < n`), so the
/// failure is specifically the `seen += 1` site.
#[test]
fn loop_body_unbounded_u64_accumulator_overflow_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(n: u64) {
            let mut seen: u64 = 0;
            let mut i: u64 = 0;
            while i < n {
                seen += 1u64;
                i += 1u64;
            }
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "while-loop body unbounded seen += 1 (u64 overflow)",
    );
}

/// NO OVER-REJECTION: the guard `i < n` is assumed at body entry, so the common
/// counter `i += 1` (with `i < n <= u64::MAX`, hence `i + 1 <= u64::MAX`) does
/// NOT overflow and the loop verifies — without any invariant.
#[test]
fn loop_body_guard_bounded_counter_verifies() {
    assert_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(n: u64) {
            let mut i: u64 = 0;
            while i < n {
                i += 1u64;
            }
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "while-loop body guard-bounded i += 1 (no overflow)",
    );
}

/// NO OVER-REJECTION: a wider-type body site (`(x as u128) + 100`) cannot
/// overflow regardless of the havoc'd value, so it verifies.
#[test]
fn loop_body_wide_type_site_verifies() {
    assert_verified(
        r#"
        #[trust_vc::ensures(true)]
        fn f(n: u64) {
            let mut x: u64 = 0;
            let mut i: u64 = 0;
            while i < n {
                let y: u128 = (x as u128) + 100u128;
                i += 1u64;
            }
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "while-loop body (x as u128) + 100 (no overflow)",
    );
}

/// NO OVER-REJECTION: a plain-assign param counter with a sound, engine-provable
/// invariant verifies — the invariant is threaded into the body arithmetic guard
/// alongside the loop guard.
#[test]
fn loop_body_invariant_counter_verifies() {
    assert_verified(
        r#"
        #[trust_vc::requires(i <= n)]
        #[trust_vc::ensures(true)]
        fn f(mut i: u64, n: u64) {
            while i < n {
                trust_vc::invariant!(i <= n);
                i = i + 1u64;
            }
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "while-loop body invariant-bounded i = i + 1 (no overflow)",
    );
}

/// NO OVER-REJECTION + LOAD-BEARING INVARIANT: the invariant `s == i` is the SOLE
/// bound on the accumulator `s` (the guard `i < n` bounds only `i`), so without
/// it `s + 1` would overflow at `u64::MAX`. The flat plain-assign body lets the
/// engine prove `s == i` (M4 single-iteration transition), and the fix threads
/// that invariant into the body arithmetic obligation over the fresh havoc
/// symbols — so `s = s + 1` verifies. This is the cardinal "invariant pins the
/// var in range ⇒ still Verifies" witness.
#[test]
fn loop_body_load_bearing_relational_invariant_verifies() {
    assert_verified(
        r#"
        #[trust_vc::requires(i == 0u64)]
        #[trust_vc::requires(s == 0u64)]
        #[trust_vc::requires(n <= 100u64)]
        #[trust_vc::ensures(true)]
        fn f(mut i: u64, mut s: u64, n: u64) {
            while i < n {
                trust_vc::invariant!(s == i);
                i = i + 1u64;
                s = s + 1u64;
            }
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "while-loop body load-bearing invariant s == i (no overflow)",
    );
}

/// A nested arithmetic site (`let y = x + 100`, not a compound) inside the loop
/// body is also checked against the havoc'd entry value.
#[test]
fn loop_body_let_init_u8_overflow_is_rejected() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(true)]
        fn f(mut x: u8, n: u64) {
            let mut i: u64 = 0;
            while i < n {
                let y: u8 = x + 100u8;
                x += 1u8;
                i += 1u64;
            }
            trust_vc::assert!(true);
        }
        "#,
        "f",
        "while-loop body let y = x + 100 (u8 overflow)",
    );
}

/// NO OVER-REJECTION (havoc-consistency deferral): when a loop-body site
/// references a modified scalar INDIRECTLY — through a body-local that captured
/// it before the havoc rename (`let k = i; k = k + 1`) — the rendered obligation
/// would mix the fresh symbol (in the guard) with the bare name (in the site),
/// an inconsistent goal. The fix DEFERS such a site (emits nothing for it),
/// exactly the pre-existing loop-body behavior, while still emitting the DIRECT
/// `i = i + 1` site over the havoc symbol. This pins that:
///   * the direct `i = i + 1` overflow_check IS emitted over `i__loopbody_*`, and
///   * NO emitted overflow_check mixes the bare counter `i` with its havoc alias
///     (the inconsistent form that would over-reject / vacuously verify).
#[test]
fn loop_body_indirect_capture_site_is_deferred_consistently() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn f(mut i: u64) {
            let mut k = 12u64;
            while i < 20u64 {
                let mut k = i;
                i = i + 1u64;
                k = k + 1u64;
                trust_vc::assert!(k == i);
            }
            k = k + 1u64;
            trust_vc::assert!(k == 13u64);
        }
        "#;
    let file = parse_file(code).expect("parse");
    let func = find_function(&file, "f").expect("fn f");
    let vc = extract_verification_conditions(func).expect("extract");
    let overflow_conditions: Vec<&str> = vc
        .obligations
        .iter()
        .filter(|o| o.name.starts_with("overflow_check"))
        .map(|o| o.condition.as_str())
        .collect();
    // Whole-word search for the bare counter `i` (must NOT match inside
    // `i__loopbody_0`, where `i` is followed by an identifier char).
    fn mentions_bare_i(cond: &str) -> bool {
        let bytes = cond.as_bytes();
        let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
        let mut from = 0;
        while let Some(rel) = cond[from..].find('i') {
            let at = from + rel;
            let before_ok = at == 0 || !is_ident(bytes[at - 1]);
            let after_ok = at + 1 == bytes.len() || !is_ident(bytes[at + 1]);
            if before_ok && after_ok {
                return true;
            }
            from = at + 1;
        }
        false
    }
    // The direct `i = i + 1` site is emitted over the fresh havoc symbol.
    assert!(
        overflow_conditions.iter().any(|c| c.contains("i__loopbody")),
        "direct `i = i + 1` should emit an overflow check over the havoc symbol; got {overflow_conditions:?}"
    );
    // No emitted overflow check mixes the havoc alias with a bare counter `i`:
    // every emitted loop-body check is havoc-consistent (the inconsistent
    // `k = k + 1` site — which captured bare `i` — is deferred, emitting nothing).
    for cond in &overflow_conditions {
        assert!(
            !(cond.contains("i__loopbody") && mentions_bare_i(cond)),
            "an emitted loop-body overflow check mixes havoc and bare `i` (inconsistent): {cond}"
        );
    }
}
