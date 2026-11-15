// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS regression: exec arithmetic-safety / index-bounds panic-freedom of
//! an `if` / `else if` / `while` CONDITION (test) expression.
//!
//! An `if`/`while` boolean test is evaluated EXACTLY ONCE, UNCONDITIONALLY,
//! before either branch / the first iteration — exactly like a `match`
//! scrutinee. So a panic-carrying arithmetic site (`if a / b > 0`,
//! `while a + b > 0`, signed `i32::MIN / -1`, `a - b` underflow) or an OOB
//! index (`if arr[i] > 0`) in the condition carries a real exec panic obligation.
//!
//! `visit_expr_if` / `visit_expr_while` (body_extract.rs) previously lowered the
//! condition with `visit_expr` + `expr_to_scoped_string` for value-numbering /
//! path-condition rendering but NEVER called the arith-safety / index-bounds
//! emitters on it (unlike `visit_expr_match`, which anchors both on the
//! scrutinee). So a div-by-zero / overflow / OOB in the condition silently
//! `Verified` (`#[ensures(true)] fn f(a,b){ if a / b > 0 {} }` accepts despite
//! `f(0,0)` panicking). The `while` case was masked further when a `break` body
//! removed the negated-guard post-loop side condition.
//!
//! The fix emits the same reflexive obligations the straight-line / match paths
//! use, at the PRE-BRANCH / PRE-loop program point (enclosing path conditions
//! only — `!(c)` for an `else if` nested in the else arm, the left-operand guard
//! for a short-circuit `&&`/`||` right operand). It is direction-correct, so it
//! must:
//!   * FAIL CLOSED (not `Verified`) for a condition that panics, and
//!   * STILL VERIFY a condition that is genuinely SAFE under its preconditions /
//!     reachability guard (`if b > 0`, `if a / b > 0` under `requires(b != 0)`,
//!     `b != 0 && a / b > 0`) — NO over-rejection.

use std::sync::atomic::{AtomicU64, Ordering};
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SOURCE: &str = r#"
// ======================================================================
// UNSAFE: panic-carrying arithmetic / index in an if / else-if / while
// CONDITION -> must NEVER Verify.
// ======================================================================

// if-condition divide-by-zero (f(0, 0) panics).
#[trust_vc::ensures(true)]
fn if_div(a: u64, b: u64) { if a / b > 0u64 { } }

// Both branches present — neither re-lowers the condition.
#[trust_vc::ensures(true)]
fn if_div_else(a: u64, b: u64) { if a / b > 0u64 { } else { } }

// if-condition unsigned subtraction underflow (f(0, 1)).
#[trust_vc::ensures(true)]
fn if_sub(a: u64, b: u64) { if a - b > 0u64 { } }

// if-condition OOB array index (i out of range).
#[trust_vc::ensures(true)]
fn if_index(arr: [u64; 3], i: usize) { if arr[i] > 0u64 { } }

// if-condition signed division overflow: i32::MIN / -1 under requires(b != 0).
#[trust_vc::requires(b != 0i32)]
#[trust_vc::ensures(true)]
fn if_signed_div(a: i32, b: i32) { if a / b > 0i32 { } }

// else-if condition divide-by-zero: a / b evaluated only on the !(c) path.
#[trust_vc::ensures(true)]
fn elseif_div(a: u64, b: u64, c: bool) { if c { } else if a / b > 0u64 { } }

// Short-circuit RIGHT operand of an if-guard: a / b reachable when a > 0.
#[trust_vc::ensures(true)]
fn if_sc_right_div(a: u64, b: u64) { if a > 0u64 && a / b > 0u64 { } }

// while-guard divide-by-zero, masked by the `break` body.
#[trust_vc::ensures(true)]
fn while_div(a: u64, b: u64) { while a / b > 0u64 { break; } }

// while-guard addition overflow (a = u64::MAX, b = 1).
#[trust_vc::ensures(true)]
fn while_add(a: u64, b: u64) { while a + b > 0u64 { break; } }

// while-guard subtraction underflow.
#[trust_vc::ensures(true)]
fn while_sub(a: u64, b: u64) { while a - b > 0u64 { break; } }

// while-guard multiplication overflow.
#[trust_vc::ensures(true)]
fn while_mul(a: u64, b: u64) { while a * b > 0u64 { break; } }

// while-guard short-circuit RIGHT operand divide-by-zero.
#[trust_vc::ensures(true)]
fn while_sc_right_div(a: u64, b: u64) { while a > 0u64 && a / b > 0u64 { break; } }

// while-guard LEFT operand divide-by-zero (unconditional).
#[trust_vc::ensures(true)]
fn while_left_div(a: u64, b: u64) { while a / b > 0u64 && a > 0u64 { break; } }

// ======================================================================
// SAFE: the condition is genuinely panic-free under its preconditions /
// reachability guard -> must STILL Verify (no over-rejection).
// ======================================================================

// Division by a non-zero CONSTANT can never panic.
#[trust_vc::ensures(true)]
fn if_div_const_safe(a: u32) { if a / 2u32 > 0u32 { } }

// requires(b != 0) makes a / b safe in the condition.
#[trust_vc::requires(b != 0u64)]
#[trust_vc::ensures(true)]
fn if_div_safe(a: u64, b: u64) { if a / b > 0u64 { } }

// requires excludes both b == 0 and the MIN/-1 overflow witness.
#[trust_vc::requires(b != 0i32)]
#[trust_vc::requires(!(a == -2147483648i32 && b == -1i32))]
#[trust_vc::ensures(true)]
fn if_signed_div_safe(a: i32, b: i32) { if a / b > 0i32 { } }

// A plain boolean comparison condition carries no arithmetic obligation.
#[trust_vc::ensures(true)]
fn if_bool_safe(a: u64, b: u64) { if b > 0u64 { } }

// requires(b != 0) makes the while guard safe.
#[trust_vc::requires(b != 0u64)]
#[trust_vc::ensures(true)]
fn while_div_safe(a: u64, b: u64) { while a / b > 0u64 { break; } }

// Short-circuit right operand reachable only when b != 0 -> a / b is safe.
#[trust_vc::ensures(true)]
fn if_sc_right_safe(a: u64, b: u64) { if b != 0u64 && a / b > 0u64 { } }

// Same, in a while guard.
#[trust_vc::ensures(true)]
fn while_sc_right_safe(a: u64, b: u64) { while b != 0u64 && a / b > 0u64 { break; } }

// In-bounds constant index in the condition.
#[trust_vc::ensures(true)]
fn if_index_safe(arr: [u64; 3]) { if arr[0] > 0u64 { } }

// else-if condition that is safe under its precondition.
#[trust_vc::requires(c)]
#[trust_vc::ensures(true)]
fn elseif_div_safe(a: u64, b: u64, c: bool) { if c { } else if a / b > 0u64 { } }
"#;

static SEQ: AtomicU64 = AtomicU64::new(0);

fn verify(func: &str) -> VerifyResult {
    let path = std::env::temp_dir().join(format!(
        "trust_vc_if_while_cond_arith_{}_{}.rs",
        std::process::id(),
        SEQ.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, SOURCE).expect("write temp source");
    let result = verify_function_from_file(path.to_str().unwrap(), func)
        .unwrap_or_else(|e| panic!("{func} should verify-from-file without error: {e}"));
    let _ = std::fs::remove_file(&path);
    result
}

#[test]
fn if_while_condition_panic_never_verifies() {
    for f in [
        "if_div",
        "if_div_else",
        "if_sub",
        "if_index",
        "if_signed_div",
        "elseif_div",
        "if_sc_right_div",
        "while_div",
        "while_add",
        "while_sub",
        "while_mul",
        "while_sc_right_div",
        "while_left_div",
    ] {
        let result = verify(f);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "{f}: panic-carrying arithmetic / index in an if/while CONDITION must \
             NEVER verify, got {result:?}"
        );
    }
}

#[test]
fn if_while_condition_unsafe_is_a_decisive_counterexample() {
    // Soundness witness: the dropped condition-position obligation is genuinely
    // enforced with a concrete refuting model (not merely Unknown) for the
    // scalar-arithmetic cases. (The pure index-OOB case `if_index` solves to
    // Unknown(Incompleteness) — still "not Verified" — matching the established
    // value-position behavior, so it is excluded from the decisive-CEX set.)
    for f in [
        "if_div",
        "if_sub",
        "if_signed_div",
        "elseif_div",
        "if_sc_right_div",
        "while_div",
        "while_add",
        "while_mul",
    ] {
        assert!(
            matches!(verify(f), VerifyResult::Counterexample { .. }),
            "{f}: should expose a decisive counterexample, got {:?}",
            verify(f)
        );
    }
}

#[test]
fn if_while_condition_safe_still_verifies() {
    // No over-rejection: a condition that is panic-free under its preconditions /
    // reachability guard must continue to Verify.
    for f in [
        "if_div_const_safe",
        "if_div_safe",
        "if_signed_div_safe",
        "if_bool_safe",
        "while_div_safe",
        "if_sc_right_safe",
        "while_sc_right_safe",
        "if_index_safe",
        "elseif_div_safe",
    ] {
        assert!(
            matches!(verify(f), VerifyResult::Verified),
            "{f}: a condition that is safe under its guard / precondition must \
             STILL verify (no over-rejection), got {:?}",
            verify(f)
        );
    }
}
