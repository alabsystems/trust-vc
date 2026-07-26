// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial (overflow/arithmetic): exec u64 DIVIDE-BY-ZERO in a MATCH-ARM GUARD
//! is never checked.
//!
//! DISTINCT mechanism from the `return` cases. `visit_expr_match` instruments the
//! match SCRUTINEE with emit_exec_arith_safety_checks_in_expr
//! (body_extract.rs:10104) and each arm BODY (body_extract.rs:10266), but the arm
//! GUARD is only `visit_expr`'d (body_extract.rs:10256-10258) with NO
//! emit_exec_arith_safety_checks_in_expr call. This is the direct analog of the
//! `if` CONDITION, which needed its OWN explicit emit (body_extract.rs:9927,
//! commented "visit_expr above only did value-numbering / path-condition rendering
//! and never emitted these, so the obligation silently dropped"). The equivalent
//! `if a / b > 0u64 { }` IS therefore checked, but the `match _ if a / b > 0u64`
//! guard is not: its `a / b` carries no divide-by-zero obligation. The arm bodies
//! are unit and the contract is `ensures(true)`, so the guard value is never used
//! in any goal — the divide is a pure dropped side-effect.

// TARGET (correct verdict: NOT Verified / Counterexample).
// Witness b = 0: the arm guard evaluates `a / 0`, a divide-by-zero panic. Exec
// div0_behavior is `Error`, so Verus rejects this; the un-instrumented guard makes
// the engine accept it.
#[trust_vc::ensures(true)]
fn div0_in_match_guard(a: u64, b: u64) {
    match a {
        _ if a / b > 0u64 => {}
        _ => {}
    }
}

// POSITIVE CONTROL (correct verdict: Verified).
// A division guarded safe by `requires(b > 0)` in TAIL position (walker-
// instrumented), with a genuinely-true postcondition. Proves the div machinery
// works and a safe division verifies.
#[trust_vc::requires(b > 0u64)]
#[trust_vc::ensures(result == a / b)]
fn safe_div_tail(a: u64, b: u64) -> u64 {
    a / b
}
