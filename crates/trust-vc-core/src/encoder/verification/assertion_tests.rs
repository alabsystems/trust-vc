// Tests for assertion verification orchestration.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Split from `assertion.rs` for the 500-line limit (#2621).

use super::*;

#[test]
fn test_convert_setup_error_ay_panic_becomes_unknown() {
    let result = convert_setup_error(TrustVcError::Encoding {
        context: "ay solver panic",
        detail: "sort mismatch: expected Bool, got BV32".to_string(),
    });

    assert!(
        matches!(result, Ok(AssertionOutcome::Unknown { .. })),
        "caught ay panics should stay in the outcome channel as Unknown: {:?}",
        result
    );
}

#[test]
fn test_convert_setup_error_sort_mismatch_stays_trust_vc_error() {
    let result = convert_setup_error(TrustVcError::Encoding {
        context: "encode typed assumption",
        detail: "Failed to encode assumption 'return_value': sort mismatch in apply".to_string(),
    });

    match result {
        Err(TrustVcError::Encoding { context, detail }) => {
            assert_eq!(context, "encode typed assumption");
            assert!(detail.contains("return_value"));
        }
        other => panic!(
            "ordinary setup encoding failures should remain TrustVcError::Encoding, got: {:?}",
            other
        ),
    }
}

#[test]
fn test_convert_setup_error_non_ay_error_stays_trust_vc_error() {
    let result = convert_setup_error(TrustVcError::Encoding {
        context: "verification setup",
        detail: "division by zero".to_string(),
    });

    match result {
        Err(TrustVcError::Encoding { context, detail }) => {
            assert_eq!(context, "verification setup");
            assert_eq!(detail, "division by zero");
        }
        other => panic!(
            "non-ay setup failures should remain TrustVcError::Encoding, got: {:?}",
            other
        ),
    }
}

// ── NRA dispatch-gate boundary (real_nonlinear1 vs real_nonlinear2) ──────────
//
// `is_nonlinear_arith_mode` is the soundness-critical switch that decides
// whether the nonlinear-real certificate pre-pass (`nonlinear_real::
// try_prove_nonlinear_real_outcome`) runs for an obligation. Upstream
// `real.rs` carries the *same* goal twice:
//   * real_nonlinear1 — `by (nonlinear_arith)` ⇒ SolverMode::NonlinearArith
//     ⇒ gate open ⇒ certificate search discharges it (=> Ok(())),
//   * real_nonlinear2 — no hint ⇒ SolverMode::Default/None ⇒ gate CLOSED
//     ⇒ falls through to the ordinary solver, which cannot prove it (=> FAILS).
// These tests pin both directions of that gate.

use crate::vc::SolverMode;

/// should-VERIFY direction: the `by (nonlinear_arith)` hint (the real_nonlinear1
/// case) opens the gate so the certificate pre-pass is consulted.
#[test]
fn nra_gate_open_for_nonlinear_arith_mode() {
    assert!(
        is_nonlinear_arith_mode(Some(SolverMode::NonlinearArith)),
        "an explicit by(nonlinear_arith) hint must open the NRA certificate pre-pass \
         (this is the real_nonlinear1 path)"
    );
}

/// should-FAIL direction: every non-`NonlinearArith` mode must keep the gate
/// CLOSED. The `None` default is the real_nonlinear2 case — the identical goal
/// with no hint must NOT reach the NRA pre-pass, so it falls through to the
/// ordinary solver and fails exactly as Verus expects. A leak in any of these
/// rows would silently prove real_nonlinear2 and diverge from upstream.
#[test]
fn nra_gate_closed_for_every_non_nonlinear_arith_mode() {
    // The default/hint-free obligation: the real_nonlinear2 shape.
    assert!(
        !is_nonlinear_arith_mode(None),
        "SOUNDNESS: a hint-free obligation (None) must NOT trigger the NRA pre-pass \
         — this is the real_nonlinear2 case that Verus expects to FAIL"
    );
    for mode in [
        SolverMode::Default,
        SolverMode::BitVector,
        SolverMode::Compute,
    ] {
        assert!(
            !is_nonlinear_arith_mode(Some(mode)),
            "SOUNDNESS: {mode:?} must NOT open the NRA pre-pass; only NonlinearArith may"
        );
    }
}

// ----------------------------------------------------------------------
// THE INT-RETRY GATE (`int_fallback_allowed`).
//
// Three conjuncts, each pinned by a test that flips it alone against a
// control in which the retry is open, so removing any one of them from the
// call site reds a named test. The third conjunct is fail-closed
// conservatism that only ever suppresses a TIMEOUT -> Verified upgrade, so
// these pins are the only thing that can measure it at all.
// ----------------------------------------------------------------------

/// `a < 100u32` — reads the same in both arithmetic universes.
fn crossing_fact_expr() -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Lt,
        left: Box::new(TrustVcExpr::Var {
            name: "a".to_string(),
            ty: crate::ir::TrustVcType::Uint { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 100,
            ty: crate::ir::TrustVcType::Uint { width: 32 },
        }),
    }
}

/// `b == a + 1u32` — WRAPS at a fixed width, so the reading gate rewrites it
/// on the way into the integers.
fn rewritten_fact_expr() -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Eq,
        left: Box::new(TrustVcExpr::Var {
            name: "b".to_string(),
            ty: crate::ir::TrustVcType::Uint { width: 32 },
        }),
        right: Box::new(TrustVcExpr::Arith {
            op: crate::ir::ArithOp::Add,
            left: Box::new(TrustVcExpr::Var {
                name: "a".to_string(),
                ty: crate::ir::TrustVcType::Uint { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 1,
                ty: crate::ir::TrustVcType::Uint { width: 32 },
            }),
            ty: crate::ir::TrustVcType::Uint { width: 32 },
        }),
    }
}

fn assume_fact(expr: TrustVcExpr) -> PreparedObligation {
    PreparedObligation {
        name: "f".to_string(),
        kind: ObligationKind::Assume,
        location: None,
        condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
        bound_vars: None,
        trigger_patterns: None,
        prepared_triggers: None,
        solver_mode: None,
        is_opaque: false,
        is_inline: false,
        broadcast_group: None,
        invariant_namespace: None,
        trigger_inference_mode: None,
        broadcast_guard: None,
        raw_broadcast_guard_count: 0,
        step_meta: None,
        condition: String::new(),
        expr,
    }
}

fn int_retry_gate(fact: TrustVcExpr, is_nonlinear_arith: bool, overflow_checked: bool) -> bool {
    let ctx = crate::prepared_context::PreparedVerificationContext::default();
    let fact = assume_fact(fact);
    let assumptions = [&fact];
    let empty: [&PreparedObligation; 0] = [];
    let slices = VerificationSlices::new(&ctx, &assumptions, &empty, &empty, &empty, &empty);
    int_fallback_allowed(&slices, is_nonlinear_arith, overflow_checked)
}

/// CONTROL: overflow checked, an ordinary goal, and a fact that crosses — the
/// retry is open. Every pin below flips exactly one of those.
#[test]
fn the_int_retry_is_open_when_all_three_conditions_hold() {
    assert!(int_retry_gate(crossing_fact_expr(), false, true));
}

/// LIAR TWIN 1: without the no-overflow check the goal's own two readings need
/// not agree, so re-solving it over `Int` proves a different statement.
#[test]
fn the_int_retry_is_closed_when_the_goal_overflow_check_did_not_run() {
    assert!(!int_retry_gate(crossing_fact_expr(), false, false));
}

/// LIAR TWIN 2: a `by(nonlinear_arith)` goal is already solved in the
/// integers; the "retry" would be the identical query.
#[test]
fn the_int_retry_is_closed_for_a_nonlinear_arith_goal() {
    assert!(!int_retry_gate(crossing_fact_expr(), true, true));
}

// ----------------------------------------------------------------------
// THE EXEC-ARITH OVERFLOW GATE (`exec_arith_overflow_in_scope`), nonlinear row.
//
// The `!is_nonlinear_arith_mode(..)` conjunct reached this branch UNPINNED:
// neutralising it alone red nothing, anywhere. It is KEPT, and these pins say
// why it is not documentation pretending to be logic.
//
// THE OFFERED REASON WAS HALF RIGHT. "A nonlinear goal already sets
// `use_int_for_measures`, and the Int lane emits no no-overflow predicates" is
// true for `+`, `-` and `*` only: `encode_int_arith` computes
// `wrap_ctx = None` when `use_int_arithmetic` is set, and each of those three
// arms is gated on `wrap_ctx.is_some()`. The `Div` and `Rem` arms are NOT —
// they push "division by zero" / "modulo by zero" (and the signed MIN/-1
// guard) gated only on `overflow_behavior.should_check()` and
// `quantifier_depth == 0`. Collection preconditions (`Seq::subrange` bounds,
// index range, carrier representability) are pushed by the collection encoders
// in either lane as well.
//
// So for a `by(nonlinear_arith)` goal there IS something for the assume site
// in `solve.rs` to assume — while the CHECK that would justify it is skipped
// outright, by the separate `!is_nonlinear_arith &&` guard on the
// check-emitting block in `verify_single_assertion_typed_inner`. Without this
// conjunct the assume site would assert `b != 0` for a goal nobody proved
// `b != 0` for: a hypothesis that RESTRICTS models, i.e. exactly the
// assume-what-was-never-checked shape this gate was introduced to close, and
// the one direction in which it can make a false goal come back `Verified`.
//
// It is unpinned END TO END because the three other call sites re-guard the
// same condition themselves (the check block and `int_fallback_allowed` both
// carry their own `!is_nonlinear_arith`; the shared BV fast path refuses a
// `NonlinearArith` obligation in `can_use_shared_bv_fast_path`), so only the
// `solve.rs` assume site reads this conjunct as the ONLY guard — and reaching
// it needs a `by(nonlinear_arith)` goal carrying a symbolic divisor or a
// collection precondition, which no fixture in the corpus is. These pins
// measure the gate and its non-vacuity instead of waiting for that fixture.
//
// CORRECTION (round-7 review, disclosed in full and VERBATIM on
// `every_fact_crosses_into` in `encoder/verification/arith_reading.rs`): the
// sentence above is not an enumeration of CALL SITES.
// `exec_arith_overflow_in_scope` has FOUR production callers —
// `assertion.rs:637` and `:903`, `assertion_bv_reuse.rs:205`,
// `solve.rs:293`. The named "check block" and `int_fallback_allowed` are two
// CONSUMERS of the single `:903` call, and the unnamed fourth caller, the
// confirmation rerun's `allow_int_fallback` at `:637`, is closed for a
// nonlinear goal by its own `!effective_int_mode` (`initial_int_mode` is
// `use_int_for_measures`, true whenever `is_nonlinear_arith` is) rather than
// by a literal `!is_nonlinear_arith`. The substantive conclusion — only the
// `solve.rs` assume site reads this conjunct as its ONLY guard — is correct
// as measured.
// ----------------------------------------------------------------------

/// `a / b > 0u32` — a symbolic divisor, so the Int lane emits a
/// divide-by-zero predicate even with every wrap context switched off.
fn symbolic_division_expr() -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Gt,
        left: Box::new(TrustVcExpr::Arith {
            op: crate::ir::ArithOp::Div,
            left: Box::new(TrustVcExpr::Var {
                name: "a".to_string(),
                ty: crate::ir::TrustVcType::Uint { width: 32 },
            }),
            right: Box::new(TrustVcExpr::Var {
                name: "b".to_string(),
                ty: crate::ir::TrustVcType::Uint { width: 32 },
            }),
            ty: crate::ir::TrustVcType::Uint { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: crate::ir::TrustVcType::Uint { width: 32 },
        }),
    }
}

fn goal_with_mode(expr: TrustVcExpr, mode: Option<SolverMode>) -> PreparedObligation {
    let mut obligation = assume_fact(expr);
    obligation.name = "assertion_1".to_string();
    obligation.kind = ObligationKind::Assert;
    obligation.solver_mode = mode;
    obligation
}

/// THE PIN. Removing `!is_nonlinear_arith_mode(..)` from
/// `exec_arith_overflow_in_scope` reds exactly this row and leaves the other
/// four passing.
#[test]
fn the_exec_arith_overflow_gate_is_closed_for_a_nonlinear_arith_goal() {
    assert!(
        !exec_arith_overflow_in_scope(
            true,
            &goal_with_mode(symbolic_division_expr(), Some(SolverMode::NonlinearArith)),
        ),
        "SOUNDNESS: the overflow CHECK never runs for a by(nonlinear_arith) goal, so the \
         assume site in solve.rs may not assume its predicates either"
    );
}

/// CONTROL plus the two other closed rows, so the pin above is the nonlinear
/// conjunct and not the gate being closed for everything.
#[test]
fn the_exec_arith_overflow_gate_is_open_for_an_ordinary_goal() {
    for mode in [None, Some(SolverMode::Default), Some(SolverMode::Compute)] {
        assert!(
            exec_arith_overflow_in_scope(true, &goal_with_mode(symbolic_division_expr(), mode)),
            "an ordinary goal ({mode:?}) still checks, and still assumes, its own predicates"
        );
    }
    assert!(
        !exec_arith_overflow_in_scope(
            true,
            &goal_with_mode(symbolic_division_expr(), Some(SolverMode::BitVector)),
        ),
        "by(bit_vector) WRAPS, so there is no no-overflow property to check or assume"
    );
    assert!(
        !exec_arith_overflow_in_scope(false, &goal_with_mode(symbolic_division_expr(), None),),
        "and the context switch still dominates every row"
    );
}

/// NON-VACUITY, and the correction of the offered reason. If the Int lane
/// really emitted nothing, the pin above would be suppressing an empty list
/// and the conjunct would be pure documentation. It is not: built in the very
/// lane a `by(nonlinear_arith)` goal runs in (`use_int_for_measures = true`),
/// the encoder still produces a divide-by-zero predicate for a symbolic
/// divisor. That is the unproven fact the conjunct keeps out of the solver.
#[test]
fn the_int_lane_still_emits_a_predicate_the_nonlinear_check_never_ran() {
    let ctx = crate::prepared_context::PreparedVerificationContext {
        variables: vec![
            crate::vc::VariableDecl::new("a", crate::ir::TrustVcType::Uint { width: 32 }),
            crate::vc::VariableDecl::new("b", crate::ir::TrustVcType::Uint { width: 32 }),
        ],
        ..Default::default()
    };
    let empty: [&PreparedObligation; 0] = [];
    let slices = VerificationSlices::new(&ctx, &empty, &empty, &empty, &empty, &empty);
    let mut encoder = AYEncoder::setup_from_prepared(&slices, true, None)
        .expect("an int-lane encoder over two scalars sets up");
    let expr = symbolic_division_expr();
    let (_term, checks) = encoder
        .resolve_condition_with_overflow_typed(&expr, true)
        .expect("`a / b > 0` encodes in the int lane");
    assert!(
        !checks.is_empty(),
        "the Int lane is NOT predicate-free: a symbolic divisor still carries a \
         divide-by-zero obligation, so the nonlinear conjunct suppresses a real \
         assumption rather than an empty list"
    );
    assert!(
        checks.iter().any(|(label, _)| label.contains("zero")),
        "and it is the divide-by-zero one: {:?}",
        checks
            .iter()
            .map(|(l, _)| l.to_string())
            .collect::<Vec<_>>()
    );
}

/// LIAR TWIN 3: one fact the reading gate would REWRITE on the way into the
/// integers closes it. That rewrite's guard is known incomplete for a unary
/// `-` that DOMINATES the node it bounds (see
/// `arith_reading::every_fact_crosses_into`), and a retry beside a mis-guarded
/// fact could accept a vacuous `Verified`. Conservatism, not a live hole: the
/// corrected witness is fail-closed at this HEAD (measured) and, per the
/// round-6 review, at the merge base too.
#[test]
fn the_int_retry_is_closed_beside_a_fact_the_reading_gate_rewrites() {
    assert!(!int_retry_gate(rewritten_fact_expr(), false, true));
}
