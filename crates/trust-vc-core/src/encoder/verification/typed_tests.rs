// Tests for postcondition assumption-forwarding classification (#2778).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// These exercise the soundness boundary of the assumption-forwarding pre-pass
// in `verify_validated` (typed.rs:486-593). The pre-pass forwards a body
// `assert!` to the postcondition group ONLY when:
//   * it is `forwardable_body_assert` (a non-postcondition, non-Compute
//     `ObligationKind::Assert`), AND
//   * it independently verifies under the requires-derived assumptions.
// and the postcondition group is identified by `postcondition_obligation`.
//
// The classification predicates are the load-bearing gate: anything they
// wrongly admit would be forwarded as an unconditional assumption, so the
// should-FAIL direction (variants that must NOT be forwardable / must NOT be
// treated as postconditions) is the soundness-critical half.

use super::{forwardable_body_assert, postcondition_obligation};
use crate::ir::TrustVcExpr;
use crate::prepared_context::PreparedObligation;
use crate::vc::{ConditionOrigin, ObligationKind, SolverMode};

/// Builds a minimal `PreparedObligation` for classification tests. The
/// classification predicates only read `name`, `kind`, and `solver_mode`; every
/// other field is a benign default.
fn obligation(
    name: &str,
    kind: ObligationKind,
    solver_mode: Option<SolverMode>,
) -> PreparedObligation {
    PreparedObligation {
        name: name.to_string(),
        kind,
        location: None,
        condition_origin: ConditionOrigin::LoweredFromCondition,
        bound_vars: None,
        trigger_patterns: None,
        prepared_triggers: None,
        solver_mode,
        is_opaque: false,
        is_inline: false,
        broadcast_group: None,
        condition: "true".to_string(),
        expr: TrustVcExpr::BoolLit(true),
        invariant_namespace: None,
        trigger_inference_mode: None,
        broadcast_guard: None,
        raw_broadcast_guard_count: 0,
        step_meta: None,
    }
}

// ── should-VERIFY direction: a plain body assert is forwardable ──────────────

/// A straight-line body `assert!` (an `ObligationKind::Assert` that is not the
/// postcondition and not in Compute mode) is the canonical forwardable witness —
/// this is the `archimedean_nat` body `assert(x < nat_to_real(a + 1))` shape.
#[test]
fn plain_body_assert_is_forwardable() {
    let body_assert = obligation(
        "assert_x_lt_nat_to_real",
        ObligationKind::Assert,
        Some(SolverMode::Default),
    );
    assert!(
        forwardable_body_assert(&body_assert),
        "a non-postcondition Assert must be forwardable so its proven fact can \
         reach the postcondition group"
    );
    assert!(
        !postcondition_obligation(&body_assert),
        "a body assert is not the function postcondition"
    );
}

/// A body assert with no explicit solver mode (the common case) is forwardable;
/// `forwardable_body_assert` only excludes the *Compute* mode.
#[test]
fn body_assert_without_solver_mode_is_forwardable() {
    let body_assert = obligation("assert_witness", ObligationKind::Assert, None);
    assert!(
        forwardable_body_assert(&body_assert),
        "a default-mode (None) Assert must be forwardable"
    );
}

/// The function postcondition is itself an `ObligationKind::Assert` named exactly
/// `"postcondition"`; it must be recognized as the postcondition (so it is the
/// one that *receives* forwarded facts).
#[test]
fn postcondition_named_assert_is_recognized() {
    let post = obligation(
        "postcondition",
        ObligationKind::Assert,
        Some(SolverMode::Default),
    );
    assert!(
        postcondition_obligation(&post),
        "the `ensures` clause materializes as an Assert named `postcondition`"
    );
}

// ── should-FAIL direction: the soundness boundary on what is NOT forwarded ───

/// The postcondition must NEVER be forwarded as an assumption — forwarding the
/// goal as its own hypothesis would be circular/unsound. It is excluded from
/// `forwardable_body_assert` by name even though its kind is `Assert`.
#[test]
fn postcondition_is_not_forwardable() {
    let post = obligation(
        "postcondition",
        ObligationKind::Assert,
        Some(SolverMode::Default),
    );
    assert!(
        !forwardable_body_assert(&post),
        "SOUNDNESS: the postcondition must not be forwarded as an assumption to \
         itself (would be circular)"
    );
}

/// `ObligationKind::Ensures` obligations are produced by internal mechanisms
/// (e.g. closure ensures) interleaved among body asserts; they are neither
/// forwardable nor the function postcondition, so they keep their original
/// position untouched.
#[test]
fn ensures_kind_is_neither_forwardable_nor_postcondition() {
    let ens = obligation(
        "__option_unwrap_closure_ensures",
        ObligationKind::Ensures,
        Some(SolverMode::Default),
    );
    assert!(
        !forwardable_body_assert(&ens),
        "an Ensures-kind obligation is not a straight-line body assert"
    );
    assert!(
        !postcondition_obligation(&ens),
        "an Ensures-kind obligation is not the function postcondition"
    );
}

/// A Compute-mode assert is discharged by concrete evaluation, not SMT
/// encoding, so it is never added to the assumption set — forwarding it would be
/// a no-op at best. It must be excluded from `forwardable_body_assert`.
#[test]
fn compute_mode_assert_is_not_forwardable() {
    let compute_assert = obligation(
        "assert_by_compute",
        ObligationKind::Assert,
        Some(SolverMode::Compute),
    );
    assert!(
        !forwardable_body_assert(&compute_assert),
        "a Compute-mode assert is not encoded into the assumption set"
    );
}

/// Assumptions, requires, loop invariants, and other non-Assert kinds are not
/// straight-line body asserts and must never be picked up by the forwarding
/// candidate filter.
#[test]
fn non_assert_kinds_are_not_forwardable() {
    for kind in [
        ObligationKind::Assume,
        ObligationKind::Requires,
        ObligationKind::Ensures,
        ObligationKind::LoopInvariant,
        ObligationKind::LoopEnsures,
        ObligationKind::AssertBy,
        ObligationKind::BroadcastAssume,
    ] {
        let ob = obligation("x", kind, Some(SolverMode::Default));
        assert!(
            !forwardable_body_assert(&ob),
            "{kind:?} is not a straight-line body Assert and must not be forwardable"
        );
        assert!(
            !postcondition_obligation(&ob),
            "{kind:?} is not the function postcondition"
        );
    }
}

// ── partition behavior used by the pre-pass at typed.rs:523-543 ──────────────

/// The pre-pass partitions `plan.assertions` into (postconditions, others) and
/// then filters the others by `forwardable_body_assert`. This reproduces that
/// pipeline over a representative obligation stream and pins the resulting sets,
/// covering BOTH directions in one end-to-end shape:
///   forwarded     = {the one plain body assert}
///   postconditions = {the one `postcondition` Assert}
///   excluded       = {Compute assert, Ensures, the postcondition}
#[test]
fn partition_forwards_only_plain_body_asserts() {
    let stream = [
        obligation(
            "postcondition",
            ObligationKind::Assert,
            Some(SolverMode::Default),
        ),
        obligation(
            "assert_witness",
            ObligationKind::Assert,
            Some(SolverMode::Default),
        ),
        obligation(
            "assert_by_compute",
            ObligationKind::Assert,
            Some(SolverMode::Compute),
        ),
        obligation(
            "__closure_ensures",
            ObligationKind::Ensures,
            Some(SolverMode::Default),
        ),
    ];

    let (postconditions, others): (Vec<&PreparedObligation>, Vec<&PreparedObligation>) =
        stream.iter().partition(|o| postcondition_obligation(o));

    let forwardable: Vec<&str> = others
        .iter()
        .filter(|o| forwardable_body_assert(o))
        .map(|o| o.name.as_str())
        .collect();

    // should-VERIFY: exactly the one plain body assert is forwarded.
    assert_eq!(
        forwardable,
        vec!["assert_witness"],
        "only the plain straight-line body assert may be forwarded"
    );

    // The postcondition is correctly singled out as the receiver.
    let post_names: Vec<&str> = postconditions.iter().map(|o| o.name.as_str()).collect();
    assert_eq!(post_names, vec!["postcondition"]);

    // should-FAIL: the Compute assert, the Ensures obligation, and the
    // postcondition are all kept OUT of the forwarded set.
    assert!(!forwardable.contains(&"assert_by_compute"));
    assert!(!forwardable.contains(&"__closure_ensures"));
    assert!(!forwardable.contains(&"postcondition"));
}
