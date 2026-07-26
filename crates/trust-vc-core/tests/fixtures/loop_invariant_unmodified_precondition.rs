// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Fixture for the frame-condition inductive step carrying FUNCTION PRECONDITIONS
// over UNMODIFIED (frame-preserved) variables. Verified by
// `loop_invariant_unmodified_precondition_soundness.rs`.

// (1) VERIFIED — the loop invariant `acc_eval >= acc_rhs` is preserved across an
// arbitrary (symbolic `n`) number of iterations because the step's entailment
// `step_eval >= step_rhs` (a precondition over the UNMODIFIED params `step_eval`,
// `step_rhs`) is now carried into the inductive step. Each iteration adds the
// step's LHS value and degree; `(acc_eval >= acc_rhs) && (step_eval >= step_rhs)`
// implies `acc_eval + step_eval >= acc_rhs + step_rhs`, so the invariant holds.
#[trust_vc::requires(acc_eval >= acc_rhs)]
#[trust_vc::requires(step_eval >= step_rhs)]
#[trust_vc::ensures(acc_eval >= acc_rhs)]
pub fn accumulate_entailed(
    mut acc_eval: int,
    mut acc_rhs: int,
    step_eval: int,
    step_rhs: int,
    mut k: int,
    n: int,
) {
    while k < n {
        trust_vc::invariant!(acc_eval >= acc_rhs);
        acc_eval = acc_eval + step_eval;
        acc_rhs = acc_rhs + step_rhs;
        k = k + 1;
    }
}

// (2) COUNTEREXAMPLE (load-bearing precondition) — the SAME loop WITHOUT the
// `step_eval >= step_rhs` precondition. The added step may lower the accumulator
// below its degree (`step_eval < step_rhs`), so the invariant is NOT preserved.
// The fix is sound, not blanket-accepting: dropping the frame-preserved fact
// flips the result to a refutation.
#[trust_vc::requires(acc_eval >= acc_rhs)]
#[trust_vc::ensures(acc_eval >= acc_rhs)]
pub fn accumulate_no_step_bound(
    mut acc_eval: int,
    mut acc_rhs: int,
    step_eval: int,
    step_rhs: int,
    mut k: int,
    n: int,
) {
    while k < n {
        trust_vc::invariant!(acc_eval >= acc_rhs);
        acc_eval = acc_eval + step_eval;
        acc_rhs = acc_rhs + step_rhs;
        k = k + 1;
    }
}

// (3) COUNTEREXAMPLE (soundness of the gate) — a precondition over a MODIFIED
// variable must NOT be carried into the inductive step. `acc_eval >= 0` mentions
// `acc_eval`, which the body modifies, so it can become false after iterations
// (`step_eval` is unconstrained). The engine must still REJECT the invariant
// `acc_eval >= 0`: only preconditions whose variables are ALL unmodified are
// re-assumed.
#[trust_vc::requires(acc_eval >= 0)]
#[trust_vc::ensures(acc_eval >= 0)]
pub fn modified_precondition_not_carried(
    mut acc_eval: int,
    step_eval: int,
    mut k: int,
    n: int,
) {
    while k < n {
        trust_vc::invariant!(acc_eval >= 0);
        acc_eval = acc_eval + step_eval;
        k = k + 1;
    }
}
