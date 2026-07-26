// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// FRESH adversarial fixture for the file-path `loop_decreases!` WF1
// non-negativity FLOOR, targeting the ay bump a998c3e3 -> 4df6ab25 (the
// forall_inst / quantified-refutation delta). Verified via
// `verify_function_from_file`.
//
// Distinct from the existing WF1 probe `int_floor_probe`: THAT probe's floor
// query is quantifier-FREE, so it never runs the new ay's forall_inst
// quantifier expansion. THIS probe injects an assumed `forall` into the WF1
// floor query along BOTH assumption paths of `verify_measure_nonneg_floor` — a
// loop `invariant!(forall ...)` (assumed at the current, HAVOC'd loop head) and
// a `requires(forall ...)` (pre-state-rewritten but preserved as a concrete
// quantifier under the floor's havoc) — while keeping the measure a genuinely
// unbounded-below mathematical `int`.

// A NON-divergent `int` count-up loop whose measure `3 - i` strictly DECREASES
// each iteration (WF2 holds: i++  =>  3-(i+1) < 3-i) but goes NEGATIVE once
// i > 3 (e.g. i == 9  =>  3 - 9 == -6), a perfectly representable mathematical
// `int` — there is NO bit-vector 0-floor to fall back on, so this is the
// cardinal unbounded-below `int` hole the lane was quarantined for. The
// invariants bound i on BOTH sides as two SEPARATE clauses (a single
// `&&`-conjoined invariant is silently dropped by the file-path extractor), so
// `3 - i` stays in [-7, 3] and the loop exits at i == 10 (non-divergent, so it
// clears the whole-function vacuous-truth precheck and reaches the measure
// lane). WF2 (descent) holds, so ONLY the WF1 floor can reject: `3 - i >= 0`
// (<=>  i <= 3) is genuinely refutable at e.g. i == 9. CORRECT VERDICT:
// Counterexample from the WF1 non-negativity floor.
//
// The two `forall` facts are arithmetic tautologies once the measure-shaped
// bodies are normalized (`(k < i) ==> (3 - k > 3 - i)`  <=>  `(k<i) ==> (k<i)`,
// and `(k >= i) ==> (3 - k <= 3 - i)`  <=>  `(k>=i) ==> (k>=i)`): they are
// SATISFIABLE together with `3 - i < 0` and bound NOTHING, so a SOUND solver
// keeps the floor query SAT and returns the WF1 Counterexample. Their sole
// purpose is to force the new ay's forall_inst quantifier-expansion to RUN while
// discharging the floor. If that expansion leaks a spurious ground conjunct —
// an unguarded body from the ded7b9c7 assume-mismatch fix, a datatype-skolem
// universe atom per e4fbaca7, or a mis-certified quantified refutation per
// a4409f83 — the floor premise set goes spuriously UNSAT and the floor
// VACUOUSLY discharges. A `Verified` here is the reopened cardinal false-verify.
// The `3 - k` / `3 - i` term shapes are shared with the measure so the
// quantifier can be instantiated at k := i against the floor's own ground term.
#[trust_vc::requires(i >= 0)]
#[trust_vc::requires(i <= 10)]
#[trust_vc::requires(forall|k: int| (k >= i) ==> (3 - k <= 3 - i))]
#[trust_vc::ensures(true)]
fn quantified_floor_probe(mut i: int) {
    while i < 10 {
        trust_vc::invariant!(i >= 0);
        trust_vc::invariant!(i <= 10);
        trust_vc::invariant!(forall|k: int| (k < i) ==> (3 - k > 3 - i));
        trust_vc::loop_decreases!(3 - i);
        i = i + 1;
    }
}
