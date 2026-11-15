// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the file-path `loop_decreases!` adversarial soundness suite.
// Verified via `verify_function_from_file` in `loop_decreases_soundness.rs`.

// ---------------------------------------------------------------------------
// POSITIVE: a genuinely terminating loop verifies.
// ---------------------------------------------------------------------------

// Count-up: measure `10 - i` strictly decreases each iteration (i increments,
// guard i < 10); the precondition establishes the invariant at entry. VERIFIED.
#[trust_vc::requires(i <= 10u64)]
#[trust_vc::ensures(true)]
fn terminating_countup(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_decreases!(10u64 - i);

        i = i + 1u64;
    }
}

// Count-down: measure `i` strictly decreases as i counts down. VERIFIED.
#[trust_vc::requires(i <= 100u64)]
#[trust_vc::ensures(true)]
fn terminating_countdown(mut i: u64) {
    while i > 0u64 {
        trust_vc::invariant!(i <= 100u64);
        trust_vc::loop_decreases!(i);

        i = i - 1u64;
    }
}

// ---------------------------------------------------------------------------
// NEGATIVE (bad measure): the measure does NOT strictly decrease.
// ---------------------------------------------------------------------------

// Measure `i` INCREASES each iteration (i = i + 1). The decrease obligation
// `i < i_entry` is violated. COUNTEREXAMPLE — must never verify.
#[trust_vc::requires(i <= 10u64)]
#[trust_vc::ensures(true)]
fn bad_measure_increases(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_decreases!(i);

        i = i + 1u64;
    }
}

// ---------------------------------------------------------------------------
// NEGATIVE (well-foundedness): the measure strictly decreases but goes NEGATIVE.
// ---------------------------------------------------------------------------

// Measure `5 - i` strictly decreases, but the invariant only bounds i <= 10, so
// once i > 5 the measure would go negative (underflow). The non-negativity /
// overflow check catches this. COUNTEREXAMPLE — proves the nonneg is a real
// check, not the vacuous unsigned `>= 0`.
#[trust_vc::requires(i <= 10u64)]
#[trust_vc::ensures(true)]
fn measure_goes_negative(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_decreases!(5u64 - i);

        i = i + 1u64;
    }
}

// ---------------------------------------------------------------------------
// LANDMINE (continue-interior non-termination): a `continue` back-edge skips the
// measure update, so the loop does not terminate. The bare `loop{}` captures no
// single-iteration transition, so the decrease keeps a free entry variable.
// COUNTEREXAMPLE — must never verify (upstream Verus rejects this shape).
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn continue_skips_measure(mut i: u64) {
    loop {
        trust_vc::loop_decreases!(i);

        if i == 0u64 {
            break;
        }

        if i == 20u64 {
            continue;
        }

        i = i - 1u64;
    }
}

// ---------------------------------------------------------------------------
// POSITIVE (break-interior body, rows 430/431 — 2026-09-10): a break-only
// `if cond { break; }` keeps the body in the exact-transition lane, so the
// measure IS registered: WF1 under the invariant, WF2 under `guard ∧ ¬cond`
// with the exact `i + 1` transition. The loop genuinely terminates, so it
// VERIFIES. (Before that landing the `if { break }` made the body non-flat and
// this was pinned as an under-verifying Counterexample.)
// ---------------------------------------------------------------------------
#[trust_vc::requires(i <= 10u64)]
#[trust_vc::ensures(true)]
fn break_interior_non_flat(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_decreases!(10u64 - i);

        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
}

// ---------------------------------------------------------------------------
// LANDMINE (break-interior body, BAD measure): same shape, but the measure `i`
// GROWS on every head-to-head iteration. The exact lane must REFUTE WF2 — the
// break site exempts nothing about the measure. Must NOT verify.
// ---------------------------------------------------------------------------
#[trust_vc::requires(i <= 10u64)]
#[trust_vc::ensures(true)]
fn break_interior_bad_measure(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::loop_decreases!(i);

        i = i + 1u64;
        if i == 10u64 {
            break;
        }
    }
}

// A strictly decreasing mathematical integer is not, by itself, a
// well-founded measure.  Omitting the base/non-negativity obligation would
// incorrectly accept this loop, which decreases forever below zero.
//
// This loop DIVERGES (the invariant `i < 0` implies the guard `i < 0`, so it
// never exits), so the whole-function vacuous-truth precheck fires first
// (`requires(i < 0)` contradicts the auto-generated normal-exit fact
// `!(i < 0)` ≡ `i >= 0`) and reports Unknown — a fail-closed non-`Verified`.
// The NON-divergent `int_floor_probe` below exercises the SAME missing-floor
// on an `int` measure through the WF1 lane directly, for a clean WF1
// Counterexample.
#[trust_vc::requires(i < 0)]
#[trust_vc::ensures(true)]
fn unbounded_negative_measure(mut i: int) {
    while i < 0 {
        trust_vc::invariant!(i < 0);
        trust_vc::loop_decreases!(i);
        i = i - 1;
    }
}

// WF1 FLOOR probe on a SIGNED `i32` measure, NON-divergent (the loop exits at
// `i == 10`) so it reaches the measure lane. The measure `3 - i` strictly
// DECREASES each iteration (WF2 holds, as `i` counts up), but under the invariant
// `i <= 10` and guard `i < 10` it goes NEGATIVE once `i > 3` (e.g. `i == 5` gives
// `3 - 5 == -2`, a perfectly representable i32 — no overflow/underflow), so the
// WF1 non-negativity floor `3 - i >= 0` is refuted in the measure's own SIGNED
// sort. This is a real signed refutation, NOT the exec-underflow path and NOT the
// vacuous unsigned tautology `>= 0`: it exercises exactly the floor discipline
// that a mathematical `int` measure needs (and that `unbounded_negative_measure`
// intends), but on a well-formed exec type so it clears the divergent-loop
// precheck and produces a clean WF1 Counterexample. WF1 is load-bearing here:
// with the floor removed, WF2 alone would falsely accept this
// strictly-decreasing-below-zero measure.
// The invariant bounds `i` on BOTH sides (`i >= 0` and `i <= 10`, as two
// separate clauses — a single `&&`-conjoined invariant/requires is silently
// dropped by the file-path extractor, which would make the loop vacuously
// verify) so the measure `3 - i` stays in `[-7, 3]` and can NEVER overflow i32.
// That forces the WF1 Counterexample to come from the genuine SIGNED refutation
// `3 - i >= 0` ⇔ `i <= 3` (falsified at e.g. `i == 9`, giving `3 - 9 == -6`),
// NOT from a subtraction-overflow escape.
#[trust_vc::requires(i >= 0i32)]
#[trust_vc::requires(i <= 10i32)]
#[trust_vc::ensures(true)]
fn int_floor_probe(mut i: i32) {
    while i < 10i32 {
        trust_vc::invariant!(i >= 0i32);
        trust_vc::invariant!(i <= 10i32);
        trust_vc::loop_decreases!(3i32 - i);
        i = i + 1i32;
    }
}
