// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Adversarial soundness fixtures for match-guard support. Read via
// verify_function_from_file (syn-parsed, NOT compiled), so a deliberately
// non-exhaustive match is permitted here to probe the exhaustiveness guard.
//
// Each `trap*` function must NOT verify (counterexample or fail-closed Error);
// the `positive*` functions confirm guards actually work.

enum MatchMaybe {
    None,
    Some(u64),
}

enum TrapE {
    A,
    B,
}

// TRAP #1: a guarded IRREFUTABLE arm (`n if ...`) must be conditional, not the
// unconditional default. With x = 5 the guard is false, so the real result is 999,
// and asserting result == 0 must be a COUNTEREXAMPLE — never a false-verify.
#[trust_vc::ensures(result == 0u64)]
fn trap1_guarded_irrefutable_arm(x: u64) -> u64 {
    match x {
        n if n > 100u64 => 0u64,
        _ => 999u64,
    }
}

// TRAP #1b: the `_ if g =>` guarded-wildcard form, same hazard.
#[trust_vc::ensures(result == 0u64)]
fn trap1b_guarded_wildcard_arm(x: u64) -> u64 {
    match x {
        _ if x > 100u64 => 0u64,
        _ => 999u64,
    }
}

// TRAP #2: a guarded arm covers nothing, so `TrapE::B` is uncovered when its guard
// is false — the match is non-exhaustive and must FAIL CLOSED (Error), never verify.
#[trust_vc::ensures(result == 5u64)]
fn trap2_guarded_non_exhaustive(x: TrapE, n: u64) -> u64 {
    match x {
        TrapE::A => 5u64,
        TrapE::B if n > 1000u64 => 5u64,
    }
}

// TRAP #3: constant folding must not pick a guarded arm whose guard is false. The
// first arm's guard (100 < 10) is false, so the true value is 104; asserting 102
// (the dropped arm's value) must be a COUNTEREXAMPLE.
#[trust_vc::ensures(result == 102u64)]
fn trap3_const_fold_wrong_arm() -> u64 {
    match MatchMaybe::Some(100u64) {
        MatchMaybe::Some(n) if n < 10u64 => n + 2u64,
        MatchMaybe::Some(n) => n + 4u64,
        MatchMaybe::None => 0u64,
    }
}

// Positive: the guard genuinely selects the correct arm. Constant bodies so the
// selection is isolated from the pre-existing arm-body-arithmetic-over-binding
// limitation (see the test module). 100 < 10 is false ⇒ the second Some arm ⇒ 7.
#[trust_vc::ensures(result == 7u64)]
fn positive_guard_constant_bodies() -> u64 {
    match MatchMaybe::Some(100u64) {
        MatchMaybe::Some(n) if n < 10u64 => 5u64,
        MatchMaybe::Some(_) => 7u64,
        MatchMaybe::None => 0u64,
    }
}
