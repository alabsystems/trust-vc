// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the adversarial soundness suite `loop_return_invariant_soundness.rs`.
// Verified via verify_function_from_file, cache-OFF.
//
// PHASE E — early-return-from-loop. A `loop`/`while`/`for` body is HAVOC'd across
// iterations (the invariant is the only fact carried), so an explicit `return X`
// inside it is admitted into the multiple-return disjunction ONLY when `X` is
// provably LOOP-INVARIANT: a literal constant, or an immutable parameter that is
// never written or rebound in the loop. Such an `X` is identical regardless of
// the havoc, so `result == X` is a sound member of the return over-approximation.
//
// THE CRUX (why the loop-invariance gate is load-bearing, not cosmetic): a
// `return X` that reads loop-MUTATED state has an INDETERMINATE value under
// havoc. Admitting `result == X` for such an `X` — with `X` bound to its
// pre-loop value — would let a postcondition that is false in general FALSE-
// VERIFY. The `havoc_trap` / `loop_written_param` fixtures below are exactly
// that shape; they MUST stay fail-closed (Ambiguous → extraction error).

#![allow(dead_code, unreachable_code, unused_variables, unused_mut)]

// ---------------------------------------------------------------------------
// POSITIVE #1 — a literal-constant loop-return joins the fall-through tail in a
// sound disjunction. result ∈ {7, 13}; the matching ensures MUST VERIFY.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(result == 7u64 || result == 13u64)]
fn loop_const_return_disjunction_verified(flag: bool) -> u64 {
    loop {
        if flag {
            return 7u64;
        }
        break;
    }
    13u64
}

// ---------------------------------------------------------------------------
// POSITIVE #2 — an IMMUTABLE parameter (`early`) that is never written or rebound
// in the loop is loop-invariant, so `return early` joins the tail param `late` in
// a sound disjunction. result ∈ {early, late}; the matching ensures MUST VERIFY.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(result == early || result == late)]
fn loop_invariant_param_return_disjunction_verified(flag: bool, early: u64, late: u64) -> u64 {
    loop {
        if flag {
            return early;
        }
        break;
    }
    late
}

// ---------------------------------------------------------------------------
// POSITIVE #3 — the `while` variant of the literal-constant loop-return.
// result ∈ {7, 17}; the matching ensures MUST VERIFY.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(result == 7u64 || result == 17u64)]
fn while_loop_const_return_verified(flag: bool) -> u64 {
    while flag {
        return 7u64;
    }
    17u64
}

// ---------------------------------------------------------------------------
// POSITIVE #4 — the `for` variant of the literal-constant loop-return.
// result ∈ {7, 17}; the matching ensures MUST VERIFY.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(result == 7u64 || result == 17u64)]
fn for_loop_const_return_verified() -> u64 {
    for value in [0u64, 1u64] {
        if value == 1u64 {
            return 7u64;
        }
    }
    17u64
}

// ---------------------------------------------------------------------------
// FALSE-POSTCONDITION — the SAME admitted shape as POSITIVE #1, but the ensures
// holds for only ONE disjunct. The fall-through value 13 is a live witness, so
// this MUST produce a model-bearing COUNTEREXAMPLE (the disjunction is genuinely
// modeled — not silently dropped, which would have let this verify).
// ---------------------------------------------------------------------------
#[trust_vc::ensures(result == 7u64)]
fn loop_const_return_false_postcondition_counterexample(flag: bool) -> u64 {
    loop {
        if flag {
            return 7u64;
        }
        break;
    }
    13u64
}

// ---------------------------------------------------------------------------
// HAVOC FALSE-VERIFY TRAP (the crux): the loop MUTATES a local `acc` and returns
// it. `acc` is loop-written, so it is NOT loop-invariant and the loop-return is
// REJECTED (Ambiguous → extraction error). It MUST NOT VERIFY.
//
// Why this is the trap: the real function returns `acc == 1` on the early path
// (never 0) or falls through to 0. `ensures(result == 0)` is therefore FALSE for
// flag=true. Had the gate admitted `result == acc` binding `acc` to its pre-loop
// value 0, the disjunction would collapse to `result == 0 || result == 0` and
// FALSE-VERIFY. A `Verified` here means the loop-invariance gate leaked.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(result == 0u64)]
fn loop_mutated_local_return_havoc_trap_fail_closed(flag: bool) -> u64 {
    let mut acc = 0u64;
    loop {
        acc = acc + 1u64;
        if flag {
            return acc;
        }
        break;
    }
    0u64
}

// ---------------------------------------------------------------------------
// LOOP-INVARIANT-CHECK PROBE (isolates the loop-WRITTEN check): `x` IS a
// parameter (so the "is a parameter" half of the gate passes) but is ASSIGNED in
// the loop (`x = x + 1`), so the "not loop-written" half must reject it. It MUST
// NOT VERIFY.
//
// Discriminator: with requires(x == 5), the real function returns `x == 6` on the
// early path (never 5) or falls through to 99. `ensures(result == 5 || result ==
// 99)` is FALSE for flag=true (result is 6). Had the gate admitted `result == x`
// binding `x` to its ENTRY value 5, this would FALSE-VERIFY. Forgetting the
// loop-written check is exactly the bug this catches.
// ---------------------------------------------------------------------------
#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(result == 5u64 || result == 99u64)]
fn loop_written_param_return_fail_closed(mut x: u64, flag: bool) -> u64 {
    loop {
        x = x + 1u64;
        if flag {
            return x;
        }
        break;
    }
    99u64
}

// ---------------------------------------------------------------------------
// LOOP-VARIABLE PROBE — the `for` loop variable `value` is rebound every
// iteration and is not a parameter, so `return value` is NOT provably loop-
// invariant and MUST fail closed (conservative rejection). The ensures happens
// to be true, but soundness requires we decline what we cannot prove invariant.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(result == 0u64 || result == 17u64)]
fn for_loop_variable_return_fail_closed() -> u64 {
    for value in [0u64, 5u64] {
        return value;
    }
    17u64
}
