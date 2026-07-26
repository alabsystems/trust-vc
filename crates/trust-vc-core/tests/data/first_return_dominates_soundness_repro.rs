// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the adversarial soundness suite `first_return_dominates_soundness.rs`.
// Verified via verify_function_from_file, cache-OFF.
//
// A statement-level `return` unconditionally diverges, so the FIRST top-level
// `return` in a block DOMINATES: it is the sole reachable return value and every
// later statement (including further top-level `return`s) is dead code. The
// classifier relaxation from `> 1` to `>= 1` (return_extract.rs) therefore lifts
// only the multiple-top-level-returns CONSERVATISM guard, never a soundness guard.
//
// LOAD-BEARING CRUX (why "first" and not merely "some"): result pins to the FIRST
// return, so with `return A; return B;` a postcondition on A VERIFIES while the
// same postcondition on B (dead code) must COUNTEREXAMPLE. Reversing the order
// flips which literal is live — the discriminator is ORDER-SENSITIVE.
//
// GUARD-INTACT: a reachable *nested* return that could run before the first
// top-level return still trips a NestedReturnScan guard (`nested_returns.values`
// non-empty at line 86, or the `unsupported` local-initializer guard) and stays
// fail-closed (Ambiguous), so no wrong result is verified.

#![allow(dead_code, unreachable_code, unused_variables)]

// ---------------------------------------------------------------------------
// DISCRIMINATOR: `return 11; return 13;` — the FIRST return (11) dominates.
// The postcondition on the first value MUST VERIFY.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(result == 11u8)]
fn first_value_pinned_verified() -> u8 {
    return 11u8;
    return 13u8;
}

// ---------------------------------------------------------------------------
// DISCRIMINATOR (the crux): the SECOND value (13) is DEAD code. A postcondition
// pinning the result to 13 MUST COUNTEREXAMPLE — result is 11, not "some" return.
// A `Verified` here = the change merged multiple returns unsoundly.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(result == 13u8)]
fn second_value_is_dead_counterexample() -> u8 {
    return 11u8;
    return 13u8;
}

// ---------------------------------------------------------------------------
// ORDER-SENSITIVITY: reversed to `return 13; return 11;`. Now the FIRST return is
// 13, so the postcondition on 13 MUST VERIFY.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(result == 13u8)]
fn reordered_first_value_pinned_verified() -> u8 {
    return 13u8;
    return 11u8;
}

// ---------------------------------------------------------------------------
// ORDER-SENSITIVITY (companion): with `return 13; return 11;`, the second value
// (11) is now DEAD. The postcondition on 11 MUST COUNTEREXAMPLE.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(result == 11u8)]
fn reordered_second_value_is_dead_counterexample() -> u8 {
    return 13u8;
    return 11u8;
}

// ---------------------------------------------------------------------------
// GUARD-INTACT #1 (the load-bearing line-86 guard): a reachable NESTED return
// (`return 1u8`) precedes the top-level returns, so `nested_returns.values` is
// non-empty and classification stays Ambiguous ("nested explicit return path
// after top-level return"). result could be 1u8, so `result == 11u8` is FALSE —
// it MUST NOT VERIFY. A `Verified` here = the nested-return guard leaked.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(result == 11u8)]
fn guard_reachable_nested_return_before_top_level_fail_closed(flag: bool) -> u8 {
    if flag {
        return 1u8;
    }
    return 11u8;
    return 13u8;
}

// ---------------------------------------------------------------------------
// GUARD-INTACT #2 (the task's local-initializer shape): a nested return inside a
// local initializer before the top-level returns. Trips the "local initializer
// explicit return path" guard and stays fail-closed. result could be 1u8, so
// `result == 11u8` MUST NOT VERIFY.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(result == 11u8)]
fn guard_nested_return_in_local_init_fail_closed(flag: bool) -> u8 {
    let x = if flag { return 1u8 } else { 2u8 };
    return 11u8;
    return 13u8;
}
