// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Probe: a top-level `@`-binding refinement must NOT be silently dropped.

// `n @ 0` matches ONLY when x == 0. For x != 0 the `_` arm yields `result == x`,
// so `ensures(result == 5)` is FALSE. If `@ 0` is dropped (mis-lowered to the
// irrefutable `n`), the first arm always matches -> result always 5 -> the false
// postcondition VERIFIES. That is the cardinal false-verify. Correct: NOT Verified.
#[trust_vc::ensures(result == 5)]
fn at_zero_refinement_must_not_drop(x: u64) -> u64 {
    match x {
        n @ 0 => 5,
        _ => x,
    }
}

// Control: a bare binding `n` (no `@`) IS irrefutable, so result == x always;
// `ensures(result == x)` is genuinely TRUE. Confirms the machinery works when
// there is no dropped refinement.
#[trust_vc::ensures(result == x)]
fn bare_binding_is_irrefutable(x: u64) -> u64 {
    match x {
        n => n,
    }
}
