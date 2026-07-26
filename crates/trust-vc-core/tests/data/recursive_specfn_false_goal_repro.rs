// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Robustness probe (#54): verifying a FALSE goal against a CORRECT recursive
// spec fn (decreasing measure, faithful defining axiom) must return a definitive
// result (Counterexample preferred, Unknown acceptable), and the matching TRUE
// goal must Verify. Neither may crash (no SIGBUS/stack-overflow).
//
// The historical crash: the demand-inline retry (#2655) promoted the recursive
// spec fn to an inline body and `substitute_inline_calls` recursed forever
// inlining the self/mutual call. Both a self-recursive `good` and a mutually
// recursive `ping`/`pong` are exercised here so the catalog recursion filter
// AND the inline-expansion depth backstop are both covered.

// --- bit-vector (u64) correctly-decreasing self-recursion ---

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn good(n: u64) -> u64 {
    if n == 0u64 {
        0u64
    } else {
        good(n - 1u64) + 1u64
    }
}

// FALSE: good(0) == 0, not 1.
#[trust_vc::ensures(true)]
fn false_good0_eq1() {
    trust_vc::assert!(good(0u64) == 1u64);
}

// FALSE: good(1) == 1, not 5.
#[trust_vc::ensures(true)]
fn false_good1_eq5() {
    trust_vc::assert!(good(1u64) == 5u64);
}

// FALSE: good(2) == 2, not 1.
#[trust_vc::ensures(true)]
fn false_good2_eq1() {
    trust_vc::assert!(good(2u64) == 1u64);
}

// TRUE: good(0) == 0.
#[trust_vc::ensures(true)]
fn true_good0_eq0() {
    trust_vc::assert!(good(0u64) == 0u64);
}

// TRUE: good(1) == 1.
#[trust_vc::ensures(true)]
fn true_good1_eq1() {
    trust_vc::assert!(good(1u64) == 1u64);
}

// TRUE: good(2) == 2.
#[trust_vc::ensures(true)]
fn true_good2_eq2() {
    trust_vc::assert!(good(2u64) == 2u64);
}

// --- nat correctly-decreasing self-recursion (mirror, no BV wraparound) ---

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn goodn(n: nat) -> nat {
    if n == 0 {
        0
    } else {
        (goodn((n - 1) as nat) + 1) as nat
    }
}

#[trust_vc::ensures(true)]
fn false_goodn0_eq1() {
    trust_vc::assert!(goodn(0) == 1);
}

#[trust_vc::ensures(true)]
fn true_goodn0_eq0() {
    trust_vc::assert!(goodn(0) == 0);
}

// --- mutually recursive, correctly decreasing (count down on nat) ---
// Exercises the inline-expansion depth backstop: the self-recursion catalog
// filter does NOT exclude these (neither body calls ITSELF), so a naive inline
// would chase ping -> pong -> ping -> ... forever.

#[trust_vc::spec]
#[trust_vc::decreases(i)]
fn ping(i: u64) -> u64 {
    if i == 0u64 { 0u64 } else { 1u64 + pong(i - 1u64) }
}

#[trust_vc::spec]
#[trust_vc::decreases(i)]
fn pong(i: u64) -> u64 {
    if i == 0u64 { 0u64 } else { 1u64 + ping(i - 1u64) }
}

// FALSE: ping(0) == 0, not 1.
#[trust_vc::ensures(true)]
fn false_ping0_eq1() {
    trust_vc::assert!(ping(0u64) == 1u64);
}

// TRUE: ping(0) == 0.
#[trust_vc::ensures(true)]
fn true_ping0_eq0() {
    trust_vc::assert!(ping(0u64) == 0u64);
}
