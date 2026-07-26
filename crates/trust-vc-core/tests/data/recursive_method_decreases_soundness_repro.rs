// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Adversarial fixtures for Stage-2 method-cycle termination (source_cycle_
// terminates now analyzes inherent methods). A recursive method WITH a
// #[decreases] attribute whose measure does NOT actually shrink must STILL be
// suppressed (registered uninterpreted) — publishing its single-return body
// axiom would let `m(s,n) == m(s,n) + 1` (i.e. 0 == 1) verify a false goal.
// Only a method whose measure is PROVEN to strictly decrease may publish.

struct S;

impl S {
    // VALID: n strictly decreases (n -> n-1). Body axiom MUST publish.
    #[trust_vc::proof]
    #[trust_vc::decreases(n)]
    fn good(&self, n: u32) -> u32 {
        if n == 0u32 { 0u32 } else { self.good(n - 1u32) }
    }

    // BOGUS #1: same argument passed back (n -> n). Measure does NOT shrink;
    // the `+ 1` makes it the `f(n) == f(n) + 1` (0 == 1) exploit. MUST be
    // suppressed despite carrying #[decreases].
    #[trust_vc::proof]
    #[trust_vc::decreases(n)]
    fn bad_same(&self, n: u32) -> u32 {
        self.bad_same(n) + 1u32
    }

    // BOGUS #2: argument INCREASES (n -> n+1). Clearly non-terminating. MUST be
    // suppressed.
    #[trust_vc::proof]
    #[trust_vc::decreases(n)]
    fn bad_inc(&self, n: u32) -> u32 {
        self.bad_inc(n + 1u32) + 1u32
    }
}

// ---- POSITIVE: the valid method's base case reduces. MUST verify. ----
#[trust_vc::ensures(true)]
fn good_base(s: S) {
    trust_vc::assert!(s.good(0u32) == 0u32);
}

// ---- CARDINAL: bogus-measure methods must NOT publish a usable axiom. ----
#[trust_vc::ensures(true)]
fn exploit_bad_same(s: S) {
    trust_vc::assert!(s.bad_same(3u32) == s.bad_same(3u32) + 1u32);
}
#[trust_vc::ensures(true)]
fn exploit_bad_inc(s: S) {
    trust_vc::assert!(s.bad_inc(3u32) == s.bad_inc(3u32) + 1u32);
}
// assert!(false) with the bogus axiom in scope must NOT verify either.
#[trust_vc::ensures(true)]
fn exploit_bad_same_false(s: S) {
    let _z = s.bad_same(0u32);
    trust_vc::assert!(false);
}
