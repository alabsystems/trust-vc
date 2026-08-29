// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the deterministic conflict-budget acceptance tests
// (`tests/deterministic_conflict_budget.rs`).
//
// The parity chain is the probe: an 8-variable boolean XOR-parity identity
// whose refutation-of-negation genuinely searches in ay's MAIN CDCL loop —
// the loop the `:rlimit` conflict budget governs. Measured (2026-08-26,
// modified CLI, cache off): verifies in ~0.2s with the default budget, and
// deterministically exhausts a 1-conflict and a 10-conflict budget on every
// repeat. A BV-heavy probe is deliberately NOT used here: BV bit-blasting
// work happens in a sub-solver the conflict budget does not see (see
// `BV_HARD_TIMEOUT` in `encoder/verification/timeout.rs`), so a BV shape
// cannot demonstrate that the budget binds.

// Control: no rlimit — the calibrated default budget applies and the parity
// identity must verify.
#[trust_vc::ensures(true)]
fn parity_default_budget(a: bool, b: bool, c: bool, d: bool, e: bool, f: bool, g: bool, h: bool) {
    trust_vc::assert!(
        (((a != b) != (c != d)) != ((e != f) != (g != h)))
            == (((h != a) != (b != g)) != ((c != f) != (d != e)))
    );
}

// rlimit(0.000001) rounds to a 1-conflict deterministic budget: the budget
// must BIND — Unknown with a `resourceout` reason naming the budget — and
// must NEVER verify.
#[verifier::rlimit(0.000001)]
#[trust_vc::ensures(true)]
fn parity_one_conflict(a: bool, b: bool, c: bool, d: bool, e: bool, f: bool, g: bool, h: bool) {
    trust_vc::assert!(
        (((a != b) != (c != d)) != ((e != f) != (g != h)))
            == (((h != a) != (b != g)) != ((c != f) != (d != e)))
    );
}

// rlimit(1000) = 40M conflicts: a huge budget must change nothing relative to
// the default — the identity still verifies.
#[verifier::rlimit(1000)]
#[trust_vc::ensures(true)]
fn parity_huge_budget(a: bool, b: bool, c: bool, d: bool, e: bool, f: bool, g: bool, h: bool) {
    trust_vc::assert!(
        (((a != b) != (c != d)) != ((e != f) != (g != h)))
            == (((h != a) != (b != g)) != ((c != f) != (d != e)))
    );
}

// LIAR PIN: a false postcondition under a huge bounded budget must still
// REFUTE — a big work grant buys work, never a verdict.
#[verifier::rlimit(1000)]
#[trust_vc::ensures(result == 42u64)]
fn liar_under_huge_budget() -> u64 {
    7u64
}

// LIAR PIN: `rlimit(infinity)` (decline a trust-vc budget; ay's own default
// allowance governs) must still REFUTE a false postcondition.
#[verifier::rlimit(infinity)]
#[trust_vc::ensures(result == 42u64)]
fn liar_under_infinity() -> u64 {
    7u64
}
