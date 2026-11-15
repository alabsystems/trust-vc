// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Probe: an unrecognized `trust_vc::`-namespaced contract attribute must NOT be
// silently discarded by the file-VC lane.
//
// `ghost_ensures` and `ensurez` are NOT `#[proc_macro_attribute]` exports, so
// the compiled lane never sees them. The file-VC lane (`verify_function_from
// _file` / `cargo trust-vc check`) reads attributes straight off the AST, and
// its outer allowlist match used to end in `_ => {}` — an unknown
// `trust_vc::`-namespaced clause was DROPPED. With the clause gone the function
// carries no postcondition at all, so the false claim `result > 100` verifies.
// Correct behaviour: decline (an Err/`unknown trust_vc attribute`), never
// `Verified`.

// FV-2 reproducer #1: `ghost_ensures` — a real trust_vc macro name, but a
// function-like `#[proc_macro]`, not an attribute. Dropped silently.
#[trust_vc::ghost_ensures(result > 100u64)]
fn ghost_ensures_must_not_be_dropped(x: u64) -> u64 {
    trust_vc::assert!(1u64 == 1u64);
    1u64
}

// FV-2 reproducer #2: `ensurez` — a plain typo of `ensures`. Dropped silently.
#[trust_vc::ensurez(result > 100u64)]
fn unknown_segment_must_not_be_dropped(x: u64) -> u64 {
    trust_vc::assert!(1u64 == 1u64);
    1u64
}

// FV-2 reproducer #3 (`masked`): the dropped clause sits NEXT TO a surviving
// one, so the `OnlyAssumptions` emptiness floor cannot see it — the context has
// a live assertion lane from `#[ensures(true)]`.
#[trust_vc::ensures(true)]
#[trust_vc::ensurez(result > 100u64)]
fn masked_dropped_clause_must_not_verify(x: u64) -> u64 {
    trust_vc::assert!(1u64 == 1u64);
    1u64
}

// NARROWNESS PIN 1: the same shape spelled with the CORRECT clause name and a
// TRUE postcondition must still verify.
#[trust_vc::ensures(result == 1u64)]
fn correct_clause_still_verifies(x: u64) -> u64 {
    trust_vc::assert!(1u64 == 1u64);
    1u64
}

// NARROWNESS PIN 2: non-`trust_vc::` attributes must stay silently ignored.
// `#[must_use]`, `#[allow(..)]`, `#[cfg_attr(..)]` and doc comments (which
// lower to `#[doc = ".."]`) are ordinary Rust and carry no verification
// meaning here. The gate must not widen to any of them. A FOREIGN namespaced
// path (`#[some_crate::widget]`) is pinned in
// `dropped_contract_attr_foreign.rs`: it can be an attribute macro, which
// refuses its whole file.
/// A doc comment must not trip the gate.
#[must_use]
#[allow(dead_code)]
#[cfg_attr(test, allow(unused_variables))]
#[trust_vc::ensures(result == 1u64)]
fn foreign_attributes_still_ignored(x: u64) -> u64 {
    trust_vc::assert!(1u64 == 1u64);
    1u64
}

// NARROWNESS PIN 3: a KNOWN trust_vc attribute that this extraction pass does
// not itself consume (it is read by other passes, or is a pure marker) must
// still be ignored here rather than rejected.
#[trust_vc::verifier(nonlinear)]
#[trust_vc::ensures(result == 1u64)]
fn known_other_trust_vc_attribute_still_verifies(x: u64) -> u64 {
    trust_vc::assert!(1u64 == 1u64);
    1u64
}
