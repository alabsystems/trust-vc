// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! NARROWNESS PINS. Nothing in this file binds any special macro name, so every
//! function here must resolve and verify (or refute) exactly as it did before
//! the scope pass existed. A fix that declines these has traded a false verify
//! for a capability loss.

use trust_vc::{assume, ensures};
// A named import from the lane's own crate, not `vstd::prelude::*`: a glob
// from outside the file can bind the primitive type names spelled here (the
// type-name rule) and a trait whose method a call here takes (the trait
// method rule), and either refuses a `Verified` answer, which these pins of
// macro names do not test.
use trust_vc_types::seq;

/// The unqualified spelling — 78 occurrences in the ported corpus.
#[trust_vc::ensures(true)]
fn bare_assume_still_verifies(x: u64) -> u64 {
    assume!(x == 0u64);
    trust_vc::assert!(x <= 255u64);
    0u64
}

/// The qualified spelling — 197 occurrences in the ported corpus.
#[trust_vc::ensures(true)]
fn qualified_assume_still_verifies(x: u64) -> u64 {
    trust_vc::assume!(x == 0u64);
    trust_vc::assert!(x <= 255u64);
    0u64
}

/// `matches!` must still desugar to its `match` expansion...
#[trust_vc::ensures(true)]
fn matches_still_verifies() -> u64 {
    let y: u8 = 7u8;
    trust_vc::assert!(matches!(y, 7u8));
    0u64
}

/// ...in BOTH directions: a false `matches!` claim must still be refuted, not
/// swallowed by a fail-closed error.
#[trust_vc::ensures(true)]
fn false_matches_still_refutes() -> u64 {
    let y: u8 = 7u8;
    trust_vc::assert!(matches!(y, 8u8));
    0u64
}

/// The contract-ATTRIBUTE position — the one the shadow reproducer used — must
/// keep resolving `matches!` when nothing shadows it.
#[trust_vc::requires(y == 7u8)]
#[trust_vc::ensures(matches!(y, 7u8))]
fn matches_in_contract_still_verifies(y: u8) -> u64 {
    0u64
}

mod inner {
    /// A function in a nested module, with nothing shadowed anywhere, resolves
    /// the bare name exactly as the top level does.
    #[trust_vc::ensures(true)]
    pub fn module_function_still_verifies(x: u64) -> u64 {
        assume!(x == 0u64);
        trust_vc::assert!(x <= 255u64);
        0u64
    }
}

/// NARROWNESS PIN: `trust_vc_types::seq!` — the spelling the ported corpus
/// writes 284 times — must keep resolving.
#[trust_vc::ensures(true)]
fn qualified_seq_still_verifies() -> u64 {
    let s = trust_vc_types::seq![1u64, 2u64, 3u64];
    trust_vc::assert!(s.len() == 3);
    0u64
}

/// NARROWNESS PIN: the bare spelling of the same lane.
#[trust_vc::ensures(true)]
fn bare_seq_still_verifies() -> u64 {
    let s = seq![1u64, 2u64, 3u64];
    trust_vc::assert!(s.len() == 3);
    0u64
}

/// NARROWNESS PIN: `crate::seq!` points back into this file, which shadows
/// nothing, so it must resolve rather than be declined as a foreign root.
#[trust_vc::ensures(true)]
fn crate_qualified_seq_still_verifies() -> u64 {
    let s = crate::seq![1u64, 2u64, 3u64];
    trust_vc::assert!(s.len() == 3);
    0u64
}
