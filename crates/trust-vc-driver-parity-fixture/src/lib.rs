//! Real-macro fixture for the trust-vc-driver-vs-syn parity witness.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Every function here uses the REAL `#[trust_vc::contract(...)]` macro (not a
//! hand-written `requires`/`ensures` marker shim) and sits inside the
//! rustc-driver front end's supported scalar-Hoare fragment, so BOTH the trusted
//! syn path and the nightly rustc-driver bin classify each as a verification
//! target and reach a definite verdict.
//!
//! The pair is deliberately non-degenerate: `inc` VERIFIES and `inc_bad` (an
//! intentionally FALSE postcondition over the same body) is REFUTED. Agreement
//! on BOTH directions is what makes the driver-vs-syn parity a real witness
//! rather than a vacuous "everything passes".
//!
//! `scripts/driver-real-macro-parity.sh` drives this file through both paths and
//! asserts driver == syn per function (and that the driver never proves more
//! than syn). Under the default `cargo`/`targo` build the contract macros expand
//! to ordinary runtime `assert!`s, so the crate just compiles as a normal leaf.

/// VERIFIES: `requires(x < 100)` guards the `x + 1` against `u32` overflow, and
/// the returned value `x + 1` is strictly greater than `x`.
#[trust_vc::contract(
    requires(x < 100),
    ensures(ret > x),
    returns(ret),
)]
pub fn inc(x: u32) -> u32 {
    x + 1
}

/// REFUTED: the body returns `x + 1`, but the postcondition claims `x + 2`, so
/// the postcondition is false. This proves the driver lowered the REAL body
/// relation (not a vacuous constant) — it must disagree with the post exactly
/// where syn does.
#[trust_vc::contract(
    requires(x < 100),
    ensures(ret == x + 2),
    returns(ret),
)]
pub fn inc_bad(x: u32) -> u32 {
    x + 1
}

/// VERIFIES: a second, distinct in-fragment relation (`2 * x`) with a matching
/// exact postcondition, so the witness compares more than one passing function.
#[trust_vc::contract(
    requires(x < 100),
    ensures(ret == x + x),
    returns(ret),
)]
pub fn double(x: u32) -> u32 {
    x + x
}
