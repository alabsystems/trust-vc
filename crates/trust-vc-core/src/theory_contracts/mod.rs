// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Contracts for ay's theory solvers (EUF, BV, LRA, NIA).
//!
//! This module provides trait-based contract abstractions for ay-dpll's
//! individual theory solvers. Each theory's contract captures the mathematical
//! invariants that a correct theory solver implementation must satisfy.
//!
//! The contracts follow the same pattern as [`ay_contracts`](super::ay_contracts):
//! we define trait abstractions that capture the *contract shape* — the logical
//! relationship between inputs and outputs — and verify those contracts hold
//! for reference implementations via executable specification validators.
//!
//! # Theory Contracts
//!
//! 1. **[`ContractEuf`]** — Equality with Uninterpreted Functions (congruence
//!    closure completeness, transitivity, congruence).
//!
//! 2. **[`ContractBv`]** — Bitvector theory (width-bounded results, modular
//!    arithmetic, shift semantics, sign extension).
//!
//! 3. **[`ContractLra`]** — Linear Real Arithmetic (feasibility checking,
//!    Farkas certificates for infeasibility, bound tightening).
//!
//! 4. **[`ContractNia`]** — Nonlinear Integer Arithmetic (model correctness,
//!    cross-multiplication bounds, interval arithmetic).
//!
//! Historical source snapshot: ay-dpll rev 288ef6dd,
//! designs/2026-03-28-self-verifying-solver.md. Current TrustVc ay pin is the
//! workspace dependency revision in Cargo.toml.
//! Reference: ay_contracts.rs (DPLL contracts pattern)

// Items in this module are the contract API surface for ay theory self-verification.
// No production consumers exist yet — tests are the primary exerciser.
#![allow(dead_code)]

mod bv;
mod euf;
mod lra;
mod nia;
#[cfg(test)]
mod tests;

#[allow(unused_imports)]
pub(crate) use bv::*;
#[allow(unused_imports)]
pub(crate) use euf::*;
#[allow(unused_imports)]
pub(crate) use lra::*;
#[allow(unused_imports)]
pub(crate) use nia::*;
