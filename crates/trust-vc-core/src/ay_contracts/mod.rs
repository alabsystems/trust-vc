// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compilable extern_spec-style contracts for ay-dpll functions.
//!
//! This module provides trait-based abstractions that capture the pre/post
//! conditions of key ay-dpll functions documented in [`ay_specs`](super::ay_specs).
//! The traits express the contract shapes WITHOUT importing ay internal types
//! directly, enabling verification of the contract semantics within trust-vc-core.
//!
//! # Design
//!
//! ay-dpll's `TheoryExtension` is an internal type (not part of the public API),
//! so trust-vc-core cannot directly annotate it with `extern_spec!`. Instead, we
//! define trait abstractions that capture the *contract shape* — the logical
//! relationship between inputs and outputs — and verify those contracts hold
//! for concrete implementations.
//!
//! Four contracts are implemented:
//!
//! 1. **`term_to_literal`** via [`TheoryAtomRegistry`] — the simplest ay-dpll
//!    function with a pure lookup contract.
//!
//! 2. **`as_str` for theory kinds** via [`TheoryKindLabel`] — a trivial
//!    exhaustive mapping contract matching `AYTheoryKind::as_str` from the
//!    trust-vc-kernel bridge.
//!
//! Historical source snapshot: ay-dpll rev 288ef6dd, ay_specs.rs stubs #2,
//! and trust-vc-kernel bridge. Current TrustVc ay pin is the workspace dependency
//! revision in Cargo.toml.
//! Reference: designs/2026-03-28-self-verifying-solver.md

// Items in this module are the contract API surface for ay self-verification.
// No production consumers exist yet — tests are the primary exerciser.
#![allow(dead_code)]

mod atom_registry;
mod bcp_decision;
mod cdcl;
mod restart_policy;
#[cfg(test)]
mod tests;

#[allow(unused_imports)]
pub(crate) use atom_registry::*;
#[allow(unused_imports)]
pub(crate) use bcp_decision::*;
#[allow(unused_imports)]
pub(crate) use cdcl::*;
#[allow(unused_imports)]
pub(crate) use restart_policy::*;
