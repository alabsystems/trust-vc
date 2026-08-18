//! Single-assertion verification — fresh-encoder-per-assertion strategy.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # Module Structure
//!
//! - `timeout`: Solver-thread capacity and timeout control
//! - `panic`: Panic classification and ay panic boundary handling
//! - `assertion`: Single-assertion verification orchestration and retry cascade
//! - `assertion_timeout`: Solver-thread timeout handoff (deduplicated)
//! - `assumption`: Typed assumption encoding and equality reconciliation
//! - `broadcast`: Quantified broadcast encoding with trigger handling
//! - `overflow`: Overflow predicate checking (shared by assertion and invariants)
//! - `confirmation`: Shared confirmation wrapper + retry for collection assertions
//! - `ground_seeding`: Collection ground-term seeding for quantified arrays
//! - `invariants`: Inductive-step verification logic for loop invariants
//! - `rewrite`: String rewriting helpers for pre-state variable substitution
//! - `solve`: Panic-safe solve envelope and assertion-result decoding
//! - `split`: Assertion splitting for localized error diagnostics
//! - `test_hooks`: Deterministic test-only hooks for assertion-path regressions

use crate::error::TrustVcError;
use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};

pub(super) mod assertion;
pub(super) mod assertion_bv_reuse;
pub(super) mod assertion_timeout;
pub(super) mod assumption;
pub(in crate::encoder) mod body_support;
pub(super) mod broadcast;
pub(in crate::encoder) mod broadcast_model_revalidation;
pub(in crate::encoder) mod cache;
pub(super) mod compute;
pub(super) mod confirmation;
pub(super) mod frame_state;
pub(super) mod ground_seeding;
pub(super) mod invariants;
pub(in crate::encoder) mod model_render;
pub(super) mod nonlinear_real;
pub(crate) mod outcome;
pub(super) mod overflow;
pub(super) mod overflow_logic;
pub(super) mod panic;
pub(in crate::encoder) mod pruning;
pub(super) mod rewrite;
pub(super) mod setup;
pub(super) mod solve;
pub(in crate::encoder) mod split;
pub(in crate::encoder) mod test_gate;
pub(in crate::encoder) mod test_hooks;
#[cfg(test)]
mod tests;
pub(super) mod timeout;
pub(super) mod trait_conformance;
pub(super) mod typed;
pub(super) mod typed_assertions;
pub(crate) mod unknown_category;
pub(super) mod vacuous;

/// Suffix for pre-state variable names in inductive step verification.
///
/// Uses a double-underscore prefix to avoid collision with user variable names.
/// Previously `_pre`, which collided if a user declared a variable like `x_pre`
/// — the pre-state of `x` and the user's `x_pre` would share the same ay symbol.
/// Fixes #1728.
pub(super) const PRE_STATE_SUFFIX: &str = "__trust_vc_pre";

/// Groups the obligation slices that travel together through assertion
/// verification, encoder setup, and retry paths.
#[derive(Clone, Copy)]
pub(in crate::encoder) struct VerificationSlices<'a> {
    pub ctx: &'a PreparedVerificationContext,
    pub assumptions: &'a [&'a PreparedObligation],
    pub broadcast_assumptions: &'a [&'a PreparedObligation],
    pub verified_invariants: &'a [&'a PreparedObligation],
    pub verified_assert_by: &'a [&'a PreparedObligation],
    pub scoped_assumptions: &'a [&'a PreparedObligation],
}

impl<'a> VerificationSlices<'a> {
    pub(in crate::encoder) fn new(
        ctx: &'a PreparedVerificationContext,
        assumptions: &'a [&'a PreparedObligation],
        broadcast_assumptions: &'a [&'a PreparedObligation],
        verified_invariants: &'a [&'a PreparedObligation],
        verified_assert_by: &'a [&'a PreparedObligation],
        scoped_assumptions: &'a [&'a PreparedObligation],
    ) -> Self {
        Self {
            ctx,
            assumptions,
            broadcast_assumptions,
            verified_invariants,
            verified_assert_by,
            scoped_assumptions,
        }
    }
}

pub(super) fn encoding_error(context: &'static str, detail: impl Into<String>) -> TrustVcError {
    TrustVcError::Encoding {
        context,
        detail: detail.into(),
    }
}
