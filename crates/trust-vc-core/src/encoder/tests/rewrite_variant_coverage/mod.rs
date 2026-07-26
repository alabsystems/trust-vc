//! Proof coverage tests for rename_vars TrustVcExpr variant handling.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These tests cover the TrustVcExpr variants in `rename_vars` that had
//! zero test coverage, identified by P1-483 proof_coverage audit.
//! Soundness-critical: CollectionOp and Index `receiver_name` must be
//! renamed during pre-state substitution for inductive step correctness.
//!
//! Original monolith (668 lines, 17 tests) split for maintainability (#2145).

use crate::encoder::verification::rewrite::replace_vars_with_pre_typed;
use crate::ir::{
    ArithOp, CollectionOp, CompareOp, MatchArm, MatchPattern, QuantifierKind, SpecialArithOp,
    TrustVcExpr, TrustVcType, WrappingMode,
};
use crate::vc::VariableDecl;

// Re-export shared test helpers so sub-modules get them via `use super::*`.
pub(super) use crate::encoder::tests::{i32_ty, int_lit, make_vars, var};

mod collection_and_index;
mod expression_variants;

pub(super) fn seq_i32_ty() -> TrustVcType {
    TrustVcType::Seq(Box::new(i32_ty()))
}
