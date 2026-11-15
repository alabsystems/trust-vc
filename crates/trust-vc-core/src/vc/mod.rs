//! Verification condition generation for trust_vc.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module provides types and utilities for generating ay verification
//! conditions from Rust proof functions.
//!
//! # Architecture
//!
//! ```text
//! Proof Function AST
//!        |
//!        v
//!    VC Generator (this module)
//!        |
//!        v
//! VerificationContext data
//!        |
//!        v
//!   vc::verify boundary
//!        |
//!        v
//!    AYEncoder (encoder module)
//!        |
//!        v
//!    SMT Solving (ay-dpll)
//! ```
//!
//! # Usage
//!
//! See `crates/trust_vc/tests/` for end-to-end usage patterns. The primary
//! verification path uses typed `TrustVcExpr` IR; the string API
//! (`declare_var`/`add_assert`) remains available for backward compatibility.

mod context;
mod obligation;
mod verify;

pub use context::{
    BitshiftBehavior, DemandInlineConfig, Div0Behavior, FunctionContext, OverflowBehavior,
    VariableDecl, VerificationContext, VerificationMode,
};
pub(crate) use context::{CollectionOrigin, SelfReceiverKind};
pub(crate) use obligation::{
    is_closure_scoped_obligation_name, BroadcastGuardClause, CLOSURE_SCOPED_OBLIGATION_PREFIX,
};
pub use obligation::{
    ConditionOrigin, InvariantMask, ObligationKind, ProofObligation, ProofStepMeta, SolverMode,
    TypedProofObligation,
};

#[cfg(test)]
mod tests;
