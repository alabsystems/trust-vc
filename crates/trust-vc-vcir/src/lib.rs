//! VcIR: the program IR trust-vc verifies.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! VcIR is the single input format of trust-vc's program-level verifier.
//! A producer builds a [`VcCrate`]:
//!
//! * the rustc reader (`trust-vc-rustc`) builds it from HIR and type-check
//!   results of Verus code, matching Verus markers by definition identity;
//! * a trust-ir adapter can later build the subset native Trust clauses need.
//!
//! [`check_crate`] decides whether a crate is well formed; the VC generator
//! ([`vcgen::generate`]) turns each function of an accepted crate into one
//! solver query per checked site. With the `solve` feature, [`solve`]
//! answers those queries with trust-vc-core.
//!
//! # Shape
//!
//! * Items are keyed by [`FnId`] / [`AdtId`], content hashes of definition
//!   paths, never by name.
//! * A function has a mode ([`Mode`]), a table of locals (parameters, the
//!   return value, lets, temporaries, spec-bound names), contract clauses and
//!   a body: nothing, a spec expression, or statements.
//! * Statements ([`StmtKind`]) are structured control flow over places,
//!   loops included ([`Loop`]; `break` and `continue` name their loop by
//!   [`LoopId`]). Every effect is a statement; expressions ([`ExprKind`])
//!   are pure.
//! * Every check the VC generator performs has a [`SiteId`]: assertions,
//!   call preconditions, return postconditions, loop invariants and
//!   measures, and exec arithmetic.
//! * Positions are opaque [`SpanId`]s that only the producer interprets.
//!
//! # Semantics the producer relies on
//!
//! * Integers are mathematical values; a machine type restricts the range
//!   (Verus's reading). Spec arithmetic is exact and typed `int`/`nat`; exec
//!   arithmetic is checked at a site (see [`crate::expr`]).
//! * In a postcondition, reading a parameter means its value on entry, as in
//!   Verus (a `mut` parameter assigned in the body is still read at entry).
//!   The current value behind a `&mut` parameter is read with a `Deref`
//!   projection and its entry value with [`ExprKind::Old`].
//! * An assertion is checked at its site and assumed afterwards.
//!
//! The format is versioned by [`SCHEMA`]; a change that alters the meaning
//! of an existing node bumps it.

pub mod bitvector;
mod expr;
mod ids;
mod instance_semantics;
mod item;
pub mod pretty;
#[cfg(feature = "solve")]
pub mod solve;
mod stmt;
pub mod triggers;
mod ty;
pub mod vcgen;
pub mod wf;

pub use expr::{
    BinOp, CastKind, Expr, ExprKind, IntLit, IntegerConstant, Lit, Place, Projection, QuantKind,
    UnOp,
};
pub use ids::{AdtId, DefHash, FnId, LocalId, LoopId, SiteId, SpanId};
pub use item::{
    AdtDecl, AdtKind, Body, Clause, ConstMode, DefOrder, FieldDecl, FnAttrs, FnDecl, FnKind,
    FnRole, GenericInstance, LocalDecl, LocalKind, Mode, RecGroup, Rlimit, VariantDecl, VcCrate,
};
pub use stmt::{
    Block, ClauseAttrs, InvariantKind, Loop, LoopCond, LoopInvariant, LoopSites, Stmt, StmtKind,
};
pub use ty::{IntRange, Ty, MACHINE_WIDTHS};
pub use wf::{check_crate, check_crate_for_diagnostics, DiagnosticWf, WfClass, WfError};

/// Schema name of this format, as trust-ir's `ProofFormula.schema` would
/// reference it.
pub const SCHEMA: &str = "trust-vc.vcir@9";
