//! Lowers `syn::Expr` AST into typed `TrustVcExpr` IR.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module provides `lower_syn_expr()` which walks a `syn::Expr` tree
//! and produces a `TrustVcExpr`, returning structured errors for unsupported
//! variants. No silent drops — every syn::Expr arm is handled explicitly.
//!
//! Part of #1550 Phase 3 (#1864).

mod arrays;
mod atoms;
mod control_flow;
pub(crate) mod diagnostic_parity;
mod dispatch;
mod entry;
mod env;
mod error;
mod match_lowering;
pub(crate) mod operators;
pub(crate) mod place;
#[cfg(test)]
mod tests_connective_lowering;
#[cfg(test)]
mod tests_control_flow;
#[cfg(test)]
mod tests_depth_limit;
#[cfg(test)]
mod tests_dispatch;
#[cfg(test)]
mod tests_extensional_macros;
#[cfg(test)]
mod tests_let_inference;
#[cfg(test)]
mod tests_literals_vars;
#[cfg(test)]
mod tests_operators;
#[cfg(test)]
mod tests_round_trip;
#[cfg(test)]
mod tests_support;
mod types;

#[cfg(test)]
pub(crate) use atoms::trust_vc_type_from_syn_type;
pub(crate) use atoms::{
    expr_path_to_string, path_to_string, trust_vc_type_from_syn_type_with_env, type_from_int_suffix,
};
pub(crate) use dispatch::substitute_type_params;
pub(crate) use entry::lower_syn_expr;
pub(crate) use entry::{lower_syn_expr_with_depth, next_lowering_depth};
#[cfg(test)]
pub(crate) use env::ConstructorMeta;
pub(crate) use env::{
    MethodMeta, TypeEnv, COLLECTION_CONSTRUCTOR_PREFIX, SEQ_FROM_FN_BUILTIN, SET_NEW_BUILTIN,
};
pub use error::LoweringError;
pub(crate) use types::infer_expr_type;

/// Synthetic call inserted only into source-catalog body axioms whose declared
/// result is mathematical `int`. Lowering accepts it only with the matching
/// crate-private obligation capability; authored source cannot opt itself in.
pub(crate) const SOURCE_CATALOG_MATH_INT_MARKER: &str = "__trust_vc_math_int_expr";
