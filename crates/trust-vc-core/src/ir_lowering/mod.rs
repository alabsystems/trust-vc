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
mod typing_check;
mod untyped_site;
pub(crate) use untyped_site::{
    collapse_undetermined_forms, constant_form_panicking_type, holds_undetermined_form,
    pin_untyped_at_i32,
};

#[cfg(test)]
pub(crate) use atoms::trust_vc_type_from_syn_type;
#[cfg(test)]
pub(crate) use atoms::typed_int_literal;
pub(crate) use atoms::{
    expr_path_to_string, path_to_string, trust_vc_type_from_syn_type_with_env, type_from_int_suffix,
};
pub(crate) use dispatch::substitute_type_params;
pub(crate) use dispatch::{UNWRAP_ERR_REQUIRES_MARKER, UNWRAP_REQUIRES_MARKER};
pub(crate) use entry::lower_syn_expr;
pub(crate) use entry::{lower_syn_expr_with_depth, next_lowering_depth};
#[cfg(test)]
pub(crate) use env::ConstructorMeta;
pub(crate) use env::{
    MethodMeta, TypeEnv, BIND_LIKE_MARKER, COLLECTION_CONSTRUCTOR_PREFIX, LET_BOUND_MARKER,
    SELF_TYPED_MARKER, SEQ_FROM_FN_BUILTIN, SET_NEW_BUILTIN, SLOT_TYPED_MARKER,
    UNTYPED_BINDING_MARKER, UNTYPED_SITE_MARKER,
};
pub use error::LoweringError;
pub(crate) use error::UNMODELED_SHADOW_INFIX;
pub(crate) use types::{
    arith_node_type, binary_operand_types, bind_call_argument, derive_arms_int_type,
    derive_binary_int_type, derived_node_type, fixed_width_type_within, infer_expr_type,
    int_binding, is_fixed_width_int, is_integer_type, is_untyped_literal, is_untyped_operation,
    pin_substituted_value, slot_type_like, type_holds_integer, untyped_form_is_conditional,
    untyped_literal_at_peer, untyped_literal_fits, untyped_literal_value,
    untyped_operation_value_all_types_agree, witness_fixes_no_type, IntBinding,
};
pub(crate) use typing_check::{
    integer_positions_agree, type_holds_an_integer, validate_ir_typing, TypingScope,
};

/// Synthetic call inserted only into source-catalog body axioms whose declared
/// result is mathematical `int`. Lowering accepts it only with the matching
/// crate-private obligation capability; authored source cannot opt itself in.
pub(crate) const SOURCE_CATALOG_MATH_INT_MARKER: &str = "__trust_vc_math_int_expr";
