// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for invariant open/close protocol encoding (#2427 Slice 4).
//!
//! Validates:
//! - InvariantOpen predicate assumed for unconstrained inner variable
//! - InvariantClose predicate assertion succeeds when body preserves invariant
//! - InvariantClose assertion fails when body violates invariant
//! - Mixed obligations: regular assumes + invariant open/close + regular asserts

mod combined;
mod mask;
mod mask_namespace;
mod protocol;

use std::collections::{HashMap, HashSet};

use super::*;
use crate::ir::{ArithOp, CompareOp, LogicOp, TrustVcExpr, TrustVcType};
use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};
use crate::vc::{InvariantMask, ObligationKind, VariableDecl, VerificationMode};

fn i32_type() -> TrustVcType {
    TrustVcType::Int { width: 32 }
}

/// Build a PreparedVerificationContext with the given variables and obligations.
fn build_invariant_context(
    vars: Vec<VariableDecl>,
    obligations: Vec<PreparedObligation>,
) -> PreparedVerificationContext {
    PreparedVerificationContext {
        obligations,
        variables: vars,
        function_context: None,
        trait_decls: vec![],
        trait_impl_decls: vec![],
        verification_mode: VerificationMode::BodyLevel,
        overflow_behavior: crate::vc::OverflowBehavior::Allow,
        div0_behavior: crate::vc::Div0Behavior::default(),
        bitshift_behavior: crate::vc::BitshiftBehavior::default(),
        broadcast_use_groups: HashSet::new(),
        assert_by_scopes: HashMap::new(),
        forall_bound_vars: HashMap::new(),
        loop_guards: HashMap::new(),
        loop_modified_vars: HashMap::new(),
        has_collection_context: false,
        revealed_fns: HashSet::new(),
        helper_function_contexts: Vec::new(),
        struct_types: vec![],
        type_invariants: HashMap::new(),
        invariant_mask: InvariantMask::default(),
        tracked_params: HashSet::new(),
        rlimit_ms: None,
        demand_inline: crate::vc::DemandInlineConfig::new(),
        counterexample_var_meta: HashMap::new(),
        ..Default::default()
    }
}

/// Helper: create a predicate expression `inner >= 0 && inner <= limit`.
fn bounded_predicate(var_name: &str, limit: i128) -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(TrustVcExpr::Var {
                name: var_name.to_string(),
                ty: i32_type(),
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: i32_type(),
            }),
        }),
        right: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Le,
            left: Box::new(TrustVcExpr::Var {
                name: var_name.to_string(),
                ty: i32_type(),
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: limit,
                ty: i32_type(),
            }),
        }),
    }
}

/// Helper: build an invariant context with a specific mask.
fn build_masked_context(
    vars: Vec<VariableDecl>,
    obligations: Vec<PreparedObligation>,
    mask: InvariantMask,
) -> PreparedVerificationContext {
    PreparedVerificationContext {
        obligations,
        variables: vars,
        function_context: None,
        trait_decls: vec![],
        trait_impl_decls: vec![],
        verification_mode: VerificationMode::BodyLevel,
        overflow_behavior: crate::vc::OverflowBehavior::Allow,
        div0_behavior: crate::vc::Div0Behavior::default(),
        bitshift_behavior: crate::vc::BitshiftBehavior::default(),
        broadcast_use_groups: HashSet::new(),
        assert_by_scopes: HashMap::new(),
        forall_bound_vars: HashMap::new(),
        loop_guards: HashMap::new(),
        loop_modified_vars: HashMap::new(),
        has_collection_context: false,
        revealed_fns: HashSet::new(),
        helper_function_contexts: Vec::new(),
        struct_types: vec![],
        type_invariants: HashMap::new(),
        invariant_mask: mask,
        tracked_params: HashSet::new(),
        rlimit_ms: None,
        demand_inline: crate::vc::DemandInlineConfig::new(),
        counterexample_var_meta: HashMap::new(),
        ..Default::default()
    }
}

// expect_error is available via `use super::*` from result_oracles re-exports.
