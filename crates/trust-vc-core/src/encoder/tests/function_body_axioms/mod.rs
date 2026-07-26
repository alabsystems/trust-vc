//! Tests for spec-function body reasoning via BroadcastAssume obligations.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Original monolith (730 lines, 20 tests) split for maintainability (#2145).

use super::*;
use crate::vc::{FunctionContext, ProofObligation};

mod basic_axioms;
mod complex_and_broadcast;
mod fixpoint;
mod non_convergence;
mod recursive_integration;

fn register_spec_function(
    ctx: &mut VerificationContext,
    name: &str,
    params: &[(&str, &str)],
    return_type: &str,
) {
    ctx.set_function_context(FunctionContext {
        name: name.to_string(),
        params: params
            .iter()
            .map(|(param, ty)| {
                (
                    (*param).to_string(),
                    crate::ir::TrustVcType::from_str(ty).unwrap(),
                )
            })
            .collect(),
        return_type: crate::ir::TrustVcType::from_str(return_type).unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });
}

fn add_body_axiom(
    ctx: &mut VerificationContext,
    name: &str,
    params: &[(&str, &str)],
    condition: &str,
    trigger: &str,
) {
    for (param, ty) in params {
        ctx.declare_var_typed(param, crate::ir::TrustVcType::parse_or_opaque(ty));
    }

    let bound_vars: Vec<String> = params.iter().map(|(param, _)| param.to_string()).collect();

    ctx.obligations.push(
        ProofObligation::broadcast_assume(format!("__body_axiom_{name}"), condition)
            .with_bound_vars(bound_vars)
            .with_trigger_patterns(vec![vec![trigger.to_string()]]),
    );
}
