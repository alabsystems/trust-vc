//! Shared pre/post-state frame condition helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracted from `invariants/frame_condition.rs` so both the inductive-step
//! path and the post-loop assertion path share the same logic for:
//! - declaring pre-state variables
//! - adding scalar frame equalities for unmodified variables
//! - adding collection-length equalities for unmodified collections
//! - aliasing Map domain terms to the pre-state domain term (#2384)
//!
//! Part of #2448.

use std::collections::HashSet;

use crate::encoder::AYEncoder;
use crate::error::TrustVcResult;
use crate::ir::TrustVcExpr;
use crate::vc::VariableDecl;

/// Declare a pre-state variable for every context variable.
pub(super) fn declare_pre_state_variables(
    encoder: &mut AYEncoder,
    variables: &[VariableDecl],
) -> TrustVcResult<()> {
    for var in variables {
        let pre_var = VariableDecl {
            name: format!("{}{}", var.name, super::PRE_STATE_SUFFIX),
            ty: var.ty.clone(),
            // The pre-state copy of a framed Vec is the SAME collection (length
            // unchanged across the loop), so it keeps the length bound.
            bounded_len: var.bounded_len,
        };
        encoder.declare_variable(&pre_var)?;
    }
    Ok(())
}

/// Alias post-state collection variable terms to their pre-state ay terms
/// for unmodified (framed) variables.
///
/// ay-dpll does not propagate `eq(a, b)` for Array-sorted terms to
/// `select(a, k) == select(b, k)` (#2384). When a collection variable is
/// unmodified by the loop body, making the post-state term literally the same
/// ay object as the pre-state term bypasses this limitation. All subsequent
/// element accesses (broadcasts, ground seeds, goal assertions) then reference
/// a single array, and the proof that the invariant is preserved becomes
/// trivial: the goal and the pre-state assumption reference the same terms.
///
/// Must be called AFTER `declare_pre_state_variables` and BEFORE broadcasts
/// and ground seeding so all encoding paths use the aliased term.
/// Part of #2390.
pub(super) fn alias_framed_collection_variables(
    encoder: &mut AYEncoder,
    variables: &[VariableDecl],
    modified_set: &HashSet<&str>,
) {
    for var in variables {
        if modified_set.contains(var.name.as_str()) || !var.ty.is_collection() {
            continue;
        }
        let pre_name = format!("{}{}", var.name, super::PRE_STATE_SUFFIX);

        // Alias the variable term (array constant).
        if let Some(&pre_term) = encoder.variables.get(&pre_name) {
            encoder.variables.insert(var.name.clone(), pre_term);
        }

        // Alias the length term so s.len() resolves to the same BV as s_pre.len().
        if let Some(&pre_len) = encoder.collection_lengths.get(&pre_name) {
            encoder.collection_lengths.insert(var.name.clone(), pre_len);
        }

        // Alias Map domain term (defense-in-depth: add_unmodified_frame_conditions
        // also aliases Map domains, but doing it here ensures consistency before
        // broadcasts are encoded).
        if matches!(&var.ty, crate::ir::TrustVcType::Map(_, _)) {
            let dom_name = format!("{}_dom", var.name);
            let pre_dom_name = format!("{}_dom", pre_name);
            if let Some(&pre_dom_term) = encoder.variables.get(&pre_dom_name) {
                encoder.variables.insert(dom_name, pre_dom_term);
            }
        }
    }
}

/// Add frame conditions for all unmodified variables.
///
/// For each variable NOT in `modified_set`:
/// 1. Assert `var == var__trust_vc_pre` (scalar equality).
/// 2. If the variable is a collection, assert length equality at the ay level.
/// 3. If the variable is a Map, alias the post-state domain to the pre-state
///    domain term (ay-dpll #2384 workaround).
pub(super) fn add_unmodified_frame_conditions(
    encoder: &mut AYEncoder,
    variables: &[VariableDecl],
    modified_set: &HashSet<&str>,
    eq_queue: &mut Vec<TrustVcExpr>,
    error_context: &'static str,
) -> TrustVcResult<()> {
    for var in variables {
        if modified_set.contains(var.name.as_str()) {
            continue;
        }

        // 1. Scalar frame equality: var == var__trust_vc_pre, the same value
        // (a float frame keeps a NaN; see `crate::float_identity`).
        let frame_expr = crate::float_identity::identity_equation(
            TrustVcExpr::Var {
                name: var.name.clone(),
                ty: var.ty.clone(),
            },
            TrustVcExpr::Var {
                name: format!("{}{}", var.name, super::PRE_STATE_SUFFIX),
                ty: var.ty.clone(),
            },
        );
        encoder
            .add_typed_assumption(&format!("{}_frame", var.name), &frame_expr, Some(eq_queue))
            .map_err(|err| {
                super::encoding_error(
                    error_context,
                    format!("Failed to add frame condition for {}: {}", var.name, err),
                )
            })?;

        // 2. Collection length equality at the ay term level.
        if var.ty.is_collection() {
            let pre_name = format!("{}{}", var.name, super::PRE_STATE_SUFFIX);
            let cur_len = encoder.collection_lengths.get(&var.name);
            let pre_len = encoder.collection_lengths.get(&pre_name);
            if let (Some(&len_term), Some(&pre_len_term)) = (cur_len, pre_len) {
                let eq = encoder.solver.try_eq(len_term, pre_len_term).map_err(|e| {
                    super::encoding_error(
                        error_context,
                        format!(
                            "Failed to encode collection frame condition for {}: {}",
                            var.name, e
                        ),
                    )
                })?;
                encoder.solver.try_assert_term(eq).map_err(|e| {
                    super::encoding_error(
                        error_context,
                        format!(
                            "Failed to assert collection frame condition for {}: {}",
                            var.name, e
                        ),
                    )
                })?;
            } else {
                tracing::warn!(
                    var = %var.name,
                    has_current = cur_len.is_some(),
                    has_pre = pre_len.is_some(),
                    "collection length frame condition dropped: missing length term(s)"
                );
            }
        }

        // 3. Map domain alias (#2384 workaround).
        if let crate::ir::TrustVcType::Map(_, _) = &var.ty {
            alias_map_domain_to_pre_state(
                encoder,
                &var.name,
                &format!("{}{}", var.name, super::PRE_STATE_SUFFIX),
            );
        }
    }
    Ok(())
}

/// Alias the post-state Map domain variable to the pre-state domain term.
///
/// ay-dpll does not propagate `eq(a, b)` for Array-sorted terms to
/// `select(a, k) == select(b, k)` (#2384). Asserting `dom == pre_dom` is
/// therefore ineffective. The workaround makes the post-state domain *be*
/// the pre-state term so every subsequent `contains_key(k)` reads `pre_dom`
/// directly.
pub(super) fn alias_map_domain_to_pre_state(
    encoder: &mut AYEncoder,
    var_name: &str,
    pre_var_name: &str,
) {
    let dom_name = format!("{}_dom", var_name);
    let pre_dom_name = format!("{}_dom", pre_var_name);
    if let Some(&pre_dom_term) = encoder.variables.get(&pre_dom_name) {
        encoder.variables.insert(dom_name, pre_dom_term);
    } else {
        tracing::warn!(
            var = %var_name,
            pre_var = %pre_var_name,
            "map domain alias skipped: pre-state domain term not found"
        );
    }
}
