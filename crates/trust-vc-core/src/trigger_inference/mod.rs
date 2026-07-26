//! Automatic trigger inference for quantifiers.
//!
//! When a quantifier lacks explicit trigger annotations, this module infers
//! trigger patterns from the quantifier body. Follows Verus's approach:
//! collect eligible sub-expressions, check coverage of all bound variables,
//! score candidates, and select the best trigger group(s).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #2461.

mod candidate;
mod scope;
mod selection;

#[cfg(test)]
mod tests_api;
#[cfg(test)]
mod tests_shadowing;
#[cfg(test)]
mod tests_support;

use std::collections::HashSet;

use crate::ir_expr::TrustVcExpr;

/// Controls whether trigger inference returns only the best single trigger group
/// (conservative) or all valid trigger groups (aggressive).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TriggerInferenceMode {
    /// Best single trigger group only (default, matches Verus's default).
    #[default]
    Conservative,
    /// All valid trigger groups.
    Aggressive,
}

/// Infer triggers with an explicit mode selector.
pub fn infer_triggers_with_mode(
    bound_vars: &[(String, crate::ir::TrustVcType)],
    body: &TrustVcExpr,
    mode: TriggerInferenceMode,
) -> Vec<Vec<TrustVcExpr>> {
    match mode {
        TriggerInferenceMode::Conservative => infer_triggers(bound_vars, body),
        TriggerInferenceMode::Aggressive => infer_triggers_aggressive(bound_vars, body),
    }
}

/// Infer triggers from names with an explicit mode selector.
pub fn infer_triggers_from_names_with_mode(
    bound_names: &[&str],
    body: &TrustVcExpr,
    mode: TriggerInferenceMode,
) -> Vec<Vec<TrustVcExpr>> {
    match mode {
        TriggerInferenceMode::Conservative => infer_triggers_from_names(bound_names, body),
        TriggerInferenceMode::Aggressive => infer_triggers_aggressive_from_names(bound_names, body),
    }
}

/// Infer trigger patterns from a quantifier body.
///
/// Returns a list of trigger groups. Each group is a `Vec<TrustVcExpr>` whose
/// union covers all bound variables. Returns empty if no valid triggers found
/// (the quantifier proceeds trigger-less, same as today).
///
/// `bound_vars` are `(name, type)` pairs from the quantifier declaration.
pub fn infer_triggers(
    bound_vars: &[(String, crate::ir::TrustVcType)],
    body: &TrustVcExpr,
) -> Vec<Vec<TrustVcExpr>> {
    let names: Vec<&str> = bound_vars.iter().map(|(n, _)| n.as_str()).collect();
    infer_triggers_from_names(&names, body)
}

/// Infer triggers in aggressive mode (all valid trigger groups).
pub fn infer_triggers_aggressive(
    bound_vars: &[(String, crate::ir::TrustVcType)],
    body: &TrustVcExpr,
) -> Vec<Vec<TrustVcExpr>> {
    let names: Vec<&str> = bound_vars.iter().map(|(n, _)| n.as_str()).collect();
    infer_triggers_aggressive_from_names(&names, body)
}

/// Infer triggers using only bound variable names (no type info needed).
/// Used by the broadcast path where only names are available.
pub fn infer_triggers_from_names(
    bound_names: &[&str],
    body: &TrustVcExpr,
) -> Vec<Vec<TrustVcExpr>> {
    let bound_set: HashSet<&str> = bound_names.iter().copied().collect();
    if bound_set.is_empty() {
        return Vec::new();
    }

    let candidates = candidate::collect_candidates(body, &bound_set);
    if candidates.is_empty() {
        return Vec::new();
    }

    selection::select_conservative(&candidates, &bound_set)
}

/// Aggressive mode using only bound variable names.
pub fn infer_triggers_aggressive_from_names(
    bound_names: &[&str],
    body: &TrustVcExpr,
) -> Vec<Vec<TrustVcExpr>> {
    let bound_set: HashSet<&str> = bound_names.iter().copied().collect();
    if bound_set.is_empty() {
        return Vec::new();
    }

    let candidates = candidate::collect_candidates(body, &bound_set);
    if candidates.is_empty() {
        return Vec::new();
    }

    selection::select_aggressive(&candidates, &bound_set)
}
