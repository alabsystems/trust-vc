//! Rewriting helpers for pre-state variable substitution.
//!
//! Provides both string-based (`replace_vars_with_pre`, used by invariant
//! inductive step) and typed (`replace_vars_with_pre_typed`) substitution.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;

use crate::ir::TrustVcExpr;
use crate::vc::VariableDecl;

use super::PRE_STATE_SUFFIX;

/// Replaces variable names in a condition string with their pre-state suffixed versions.
///
/// Uses word-boundary-aware replacement: only replaces when the variable name
/// appears as a complete identifier (not as part of a longer name).
/// Uses `PRE_STATE_SUFFIX` (`__trust_vc_pre`) to avoid collision with user
/// variable names (#1728).
///
/// Superseded by `replace_vars_with_pre_typed` in production; retained for
/// test coverage of the string-based rewrite logic.
#[cfg(test)]
pub(in crate::encoder) fn replace_vars_with_pre(
    condition: &str,
    variables: &[VariableDecl],
) -> String {
    let mut result = condition.to_string();
    // Sort variables by name length (longest first) to avoid partial replacements
    // e.g., replace "idx" before "i" so "idx" doesn't become "i__trust_vc_prex"
    let mut sorted_vars: Vec<&VariableDecl> = variables.iter().collect();
    sorted_vars.sort_by_key(|var| std::cmp::Reverse(var.name.len()));

    for var in sorted_vars {
        let replacement = format!("{}{}", var.name, PRE_STATE_SUFFIX);
        result = replace_whole_word(&result, &var.name, &replacement);
    }
    result
}

/// Replaces all occurrences of `word` in `text` that appear as complete identifiers.
///
/// A word boundary is defined as a position where the adjacent character is not
/// alphanumeric or underscore (Rust identifier characters).
///
/// Uses `char_indices()` for correct UTF-8 handling (#1655).
#[cfg(test)]
pub(in crate::encoder) fn replace_whole_word(text: &str, word: &str, replacement: &str) -> String {
    if word.is_empty() {
        return text.to_string();
    }

    let mut result = String::with_capacity(text.len() + replacement.len());
    let mut i = 0;

    while i < text.len() {
        if text[i..].starts_with(word) {
            // Check left boundary: char before match must not be an identifier char
            let left_ok = i == 0 || !text[..i].ends_with(is_identifier_char);
            // Check right boundary: char after match must not be an identifier char
            let right_pos = i + word.len();
            let right_ok =
                right_pos >= text.len() || !text[right_pos..].starts_with(is_identifier_char);

            if left_ok && right_ok {
                result.push_str(replacement);
                i += word.len();
                continue;
            }
        }
        // Advance by one character (handles multi-byte UTF-8 correctly)
        let ch = text[i..].chars().next().expect("invariant: i < text.len()");
        result.push(ch);
        i += ch.len_utf8();
    }

    result
}

#[cfg(test)]
fn is_identifier_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Extracts target variable names as a borrowed set for batch rewriting.
pub(in crate::encoder) fn collect_pre_state_target_names(
    variables: &[VariableDecl],
) -> HashSet<&str> {
    variables.iter().map(|v| v.name.as_str()).collect()
}

#[cfg(test)]
pub(in crate::encoder) fn replace_vars_with_pre_typed(
    expr: &TrustVcExpr,
    variables: &[VariableDecl],
) -> TrustVcExpr {
    let targets = collect_pre_state_target_names(variables);
    replace_vars_with_pre_typed_with_targets(expr, &targets)
}

/// Typed pre-state rewrite using a caller-provided target set.
///
/// Callers that rewrite multiple expressions against the same variable list can
/// precompute the target names once and reuse them across the whole batch.
/// Part of #1786. Migrated to scope-aware folder as part of #2641.
pub(in crate::encoder) fn replace_vars_with_pre_typed_with_targets(
    expr: &TrustVcExpr,
    targets: &HashSet<&str>,
) -> TrustVcExpr {
    use crate::ir_expr_traversal::{fold_expr_scoped_children, ScopeAwareTrustVcExprFolder};

    struct Renamer<'a> {
        targets: &'a HashSet<&'a str>,
    }
    impl ScopeAwareTrustVcExprFolder for Renamer<'_> {
        fn fold_expr_scoped(&mut self, expr: TrustVcExpr, bound: &HashSet<&str>) -> TrustVcExpr {
            let should_rename =
                |name: &str| -> bool { self.targets.contains(name) && !bound.contains(name) };
            match expr {
                TrustVcExpr::Var { ref name, .. } if should_rename(name) => {
                    let TrustVcExpr::Var { name, ty } = expr else {
                        unreachable!()
                    };
                    TrustVcExpr::Var {
                        name: format!("{}{}", name, PRE_STATE_SUFFIX),
                        ty,
                    }
                }
                other => {
                    let mut folded = fold_expr_scoped_children(self, other, bound);
                    match &mut folded {
                        TrustVcExpr::CollectionOp {
                            receiver_name: Some(n),
                            ..
                        } if should_rename(n) => {
                            *n = format!("{}{}", n, PRE_STATE_SUFFIX);
                        }
                        TrustVcExpr::Index {
                            receiver_name: Some(n),
                            ..
                        } if should_rename(n) => {
                            *n = format!("{}{}", n, PRE_STATE_SUFFIX);
                        }
                        TrustVcExpr::ReadPlace { place, .. } if should_rename(&place.root_name) => {
                            place.root_name = format!("{}{}", place.root_name, PRE_STATE_SUFFIX);
                        }
                        TrustVcExpr::PlaceDisjoint { left, right } => {
                            for place in [left, right] {
                                if should_rename(&place.root_name) {
                                    place.root_name =
                                        format!("{}{}", place.root_name, PRE_STATE_SUFFIX);
                                }
                            }
                        }
                        _ => {}
                    }
                    folded
                }
            }
        }
    }

    let mut renamer = Renamer { targets };
    renamer.fold_expr_scoped(expr.clone(), &HashSet::new())
}
