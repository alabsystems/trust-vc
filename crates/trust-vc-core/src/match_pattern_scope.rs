// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Canonical helpers for [`MatchPattern`] binding semantics.
//!
//! Every scope-aware traversal that enters a binding scope needs a consistent
//! way to subtract newly-bound names. Match-arm pattern bindings are the
//! original motivation, but the same helper surface also serves `let`,
//! quantifier, `choose`, and spec-closure scopes so callers don't each
//! re-implement the same subtraction logic.

use crate::ir_expr::MatchPattern;
use std::collections::HashSet;

pub(crate) const IGNORED_MATCH_BINDING_PREFIX: &str = "__trust_vc_ignored_match_binding_";

pub(crate) fn is_ignored_match_binding(name: &str) -> bool {
    name.starts_with(IGNORED_MATCH_BINDING_PREFIX)
}

/// Returns all variable names bound by a match pattern.
///
/// - `Ident(name)` binds `name`.
/// - `Constructor { bindings, .. }` binds each name in `bindings`.
/// - `Struct { fields, .. }` binds each non-wildcard field binding.
/// - `Or(pats)` unions the bindings of all alternatives (Rust guarantees
///   each alternative binds the same names, but we collect them all for
///   robustness).
/// - `Lit` and `Wildcard` bind nothing.
pub(crate) fn pattern_bound_names(pattern: &MatchPattern) -> Vec<String> {
    match pattern {
        MatchPattern::Ident(name) => vec![name.clone()],
        MatchPattern::Constructor { bindings, .. } => bindings
            .iter()
            .filter(|name| !is_ignored_match_binding(name))
            .cloned()
            .collect(),
        MatchPattern::Struct { fields, .. } => fields
            .iter()
            .filter_map(|field| field.binding.clone())
            .collect(),
        MatchPattern::Or(pats) => {
            let mut names = Vec::new();
            for p in pats {
                names.extend(pattern_bound_names(p));
            }
            names
        }
        MatchPattern::Lit(_) | MatchPattern::Wildcard => vec![],
    }
}

/// Inserts all names bound by `pattern` into `bound`.
///
/// This is the `HashSet`-oriented variant of [`pattern_bound_names`], useful
/// when callers already accumulate bound names into a set (e.g. free-variable
/// collection, rename scoping).
#[cfg(test)]
pub(crate) fn collect_pattern_bindings(pattern: &MatchPattern, bound: &mut HashSet<String>) {
    match pattern {
        MatchPattern::Ident(name) => {
            bound.insert(name.clone());
        }
        MatchPattern::Constructor { bindings, .. } => {
            for name in bindings {
                if !is_ignored_match_binding(name) {
                    bound.insert(name.clone());
                }
            }
        }
        MatchPattern::Struct { fields, .. } => {
            for field in fields {
                if let Some(binding_name) = &field.binding {
                    bound.insert(binding_name.clone());
                }
            }
        }
        MatchPattern::Or(pats) => {
            for p in pats {
                collect_pattern_bindings(p, bound);
            }
        }
        MatchPattern::Lit(_) | MatchPattern::Wildcard => {}
    }
}

/// Returns a reduced scope with pattern-bound names removed, or `None` if
/// no names overlap (avoiding allocation when shadowing doesn't occur).
///
/// Callers use the returned set for the arm body and fall back to the
/// original scope when `None` is returned.
pub(crate) fn without_pattern_bound_names<'a>(
    scope: &HashSet<&'a str>,
    pattern: &MatchPattern,
) -> Option<HashSet<&'a str>> {
    let names = pattern_bound_names(pattern);
    if names.iter().any(|n| scope.contains(n.as_str())) {
        let mut reduced = scope.clone();
        for n in &names {
            reduced.remove(n.as_str());
        }
        Some(reduced)
    } else {
        None
    }
}

/// Returns a reduced scope with one newly-bound name removed, or `None` when
/// the name does not overlap the current scope.
pub(crate) fn without_name<'a>(scope: &HashSet<&'a str>, name: &str) -> Option<HashSet<&'a str>> {
    if scope.contains(name) {
        let mut reduced = scope.clone();
        reduced.remove(name);
        Some(reduced)
    } else {
        None
    }
}

/// Returns a reduced scope with multiple newly-bound names removed, or `None`
/// when none of them overlap the current scope.
pub(crate) fn without_names<'a>(
    scope: &HashSet<&'a str>,
    names: &[&str],
) -> Option<HashSet<&'a str>> {
    if names.iter().any(|name| scope.contains(*name)) {
        let mut reduced = scope.clone();
        for name in names {
            reduced.remove(*name);
        }
        Some(reduced)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ident_pattern_binds_name() {
        let pat = MatchPattern::Ident("x".into());
        assert_eq!(pattern_bound_names(&pat), vec!["x"]);
    }

    #[test]
    fn test_constructor_pattern_binds_all_fields() {
        let pat = MatchPattern::Constructor {
            variant_name: "Some".into(),
            bindings: vec!["a".into(), "b".into()],
            has_rest: false,
        };
        assert_eq!(pattern_bound_names(&pat), vec!["a", "b"]);
    }

    #[test]
    fn test_struct_pattern_binds_only_named_fields() {
        let pat = MatchPattern::Struct {
            variant_name: "Counter".into(),
            fields: vec![
                crate::ir_expr::StructPatternField {
                    field_name: "count".into(),
                    binding: Some("c".into()),
                },
                crate::ir_expr::StructPatternField {
                    field_name: "max".into(),
                    binding: None,
                },
            ],
            has_rest: true,
        };
        assert_eq!(pattern_bound_names(&pat), vec!["c"]);
    }

    #[test]
    fn test_or_pattern_unions_all_alternatives() {
        let pat = MatchPattern::Or(vec![
            MatchPattern::Constructor {
                variant_name: "Foo".into(),
                bindings: vec!["x".into()],
                has_rest: false,
            },
            MatchPattern::Constructor {
                variant_name: "Bar".into(),
                bindings: vec!["x".into()],
                has_rest: false,
            },
        ]);
        let names = pattern_bound_names(&pat);
        // Rust guarantees same bindings — we get both for robustness
        assert_eq!(names, vec!["x", "x"]);
    }

    #[test]
    fn test_wildcard_and_lit_bind_nothing() {
        assert!(pattern_bound_names(&MatchPattern::Wildcard).is_empty());
        use crate::ir_expr::TrustVcExpr;
        let lit = MatchPattern::Lit(TrustVcExpr::IntLit {
            value: 42,
            ty: crate::ir::TrustVcType::Int { width: 32 },
        });
        assert!(pattern_bound_names(&lit).is_empty());
    }

    #[test]
    fn test_collect_pattern_bindings_into_set() {
        let pat = MatchPattern::Constructor {
            variant_name: "Pair".into(),
            bindings: vec!["a".into(), "b".into()],
            has_rest: false,
        };
        let mut bound = HashSet::new();
        collect_pattern_bindings(&pat, &mut bound);
        assert!(bound.contains("a"));
        assert!(bound.contains("b"));
        assert_eq!(bound.len(), 2);
    }

    #[test]
    fn test_collect_struct_pattern_bindings_skips_wildcards() {
        let pat = MatchPattern::Struct {
            variant_name: "Counter".into(),
            fields: vec![
                crate::ir_expr::StructPatternField {
                    field_name: "count".into(),
                    binding: Some("value".into()),
                },
                crate::ir_expr::StructPatternField {
                    field_name: "max".into(),
                    binding: None,
                },
            ],
            has_rest: true,
        };
        let mut bound = HashSet::new();
        collect_pattern_bindings(&pat, &mut bound);
        assert!(bound.contains("value"));
        assert_eq!(bound.len(), 1);
    }

    #[test]
    fn test_without_pattern_bound_names_removes_overlap() {
        let scope: HashSet<&str> = ["x", "y", "z"].into_iter().collect();
        let pat = MatchPattern::Constructor {
            variant_name: "Some".into(),
            bindings: vec!["x".into()],
            has_rest: false,
        };
        let reduced = without_pattern_bound_names(&scope, &pat).unwrap();
        assert!(!reduced.contains("x"));
        assert!(reduced.contains("y"));
        assert!(reduced.contains("z"));
    }

    #[test]
    fn test_without_pattern_bound_names_none_when_no_overlap() {
        let scope: HashSet<&str> = ["a", "b"].into_iter().collect();
        let pat = MatchPattern::Ident("x".into());
        assert!(without_pattern_bound_names(&scope, &pat).is_none());
    }

    #[test]
    fn test_nested_or_pattern_scope_removal() {
        let scope: HashSet<&str> = ["x", "y"].into_iter().collect();
        let pat = MatchPattern::Or(vec![
            MatchPattern::Ident("x".into()),
            MatchPattern::Ident("x".into()),
        ]);
        let reduced = without_pattern_bound_names(&scope, &pat).unwrap();
        assert!(!reduced.contains("x"));
        assert!(reduced.contains("y"));
    }

    #[test]
    fn test_without_name_removes_one_overlap() {
        let scope: HashSet<&str> = ["x", "y"].into_iter().collect();
        let reduced = without_name(&scope, "x").unwrap();
        assert!(!reduced.contains("x"));
        assert!(reduced.contains("y"));
    }

    #[test]
    fn test_without_name_returns_none_when_absent() {
        let scope: HashSet<&str> = ["x"].into_iter().collect();
        assert!(without_name(&scope, "y").is_none());
    }

    #[test]
    fn test_without_names_removes_all_overlaps() {
        let scope: HashSet<&str> = ["x", "y", "z"].into_iter().collect();
        let reduced = without_names(&scope, &["x", "z"]).unwrap();
        assert!(!reduced.contains("x"));
        assert!(reduced.contains("y"));
        assert!(!reduced.contains("z"));
    }

    #[test]
    fn test_without_names_returns_none_when_disjoint() {
        let scope: HashSet<&str> = ["x", "y"].into_iter().collect();
        assert!(without_names(&scope, &["a", "b"]).is_none());
    }
}
