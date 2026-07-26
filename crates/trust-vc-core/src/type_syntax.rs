//! Shared type-string parsing helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module provides generic type-string utilities that both `ir` and
//! `encoder` depend on, breaking the `ir -> encoder` dependency cycle (#2152).

use quote::ToTokens;

/// Splits a two-argument generic type string like "K, V" into ("K", "V").
///
/// Handles nested generics and tuple/group nesting correctly, e.g.
/// "Map<A, B>, C" -> ("Map<A, B>", "C") and "(usize, T), U" -> ("(usize, T)", "U").
pub(crate) fn split_generic_args(s: &str) -> Option<(&str, &str)> {
    let mut angle_depth = 0;
    let mut paren_depth = 0;
    let mut bracket_depth = 0;
    for (i, c) in s.char_indices() {
        match c {
            '<' => angle_depth += 1,
            '>' => angle_depth -= 1,
            '(' => paren_depth += 1,
            ')' => paren_depth -= 1,
            '[' => bracket_depth += 1,
            ']' => bracket_depth -= 1,
            ',' if angle_depth == 0 && paren_depth == 0 && bracket_depth == 0 => {
                return Some((&s[..i], &s[i + 1..]));
            }
            _ => {}
        }
    }
    None
}

/// Splits a comma-separated type list on top-level commas.
///
/// Nested generic, tuple, array, and brace-delimited commas are preserved
/// inside each element.
pub(crate) fn split_top_level_args(s: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut angle_depth = 0;
    let mut paren_depth = 0;
    let mut bracket_depth = 0;
    let mut brace_depth = 0;
    let mut start = 0;

    for (i, c) in s.char_indices() {
        match c {
            '<' => angle_depth += 1,
            '>' => angle_depth -= 1,
            '(' => paren_depth += 1,
            ')' => paren_depth -= 1,
            '[' => bracket_depth += 1,
            ']' => bracket_depth -= 1,
            '{' => brace_depth += 1,
            '}' => brace_depth -= 1,
            ',' if angle_depth == 0
                && paren_depth == 0
                && bracket_depth == 0
                && brace_depth == 0 =>
            {
                parts.push(s[start..i].trim());
                start = i + 1;
            }
            _ => {}
        }
    }

    let tail = s[start..].trim();
    if !tail.is_empty() {
        parts.push(tail);
    }
    parts
}

/// Parses an expression and returns tuple components when the expression is an
/// actual tuple after stripping outer parentheses and invisible groups.
pub(crate) fn parse_tuple_expr_components(s: &str) -> Result<Option<Vec<String>>, syn::Error> {
    let expr: syn::Expr = syn::parse_str(s)?;
    let syn::Expr::Tuple(tuple) = strip_expr_parens(&expr) else {
        return Ok(None);
    };

    Ok(Some(
        tuple
            .elems
            .iter()
            .map(|expr| expr.into_token_stream().to_string())
            .collect(),
    ))
}

fn strip_expr_parens(expr: &syn::Expr) -> &syn::Expr {
    match expr {
        syn::Expr::Paren(paren) => strip_expr_parens(&paren.expr),
        syn::Expr::Group(group) => strip_expr_parens(&group.expr),
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn compact(s: &str) -> String {
        s.chars().filter(|c| !c.is_whitespace()).collect()
    }

    #[test]
    fn test_split_generic_args_simple() {
        assert_eq!(split_generic_args("K, V"), Some(("K", " V")));
    }

    #[test]
    fn test_split_generic_args_nested() {
        assert_eq!(
            split_generic_args("Map<A, B>, C"),
            Some(("Map<A, B>", " C"))
        );
    }

    #[test]
    fn test_split_generic_args_no_comma() {
        assert_eq!(split_generic_args("i32"), None);
    }

    #[test]
    fn test_split_generic_args_deeply_nested() {
        assert_eq!(
            split_generic_args("Map<Seq<i32>, Set<u64>>, bool"),
            Some(("Map<Seq<i32>, Set<u64>>", " bool"))
        );
    }

    #[test]
    fn test_split_generic_args_empty() {
        assert_eq!(split_generic_args(""), None);
    }

    #[test]
    fn test_split_generic_args_tuple_first_arg() {
        assert_eq!(
            split_generic_args("(usize, T), U"),
            Some(("(usize, T)", " U"))
        );
    }

    #[test]
    fn test_split_top_level_args_tuple_and_generic_nesting() {
        assert_eq!(
            split_top_level_args("usize, Map<Seq<i32>, Set<u64>>, (bool, char)"),
            vec!["usize", "Map<Seq<i32>, Set<u64>>", "(bool, char)"]
        );
    }

    #[test]
    fn test_split_top_level_args_preserves_struct_literal_commas() {
        assert_eq!(
            split_top_level_args("f(Foo { x: a, y: b }), c"),
            vec!["f(Foo { x: a, y: b })", "c"]
        );
    }

    #[test]
    fn test_parse_tuple_expr_components_preserves_shift_operator_tuple_component() {
        let parts = parse_tuple_expr_components("(n >> 1, c)")
            .expect("shift-expression tuple should parse cleanly")
            .expect("shift-expression should stay a tuple");

        assert_eq!(
            parts
                .into_iter()
                .map(|part| compact(&part))
                .collect::<Vec<_>>(),
            vec!["n>>1", "c"]
        );
    }

    #[test]
    fn test_parse_tuple_expr_components_preserves_turbofish_commas() {
        let parts = parse_tuple_expr_components("(foo::<A, B>(x), c)")
            .expect("turbofish tuple should parse cleanly")
            .expect("turbofish expression should stay a tuple");

        assert_eq!(
            parts
                .into_iter()
                .map(|part| compact(&part))
                .collect::<Vec<_>>(),
            vec!["foo::<A,B>(x)", "c"]
        );
    }

    #[test]
    fn test_parse_tuple_expr_components_rejects_parenthesized_singleton() {
        let parts = parse_tuple_expr_components("(f(a, b))")
            .expect("parenthesized singleton should parse as an expression");

        assert!(
            parts.is_none(),
            "parenthesized singleton should stay a single measure, got {:?}",
            parts
        );
    }
}
