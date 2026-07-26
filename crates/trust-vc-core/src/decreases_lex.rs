//! Lexicographic ordering for tuple decreases measures.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Decomposes tuple measures `(a, b)` into scalar comparisons with
//! lexicographic ordering — the standard approach for termination proofs.
//! `(a', b') < (a, b)` iff `a' < a || (a' == a && b' < b)`.
//!
//! Fixes #1632.

/// Generates the lexicographic ordering condition for tuple decreases measures.
///
/// If both old and new are tuple expressions with matching arity, returns
/// the lexicographic condition. Otherwise returns the simple `new < old`.
pub(crate) fn lexicographic_decreases_condition(old: &str, new: &str) -> String {
    match (parse_tuple_components(old), parse_tuple_components(new)) {
        (Some(old_parts), Some(new_parts)) if old_parts.len() == new_parts.len() => {
            build_lexicographic_condition(&old_parts, &new_parts)
        }
        _ => format!("{} < {}", new, old),
    }
}

/// Generates the well-founded lexicographic ordering used to admit recursive
/// defining axioms.
///
/// Integer components use Verus's bounded-below ordering:
/// `smaller(new, old) := 0 <= new && new < old`. For tuples, only the component
/// that establishes the first strict decrease needs that lower bound; later
/// components are irrelevant once an earlier component decreases. This
/// distinction is load-bearing for Ackermann-style measures, whose second new
/// component may be an uninterpreted recursive call while the first component
/// already strictly decreases.
pub(crate) fn well_founded_lexicographic_decreases_condition(old: &str, new: &str) -> String {
    match (parse_tuple_components(old), parse_tuple_components(new)) {
        (Some(old_parts), Some(new_parts)) if old_parts.len() == new_parts.len() => {
            build_well_founded_lexicographic_condition(&old_parts, &new_parts)
        }
        _ => format!("(0 <= {new}) && ({new} < {old})"),
    }
}

/// Parses a tuple expression string like `"(a, b, c)"` into components `["a", "b", "c"]`.
///
/// Returns `None` for non-tuple expressions (no leading `(`).
/// Handles nested parentheses in components, e.g. `"(m - 1, (n + 2))"` → `["m - 1", "(n + 2)"]`.
fn parse_tuple_components(s: &str) -> Option<Vec<String>> {
    let s = s.trim();
    if !s.starts_with('(') || !s.ends_with(')') {
        return None;
    }
    let inner = &s[1..s.len() - 1];
    let mut components = Vec::new();
    let mut depth = 0i32;
    let mut current = String::new();

    for ch in inner.chars() {
        match ch {
            '(' => {
                depth += 1;
                current.push(ch);
            }
            ')' => {
                depth -= 1;
                current.push(ch);
            }
            ',' if depth == 0 => {
                let trimmed = current.trim().to_string();
                if trimmed.is_empty() {
                    return None;
                }
                components.push(trimmed);
                current.clear();
            }
            _ => current.push(ch),
        }
    }
    let trimmed = current.trim().to_string();
    if trimmed.is_empty() {
        return None;
    }
    components.push(trimmed);

    if components.len() < 2 {
        return None;
    }
    Some(components)
}

/// Builds a lexicographic ordering condition from old and new tuple components.
///
/// For `(a', b') < (a, b)`: `(a' < a) || (a' == a && b' < b)`
/// For `(a', b', c') < (a, b, c)`: `(a' < a) || (a' == a && ((b' < b) || (b' == b && c' < c)))`
fn build_lexicographic_condition(old_parts: &[String], new_parts: &[String]) -> String {
    debug_assert_eq!(old_parts.len(), new_parts.len());
    build_lex_recursive(old_parts, new_parts, 0)
}

fn build_well_founded_lexicographic_condition(
    old_parts: &[String],
    new_parts: &[String],
) -> String {
    debug_assert_eq!(old_parts.len(), new_parts.len());
    build_well_founded_lex_recursive(old_parts, new_parts)
}

fn build_well_founded_lex_recursive(old_parts: &[String], new_parts: &[String]) -> String {
    let Some((old, old_rest)) = old_parts.split_first() else {
        return "false".to_string();
    };
    let Some((new, new_rest)) = new_parts.split_first() else {
        return "false".to_string();
    };
    let smaller = format!("(0 <= {new}) && ({new} < {old})");
    if old_rest.is_empty() {
        return smaller;
    }
    let equal = format!("{new} == {old}");
    let rest = build_well_founded_lex_recursive(old_rest, new_rest);
    format!("({smaller}) || ({equal} && ({rest}))")
}

#[allow(clippy::indexing_slicing)] // idx starts in-bounds and recursion stops before idx reaches len
fn build_lex_recursive(old_parts: &[String], new_parts: &[String], idx: usize) -> String {
    let remaining = old_parts.len() - idx;
    if remaining == 1 {
        return format!("{} < {}", new_parts[idx], old_parts[idx]);
    }
    let strict = format!("{} < {}", new_parts[idx], old_parts[idx]);
    let equal = format!("{} == {}", new_parts[idx], old_parts[idx]);
    let rest = build_lex_recursive(old_parts, new_parts, idx + 1);
    format!("({}) || ({} && ({}))", strict, equal, rest)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_tuple_two_components() {
        let result = parse_tuple_components("(m, n)");
        assert_eq!(result, Some(vec!["m".to_string(), "n".to_string()]));
    }

    #[test]
    fn test_parse_tuple_three_components() {
        let result = parse_tuple_components("(x, y, z)");
        assert_eq!(
            result,
            Some(vec!["x".to_string(), "y".to_string(), "z".to_string()])
        );
    }

    #[test]
    fn test_parse_tuple_with_expressions() {
        let result = parse_tuple_components("(m - 1, 1)");
        assert_eq!(result, Some(vec!["m - 1".to_string(), "1".to_string()]));
    }

    #[test]
    fn test_parse_tuple_nested_parens() {
        let result = parse_tuple_components("((a + b), c)");
        assert_eq!(result, Some(vec!["(a + b)".to_string(), "c".to_string()]));
    }

    #[test]
    fn test_parse_non_tuple() {
        assert_eq!(parse_tuple_components("n"), None);
        assert_eq!(parse_tuple_components("n - 1"), None);
    }

    #[test]
    fn test_parse_single_element_parens() {
        // (n) is not a tuple — it's a parenthesized expression
        assert_eq!(parse_tuple_components("(n)"), None);
    }

    #[test]
    fn test_lex_condition_two() {
        let old = vec!["m".to_string(), "n".to_string()];
        let new = vec!["m - 1".to_string(), "1".to_string()];
        let cond = build_lexicographic_condition(&old, &new);
        assert_eq!(cond, "(m - 1 < m) || (m - 1 == m && (1 < n))");
    }

    #[test]
    fn test_lex_condition_three() {
        let old = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let new = vec!["a2".to_string(), "b2".to_string(), "c2".to_string()];
        let cond = build_lexicographic_condition(&old, &new);
        assert_eq!(
            cond,
            "(a2 < a) || (a2 == a && ((b2 < b) || (b2 == b && (c2 < c))))"
        );
    }

    #[test]
    fn test_lexicographic_scalar_passthrough() {
        let cond = lexicographic_decreases_condition("n", "n - 1");
        assert_eq!(cond, "n - 1 < n");
    }

    #[test]
    fn test_lexicographic_tuple_condition() {
        let cond = lexicographic_decreases_condition("(m, n)", "(m - 1, 1)");
        assert_eq!(cond, "(m - 1 < m) || (m - 1 == m && (1 < n))");
    }

    #[test]
    fn test_well_founded_scalar_requires_nonnegative_new_measure() {
        let cond = well_founded_lexicographic_decreases_condition("n", "(n - 1) as nat");
        assert_eq!(cond, "(0 <= (n - 1) as nat) && ((n - 1) as nat < n)");
    }

    #[test]
    fn test_well_founded_tuple_bounds_only_strict_component() {
        let cond =
            well_founded_lexicographic_decreases_condition("(m, n)", "(m - 1, ack(m, n - 1))");
        assert_eq!(
            cond,
            "((0 <= m - 1) && (m - 1 < m)) || (m - 1 == m && ((0 <= ack(m, n - 1)) && (ack(m, n - 1) < n)))"
        );
    }

    /// Regression for #2150: proc macro codegen produces `quote!((#args)).to_string()`
    /// format which may include extra spaces. Verify decomposition handles this.
    #[test]
    fn test_codegen_format_with_spaces() {
        // quote! may produce "(m - 1 , 1)" or "(m - 1, 1)" depending on tokenization
        let cond = lexicographic_decreases_condition("(m , n)", "(m - 1 , 1)");
        assert_eq!(cond, "(m - 1 < m) || (m - 1 == m && (1 < n))");
    }

    /// Regression for #2150: triple tuple codegen format.
    #[test]
    fn test_codegen_triple_tuple() {
        let cond = lexicographic_decreases_condition("(a, b, c)", "(a - 1, b, c)");
        assert_eq!(
            cond,
            "(a - 1 < a) || (a - 1 == a && ((b < b) || (b == b && (c < c))))"
        );
    }
}
