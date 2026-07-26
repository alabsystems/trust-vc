// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Model fingerprint extraction from ay executor output.
//!
//! When the solver returns SAT, we extract variable assignments from the
//! model output and produce a deterministic fingerprint string.

use trust_vc_merge_contract::VarDecl;

/// Extracts a deterministic fingerprint from ay model text.
///
/// The fingerprint format is `name=value;name=value;...` in bundle variable
/// declaration order. This gives a stable, non-empty string for parity
/// comparison without requiring hashing.
///
/// If parsing fails for a variable, its value is recorded as `?`.
pub(crate) fn extract_model_fingerprint(model_text: &str, variables: &[VarDecl]) -> String {
    let mut parts = Vec::with_capacity(variables.len());

    for var in variables {
        let value = extract_variable_value(model_text, var.name());
        parts.push(format!("{}={}", var.name(), value));
    }

    parts.join(";")
}

/// Extracts the value of a single variable from model text.
///
/// ay model output format:
/// ```text
/// (model
///   (define-fun x () Int 42)
///   (define-fun v () (_ BitVec 32) #b00000000000000000000000000000000)
/// )
/// ```
fn extract_variable_value(model_text: &str, var_name: &str) -> String {
    // Look for (define-fun <name> () <sort> <value>)
    let pattern = format!("(define-fun {var_name} ()");
    let Some(start) = model_text.find(&pattern) else {
        return "?".to_string();
    };

    let after_pattern = &model_text[start + pattern.len()..];

    // Skip the sort — find the next token after the sort
    // The sort could be simple (Int, Bool, Real) or compound ((_ BitVec 32))
    let trimmed = after_pattern.trim_start();
    let after_sort = skip_sexp(trimmed);
    let value_region = after_sort.trim_start();

    // Extract the value up to the closing paren
    let value = extract_value_token(value_region);
    value.to_string()
}

/// Skips one S-expression (atom or parenthesized form) and returns the rest.
fn skip_sexp(s: &str) -> &str {
    let s = s.trim_start();
    if s.starts_with('(') {
        let mut depth = 0;
        for (i, ch) in s.char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        return &s[i + 1..];
                    }
                }
                _ => {}
            }
        }
        s // malformed, return as-is
    } else {
        // Simple atom — ends at whitespace or ')'
        let end = s
            .find(|c: char| c.is_whitespace() || c == ')')
            .unwrap_or(s.len());
        &s[end..]
    }
}

/// Extracts a value token (possibly a compound S-expression) from the start of the string.
fn extract_value_token(s: &str) -> &str {
    let s = s.trim_start();
    if s.starts_with('(') {
        // Compound value like (- 5) or #b... in a group
        let mut depth = 0;
        for (i, ch) in s.char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        return &s[..=i];
                    }
                }
                _ => {}
            }
        }
        s
    } else {
        // Simple value — ends at whitespace or ')'
        let end = s
            .find(|c: char| c.is_whitespace() || c == ')')
            .unwrap_or(s.len());
        &s[..end]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_vc_merge_contract::SortMeta;

    #[test]
    fn test_extract_int_variable() {
        let model = "(model\n  (define-fun x () Int 42)\n)";
        let vars = vec![VarDecl::new("x", SortMeta::MathInt)];
        let fp = extract_model_fingerprint(model, &vars);
        assert_eq!(fp, "x=42");
    }

    #[test]
    fn test_extract_negative_int() {
        let model = "(model\n  (define-fun x () Int (- 5))\n)";
        let vars = vec![VarDecl::new("x", SortMeta::MathInt)];
        let fp = extract_model_fingerprint(model, &vars);
        assert_eq!(fp, "x=(- 5)");
    }

    #[test]
    fn test_extract_bitvector() {
        let model =
            "(model\n  (define-fun v () (_ BitVec 32) #b00000000000000000000000000000101)\n)";
        let vars = vec![VarDecl::new(
            "v",
            SortMeta::BitVector {
                width: 32,
                signed: false,
            },
        )];
        let fp = extract_model_fingerprint(model, &vars);
        assert_eq!(fp, "v=#b00000000000000000000000000000101");
    }

    #[test]
    fn test_extract_bool() {
        let model = "(model\n  (define-fun b () Bool true)\n)";
        let vars = vec![VarDecl::new("b", SortMeta::Bool)];
        let fp = extract_model_fingerprint(model, &vars);
        assert_eq!(fp, "b=true");
    }

    #[test]
    fn test_multiple_variables_in_order() {
        let model = "(model\n  (define-fun a () Int 1)\n  (define-fun b () Int 2)\n)";
        let vars = vec![
            VarDecl::new("a", SortMeta::MathInt),
            VarDecl::new("b", SortMeta::MathInt),
        ];
        let fp = extract_model_fingerprint(model, &vars);
        assert_eq!(fp, "a=1;b=2");
    }

    #[test]
    fn test_missing_variable_uses_question_mark() {
        let model = "(model\n  (define-fun x () Int 42)\n)";
        let vars = vec![
            VarDecl::new("x", SortMeta::MathInt),
            VarDecl::new("y", SortMeta::MathInt),
        ];
        let fp = extract_model_fingerprint(model, &vars);
        assert_eq!(fp, "x=42;y=?");
    }
}
