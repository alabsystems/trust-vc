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
    // No up-front capacity hint: the vector grows as values are pushed, so no
    // single bulk allocation is sized by the caller-controlled slice length.
    let mut parts = Vec::new();

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
    let Some((_, after_pattern)) = model_text.split_once(pattern.as_str()) else {
        return "?".to_string();
    };

    // Skip the sort — find the next token after the sort
    // The sort could be simple (Int, Bool, Real) or compound ((_ BitVec 32))
    let trimmed = after_pattern.trim_start();
    let after_sort = skip_sexp(trimmed);
    let value_region = after_sort.trim_start();

    // Extract the value up to the closing paren
    let value = extract_value_token(value_region);
    value.to_string()
}

/// Returns the byte index of the `)` that closes the parenthesized form at
/// the start of `s`, or `None` when the form is unterminated.
///
/// `s` must start with `(`; the callers check this before calling.
fn closing_paren(s: &str) -> Option<usize> {
    let mut depth: usize = 0;
    for (i, ch) in s.char_indices() {
        match ch {
            // Nesting depth is bounded by the string length, so saturation is
            // unreachable; it only spells out that the count cannot wrap.
            '(' => depth = depth.saturating_add(1),
            ')' => {
                // The leading `(` makes depth at least 1 before any `)`, so
                // depth reaches 0 only at the matching close.
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Splits `s` at the end of a simple atom, which ends at whitespace or `)`.
/// Returns `(atom, rest)`; an atom with no terminator takes the whole string.
fn split_atom(s: &str) -> (&str, &str) {
    match s.find(|c: char| c.is_whitespace() || c == ')') {
        // `find` returns a char boundary of `s`, so the split always succeeds.
        Some(end) => s.split_at_checked(end).unwrap_or((s, "")),
        None => (s, ""),
    }
}

/// Skips one S-expression (atom or parenthesized form) and returns the rest.
fn skip_sexp(s: &str) -> &str {
    let s = s.trim_start();
    if s.starts_with('(') {
        // The rest starts after the closing `)`; malformed input is returned as-is.
        closing_paren(s)
            .and_then(|i| s.get(i..))
            .and_then(|from_close| from_close.strip_prefix(')'))
            .unwrap_or(s)
    } else {
        split_atom(s).1
    }
}

/// Extracts a value token (possibly a compound S-expression) from the start of the string.
fn extract_value_token(s: &str) -> &str {
    let s = s.trim_start();
    if s.starts_with('(') {
        // Compound value like (- 5); an unterminated form is returned as-is.
        closing_paren(s).and_then(|i| s.get(..=i)).unwrap_or(s)
    } else {
        split_atom(s).0
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

    #[test]
    fn test_nested_sort_and_nested_value() {
        let model = "(model (define-fun a () (Array Int (_ BitVec 8)) ((as const (Array Int (_ BitVec 8))) #x00)))";
        let vars = vec![VarDecl::new("a", SortMeta::MathInt)];
        let fp = extract_model_fingerprint(model, &vars);
        assert_eq!(fp, "a=((as const (Array Int (_ BitVec 8))) #x00)");
    }

    #[test]
    fn test_unterminated_value_is_returned_as_is() {
        let model = "(define-fun x () Int (- 5";
        let vars = vec![VarDecl::new("x", SortMeta::MathInt)];
        assert_eq!(extract_model_fingerprint(model, &vars), "x=(- 5");
    }

    #[test]
    fn test_unterminated_sort_leaves_text_unskipped() {
        // A malformed sort is not skipped; the value token is then the sort form.
        let model = "(define-fun x () (_ BitVec 8";
        let vars = vec![VarDecl::new("x", SortMeta::MathInt)];
        assert_eq!(extract_model_fingerprint(model, &vars), "x=(_ BitVec 8");
    }

    #[test]
    fn test_atom_value_at_end_of_input() {
        let model = "(define-fun x () Int 42";
        let vars = vec![VarDecl::new("x", SortMeta::MathInt)];
        assert_eq!(extract_model_fingerprint(model, &vars), "x=42");
    }

    #[test]
    fn test_missing_value_after_sort() {
        let model = "(define-fun x () Int";
        let vars = vec![VarDecl::new("x", SortMeta::MathInt)];
        assert_eq!(extract_model_fingerprint(model, &vars), "x=");
    }

    #[test]
    fn test_skip_sexp_and_value_token_on_multibyte_text() {
        assert_eq!(skip_sexp("(é (ü)) rest"), " rest");
        assert_eq!(skip_sexp("é) rest"), ") rest");
        assert_eq!(extract_value_token("(é (ü)) rest"), "(é (ü))");
        assert_eq!(extract_value_token("éü"), "éü");
    }
}
