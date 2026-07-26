//! Rust AST to SMT expression translator.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Translates Rust expressions collected by macros into the simplified
//! format expected by the encoder for ay verification.

use std::collections::HashMap;
use syn::{BinOp, Expr, ExprBinary, ExprTuple, ExprUnary, UnOp};

use crate::{TrustVcError, TrustVcResult};

/// Translates Rust AST expressions to SMT-compatible format.
#[derive(Debug)]
#[doc(hidden)]
pub struct RustToSmtTranslator {
    /// Maps Rust variable names to their SMT representations
    variables: HashMap<String, String>,
}

impl RustToSmtTranslator {
    /// Creates a new translator instance.
    pub fn new() -> Self {
        Self {
            variables: HashMap::new(),
        }
    }

    /// Registers a variable with its type information.
    pub fn register_variable(&mut self, name: String, ty: String) {
        self.variables.insert(name, ty);
    }

    /// Translates a Rust expression string to SMT format.
    pub fn translate(&self, rust_expr: &str) -> TrustVcResult<String> {
        self.try_translate(rust_expr)
    }

    /// Crate-private typed translator path for internal callers.
    pub(crate) fn try_translate(&self, rust_expr: &str) -> TrustVcResult<String> {
        // Quantifier expressions (forall/exists with closures) are handled
        // directly by the encoder's AST parser. Pass them through unchanged
        // to avoid the translator mangling closure syntax.
        let trimmed = rust_expr.trim();
        if trimmed.starts_with("forall(") || trimmed.starts_with("exists(") {
            return Ok(rust_expr.to_string());
        }

        // Parse the Rust expression, normalizing chained comparisons.
        let expr = crate::chained_comparisons::parse_expr_str_with_chains(rust_expr).map_err(
            |source| TrustVcError::Parse {
                context: "translate expression",
                source,
            },
        )?;

        // Translate the parsed AST
        self.translate_expr(&expr)
    }

    /// Translates a parsed Rust expression AST to SMT format.
    fn translate_expr(&self, expr: &Expr) -> TrustVcResult<String> {
        match expr {
            Expr::Binary(binary) => self.translate_binary(binary),
            Expr::Unary(unary) => self.translate_unary(unary),
            Expr::Lit(lit) => self.translate_literal(lit),
            Expr::Path(path) => self.translate_path(path),
            Expr::Paren(paren) => self.translate_expr(&paren.expr),
            Expr::MethodCall(method) => self.translate_method_call(method),
            Expr::Call(call) => self.translate_call(call),
            Expr::Tuple(tuple) => self.translate_tuple(tuple),
            _ => Err(Self::unsupported(
                "Unsupported expression type (Cast, Range, Array, Struct, etc.)",
            )),
        }
    }

    /// Translates binary operators.
    fn translate_binary(&self, binary: &ExprBinary) -> TrustVcResult<String> {
        let left = self.translate_expr(&binary.left)?;
        let right = self.translate_expr(&binary.right)?;

        let op = match &binary.op {
            BinOp::Add(_) => "+",
            BinOp::Sub(_) => "-",
            BinOp::Mul(_) => "*",
            BinOp::Div(_) => "/",
            BinOp::Rem(_) => "%",
            BinOp::And(_) => "&&",
            BinOp::Or(_) => "||",
            BinOp::Lt(_) => "<",
            BinOp::Le(_) => "<=",
            BinOp::Gt(_) => ">",
            BinOp::Ge(_) => ">=",
            BinOp::Eq(_) => "==",
            BinOp::Ne(_) => "!=",
            _ => return Err(Self::unsupported("Unsupported binary operator")),
        };

        // Keep infix notation that the encoder expects
        Ok(format!("({} {} {})", left, op, right))
    }

    /// Translates unary operators.
    fn translate_unary(&self, unary: &ExprUnary) -> TrustVcResult<String> {
        let inner = self.translate_expr(&unary.expr)?;

        match &unary.op {
            UnOp::Not(_) => Ok(format!("!({})", inner)),
            UnOp::Neg(_) => Ok(format!("(- {})", inner)),
            _ => Err(Self::unsupported("Unsupported unary operator")),
        }
    }

    /// Translates literals.
    fn translate_literal(&self, lit: &syn::ExprLit) -> TrustVcResult<String> {
        match &lit.lit {
            syn::Lit::Int(int_lit) => Ok(int_lit.to_string()),
            syn::Lit::Bool(bool_lit) => Ok(bool_lit.value.to_string()),
            _ => Err(Self::unsupported("Unsupported literal type")),
        }
    }

    /// Translates variable references.
    fn translate_path(&self, path: &syn::ExprPath) -> TrustVcResult<String> {
        // Extract the identifier
        if let Some(ident) = path.path.get_ident() {
            Ok(ident.to_string())
        } else {
            // Handle qualified paths
            let segments: Vec<String> = path
                .path
                .segments
                .iter()
                .map(|seg| seg.ident.to_string())
                .collect();
            Ok(segments.join("::"))
        }
    }

    /// Translates method calls (e.g., seq.len(), seq.index(i)).
    #[allow(clippy::indexing_slicing)] // args[0] guarded by method.args.len() == 1 in supported arms
    fn translate_method_call(&self, method: &syn::ExprMethodCall) -> TrustVcResult<String> {
        let receiver = self.translate_expr(&method.receiver)?;
        let method_name = method.method.to_string();

        match method_name.as_str() {
            "len" => Ok(format!("(len {})", receiver)),
            "index" => {
                if method.args.len() != 1 {
                    return Err(Self::unsupported("index() requires exactly one argument"));
                }
                let index = self.translate_expr(&method.args[0])?;
                Ok(format!("(select {} {})", receiver, index))
            }
            "contains" => {
                if method.args.len() != 1 {
                    return Err(Self::unsupported(
                        "contains() requires exactly one argument",
                    ));
                }
                let elem = self.translate_expr(&method.args[0])?;
                Ok(format!("(member {} {})", elem, receiver))
            }
            _ => Err(Self::unsupported(format!(
                "Unsupported method: {}",
                method_name
            ))),
        }
    }

    /// Translates function calls.
    #[allow(clippy::indexing_slicing)] // args[0]/args[1] guarded by per-function arity checks in supported arms
    fn translate_call(&self, call: &syn::ExprCall) -> TrustVcResult<String> {
        // Extract function name
        let func_name = if let Expr::Path(path) = &*call.func {
            if let Some(ident) = path.path.get_ident() {
                ident.to_string()
            } else {
                return Err(Self::unsupported(
                    "Complex function paths not yet supported",
                ));
            }
        } else {
            return Err(Self::unsupported(
                "Non-path function calls not yet supported",
            ));
        };

        // Translate arguments
        let args: TrustVcResult<Vec<String>> = call
            .args
            .iter()
            .map(|arg| self.translate_expr(arg))
            .collect();
        let args = args?;

        // Handle known functions
        match func_name.as_str() {
            "abs" => {
                if args.len() != 1 {
                    return Err(Self::unsupported("abs() requires exactly one argument"));
                }
                Ok(format!("(abs {})", args[0]))
            }
            "min" => {
                if args.len() != 2 {
                    return Err(Self::unsupported("min() requires exactly two arguments"));
                }
                Ok(format!("(min {} {})", args[0], args[1]))
            }
            "max" => {
                if args.len() != 2 {
                    return Err(Self::unsupported("max() requires exactly two arguments"));
                }
                Ok(format!("(max {} {})", args[0], args[1]))
            }
            _ => {
                // Generic function call
                Ok(format!("({} {})", func_name, args.join(" ")))
            }
        }
    }

    /// Translates tuple expressions.
    /// Tuples are used for lexicographic ordering in loop_decreases! macro.
    fn translate_tuple(&self, tuple: &ExprTuple) -> TrustVcResult<String> {
        // For lexicographic ordering, we need to translate each component
        let components: TrustVcResult<Vec<String>> = tuple
            .elems
            .iter()
            .map(|elem| self.translate_expr(elem))
            .collect();
        let components = components?;

        // Return tuple as comma-separated values in parentheses
        // The encoder will need to handle this for lexicographic comparisons
        Ok(format!("({})", components.join(", ")))
    }

    fn unsupported(detail: impl Into<String>) -> TrustVcError {
        TrustVcError::Encoding {
            context: "translate expression",
            detail: detail.into(),
        }
    }
}

impl Default for RustToSmtTranslator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_arithmetic() {
        let translator = RustToSmtTranslator::new();

        assert_eq!(translator.translate("a + b").unwrap(), "(a + b)");

        assert_eq!(translator.translate("x - 1").unwrap(), "(x - 1)");

        assert_eq!(translator.translate("2 * n").unwrap(), "(2 * n)");
    }

    #[test]
    fn test_logical_operators() {
        let translator = RustToSmtTranslator::new();

        assert_eq!(translator.translate("a && b").unwrap(), "(a && b)");

        assert_eq!(translator.translate("x || y").unwrap(), "(x || y)");

        assert_eq!(translator.translate("!flag").unwrap(), "!(flag)");
    }

    #[test]
    fn test_comparison_operators() {
        let translator = RustToSmtTranslator::new();

        assert_eq!(translator.translate("x > 0").unwrap(), "(x > 0)");

        assert_eq!(translator.translate("a <= b").unwrap(), "(a <= b)");

        assert_eq!(translator.translate("n == 5").unwrap(), "(n == 5)");
    }

    #[test]
    fn test_complex_expressions() {
        let translator = RustToSmtTranslator::new();

        assert_eq!(
            translator.translate("(a + b) > (c - d)").unwrap(),
            "((a + b) > (c - d))"
        );

        assert_eq!(
            translator.translate("x > 0 && y < 10").unwrap(),
            "((x > 0) && (y < 10))"
        );
    }

    #[test]
    fn test_tuple_translation() {
        let translator = RustToSmtTranslator::new();

        // Single element tuple
        assert_eq!(translator.translate("(a,)").unwrap(), "(a)");

        // Two element tuple
        assert_eq!(translator.translate("(a, b)").unwrap(), "(a, b)");

        // Three element tuple for lexicographic ordering
        assert_eq!(translator.translate("(x, y, z)").unwrap(), "(x, y, z)");

        // Tuple with expressions
        assert_eq!(
            translator.translate("(n - 1, m + 2)").unwrap(),
            "((n - 1), (m + 2))"
        );
    }

    #[test]
    fn test_empty_tuple() {
        let translator = RustToSmtTranslator::new();

        // Empty tuple should translate to empty parentheses
        assert_eq!(translator.translate("()").unwrap(), "()");
    }

    #[test]
    fn test_method_calls() {
        let translator = RustToSmtTranslator::new();

        assert_eq!(translator.translate("seq.len()").unwrap(), "(len seq)");

        assert_eq!(
            translator.translate("arr.index(i)").unwrap(),
            "(select arr i)"
        );
    }

    #[test]
    fn test_function_calls() {
        let translator = RustToSmtTranslator::new();

        assert_eq!(translator.translate("abs(x)").unwrap(), "(abs x)");

        assert_eq!(translator.translate("min(a, b)").unwrap(), "(min a b)");
    }

    #[test]
    fn test_quantifier_pass_through() {
        let translator = RustToSmtTranslator::new();

        // forall/exists with closures should pass through unchanged
        let forall_input = "forall(|x: i32| x == x)";
        let forall_result = translator.translate(forall_input).unwrap();
        assert_eq!(
            forall_result, forall_input,
            "forall should pass through unchanged to encoder"
        );

        let exists_input = "exists(|x: i32| x > 0)";
        let exists_result = translator.translate(exists_input).unwrap();
        assert_eq!(
            exists_result, exists_input,
            "exists should pass through unchanged to encoder"
        );
    }

    #[test]
    fn test_try_translate_reports_parse_errors_as_trust_vc_parse() {
        let translator = RustToSmtTranslator::new();

        let result = translator.try_translate("x + + y");
        match result {
            Err(TrustVcError::Parse { context, .. }) => {
                assert_eq!(context, "translate expression");
            }
            other => panic!("expected TrustVcError::Parse, got {other:?}"),
        }
    }

    #[test]
    fn test_try_translate_reports_unsupported_expr_as_encoding() {
        let translator = RustToSmtTranslator::new();

        let result = translator.try_translate("x as i64");
        match result {
            Err(TrustVcError::Encoding { context, detail }) => {
                assert_eq!(context, "translate expression");
                assert!(
                    detail.contains("Unsupported expression type"),
                    "expected unsupported expression detail, got: {detail}"
                );
            }
            other => panic!("expected TrustVcError::Encoding, got {other:?}"),
        }
    }

    #[test]
    fn test_translate_preserves_legacy_parse_message() {
        let translator = RustToSmtTranslator::new();

        let result = translator.translate("x + + y");
        let err = result.expect_err("invalid expression should fail to parse");
        assert!(matches!(
            err,
            TrustVcError::Parse {
                context: "translate expression",
                ..
            }
        ));
        assert!(
            err.to_string().starts_with("translate expression: "),
            "expected typed parse display, got: {err}"
        );
    }
}
