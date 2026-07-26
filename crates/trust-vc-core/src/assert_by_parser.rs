// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Parser for assert_by! macro to extract the condition from blocks.
//!
//! This module solves issue #753 by properly extracting the final expression
//! from assert_by! blocks that may contain let statements.
//!
//! For issue #845, let bindings are inlined into the final expression via
//! substitution so the encoder receives a fully-resolved condition.

use std::collections::HashMap;

use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::Parser;
use syn::visit_mut::{self, VisitMut};
use syn::{parse2, Block, Expr, ExprParen, Local, Pat, Stmt};

/// Result of parsing `assert_by!` input: either a single-argument form or
/// the Verus-style two-argument form `assert_by!(condition, { proof_block })`.
#[non_exhaustive]
pub enum AssertByParsed {
    /// Single-argument: `assert_by!(condition)` or `assert_by!({ let x = ...; cond })`
    Single {
        /// The full input tokens (run as the macro body).
        tokens: TokenStream,
        /// The extracted condition expression.
        condition: TokenStream,
    },
    /// Two-argument Verus-style: `assert_by!(condition, { proof_block })`
    WithProofBlock {
        /// The condition to prove.
        condition: TokenStream,
        /// The proof block body (may contain inner `trust_vc::assert!()` calls).
        proof_block: TokenStream,
    },
}

/// Parses `assert_by!` input, detecting the Verus-style two-argument form.
///
/// Two-argument form: `assert_by!(condition, { proof_block })` — the condition
/// is proved using scoped helper assertions from the proof block.
///
/// Single-argument form: `assert_by!(condition)` or `assert_by!({ lets; cond })`
/// — backward compatible with existing usage.
pub fn parse_assert_by(tokens: TokenStream) -> AssertByParsed {
    // Try the two-argument form: `condition, { block }`
    if let Some(parsed) = try_parse_two_arg(tokens.clone()) {
        return parsed;
    }

    // Fall through to single-argument form
    let condition = extract_condition(tokens.clone());
    AssertByParsed::Single { tokens, condition }
}

/// Tries to parse `assert_by!(condition, { block })`.
///
/// Uses syn's Punctuated parser to split on comma. The second element must
/// be a block expression.
fn try_parse_two_arg(tokens: TokenStream) -> Option<AssertByParsed> {
    use syn::punctuated::Punctuated;

    let args: Punctuated<Expr, syn::Token![,]> =
        Punctuated::parse_terminated.parse2(tokens).ok()?;
    if args.len() != 2 {
        return None;
    }

    let mut iter = args.into_iter();
    let condition_expr = iter.next()?;
    let block_expr = iter.next()?;

    // The second argument must be a block expression `{ ... }`
    match &block_expr {
        Expr::Block(_) => {}
        _ => return None,
    }

    let condition = quote!(#condition_expr);
    let proof_block = quote!(#block_expr);
    Some(AssertByParsed::WithProofBlock {
        condition,
        proof_block,
    })
}

/// Extracts the condition expression from assert_by! input.
///
/// For blocks containing let statements, the bindings are substituted into
/// the final expression so the result is self-contained.
///
/// # Input formats
/// - Simple expression: `assert_by!(x > 0)`
/// - Block with let bindings: `assert_by!({ let y = x + 1; y > 0 })` → `(x + 1) > 0`
///
/// # Returns
/// The condition expression as a TokenStream, or the entire input if parsing fails.
pub fn extract_condition(tokens: TokenStream) -> TokenStream {
    // Try to parse as a block first (blocks are also expressions)
    if let Ok(block) = parse2::<Block>(tokens.clone()) {
        if let Some(resolved) = extract_condition_from_block(&block) {
            return quote!(#resolved);
        }
    }

    // If not a block, try to parse as a simple expression
    if let Ok(expr) = parse2::<Expr>(tokens.clone()) {
        // Check if this is a block expression
        if let Expr::Block(expr_block) = &expr {
            if let Some(resolved) = extract_condition_from_block(&expr_block.block) {
                return quote!(#resolved);
            }
        }
        // It's a simple expression, return it as-is
        return quote!(#expr);
    }

    // Proc macros receive tokens without outer braces: `let x = 1; x > 0`
    // Wrap in braces so syn can parse it as a Block
    let wrapped = quote!({ #tokens });
    if let Ok(block) = parse2::<Block>(wrapped) {
        if let Some(resolved) = extract_condition_from_block(&block) {
            return quote!(#resolved);
        }
    }

    // Fallback: return the original tokens
    tokens
}

/// Extracts the final expression from a block and substitutes let bindings.
///
/// Given `{ let a = 1; let b = a + 2; b > 0 }`, returns `(1) + 2 > 0` with
/// all local variables replaced by their binding expressions (parenthesized).
fn extract_condition_from_block(block: &Block) -> Option<Expr> {
    let mut bindings: HashMap<String, Expr> = HashMap::new();
    let mut final_expr: Option<Expr> = None;

    for (i, stmt) in block.stmts.iter().enumerate() {
        match stmt {
            Stmt::Local(local) => {
                if let Some((name, init_expr)) = extract_let_binding(local) {
                    // Substitute earlier bindings into this binding's init expression
                    let resolved_init = substitute_bindings_in_expr(init_expr, &bindings);
                    bindings.insert(name, resolved_init);
                }
            }
            Stmt::Expr(expr, semi) if i == block.stmts.len() - 1 => {
                if semi.is_some() {
                    // Block ends in semicolon — evaluates to (), not the expression.
                    // Return None to fall through to fallback (#1819).
                    return None;
                }
                final_expr = Some(expr.clone());
            }
            _ => {}
        }
    }

    let expr = final_expr?;

    if bindings.is_empty() {
        // No let bindings to substitute — return the expression directly
        return Some(expr);
    }

    // Substitute all bindings into the final expression
    Some(substitute_bindings_in_expr(expr, &bindings))
}

/// Extracts a simple let binding: `let <ident> = <expr>;` → `(name, expr)`
///
/// Handles both bare patterns (`let x = 5`) and typed patterns (`let x: i32 = 5`).
fn extract_let_binding(local: &Local) -> Option<(String, Expr)> {
    // Handle simple identifier patterns and typed patterns (not destructuring)
    let name = match &local.pat {
        Pat::Ident(pat_ident) => pat_ident.ident.to_string(),
        // `let x: Type = expr` wraps Pat::Ident inside Pat::Type
        Pat::Type(pat_type) => match pat_type.pat.as_ref() {
            Pat::Ident(pat_ident) => pat_ident.ident.to_string(),
            _ => return None,
        },
        _ => return None,
    };

    // Get the initializer expression
    let init = local.init.as_ref()?;
    Some((name, (*init.expr).clone()))
}

/// Substitutes all known bindings in an expression by replacing variable
/// references with their (parenthesized) binding expressions.
fn substitute_bindings_in_expr(mut expr: Expr, bindings: &HashMap<String, Expr>) -> Expr {
    let mut substitutor = BindingSubstitutor { bindings };
    substitutor.visit_expr_mut(&mut expr);
    expr
}

/// AST visitor that replaces `Expr::Path` nodes matching bound variables
/// with the corresponding parenthesized binding expression.
struct BindingSubstitutor<'a> {
    bindings: &'a HashMap<String, Expr>,
}

impl<'a> VisitMut for BindingSubstitutor<'a> {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        // First, recurse into children
        visit_mut::visit_expr_mut(self, expr);

        // Then check if this node is a simple path that matches a binding
        if let Expr::Path(expr_path) = expr {
            if expr_path.qself.is_none() && expr_path.path.segments.len() == 1 {
                if let Some(segment) = expr_path.path.segments.first() {
                    let ident = segment.ident.to_string();
                    if let Some(replacement) = self.bindings.get(&ident) {
                        // Replace with parenthesized binding expression
                        *expr = Expr::Paren(ExprParen {
                            attrs: Vec::new(),
                            paren_token: syn::token::Paren::default(),
                            expr: Box::new(replacement.clone()),
                        });
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_simple_expression() {
        let tokens = quote!(x > 0);
        let result = extract_condition(tokens);
        assert_eq!(result.to_string(), "x > 0");
    }

    #[test]
    fn test_extract_from_block_with_substitution() {
        let tokens = quote!({
            let y = x + 1;
            y > 0
        });
        let result = extract_condition(tokens);
        // y should be substituted with (x + 1)
        assert_eq!(result.to_string(), "(x + 1) > 0");
    }

    #[test]
    fn test_extract_from_complex_block_with_substitution() {
        let tokens = quote!({
            let a = 1;
            let b = 2;
            let c = a + b;
            c == 3
        });
        let result = extract_condition(tokens);
        // c = a + b, a = 1, b = 2 → c = (1) + (2) → ((1) + (2)) == 3
        assert_eq!(result.to_string(), "((1) + (2)) == 3");
    }

    #[test]
    fn test_no_let_bindings() {
        let tokens = quote!({ 5 > 3 });
        let result = extract_condition(tokens);
        assert_eq!(result.to_string(), "5 > 3");
    }

    #[test]
    fn test_chained_substitution() {
        let tokens = quote!({
            let a = x * 2;
            let b = a + 1;
            b > 10
        });
        let result = extract_condition(tokens);
        // b = a + 1 → (a) + 1, a = x * 2 → ((x * 2)) + 1 > 10
        // After substitution: ((x * 2) + 1) > 10
        assert_eq!(result.to_string(), "((x * 2) + 1) > 10");
    }

    #[test]
    fn test_shadowing() {
        let tokens = quote!({
            let x = 5;
            x < 10
        });
        let result = extract_condition(tokens);
        // x is rebound to 5
        assert_eq!(result.to_string(), "(5) < 10");
    }

    #[test]
    fn test_multiple_uses_of_same_var() {
        let tokens = quote!({
            let a = 3;
            a + a == 6
        });
        let result = extract_condition(tokens);
        assert_eq!(result.to_string(), "(3) + (3) == 6");
    }

    #[test]
    fn test_flat_tokens_without_braces() {
        // Proc macros receive tokens without outer braces
        let tokens = quote!(
            let product = 10 * 2;
            product == 20
        );
        let result = extract_condition(tokens);
        assert_eq!(result.to_string(), "(10 * 2) == 20");
    }

    #[test]
    fn test_flat_tokens_chained() {
        let tokens = quote!(
            let a = 1 + 2;
            let b = a * 3;
            b == 9
        );
        let result = extract_condition(tokens);
        assert_eq!(result.to_string(), "((1 + 2) * 3) == 9");
    }

    #[test]
    fn test_typed_let_binding() {
        // `let x: i32 = 5` wraps Pat::Ident inside Pat::Type
        let tokens = quote!({
            let x: i32 = 5;
            x > 0
        });
        let result = extract_condition(tokens);
        assert_eq!(result.to_string(), "(5) > 0");
    }

    #[test]
    fn test_typed_let_binding_flat() {
        let tokens = quote!(
            let val: u64 = 42;
            val == 42
        );
        let result = extract_condition(tokens);
        assert_eq!(result.to_string(), "(42) == 42");
    }

    /// Block without trailing semicolon extracts the final expression (#1819).
    #[test]
    fn test_block_without_trailing_semi_extracts() {
        let tokens = quote!({ x > 0 });
        let result = extract_condition(tokens);
        assert_eq!(result.to_string(), "x > 0");
    }

    /// Block WITH trailing semicolon falls through to fallback (#1819).
    /// `{ x > 0; }` evaluates to () in Rust — the condition is nonsensical.
    #[test]
    fn test_block_with_trailing_semi_falls_through() {
        let tokens = quote!({
            x > 0;
        });
        let result = extract_condition(tokens);
        // With trailing semicolon, extract_condition_from_block returns None.
        // The fallback path in extract_condition returns the expression as-is
        // (via the Expr::Block branch or the final fallback).
        // The key invariant: the result should NOT be just "x > 0" extracted
        // from the block. It should be the full block expression or the
        // original tokens.
        let result_str = result.to_string();
        assert!(
            result_str != "x > 0",
            "Trailing semicolon should NOT extract 'x > 0' — block evaluates to () (#1819), got: {}",
            result_str
        );
    }

    // ========================================================================
    // Two-argument form tests (Verus-style assert_by)
    // ========================================================================

    #[test]
    fn test_parse_two_arg_simple_condition_with_block() {
        let tokens = quote!(x > 0, {
            helper();
        });
        match parse_assert_by(tokens) {
            AssertByParsed::WithProofBlock {
                condition,
                proof_block,
            } => {
                assert_eq!(condition.to_string(), "x > 0");
                assert!(
                    proof_block.to_string().contains("helper"),
                    "proof block should contain helper call, got: {}",
                    proof_block
                );
            }
            AssertByParsed::Single { .. } => {
                panic!("Expected WithProofBlock for two-arg form");
            }
        }
    }

    #[test]
    fn test_parse_two_arg_complex_condition() {
        let tokens = quote!(a + b == c, {
            step1();
            step2();
        });
        match parse_assert_by(tokens) {
            AssertByParsed::WithProofBlock { condition, .. } => {
                assert_eq!(condition.to_string(), "a + b == c");
            }
            AssertByParsed::Single { .. } => {
                panic!("Expected WithProofBlock for two-arg form");
            }
        }
    }

    #[test]
    fn test_parse_single_arg_still_works() {
        let tokens = quote!(x > 0);
        match parse_assert_by(tokens) {
            AssertByParsed::Single { condition, .. } => {
                assert_eq!(condition.to_string(), "x > 0");
            }
            AssertByParsed::WithProofBlock { .. } => {
                panic!("Expected Single for single-arg form");
            }
        }
    }

    #[test]
    fn test_parse_single_arg_block_with_lets() {
        let tokens = quote!(
            let a = 1;
            let b = 2;
            a + b == 3
        );
        match parse_assert_by(tokens) {
            AssertByParsed::Single { condition, .. } => {
                let cond_str = condition.to_string();
                assert!(
                    cond_str.contains("1") && cond_str.contains("2") && cond_str.contains("== 3"),
                    "Expected substituted condition with 1, 2, == 3, got: {}",
                    cond_str
                );
            }
            AssertByParsed::WithProofBlock { .. } => {
                panic!("Expected Single for block with let bindings");
            }
        }
    }

    #[test]
    fn test_parse_two_arg_empty_proof_block() {
        let tokens = quote!(true, {});
        match parse_assert_by(tokens) {
            AssertByParsed::WithProofBlock { condition, .. } => {
                assert_eq!(condition.to_string(), "true");
            }
            AssertByParsed::Single { .. } => {
                panic!("Expected WithProofBlock for two-arg form with empty block");
            }
        }
    }

    #[test]
    fn test_parse_three_args_falls_through_to_single() {
        // Three comma-separated expressions should not match two-arg form
        let tokens = quote!(a, b, c);
        match parse_assert_by(tokens) {
            AssertByParsed::Single { .. } => {}
            AssertByParsed::WithProofBlock { .. } => {
                panic!("Three args should not match WithProofBlock");
            }
        }
    }

    #[test]
    fn test_parse_two_arg_second_not_block_falls_through() {
        // Two args but second is not a block → falls through to single
        let tokens = quote!(a > 0, b > 0);
        match parse_assert_by(tokens) {
            AssertByParsed::Single { .. } => {}
            AssertByParsed::WithProofBlock { .. } => {
                panic!("Non-block second arg should not match WithProofBlock");
            }
        }
    }
}
