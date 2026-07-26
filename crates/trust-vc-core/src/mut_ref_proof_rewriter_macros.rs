// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Macro-token rewriting helpers for `MutRefRewriter`.

use super::super::helpers::{macro_name, simple_path_ident};
use super::MutRefRewriter;
use proc_macro2::TokenStream;
use quote::quote;
use syn::fold::Fold;
use syn::{Block, Expr, ExprMacro, StmtMacro};

impl MutRefRewriter {
    pub(super) fn rewrite_stmt_macro(&mut self, mut stmt: StmtMacro) -> StmtMacro {
        let Some(name) = macro_name(&stmt.mac) else {
            return stmt;
        };

        match name.as_str() {
            "assert" | "assume" | "requires" | "ghost_requires" | "ensures" => {
                stmt.mac.tokens = self.rewrite_expr_tokens(stmt.mac.tokens.clone());
            }
            "assert_by" => {
                stmt.mac.tokens = self.rewrite_assert_by_tokens(stmt.mac.tokens.clone());
            }
            _ => {}
        }

        stmt
    }

    fn rewrite_assert_by_tokens(&mut self, tokens: TokenStream) -> TokenStream {
        match crate::parse_assert_by(tokens.clone()) {
            crate::AssertByParsed::Single { tokens, .. } => {
                self.rewrite_block_or_expr_tokens(tokens)
            }
            crate::AssertByParsed::WithProofBlock {
                condition,
                proof_block,
            } => {
                let rewritten_condition = self.rewrite_expr_tokens(condition);
                let rewritten_block = syn::parse2::<Block>(proof_block.clone())
                    .map(|block| {
                        let rewritten = self.fold_block(block);
                        quote!(#rewritten)
                    })
                    .unwrap_or(proof_block);
                quote!(#rewritten_condition, #rewritten_block)
            }
        }
    }

    fn rewrite_block_or_expr_tokens(&mut self, tokens: TokenStream) -> TokenStream {
        if let Ok(block) = syn::parse2::<Block>(tokens.clone()) {
            let rewritten = self.fold_block(block);
            return quote!(#rewritten);
        }
        self.rewrite_expr_tokens(tokens)
    }

    fn rewrite_expr_tokens(&mut self, tokens: TokenStream) -> TokenStream {
        syn::parse2::<Expr>(tokens.clone())
            .map(|expr| {
                let rewritten = self.fold_expr(expr);
                quote!(#rewritten)
            })
            .unwrap_or(tokens)
    }

    pub(super) fn try_resolve_old_macro(&mut self, expr_macro: &ExprMacro) -> Option<Expr> {
        let name = macro_name(&expr_macro.mac)?;
        if name != "old" {
            return None;
        }

        let inner_expr = syn::parse2::<Expr>(expr_macro.mac.tokens.clone()).ok()?;

        if let Some(place) = self.supported_place(&inner_expr) {
            if self.is_supported_place_use(&place) {
                return Some(self.entry_shadow_expr(&place));
            }
            self.push_place_type_error(expr_macro, &place);
            return Some(Expr::Macro(expr_macro.clone()));
        }

        if let Expr::Path(expr_path) = &inner_expr {
            if let Some(param_name) = simple_path_ident(expr_path) {
                if self.params.contains_key(&param_name) {
                    self.push_error(
                        expr_macro,
                        format!("use `old!(*{param_name})` or `old!({param_name}.field)` for mutable-reference proof parameters; `old!({param_name})` is not supported"),
                    );
                    return Some(Expr::Macro(expr_macro.clone()));
                }
            }
        }

        None
    }

    pub(super) fn fold_expr_macro(&mut self, mut expr_macro: ExprMacro) -> ExprMacro {
        let Some(name) = macro_name(&expr_macro.mac) else {
            return expr_macro;
        };

        if name == "old" {
            if let Ok(inner_expr) = syn::parse2::<Expr>(expr_macro.mac.tokens.clone()) {
                let rewritten = self.fold_expr(inner_expr);
                expr_macro.mac.tokens = quote!(#rewritten);
            }
        }

        expr_macro
    }
}
