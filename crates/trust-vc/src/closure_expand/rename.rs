// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Scoped identifier renaming for closure contract expansion.
//!
//! Renames closure parameter identifiers while preserving method names,
//! path segments, struct field names, and local shadowing.

use std::collections::{BTreeMap, BTreeSet};

use proc_macro2::{Ident, TokenStream, TokenTree};
use quote::quote;
use syn::fold::{self, Fold};
use syn::{
    Arm, Block, Expr, ExprClosure, ExprForLoop, ExprIf, ExprPath, ExprWhile, FieldValue, Local,
    Macro, Member, Pat,
};

/// Rename identifiers in a token stream per the rename map.
///
/// Parses expression tokens into a syn AST when possible so only identifier
/// uses are renamed. This preserves method names, path segments, struct field
/// names, and shadowing. Falls back to token-level rewriting for token streams
/// that are not valid expressions.
pub(super) fn rename_idents(tokens: TokenStream, renames: &[(String, String)]) -> TokenStream {
    let rename_map: BTreeMap<String, String> = renames.iter().cloned().collect();
    if rename_map.is_empty() {
        return tokens;
    }

    if let Ok(expr) = syn::parse2::<Expr>(tokens.clone()) {
        let mut renamer = ScopedIdentRenamer::new(rename_map);
        let renamed = renamer.fold_expr(expr);
        return quote!(#renamed);
    }

    rename_idents_fallback(tokens, &rename_map, &BTreeSet::new())
}

struct ScopedIdentRenamer {
    renames: BTreeMap<String, String>,
    shadowed_scopes: Vec<BTreeSet<String>>,
}

impl ScopedIdentRenamer {
    fn new(renames: BTreeMap<String, String>) -> Self {
        Self {
            renames,
            shadowed_scopes: Vec::new(),
        }
    }

    fn with_scope<T>(&mut self, bindings: Vec<String>, f: impl FnOnce(&mut Self) -> T) -> T {
        let mut scope = BTreeSet::new();
        scope.extend(bindings);
        self.shadowed_scopes.push(scope);
        let output = f(self);
        self.shadowed_scopes.pop();
        output
    }

    fn add_bindings(&mut self, bindings: Vec<String>) {
        if bindings.is_empty() {
            return;
        }

        match self.shadowed_scopes.last_mut() {
            Some(scope) => scope.extend(bindings),
            None => self.shadowed_scopes.push(bindings.into_iter().collect()),
        }
    }

    fn is_shadowed(&self, name: &str) -> bool {
        self.shadowed_scopes
            .iter()
            .rev()
            .any(|scope| scope.contains(name))
    }

    fn shadowed_names(&self) -> BTreeSet<String> {
        self.shadowed_scopes
            .iter()
            .flat_map(|scope| scope.iter().cloned())
            .collect()
    }

    fn rename_macro_tokens(&mut self, tokens: TokenStream) -> TokenStream {
        if let Ok(expr) = syn::parse2::<Expr>(tokens.clone()) {
            let renamed = self.fold_expr(expr);
            return quote!(#renamed);
        }

        rename_idents_fallback(tokens, &self.renames, &self.shadowed_names())
    }
}

impl Fold for ScopedIdentRenamer {
    fn fold_block(&mut self, block: Block) -> Block {
        self.with_scope(Vec::new(), |this| fold::fold_block(this, block))
    }

    fn fold_local(&mut self, local: Local) -> Local {
        let bindings = collect_pat_bindings(&local.pat);
        let local = fold::fold_local(self, local);
        self.add_bindings(bindings);
        local
    }

    #[allow(clippy::indexing_slicing)] // invariant: `segments[0]` guarded by `segments.len() == 1`
    fn fold_expr_path(&mut self, mut expr: ExprPath) -> ExprPath {
        expr = fold::fold_expr_path(self, expr);

        if expr.qself.is_none()
            && expr.path.leading_colon.is_none()
            && expr.path.segments.len() == 1
        {
            let ident = &expr.path.segments[0].ident;
            let name = ident.to_string();
            if !self.is_shadowed(&name) {
                if let Some(to) = self.renames.get(&name) {
                    expr.path.segments[0].ident = Ident::new(to, ident.span());
                }
            }
        }

        expr
    }

    fn fold_expr_closure(&mut self, mut expr: ExprClosure) -> ExprClosure {
        let bindings = expr
            .inputs
            .iter()
            .flat_map(collect_pat_bindings)
            .collect::<Vec<_>>();
        let body = *expr.body;
        expr.body = Box::new(self.with_scope(bindings, |this| this.fold_expr(body)));
        expr
    }

    fn fold_expr_for_loop(&mut self, mut expr: ExprForLoop) -> ExprForLoop {
        let bindings = collect_pat_bindings(expr.pat.as_ref());
        expr.expr = Box::new(self.fold_expr(*expr.expr));
        let body = expr.body;
        expr.body = self.with_scope(bindings, |this| this.fold_block(body));
        expr
    }

    fn fold_expr_if(&mut self, mut expr: ExprIf) -> ExprIf {
        expr.cond = Box::new(self.fold_expr(*expr.cond));
        let bindings = condition_bindings(expr.cond.as_ref());
        let then_branch = expr.then_branch;
        expr.then_branch = self.with_scope(bindings, |this| this.fold_block(then_branch));
        if let Some((else_token, else_branch)) = expr.else_branch {
            expr.else_branch = Some((else_token, Box::new(self.fold_expr(*else_branch))));
        }
        expr
    }

    fn fold_expr_while(&mut self, mut expr: ExprWhile) -> ExprWhile {
        expr.cond = Box::new(self.fold_expr(*expr.cond));
        let bindings = condition_bindings(expr.cond.as_ref());
        let body = expr.body;
        expr.body = self.with_scope(bindings, |this| this.fold_block(body));
        expr
    }

    fn fold_arm(&mut self, arm: Arm) -> Arm {
        let bindings = collect_pat_bindings(&arm.pat);
        self.with_scope(bindings, |this| {
            let mut arm = arm;
            if let Some((if_token, guard)) = arm.guard {
                arm.guard = Some((if_token, Box::new(this.fold_expr(*guard))));
            }
            arm.body = Box::new(this.fold_expr(*arm.body));
            arm
        })
    }

    fn fold_field_value(&mut self, mut field: FieldValue) -> FieldValue {
        let shorthand_member = if field.colon_token.is_none() {
            match &field.member {
                Member::Named(ident) => Some(ident.to_string()),
                Member::Unnamed(_) => None,
            }
        } else {
            None
        };

        field = fold::fold_field_value(self, field);

        if let Some(member_name) = shorthand_member {
            let preserves_shorthand = matches!(
                &field.expr,
                Expr::Path(expr_path)
                    if expr_path.qself.is_none()
                    && expr_path.path.leading_colon.is_none()
                    && expr_path.path.is_ident(member_name.as_str())
            );
            if !preserves_shorthand {
                field.colon_token = Some(Default::default());
            }
        }

        field
    }

    fn fold_macro(&mut self, mut mac: Macro) -> Macro {
        mac.tokens = self.rename_macro_tokens(mac.tokens);
        mac
    }
}

fn collect_pat_bindings(pat: &Pat) -> Vec<String> {
    let mut bindings = Vec::new();
    collect_pat_bindings_into(pat, &mut bindings);
    bindings
}

fn collect_pat_bindings_into(pat: &Pat, bindings: &mut Vec<String>) {
    match pat {
        Pat::Ident(pat_ident) => {
            bindings.push(pat_ident.ident.to_string());
            if let Some((_at, subpat)) = &pat_ident.subpat {
                collect_pat_bindings_into(subpat, bindings);
            }
        }
        Pat::Or(pat_or) => {
            for case in &pat_or.cases {
                collect_pat_bindings_into(case, bindings);
            }
        }
        Pat::Paren(pat_paren) => collect_pat_bindings_into(&pat_paren.pat, bindings),
        Pat::Reference(pat_ref) => collect_pat_bindings_into(&pat_ref.pat, bindings),
        Pat::Slice(pat_slice) => {
            for elem in &pat_slice.elems {
                collect_pat_bindings_into(elem, bindings);
            }
        }
        Pat::Struct(pat_struct) => {
            for field in &pat_struct.fields {
                collect_pat_bindings_into(&field.pat, bindings);
            }
        }
        Pat::Tuple(pat_tuple) => {
            for elem in &pat_tuple.elems {
                collect_pat_bindings_into(elem, bindings);
            }
        }
        Pat::TupleStruct(pat_tuple_struct) => {
            for elem in &pat_tuple_struct.elems {
                collect_pat_bindings_into(elem, bindings);
            }
        }
        Pat::Type(pat_type) => collect_pat_bindings_into(&pat_type.pat, bindings),
        _ => {}
    }
}

fn condition_bindings(expr: &Expr) -> Vec<String> {
    match expr {
        Expr::Binary(expr_binary) if matches!(expr_binary.op, syn::BinOp::And(_)) => {
            let mut bindings = condition_bindings(&expr_binary.left);
            bindings.extend(condition_bindings(&expr_binary.right));
            bindings
        }
        Expr::Group(expr_group) => condition_bindings(&expr_group.expr),
        Expr::Let(expr_let) => collect_pat_bindings(expr_let.pat.as_ref()),
        Expr::Paren(expr_paren) => condition_bindings(&expr_paren.expr),
        _ => Vec::new(),
    }
}

#[allow(clippy::indexing_slicing)] // invariant: `token_vec[i-1]` guarded by `i > 0`; `token_vec[i-2]` by `i >= 2`
fn rename_idents_fallback(
    tokens: TokenStream,
    renames: &BTreeMap<String, String>,
    shadowed: &BTreeSet<String>,
) -> TokenStream {
    let token_vec: Vec<TokenTree> = tokens.into_iter().collect();
    let mut result = Vec::with_capacity(token_vec.len());

    for (i, tt) in token_vec.iter().enumerate() {
        match tt {
            TokenTree::Ident(ident) => {
                let after_dot = i > 0 && is_dot_punct(&token_vec[i - 1]);
                let after_double_colon = i >= 2
                    && is_colon_punct(&token_vec[i - 1])
                    && is_colon_punct(&token_vec[i - 2]);
                if after_dot || after_double_colon {
                    result.push(tt.clone());
                    continue;
                }
                let name = ident.to_string();
                if shadowed.contains(&name) {
                    result.push(tt.clone());
                    continue;
                }
                if let Some(to) = renames.get(&name) {
                    result.push(TokenTree::Ident(Ident::new(to, ident.span())));
                } else {
                    result.push(tt.clone());
                }
            }
            TokenTree::Group(group) => {
                let renamed = rename_idents_fallback(group.stream(), renames, shadowed);
                result.push(TokenTree::Group(proc_macro2::Group::new(
                    group.delimiter(),
                    renamed,
                )));
            }
            _ => result.push(tt.clone()),
        }
    }
    result.into_iter().collect()
}

fn is_dot_punct(tt: &TokenTree) -> bool {
    matches!(tt, TokenTree::Punct(p) if p.as_char() == '.')
}

fn is_colon_punct(tt: &TokenTree) -> bool {
    matches!(tt, TokenTree::Punct(p) if p.as_char() == ':')
}

#[cfg(test)]
#[path = "rename_tests.rs"]
mod tests;
