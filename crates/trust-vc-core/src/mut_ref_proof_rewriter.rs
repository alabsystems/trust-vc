// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MutRefRewriter: block/stmt/expr traversal and SSA shadow versioning.

use super::helpers::{
    is_assign_binop, is_supported_referent_type, member_name, opaque_ty, place_display,
    place_expr_tokens, place_key, shadow_ident, simple_path_ident, PlaceKey,
};
use super::MutRefParam;
use crate::ir_place::TrustVcPlace;
use quote::quote;
use std::collections::BTreeMap;
use syn::fold::{self, Fold};
use syn::{Block, Expr, ExprBlock, ExprPath, ExprUnary, Ident, Stmt, UnOp};

pub(super) struct MutRefRewriter {
    pub(super) params: BTreeMap<String, MutRefParam>,
    pub(super) place_versions: BTreeMap<PlaceKey, usize>,
    pub(super) used_places: BTreeMap<PlaceKey, TrustVcPlace>,
    pub(super) nested_block_depth: usize,
    pub(super) control_flow_depth: usize,
    pub(super) errors: Vec<syn::Error>,
}

#[path = "mut_ref_proof_rewriter_macros.rs"]
mod macro_rewriting;

impl MutRefRewriter {
    pub(super) fn rewrite_block(&mut self, mut block: Block) -> Block {
        let mut rewritten = Vec::with_capacity(block.stmts.len());
        for stmt in block.stmts {
            match stmt {
                Stmt::Local(local) => rewritten.push(Stmt::Local(self.fold_local(local))),
                Stmt::Item(item) => rewritten.push(Stmt::Item(fold::fold_item(self, item))),
                Stmt::Macro(stmt_macro) => {
                    rewritten.push(Stmt::Macro(self.rewrite_stmt_macro(stmt_macro)))
                }
                Stmt::Expr(expr, semi) => self.rewrite_expr_stmt(expr, semi, &mut rewritten),
            }
        }
        block.stmts = rewritten;
        block
    }

    fn rewrite_expr_stmt(&mut self, expr: Expr, semi: Option<syn::Token![;]>, out: &mut Vec<Stmt>) {
        if let Some(stmts) = self.expand_top_level_store(&expr) {
            out.extend(stmts);
            return;
        }
        out.push(Stmt::Expr(self.fold_expr(expr), semi));
    }

    fn expand_top_level_store(&mut self, expr: &Expr) -> Option<Vec<Stmt>> {
        if self.nested_block_depth != 0 || self.control_flow_depth != 0 {
            return None;
        }

        let Expr::Assign(assign) = expr else {
            return None;
        };
        let place = self.supported_place(assign.left.as_ref())?;
        if !self.is_supported_place_use(&place) {
            return None;
        }
        let rhs = self.fold_expr((*assign.right).clone());
        let next_version = self.bump_version(&place);
        let shadow_ident = shadow_ident(&place, next_version);
        let shadow_name = shadow_ident.to_string();
        let display_name = format!("{}@{}", place_display(&place), next_version);
        let rhs_string = quote!(#rhs).to_string();
        let left = (*assign.left).clone();
        let support_root = crate::macro_support_root();

        let assign_stmt: Stmt = syn::parse_quote! {
            #left = #rhs;
        };
        let shadow_stmt: Stmt = syn::parse_quote! {
            let #shadow_ident = #rhs;
        };
        let declare_stmt: Stmt = syn::parse_quote! {
            #support_root::verify_macro::collect_variable_runtime(#shadow_name, &#shadow_ident);
        };
        let alias_stmt: Stmt = syn::parse_quote! {
            #support_root::register_counterexample_display(
                #shadow_name.to_string(),
                #display_name.to_string(),
                true
            );
        };
        let binding_stmt: Stmt = syn::parse_quote! {
            #support_root::verify_macro::collect_let_binding(
                #shadow_name.to_string(),
                #rhs_string.to_string()
            );
        };
        Some(vec![
            assign_stmt,
            shadow_stmt,
            declare_stmt,
            alias_stmt,
            binding_stmt,
        ])
    }

    fn with_nested_block<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.nested_block_depth += 1;
        let out = f(self);
        self.nested_block_depth -= 1;
        out
    }

    fn with_control_flow<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.control_flow_depth += 1;
        let out = f(self);
        self.control_flow_depth -= 1;
        out
    }

    fn supported_place(&self, expr: &Expr) -> Option<TrustVcPlace> {
        self.supported_place_inner(expr, false)
    }

    fn supported_place_inner(&self, expr: &Expr, allow_bare_param: bool) -> Option<TrustVcPlace> {
        match expr {
            Expr::Paren(paren) => self.supported_place_inner(paren.expr.as_ref(), allow_bare_param),
            Expr::Path(path) if allow_bare_param => path
                .path
                .get_ident()
                .map(Ident::to_string)
                .filter(|name| self.params.contains_key(name))
                .map(|param_name| TrustVcPlace::root(param_name, opaque_ty())),
            Expr::Unary(ExprUnary {
                op: UnOp::Deref(_),
                expr,
                ..
            }) => {
                let Expr::Path(path) = expr.as_ref() else {
                    return None;
                };
                path.path
                    .get_ident()
                    .map(Ident::to_string)
                    .filter(|name| self.params.contains_key(name))
                    .map(|param_name| TrustVcPlace::root(param_name, opaque_ty()))
            }
            Expr::Field(field) => {
                let base = self.supported_place_inner(field.base.as_ref(), true)?;
                let field_name = member_name(&field.member);
                Some(base.field(field_name, opaque_ty()))
            }
            _ => None,
        }
    }

    fn current_shadow_expr(&mut self, place: &TrustVcPlace) -> Expr {
        self.record_place_use(place.clone());
        let ident = shadow_ident(place, self.current_version(place));
        syn::parse_quote!(#ident)
    }

    fn entry_shadow_expr(&mut self, place: &TrustVcPlace) -> Expr {
        self.record_place_use(place.clone());
        let ident = shadow_ident(place, 0);
        syn::parse_quote!(#ident)
    }

    fn current_version(&self, place: &TrustVcPlace) -> usize {
        self.place_versions
            .get(&place_key(place))
            .copied()
            .unwrap_or(0)
    }

    fn bump_version(&mut self, place: &TrustVcPlace) -> usize {
        self.record_place_use(place.clone());
        let key = place_key(place);
        let version = self.place_versions.entry(key).or_insert(0);
        *version += 1;
        *version
    }

    fn record_place_use(&mut self, place: TrustVcPlace) {
        let key = place_key(&place);
        self.used_places.entry(key).or_insert(place);
    }

    fn is_supported_place_use(&self, place: &TrustVcPlace) -> bool {
        if !place.projections.is_empty() {
            return true;
        }

        let Some(param) = self.params.get(&place.root_name) else {
            return false;
        };
        let referent_ty = crate::local_vars::extract_type_string(&param.referent_ty);
        is_supported_referent_type(&referent_ty)
    }

    fn push_place_type_error(&mut self, span: impl quote::ToTokens, place: &TrustVcPlace) {
        let Some(param) = self.params.get(&place.root_name) else {
            self.push_error(
                span,
                format!(
                    "trust_vc::proof mutable-reference rewrite found unknown place root `{}`",
                    place.root_name
                ),
            );
            return;
        };
        let referent_ty = crate::local_vars::extract_type_string(&param.referent_ty);
        self.push_error(
            span,
            format!(
                "trust_vc::proof mutable-reference MVP supports direct `{}` uses only when the referent type is bool/integer, not `{}`",
                place_display(place),
                referent_ty
            ),
        );
    }

    pub(super) fn entry_statements(&self) -> Vec<Stmt> {
        let support_root = crate::macro_support_root();
        let mut stmts = Vec::new();
        for place in self.used_places.values() {
            if !self.is_supported_place_use(place) {
                continue;
            }

            let shadow_ident = shadow_ident(place, 0);
            let shadow_name = shadow_ident.to_string();
            let display_name = format!("{}@0", place_display(place));
            let Some(param) = self.params.get(&place.root_name) else {
                continue;
            };
            let place_expr = place_expr_tokens(place, &param.ident);

            let entry_stmt: Stmt = syn::parse_quote! {
                let #shadow_ident = #place_expr;
            };
            let declare_stmt: Stmt = syn::parse_quote! {
                #support_root::verify_macro::collect_variable_runtime(#shadow_name, &#shadow_ident);
            };
            let alias_stmt: Stmt = syn::parse_quote! {
                #support_root::register_counterexample_display(
                    #shadow_name.to_string(),
                    #display_name.to_string(),
                    true
                );
            };
            let capture_stmt: Stmt = syn::parse_quote! {
                #support_root::collect_let_binding_runtime_value_from_ref(
                    #shadow_name,
                    &#shadow_ident
                );
            };

            stmts.push(entry_stmt);
            stmts.push(declare_stmt);
            stmts.push(alias_stmt);
            stmts.push(capture_stmt);
        }
        stmts
    }

    fn expr_contains_supported_param(&self, expr: &Expr) -> bool {
        struct Finder<'a> {
            params: &'a BTreeMap<String, MutRefParam>,
            found: bool,
        }

        impl<'a> syn::visit::Visit<'_> for Finder<'a> {
            fn visit_expr_path(&mut self, expr_path: &ExprPath) {
                if expr_path
                    .path
                    .get_ident()
                    .map(Ident::to_string)
                    .is_some_and(|name| self.params.contains_key(&name))
                {
                    self.found = true;
                }
                syn::visit::visit_expr_path(self, expr_path);
            }
        }

        let mut finder = Finder {
            params: &self.params,
            found: false,
        };
        syn::visit::Visit::visit_expr(&mut finder, expr);
        finder.found
    }

    fn push_error(&mut self, span: impl quote::ToTokens, message: impl Into<String>) {
        self.errors
            .push(syn::Error::new_spanned(span, message.into()));
    }
}

impl Fold for MutRefRewriter {
    fn fold_block(&mut self, block: Block) -> Block {
        self.with_nested_block(|this| this.rewrite_block(block))
    }

    fn fold_expr(&mut self, expr: Expr) -> Expr {
        match expr {
            Expr::Path(expr_path) => {
                if let Some(param_name) = simple_path_ident(&expr_path) {
                    if self.params.contains_key(&param_name) {
                        self.push_error(
                            &expr_path,
                            format!("mutable-reference proof parameters must be used via `*{param_name}` in supported expressions"),
                        );
                    }
                }
                Expr::Path(expr_path)
            }
            Expr::Field(expr_field) => {
                let original = Expr::Field(expr_field.clone());
                if let Some(place) = self.supported_place(&original) {
                    if self.is_supported_place_use(&place) {
                        return self.current_shadow_expr(&place);
                    }
                    self.push_place_type_error(&expr_field, &place);
                    return Expr::Field(expr_field);
                }
                if self.expr_contains_supported_param(expr_field.base.as_ref()) {
                    self.push_error(
                        &expr_field,
                        "trust_vc::proof mutable-reference MVP only supports direct field-place reads like `x.count` or `x.inner.count`",
                    );
                    return Expr::Field(expr_field);
                }
                Expr::Field(fold::fold_expr_field(self, expr_field))
            }
            Expr::Unary(expr_unary) => {
                let original = Expr::Unary(expr_unary.clone());
                if matches!(expr_unary.op, UnOp::Deref(_)) {
                    if let Some(place) = self.supported_place(&original) {
                        if self.is_supported_place_use(&place) {
                            return self.current_shadow_expr(&place);
                        }
                        self.push_place_type_error(&expr_unary, &place);
                        return Expr::Unary(expr_unary);
                    }
                    if self.expr_contains_supported_param(expr_unary.expr.as_ref()) {
                        self.push_error(
                            &expr_unary,
                            "trust_vc::proof mutable-reference MVP only supports direct `*name` reads on `&mut` parameters",
                        );
                        return Expr::Unary(expr_unary);
                    }
                }
                Expr::Unary(fold::fold_expr_unary(self, expr_unary))
            }
            Expr::Assign(assign) => {
                if let Some(place) = self.supported_place(assign.left.as_ref()) {
                    if !self.is_supported_place_use(&place) {
                        self.push_place_type_error(&assign, &place);
                    } else {
                        self.push_error(
                            &assign,
                            "mutable-reference stores are supported only as top-level `*name = expr;` or `x.field = expr;` statements in proof bodies",
                        );
                    }
                } else if self.expr_contains_supported_param(assign.left.as_ref()) {
                    self.push_error(
                        &assign,
                        "mutable-reference stores are supported only as top-level `*name = expr;` or `x.field = expr;` statements in proof bodies",
                    );
                }
                Expr::Assign(fold::fold_expr_assign(self, assign))
            }
            Expr::Binary(binary) => {
                if is_assign_binop(&binary.op)
                    && (self.supported_place(binary.left.as_ref()).is_some()
                        || self.expr_contains_supported_param(binary.left.as_ref()))
                {
                    self.push_error(
                        &binary,
                        "compound assignment on mutable-reference proof parameters is not supported; use `*x = *x + expr`",
                    );
                }
                Expr::Binary(fold::fold_expr_binary(self, binary))
            }
            Expr::Macro(expr_macro) => {
                if let Some(resolved) = self.try_resolve_old_macro(&expr_macro) {
                    return resolved;
                }
                Expr::Macro(self.fold_expr_macro(expr_macro))
            }
            Expr::Block(expr_block) => {
                let attrs = expr_block.attrs;
                let label = expr_block.label;
                let block = self.fold_block(expr_block.block);
                Expr::Block(ExprBlock {
                    attrs,
                    label,
                    block,
                })
            }
            Expr::If(expr_if) => {
                self.with_control_flow(|this| Expr::If(fold::fold_expr_if(this, expr_if)))
            }
            Expr::Match(expr_match) => {
                self.with_control_flow(|this| Expr::Match(fold::fold_expr_match(this, expr_match)))
            }
            Expr::Loop(expr_loop) => {
                self.with_control_flow(|this| Expr::Loop(fold::fold_expr_loop(this, expr_loop)))
            }
            Expr::While(expr_while) => {
                self.with_control_flow(|this| Expr::While(fold::fold_expr_while(this, expr_while)))
            }
            Expr::ForLoop(expr_for) => self
                .with_control_flow(|this| Expr::ForLoop(fold::fold_expr_for_loop(this, expr_for))),
            other => fold::fold_expr(self, other),
        }
    }
}
