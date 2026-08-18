// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Trait specification and impl attribute expansion.
//!
//! Slice 1 of trait verification only parses the annotated Rust surface and
//! projects it into IR helpers. Later slices wire these helpers into the
//! verification pipeline.

use std::collections::HashSet;

use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};
use syn::{
    fold::Fold, spanned::Spanned, Arm, Attribute, Block, Expr, ExprClosure, ExprForLoop, ExprIf,
    ExprPath, ExprWhile, FnArg, Ident, ImplItem, ItemImpl, ItemTrait, Pat, ReturnType, Stmt,
    TraitItem, Type,
};

use crate::error::{TrustVcError, TrustVcResult};
use crate::extern_spec_helpers::{
    contract_attr_kind, encode_ident_component, extract_contracts, ContractAttrKind,
};
use crate::ir::{DatatypeVariant, TraitDecl, TraitImplDecl, TraitMethodDecl, TrustVcType};
use crate::local_vars::extract_type_string;

fn ir_path() -> TokenStream {
    let support_root = crate::macro_support_root();
    quote! { #support_root::ir }
}

#[doc(hidden)]
pub fn expand_trait_spec(input: ItemTrait) -> TokenStream {
    match parse_trait_decl(&input) {
        Ok(decl) => {
            let ir_path = ir_path();
            let helper_name = format_ident!(
                "__trust_vc_trait_decl_{}",
                encode_ident_component(&decl.name)
            );
            let decl_tokens = trait_decl_tokens(&decl);
            let mut stripped = input.clone();
            strip_trait_contract_attrs(&mut stripped);

            quote! {
                #stripped

                #[doc(hidden)]
                #[allow(dead_code)]
                fn #helper_name() -> #ir_path::TraitDecl {
                    #decl_tokens
                }
            }
        }
        Err(err) => trust_vc_error_into_compile_error(err),
    }
}

#[doc(hidden)]
pub fn expand_trait_impl(input: ItemImpl) -> TokenStream {
    // `default_ensures` is legal ONLY on a defaulted trait-method declaration.
    // Reject it on impl methods here so the proc-macro surface matches the
    // file-path surface: now that it is a recognized contract attribute,
    // `strip_impl_contract_attrs` below would otherwise silently DROP it.
    for impl_item in &input.items {
        if let ImplItem::Fn(method) = impl_item {
            if let Err(err) = crate::extern_spec_helpers::forbid_default_ensures(&method.attrs) {
                return trust_vc_error_into_compile_error(err);
            }
        }
    }
    match parse_trait_impl_decl(&input) {
        Ok(decl) => {
            let ir_path = ir_path();
            let helper_name = format_ident!(
                "__trust_vc_trait_impl_decl_{}_{}",
                encode_ident_component(&decl.trait_name),
                encode_type_component(&input.self_ty)
            );
            let decl_tokens = trait_impl_decl_tokens(&decl);
            let mut stripped = input.clone();
            strip_impl_contract_attrs(&mut stripped);

            quote! {
                #stripped

                #[doc(hidden)]
                #[allow(dead_code)]
                fn #helper_name() -> #ir_path::TraitImplDecl {
                    #decl_tokens
                }
            }
        }
        Err(err) => trust_vc_error_into_compile_error(err),
    }
}

pub(crate) fn parse_trait_decl(input: &ItemTrait) -> TrustVcResult<TraitDecl> {
    let trait_type_params = collect_type_params(&input.generics);
    let methods = input
        .items
        .iter()
        .filter_map(|item| match item {
            TraitItem::Fn(method) => Some(parse_trait_method_decl(method, &trait_type_params)),
            _ => None,
        })
        .collect::<TrustVcResult<Vec<_>>>()?;

    // Parse the trait's supertrait bounds (`trait T: Super`). Mirror
    // `append_trait_bounds`: keep only plain `Trait` bounds with the default
    // modifier (drop `?Sized`, lifetimes, `~const`, etc.), naming them by the
    // last path segment. Unit 6: a method declared on a supertrait is callable
    // through a `T`-bounded / `impl T for S` receiver, so its `requires` must be
    // discharged via the supertrait-method closure.
    let mut supertraits = Vec::new();
    for bound in &input.supertraits {
        let syn::TypeParamBound::Trait(trait_bound) = bound else {
            continue;
        };
        if !matches!(trait_bound.modifier, syn::TraitBoundModifier::None) {
            continue;
        }
        if let Some(segment) = trait_bound.path.segments.last() {
            let name = segment.ident.to_string();
            if !supertraits.contains(&name) {
                supertraits.push(name);
            }
        }
    }

    // The ORDERED type-parameter list (declaration order), distinct from the
    // unordered `collect_type_params` set used for typing: instantiation zips
    // these positionally against an impl's `trait_type_args`.
    let generics: Vec<String> = input
        .generics
        .type_params()
        .map(|param| param.ident.to_string())
        .collect();

    Ok(TraitDecl {
        name: input.ident.to_string(),
        methods,
        supertraits,
        generics,
    })
}

pub(crate) fn parse_trait_impl_decl(input: &ItemImpl) -> TrustVcResult<TraitImplDecl> {
    let (_, trait_path, _) = input.trait_.as_ref().ok_or_else(|| TrustVcError::Parse {
        context: "parse trait impl",
        source: syn::Error::new_spanned(
            input,
            "#[trust_vc::trait_impl] requires a trait implementation (`impl Trait for Type`)",
        ),
    })?;
    let impl_type_params = collect_type_params(&input.generics);
    let trait_name = trait_path
        .segments
        .last()
        .map(|segment| segment.ident.to_string())
        .ok_or_else(|| TrustVcError::Parse {
            context: "parse trait impl",
            source: syn::Error::new(
                trait_path.span(),
                "trait path must have at least one segment",
            ),
        })?;

    // The trait path's angle-bracketed type arguments (`impl T<u64> for S`),
    // in order. A TypeParam-bearing arg (blanket impl) is recorded as-is and
    // later fails instantiation eligibility; a non-type arg (const, binding)
    // becomes Opaque so arity stays aligned and every concreteness gate
    // rejects it fail-closed. Lifetimes are skipped: they never affect sorts.
    let trait_type_args: Vec<TrustVcType> = trait_path
        .segments
        .last()
        .map(|segment| match &segment.arguments {
            syn::PathArguments::AngleBracketed(args) => args
                .args
                .iter()
                .filter_map(|arg| match arg {
                    syn::GenericArgument::Type(ty) => {
                        Some(parse_trust_vc_type(ty, &impl_type_params, false))
                    }
                    syn::GenericArgument::Lifetime(_) => None,
                    _ => Some(TrustVcType::Opaque(
                        "<unsupported-trait-generic-arg>".to_string(),
                    )),
                })
                .collect(),
            _ => Vec::new(),
        })
        .unwrap_or_default();

    let concrete_type = parse_trust_vc_type(&input.self_ty, &impl_type_params, false);
    let type_name = encode_type_component(&input.self_ty);
    let method_bindings = input
        .items
        .iter()
        .filter_map(|item| match item {
            ImplItem::Fn(method) => Some((
                method.sig.ident.to_string(),
                format!("{type_name}__{}", method.sig.ident),
            )),
            _ => None,
        })
        .collect();

    // Capture the impl's associated-type bindings (`type X = T;`) so trait
    // method signatures mentioning `Self::X` can be normalized to the bound
    // type before registration / conformance. An unparseable RHS becomes
    // Opaque and keeps every downstream fail-closed guard intact.
    let assoc_type_bindings = input
        .items
        .iter()
        .filter_map(|item| match item {
            ImplItem::Type(assoc) => Some((
                assoc.ident.to_string(),
                parse_trust_vc_type(&assoc.ty, &impl_type_params, false),
            )),
            _ => None,
        })
        .collect();

    // `#[trust_vc::external]` (or bare `#[external]` after partial expansion):
    // the Verus external_trait_specification trust model — the impl's bodies
    // are trusted, so the body-conformance pass skips this impl while callers
    // still consume the trait contract.
    //
    // SOUNDNESS: match the WHOLE path, not just its last segment. This attribute
    // is a trust hatch — it skips body conformance while the trait's
    // `forall self, params. requires ==> ensures` axiom stays published to
    // callers — so which namespace asked for it is load-bearing. A trailing-
    // segment test also accepted `#[verifier::external]` and any other
    // `#[whatever::external]`, and in Verus `#[verifier::external]` means
    // "outside the verification universe", NOT "trust this body against a
    // published in-file contract". Honouring another tool's attribute as a
    // trust-vc trust grant is a proof hole with someone else's name on it.
    //
    // No in-corpus trigger today (the ported corpus uses
    // `#[verifier::external_body]`, a different ident), but this becomes an
    // ordinary shape the moment Phase 2 ingests Verus source — which is the
    // stated program, so the gate is tightened before the trigger arrives rather
    // than after.
    let is_external = input.attrs.iter().any(|attr| {
        let segments: Vec<String> = attr
            .path()
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect();
        match segments.as_slice() {
            // Bare `#[external]`, as produced by trust-vc's own partial expansion.
            [only] => only == "external",
            // Fully qualified: only trust-vc's own namespace grants this.
            [namespace, name] => namespace == "trust_vc" && name == "external",
            _ => false,
        }
    });

    Ok(
        TraitImplDecl::new(trait_name, concrete_type, method_bindings)
            .with_assoc_type_bindings(assoc_type_bindings)
            .with_external(is_external)
            .with_trait_type_args(trait_type_args),
    )
}

fn parse_trait_method_decl(
    method: &syn::TraitItemFn,
    trait_type_params: &HashSet<String>,
) -> TrustVcResult<TraitMethodDecl> {
    let known_type_params = merge_type_params(trait_type_params, &method.sig.generics);
    let (requires, mut ensures) = extract_contracts(&method.attrs, "trait_spec")?;
    normalize_trait_returns_contracts(&method.attrs, &mut ensures)?;
    let params = method
        .sig
        .inputs
        .iter()
        .enumerate()
        .filter_map(|(index, input)| match input {
            FnArg::Receiver(_) => None,
            FnArg::Typed(pat_type) => {
                let name = match pat_type.pat.as_ref() {
                    Pat::Ident(pat_ident) => pat_ident.ident.to_string(),
                    _ => format!("arg{index}"),
                };
                Some((
                    name,
                    parse_trust_vc_type(&pat_type.ty, &known_type_params, true),
                ))
            }
        })
        .collect();
    let return_type = match &method.sig.output {
        ReturnType::Default => TrustVcType::parse_or_opaque("()"),
        ReturnType::Type(_, ty) => parse_trust_vc_type(ty, &known_type_params, true),
    };

    let default_body = method.default.as_ref().map(|block| {
        // Extract the trailing expression from the block if it has exactly one.
        // This gives cleaner body text like "true" instead of "{ true }".
        if let [syn::Stmt::Expr(expr, None)] = block.stmts.as_slice() {
            return quote!(#expr).to_string();
        }
        quote!(#block).to_string()
    });

    // Harvest `default_ensures` — the extra postconditions the trait DEFAULT
    // BODY must establish. Legal ONLY on a defaulted method: a decl-only method
    // (no body) has no body to check them against, so it is ill-formed and fails
    // the file CLOSED. (`test_disallow_default_ensures1`.)
    let default_ensures = harvest_default_ensures(&method.attrs)?;
    if !default_ensures.is_empty() && method.default.is_none() {
        let attr = method
            .attrs
            .iter()
            .find(|attr| contract_attr_kind(attr) == Some(ContractAttrKind::DefaultEnsures));
        return Err(TrustVcError::Parse {
            context: "parse trait_spec contract attribute",
            source: syn::Error::new_spanned(
                attr.map_or_else(
                    || method.sig.ident.to_token_stream(),
                    ToTokens::to_token_stream,
                ),
                "default_ensures not allowed here",
            ),
        });
    }

    Ok(TraitMethodDecl {
        name: method.sig.ident.to_string(),
        params,
        return_type,
        requires,
        ensures,
        has_default: method.default.is_some(),
        default_body,
        default_ensures,
    })
}

/// Harvests each `#[default_ensures(EXPR)]` clause on a trait method into its
/// token-string form, applying the same result-binder rename that
/// `normalize_trait_returns_contracts` applies to `ensures` so the clause tracks
/// the return-value name (`test_default_ensures_ret_val_collision`).
///
/// `parse_expr_tokens_with_chains` is used so `r == i / 2` and chained
/// comparisons lower identically to `ensures`. The parenthesized `Meta::List`
/// form is required, mirroring `#[returns(..)]`/`#[ensures(..)]`.
fn harvest_default_ensures(attrs: &[Attribute]) -> TrustVcResult<Vec<String>> {
    let result_binding = trait_returns_result_binding(attrs)?;
    let mut clauses = Vec::new();
    for attr in attrs {
        if contract_attr_kind(attr) != Some(ContractAttrKind::DefaultEnsures) {
            continue;
        }
        let syn::Meta::List(meta_list) = &attr.meta else {
            return Err(TrustVcError::Parse {
                context: "parse trait_spec contract attribute",
                source: syn::Error::new_spanned(
                    attr,
                    "trait_spec: #[default_ensures] must use parenthesized form: \
                     #[default_ensures(expr)]",
                ),
            });
        };
        let expr =
            crate::chained_comparisons::parse_expr_tokens_with_chains(meta_list.tokens.clone())
                .map_err(|source| TrustVcError::Parse {
                    context: "parse trait_spec contract attribute",
                    source,
                })?;
        let mut clause = expr.to_token_stream().to_string();
        if let Some(binding) = &result_binding {
            clause = rename_result_binding(&clause, binding)?;
        }
        clauses.push(clause);
    }
    Ok(clauses)
}

/// Returns the trait method's `#[returns(<binder>)]` result-binder name when it
/// renames the result (a single ident other than `result`), so `default_ensures`
/// can track it exactly as `normalize_trait_returns_contracts` does for
/// `ensures`. The returns attribute's well-formedness (parenthesized form,
/// duplicate check) is already validated by `normalize_trait_returns_contracts`,
/// which runs first, so a malformed form is skipped here rather than
/// double-reported.
fn trait_returns_result_binding(attrs: &[Attribute]) -> TrustVcResult<Option<String>> {
    for attr in attrs {
        if contract_attr_kind(attr) != Some(ContractAttrKind::Returns) {
            continue;
        }
        let syn::Meta::List(meta_list) = &attr.meta else {
            continue;
        };
        let expr =
            crate::chained_comparisons::parse_expr_tokens_with_chains(meta_list.tokens.clone())
                .map_err(|source| TrustVcError::Parse {
                    context: "parse trait_spec contract attribute",
                    source,
                })?;
        if let Some(binding) = single_ident_expr(&expr) {
            if binding != "result" {
                return Ok(Some(binding));
            }
        }
    }
    Ok(None)
}

enum TraitReturnsContract {
    ResultBinding(String),
    EnsuresEquals(String),
}

fn normalize_trait_returns_contracts(
    attrs: &[Attribute],
    ensures: &mut Vec<String>,
) -> TrustVcResult<()> {
    let mut returns_contract: Option<TraitReturnsContract> = None;
    for attr in attrs {
        if contract_attr_kind(attr) != Some(crate::extern_spec_helpers::ContractAttrKind::Returns) {
            continue;
        }
        if returns_contract.is_some() {
            return Err(TrustVcError::Parse {
                context: "parse trait_spec contract attribute",
                source: syn::Error::new_spanned(attr, "trait_spec: duplicate returns attributes"),
            });
        }
        let meta_list = if let syn::Meta::List(meta_list) = &attr.meta {
            meta_list
        } else {
            return Err(TrustVcError::Parse {
                context: "parse trait_spec contract attribute",
                source: syn::Error::new_spanned(
                    attr,
                    "trait_spec: #[returns] must use parenthesized form: #[returns(expr)]",
                ),
            });
        };
        let expr =
            crate::chained_comparisons::parse_expr_tokens_with_chains(meta_list.tokens.clone())
                .map_err(|source| TrustVcError::Parse {
                    context: "parse trait_spec contract attribute",
                    source,
                })?;
        returns_contract = Some(match single_ident_expr(&expr) {
            Some(binding) => TraitReturnsContract::ResultBinding(binding),
            None => TraitReturnsContract::EnsuresEquals(result_equality_expr(&expr)),
        });
    }

    match returns_contract {
        Some(TraitReturnsContract::ResultBinding(binding)) if binding != "result" => {
            for condition in ensures {
                *condition = rename_result_binding(condition, &binding)?;
            }
        }
        Some(TraitReturnsContract::EnsuresEquals(expr)) => {
            ensures.push(expr);
        }
        _ => {}
    }

    Ok(())
}

fn result_equality_expr(expr: &Expr) -> String {
    let expr_text = expr.to_token_stream().to_string();
    if matches!(
        expr,
        Expr::Binary(binary) if matches!(binary.op, syn::BinOp::And(_) | syn::BinOp::Or(_))
    ) {
        format!("result == ({expr_text})")
    } else {
        format!("result == {expr_text}")
    }
}

fn single_ident_expr(expr: &Expr) -> Option<String> {
    let Expr::Path(ExprPath {
        qself: None, path, ..
    }) = expr
    else {
        return None;
    };
    (path.segments.len() == 1).then(|| path.segments[0].ident.to_string())
}

fn rename_result_binding(condition: &str, binding: &str) -> TrustVcResult<String> {
    let expr =
        crate::chained_comparisons::parse_expr_str_with_chains(condition).map_err(|source| {
            TrustVcError::Parse {
                context: "parse trait_spec contract attribute",
                source,
            }
        })?;
    let mut renamer = ResultBindingRenamer {
        from: binding.to_string(),
        to: format_ident!("result"),
        shadow_depth: 0,
    };
    Ok(renamer.fold_expr(expr).to_token_stream().to_string())
}

struct ResultBindingRenamer {
    from: String,
    to: Ident,
    shadow_depth: usize,
}

impl ResultBindingRenamer {
    fn is_shadowed(&self) -> bool {
        self.shadow_depth > 0
    }

    fn with_shadowed_scope<T>(&mut self, shadowed: bool, f: impl FnOnce(&mut Self) -> T) -> T {
        if shadowed {
            self.shadow_depth += 1;
        }
        let result = f(self);
        if shadowed {
            self.shadow_depth -= 1;
        }
        result
    }
}

impl Fold for ResultBindingRenamer {
    fn fold_expr_path(&mut self, mut expr_path: ExprPath) -> ExprPath {
        if !self.is_shadowed() && expr_path.qself.is_none() && expr_path.path.segments.len() == 1 {
            let segment = &mut expr_path.path.segments[0];
            if segment.ident == self.from {
                segment.ident = self.to.clone();
            }
        }
        syn::fold::fold_expr_path(self, expr_path)
    }

    fn fold_expr_closure(&mut self, expr_closure: ExprClosure) -> ExprClosure {
        let shadowed = expr_closure
            .inputs
            .iter()
            .any(|pat| pat_binds_ident(pat, &self.from));
        self.with_shadowed_scope(shadowed, |this| {
            syn::fold::fold_expr_closure(this, expr_closure)
        })
    }

    fn fold_expr_for_loop(&mut self, expr_for_loop: ExprForLoop) -> ExprForLoop {
        let ExprForLoop {
            attrs,
            label,
            for_token,
            pat,
            in_token,
            expr,
            body,
        } = expr_for_loop;
        let shadowed = pat_binds_ident(&pat, &self.from);
        ExprForLoop {
            attrs: self.fold_attributes(attrs),
            label: label.map(|label| self.fold_label(label)),
            for_token,
            pat: Box::new(self.fold_pat(*pat)),
            in_token,
            expr: Box::new(self.fold_expr(*expr)),
            body: self.with_shadowed_scope(shadowed, |this| this.fold_block(body)),
        }
    }

    fn fold_expr_if(&mut self, expr_if: ExprIf) -> ExprIf {
        let ExprIf {
            attrs,
            if_token,
            cond,
            then_branch,
            else_branch,
        } = expr_if;
        let shadowed = expr_let_binds_ident(&cond, &self.from);
        ExprIf {
            attrs: self.fold_attributes(attrs),
            if_token,
            cond: Box::new(self.fold_expr(*cond)),
            then_branch: self.with_shadowed_scope(shadowed, |this| this.fold_block(then_branch)),
            else_branch: else_branch
                .map(|(else_token, expr)| (else_token, Box::new(self.fold_expr(*expr)))),
        }
    }

    fn fold_expr_while(&mut self, expr_while: ExprWhile) -> ExprWhile {
        let ExprWhile {
            attrs,
            label,
            while_token,
            cond,
            body,
        } = expr_while;
        let shadowed = expr_let_binds_ident(&cond, &self.from);
        ExprWhile {
            attrs: self.fold_attributes(attrs),
            label: label.map(|label| self.fold_label(label)),
            while_token,
            cond: Box::new(self.fold_expr(*cond)),
            body: self.with_shadowed_scope(shadowed, |this| this.fold_block(body)),
        }
    }

    fn fold_arm(&mut self, arm: Arm) -> Arm {
        let Arm {
            attrs,
            pat,
            guard,
            fat_arrow_token,
            body,
            comma,
        } = arm;
        let shadowed = pat_binds_ident(&pat, &self.from);
        let pat = self.fold_pat(pat);
        self.with_shadowed_scope(shadowed, |this| Arm {
            attrs: this.fold_attributes(attrs),
            pat,
            guard: guard.map(|(if_token, expr)| (if_token, Box::new(this.fold_expr(*expr)))),
            fat_arrow_token,
            body: Box::new(this.fold_expr(*body)),
            comma,
        })
    }

    fn fold_block(&mut self, block: Block) -> Block {
        let mut local_shadows = 0usize;
        let stmts = block
            .stmts
            .into_iter()
            .map(|stmt| match stmt {
                Stmt::Local(local) => {
                    let shadowed = pat_binds_ident(&local.pat, &self.from);
                    let local = self.fold_local(local);
                    if shadowed {
                        self.shadow_depth += 1;
                        local_shadows += 1;
                    }
                    Stmt::Local(local)
                }
                other => self.fold_stmt(other),
            })
            .collect();
        self.shadow_depth -= local_shadows;
        Block {
            brace_token: block.brace_token,
            stmts,
        }
    }
}

fn expr_let_binds_ident(expr: &Expr, ident: &str) -> bool {
    match expr {
        Expr::Let(expr_let) => pat_binds_ident(&expr_let.pat, ident),
        Expr::Binary(binary) if matches!(binary.op, syn::BinOp::And(_)) => {
            expr_let_binds_ident(&binary.left, ident) || expr_let_binds_ident(&binary.right, ident)
        }
        Expr::Group(group) => expr_let_binds_ident(&group.expr, ident),
        Expr::Paren(paren) => expr_let_binds_ident(&paren.expr, ident),
        _ => false,
    }
}

fn pat_binds_ident(pat: &Pat, ident: &str) -> bool {
    match pat {
        Pat::Ident(pat_ident) => {
            pat_ident.ident == ident
                || pat_ident
                    .subpat
                    .as_ref()
                    .is_some_and(|(_, subpat)| pat_binds_ident(subpat, ident))
        }
        Pat::Or(pat_or) => pat_or.cases.iter().any(|case| pat_binds_ident(case, ident)),
        Pat::Paren(pat_paren) => pat_binds_ident(&pat_paren.pat, ident),
        Pat::Reference(pat_reference) => pat_binds_ident(&pat_reference.pat, ident),
        Pat::Slice(pat_slice) => pat_slice
            .elems
            .iter()
            .any(|elem| pat_binds_ident(elem, ident)),
        Pat::Struct(pat_struct) => pat_struct
            .fields
            .iter()
            .any(|field| pat_binds_ident(&field.pat, ident)),
        Pat::Tuple(pat_tuple) => pat_tuple
            .elems
            .iter()
            .any(|elem| pat_binds_ident(elem, ident)),
        Pat::TupleStruct(pat_tuple_struct) => pat_tuple_struct
            .elems
            .iter()
            .any(|elem| pat_binds_ident(elem, ident)),
        Pat::Type(pat_type) => pat_binds_ident(&pat_type.pat, ident),
        Pat::Const(_)
        | Pat::Lit(_)
        | Pat::Macro(_)
        | Pat::Path(_)
        | Pat::Range(_)
        | Pat::Rest(_)
        | Pat::Verbatim(_)
        | Pat::Wild(_) => false,
        _ => false,
    }
}

fn collect_type_params(generics: &syn::Generics) -> HashSet<String> {
    generics
        .type_params()
        .map(|param| param.ident.to_string())
        .collect()
}

fn merge_type_params(base: &HashSet<String>, generics: &syn::Generics) -> HashSet<String> {
    let mut merged = base.clone();
    merged.extend(collect_type_params(generics));
    merged
}

fn parse_trust_vc_type(
    ty: &Type,
    known_type_params: &HashSet<String>,
    self_is_poly: bool,
) -> TrustVcType {
    let ty_str = extract_type_string(ty);
    if self_is_poly && ty_str == "Self" {
        TrustVcType::Poly
    } else if known_type_params.contains(&ty_str) {
        TrustVcType::TypeParam(ty_str)
    } else {
        TrustVcType::parse_or_opaque(&ty_str)
    }
}

fn encode_type_component(ty: &Type) -> String {
    encode_ident_component(&extract_type_string(ty))
}

fn strip_trait_contract_attrs(item: &mut ItemTrait) {
    for trait_item in &mut item.items {
        if let TraitItem::Fn(method) = trait_item {
            strip_contract_attrs(&mut method.attrs);
        }
    }
}

fn strip_impl_contract_attrs(item: &mut ItemImpl) {
    for impl_item in &mut item.items {
        if let ImplItem::Fn(method) = impl_item {
            strip_contract_attrs(&mut method.attrs);
        }
    }
}

fn strip_contract_attrs(attrs: &mut Vec<Attribute>) {
    attrs.retain(|attr| contract_attr_kind(attr).is_none());
}

fn trust_vc_error_into_compile_error(err: TrustVcError) -> TokenStream {
    match err {
        TrustVcError::Parse { source, .. } => source.to_compile_error(),
        other => {
            syn::Error::new(proc_macro2::Span::call_site(), other.to_string()).to_compile_error()
        }
    }
}

fn trait_decl_tokens(decl: &TraitDecl) -> TokenStream {
    let ir_path = ir_path();
    let name = &decl.name;
    let methods = decl.methods.iter().map(trait_method_tokens);
    // Round-trip the supertraits (unit 6): without this, a macro-expanded trait
    // decl would lose its supertrait names and the caller-side supertrait
    // `requires` discharge would silently no-op. Same for the generics list —
    // dropping it here would silently de-parameterize macro-expanded traits.
    let supertraits = decl.supertraits.iter();
    let generics = decl.generics.iter();
    quote! {
        #ir_path::TraitDecl::new(#name, vec![#(#methods),*])
            .with_supertraits(vec![#(#supertraits.to_string()),*])
            .with_generics(vec![#(#generics.to_string()),*])
    }
}

fn trait_method_tokens(method: &TraitMethodDecl) -> TokenStream {
    let ir_path = ir_path();
    let name = &method.name;
    let params = method.params.iter().map(|(param_name, ty)| {
        let ty_tokens = trust_vc_type_tokens(ty);
        quote! { (#param_name.to_string(), #ty_tokens) }
    });
    let return_type = trust_vc_type_tokens(&method.return_type);
    let requires = method.requires.iter();
    let ensures = method.ensures.iter();
    let has_default = method.has_default;
    let default_body_tokens = match &method.default_body {
        Some(body) => quote! { Some(#body.to_string()) },
        None => quote! { None },
    };
    let default_ensures = method.default_ensures.iter();
    quote! {
        #ir_path::TraitMethodDecl::new(
            #name,
            vec![#(#params),*],
            #return_type,
            vec![#(#requires.to_string()),*],
            vec![#(#ensures.to_string()),*],
            #has_default,
            #default_body_tokens,
        )
        .with_default_ensures(vec![#(#default_ensures.to_string()),*])
    }
}

fn trait_impl_decl_tokens(decl: &TraitImplDecl) -> TokenStream {
    let ir_path = ir_path();
    let trait_name = &decl.trait_name;
    let concrete_type = trust_vc_type_tokens(&decl.concrete_type);
    let method_bindings = decl
        .method_bindings
        .iter()
        .map(|(trait_method, concrete_method)| {
            quote! { (#trait_method.to_string(), #concrete_method.to_string()) }
        });
    let assoc_type_bindings = decl.assoc_type_bindings.iter().map(|(assoc_name, ty)| {
        let ty_tokens = trust_vc_type_tokens(ty);
        quote! { (#assoc_name.to_string(), #ty_tokens) }
    });
    let is_external = decl.is_external;
    let trait_type_args = decl.trait_type_args.iter().map(trust_vc_type_tokens);
    quote! {
        #ir_path::TraitImplDecl::new(
            #trait_name,
            #concrete_type,
            vec![#(#method_bindings),*],
        )
        .with_assoc_type_bindings(vec![#(#assoc_type_bindings),*])
        .with_external(#is_external)
        .with_trait_type_args(vec![#(#trait_type_args),*])
    }
}

fn trust_vc_type_tokens(ty: &TrustVcType) -> TokenStream {
    let ir_path = ir_path();
    match ty {
        TrustVcType::Unit => quote!(#ir_path::TrustVcType::Unit),
        TrustVcType::Bool => quote!(#ir_path::TrustVcType::Bool),
        TrustVcType::Int { width } => quote!(#ir_path::TrustVcType::Int { width: #width }),
        TrustVcType::Uint { width } => {
            quote!(#ir_path::TrustVcType::Uint { width: #width })
        }
        TrustVcType::MathInt => quote!(#ir_path::TrustVcType::MathInt),
        TrustVcType::Nat => quote!(#ir_path::TrustVcType::Nat),
        TrustVcType::Real => quote!(#ir_path::TrustVcType::Real),
        TrustVcType::Float { width } => {
            quote!(#ir_path::TrustVcType::Float { width: #width })
        }
        TrustVcType::Seq(inner) => {
            let inner_tokens = trust_vc_type_tokens(inner);
            quote!(#ir_path::TrustVcType::Seq(Box::new(#inner_tokens)))
        }
        TrustVcType::Array(inner, len) => {
            let inner_tokens = trust_vc_type_tokens(inner);
            quote!(#ir_path::TrustVcType::Array(Box::new(#inner_tokens), #len))
        }
        TrustVcType::Set(inner) => {
            let inner_tokens = trust_vc_type_tokens(inner);
            quote!(#ir_path::TrustVcType::Set(Box::new(#inner_tokens)))
        }
        TrustVcType::Multiset(inner) => {
            let inner_tokens = trust_vc_type_tokens(inner);
            quote!(#ir_path::TrustVcType::Multiset(Box::new(#inner_tokens)))
        }
        TrustVcType::Map(key, value) => {
            let key_tokens = trust_vc_type_tokens(key);
            let value_tokens = trust_vc_type_tokens(value);
            quote!(#ir_path::TrustVcType::Map(Box::new(#key_tokens), Box::new(#value_tokens)))
        }
        TrustVcType::SpecFn(args, ret) => {
            let arg_tokens = args.iter().map(trust_vc_type_tokens);
            let ret_tokens = trust_vc_type_tokens(ret);
            quote!(#ir_path::TrustVcType::SpecFn(vec![#(#arg_tokens),*], Box::new(#ret_tokens)))
        }
        TrustVcType::Datatype { name, variants } => {
            let variants = variants.iter().map(datatype_variant_tokens);
            quote! {
                #ir_path::TrustVcType::Datatype {
                    name: #name.to_string(),
                    variants: vec![#(#variants),*],
                }
            }
        }
        TrustVcType::TypeParam(name) => {
            quote!(#ir_path::TrustVcType::TypeParam(#name.to_string()))
        }
        TrustVcType::RecursiveRef(name) => {
            quote!(#ir_path::TrustVcType::RecursiveRef(#name.to_string()))
        }
        TrustVcType::Poly => quote!(#ir_path::TrustVcType::Poly),
        TrustVcType::Opaque(name) => {
            quote!(#ir_path::TrustVcType::Opaque(#name.to_string()))
        }
        TrustVcType::Char => quote!(#ir_path::TrustVcType::Char),
        TrustVcType::StrSlice => quote!(#ir_path::TrustVcType::StrSlice),
        TrustVcType::String => quote!(#ir_path::TrustVcType::String),
    }
}

fn datatype_variant_tokens(variant: &DatatypeVariant) -> TokenStream {
    let ir_path = ir_path();
    let name = &variant.name;
    let fields = variant.fields.iter().map(|(field_name, ty)| {
        let ty_tokens = trust_vc_type_tokens(ty);
        quote! { (#field_name.to_string(), #ty_tokens) }
    });
    quote! {
        #ir_path::DatatypeVariant {
            name: #name.to_string(),
            fields: vec![#(#fields),*],
        }
    }
}

#[cfg(test)]
mod trait_generic_parse_tests {
    use super::*;

    fn parse_trait(src: &str) -> TraitDecl {
        let item: ItemTrait = syn::parse_str(src).expect("parse trait");
        parse_trait_decl(&item).expect("trait decl")
    }

    fn parse_impl(src: &str) -> TraitImplDecl {
        let item: ItemImpl = syn::parse_str(src).expect("parse impl");
        parse_trait_impl_decl(&item).expect("trait impl decl")
    }

    #[test]
    fn trait_generics_are_recorded_in_declaration_order() {
        let decl = parse_trait("trait T<A, B> { fn m(&self, a: A) -> B; }");
        assert_eq!(decl.generics, vec!["A".to_string(), "B".to_string()]);
    }

    #[test]
    fn non_generic_trait_records_empty_generics() {
        let decl = parse_trait("trait T { fn m(&self) -> bool; }");
        assert!(decl.generics.is_empty());
    }

    #[test]
    fn impl_trait_type_args_are_recorded() {
        let decl = parse_impl("impl T<u64> for S { fn m(&self, a: u64) -> u64 { a } }");
        assert_eq!(decl.trait_type_args, vec![TrustVcType::Uint { width: 64 }]);
    }

    #[test]
    fn impl_without_type_args_records_empty() {
        let decl = parse_impl("impl T for S { fn m(&self) -> bool { true } }");
        assert!(decl.trait_type_args.is_empty());
    }

    #[test]
    fn blanket_impl_records_type_param_bearing_arg() {
        let decl = parse_impl("impl<C> T<C> for S { fn m(&self, a: C) -> bool { true } }");
        assert_eq!(
            decl.trait_type_args,
            vec![TrustVcType::TypeParam("C".to_string())]
        );
    }

    #[test]
    fn lifetime_args_are_skipped_const_args_fail_closed_as_opaque() {
        let decl = parse_impl("impl T<'static, 3> for S { }");
        assert_eq!(
            decl.trait_type_args,
            vec![TrustVcType::Opaque(
                "<unsupported-trait-generic-arg>".to_string()
            )]
        );
    }

    #[test]
    fn trait_decl_tokens_round_trip_generics() {
        let decl = parse_trait("trait T<A> { fn m(&self, a: A) -> A; }");
        let tokens = trait_decl_tokens(&decl).to_string();
        assert!(
            tokens.contains("with_generics"),
            "macro round-trip must carry the generics list, got: {tokens}"
        );
        assert!(
            tokens.contains("\"A\""),
            "generic name must appear: {tokens}"
        );
    }

    #[test]
    fn trait_impl_decl_tokens_round_trip_type_args() {
        let decl = parse_impl("impl T<u64> for S { fn m(&self, a: u64) -> u64 { a } }");
        let tokens = trait_impl_decl_tokens(&decl).to_string();
        assert!(
            tokens.contains("with_trait_type_args"),
            "macro round-trip must carry the trait type args, got: {tokens}"
        );
        assert!(
            tokens.contains("Uint"),
            "the u64 arg must appear in the round-trip: {tokens}"
        );
    }
}
