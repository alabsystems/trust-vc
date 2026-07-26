// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::hash::{Hash, Hasher};

use quote::{format_ident, quote};
use syn::fold::{self, Fold};
use syn::visit::Visit;
use trust_vc_core::macro_support_root;

use super::{canonical_expr_ast_string, generate_obligation_collection, parse_expr_with_chains};

fn invariant_symbolic_suffix(
    inv_str: &str,
    binding_str: &str,
    body_stream: &proc_macro2::TokenStream,
) -> String {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    inv_str.hash(&mut hasher);
    binding_str.hash(&mut hasher);
    body_stream.to_string().hash(&mut hasher);
    format!("{:x}", hasher.finish())
}

fn macro_obligation_kind(path: &syn::Path) -> Option<(proc_macro2::TokenStream, &'static str)> {
    let macro_name = path.segments.last()?.ident.to_string();
    let support_root = macro_support_root();
    match macro_name.as_str() {
        "assert" => Some((
            quote! { #support_root::vc::ObligationKind::Assert },
            "assert_line_",
        )),
        "assume" => Some((
            quote! { #support_root::vc::ObligationKind::Assume },
            "assume_line_",
        )),
        "requires" => Some((
            quote! { #support_root::vc::ObligationKind::Requires },
            "requires_line_",
        )),
        "ensures" => Some((
            quote! { #support_root::vc::ObligationKind::Ensures },
            "ensures_line_",
        )),
        _ => None,
    }
}

#[allow(clippy::indexing_slicing)] // invariant: `segments[0]` guarded by `segments.len() == 1`
fn is_simple_binding_path(expr: &syn::Expr, binding: &str) -> bool {
    match expr {
        syn::Expr::Path(path) => {
            path.qself.is_none()
                && path.path.segments.len() == 1
                && path.path.segments[0].ident == binding
        }
        syn::Expr::Paren(paren) => is_simple_binding_path(&paren.expr, binding),
        _ => false,
    }
}

fn is_invariant_binding_target(expr: &syn::Expr, binding: &str) -> bool {
    match expr {
        syn::Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Deref(_)) => {
            is_simple_binding_path(&unary.expr, binding)
        }
        syn::Expr::Paren(paren) => is_invariant_binding_target(&paren.expr, binding),
        _ => false,
    }
}

#[derive(Default)]
struct BindingUseFinder {
    binding: String,
    used: bool,
}

impl Visit<'_> for BindingUseFinder {
    #[allow(clippy::indexing_slicing)] // invariant: `segments[0]` guarded by `segments.len() == 1`
    fn visit_expr_path(&mut self, expr_path: &syn::ExprPath) {
        if expr_path.qself.is_none()
            && expr_path.path.segments.len() == 1
            && expr_path.path.segments[0].ident == self.binding
        {
            self.used = true;
        }
        syn::visit::visit_expr_path(self, expr_path);
    }
}

fn stmt_uses_binding(stmt: &syn::Stmt, binding: &str) -> bool {
    let mut finder = BindingUseFinder {
        binding: binding.to_string(),
        used: false,
    };
    finder.visit_stmt(stmt);
    finder.used
}

struct InvariantExprRewriter {
    binding: String,
    shadow: syn::Ident,
    invalid_use: Option<syn::Error>,
}

impl Fold for InvariantExprRewriter {
    #[allow(clippy::indexing_slicing)] // invariant: `segments[0]` guarded by `segments.len() == 1`
    fn fold_expr(&mut self, expr: syn::Expr) -> syn::Expr {
        match expr {
            syn::Expr::Path(path)
                if path.qself.is_none()
                    && path.path.segments.len() == 1
                    && path.path.segments[0].ident == self.binding =>
            {
                self.invalid_use = Some(syn::Error::new_spanned(
                    &path,
                    format!(
                        "open_local_invariant! body must use `*{}` or `{}` field access, not the bare binding",
                        self.binding, self.binding
                    ),
                ));
                syn::Expr::Path(path)
            }
            syn::Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Deref(_)) => {
                if is_simple_binding_path(&unary.expr, &self.binding) {
                    let shadow = &self.shadow;
                    syn::parse_quote!(#shadow)
                } else {
                    syn::Expr::Unary(fold::fold_expr_unary(self, unary))
                }
            }
            syn::Expr::Field(field) if is_simple_binding_path(&field.base, &self.binding) => {
                let member = field.member;
                let shadow = &self.shadow;
                syn::parse_quote!(#shadow.#member)
            }
            syn::Expr::Macro(mut expr_macro) => {
                let macro_name = expr_macro
                    .mac
                    .path
                    .segments
                    .last()
                    .map(|segment| segment.ident.to_string());
                if macro_name.as_deref() == Some("old") {
                    if let Ok(inner_expr) = syn::parse2::<syn::Expr>(expr_macro.mac.tokens.clone())
                    {
                        let rewritten = self.fold_expr(inner_expr);
                        expr_macro.mac.tokens = quote!(#rewritten);
                    }
                }
                syn::Expr::Macro(expr_macro)
            }
            other => fold::fold_expr(self, other),
        }
    }
}

fn rewrite_invariant_expr(
    expr: syn::Expr,
    binding: &str,
    shadow: &syn::Ident,
) -> Result<syn::Expr, syn::Error> {
    let mut rewriter = InvariantExprRewriter {
        binding: binding.to_string(),
        shadow: shadow.clone(),
        invalid_use: None,
    };
    let rewritten = rewriter.fold_expr(expr);
    if let Some(err) = rewriter.invalid_use {
        Err(err)
    } else {
        Ok(rewritten)
    }
}

struct InvariantBodyLowering {
    transformed_stmts: Vec<proc_macro2::TokenStream>,
    final_shadow: syn::Ident,
    errors: Vec<proc_macro2::TokenStream>,
}

fn lower_open_invariant_body(
    body: &syn::Block,
    binding: &str,
    shadow_prefix: &str,
    binding_type_ident: &syn::Ident,
) -> InvariantBodyLowering {
    let support_root = macro_support_root();
    let mut transformed_stmts = Vec::new();
    let mut errors = Vec::new();
    let mut current_shadow = format_ident!("{}_0", shadow_prefix);
    let mut next_shadow_index = 0usize;

    for stmt in &body.stmts {
        let lowered_macro = match stmt {
            syn::Stmt::Macro(stmt_macro) => {
                Some((&stmt_macro.mac.path, stmt_macro.mac.tokens.clone()))
            }
            syn::Stmt::Expr(syn::Expr::Macro(expr_macro), _) => {
                Some((&expr_macro.mac.path, expr_macro.mac.tokens.clone()))
            }
            _ => None,
        };

        if let Some((path, tokens)) = lowered_macro {
            if let Some((kind_tokens, name_prefix)) = macro_obligation_kind(path) {
                match parse_expr_with_chains(&tokens)
                    .map_err(|err| err.to_compile_error())
                    .and_then(|expr| {
                        rewrite_invariant_expr(expr, binding, &current_shadow)
                            .map_err(|err| err.to_compile_error())
                    }) {
                    Ok(rewritten_expr) => {
                        let rewritten_tokens = quote!(#rewritten_expr);
                        let ast_string = canonical_expr_ast_string(&rewritten_tokens);
                        let collection = generate_obligation_collection(
                            &rewritten_tokens,
                            &ast_string,
                            kind_tokens,
                            name_prefix,
                        );
                        transformed_stmts.push(collection);
                    }
                    Err(err_tokens) => errors.push(err_tokens),
                }
                continue;
            }
            if tokens.to_string().contains(binding) {
                errors.push(
                    syn::Error::new_spanned(
                        stmt,
                        format!(
                            "open_local_invariant! does not yet support `{binding}` inside this macro; \
                             use trust_vc::assert!/assume!/requires!/ensures! or a direct `*{binding} = expr;` assignment"
                        ),
                    )
                    .to_compile_error(),
                );
                continue;
            }
        }

        if let syn::Stmt::Expr(syn::Expr::Assign(assign), _) = stmt {
            if is_invariant_binding_target(&assign.left, binding) {
                match rewrite_invariant_expr((*assign.right).clone(), binding, &current_shadow) {
                    Ok(rewritten_rhs) => {
                        next_shadow_index += 1;
                        let next_shadow = format_ident!("{}_{}", shadow_prefix, next_shadow_index);
                        let rhs_tokens = quote!(#rewritten_rhs);
                        let rhs_ast_string = canonical_expr_ast_string(&rhs_tokens);
                        transformed_stmts.push(quote! {
                            #support_root::verify_macro::collect_variable(
                                stringify!(#next_shadow).to_string(),
                                #binding_type_ident.to_string()
                            );
                            #support_root::verify_macro::collect_let_binding(
                                stringify!(#next_shadow).to_string(),
                                #rhs_ast_string.to_string()
                            );
                        });
                        current_shadow = next_shadow;
                    }
                    Err(err) => errors.push(err.to_compile_error()),
                }
                continue;
            }
        }

        if stmt_uses_binding(stmt, binding) {
            errors.push(
                syn::Error::new_spanned(
                    stmt,
                    format!(
                        "open_local_invariant! currently supports `{binding}` only in \
                         trust_vc::assert!/assume!/requires!/ensures! conditions and direct \
                         top-level `*{binding} = expr;` assignments"
                    ),
                )
                .to_compile_error(),
            );
            continue;
        }

        transformed_stmts.push(quote!(#stmt));
    }

    InvariantBodyLowering {
        transformed_stmts,
        final_shadow: current_shadow,
        errors,
    }
}

fn generate_invariant_predicate_collection(
    predicate_fn_ident: &syn::Ident,
    namespace_ident: &syn::Ident,
    shadow_ident: &syn::Ident,
    kind_tokens: proc_macro2::TokenStream,
    name_prefix: &str,
) -> proc_macro2::TokenStream {
    let predicate_tokens = quote! {
        #predicate_fn_ident(#namespace_ident, #shadow_ident)
    };
    let predicate_ast = canonical_expr_ast_string(&predicate_tokens);
    generate_obligation_collection(&predicate_tokens, &predicate_ast, kind_tokens, name_prefix)
}

/// Expands `open_local_invariant!(&inv => inner => { body })`.
///
/// Parses the invariant reference, binding name, and body block, then emits
/// verification markers for the encoder:
/// - Open an invariant scope with the invariant name
/// - Assume the predicate holds at entry
/// - Execute the body (may modify `inner`)
/// - Assert the predicate holds at exit
///
/// At runtime the entire block is elided (invariant interactions are ghost-only).
pub(crate) fn expand_open_local_invariant(
    tokens: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let support_root = macro_support_root();
    let items: Vec<proc_macro2::TokenTree> = tokens.into_iter().collect();

    // Parse: &inv => inner => { body }
    // Tokens: [&, inv, =>, inner, =>, { body }]
    let (inv_tokens, rest) =
        match split_at_fat_arrow(&items) {
            Some(pair) => pair,
            None => return syn::Error::new(
                proc_macro2::Span::call_site(),
                "open_local_invariant! expects: open_local_invariant!(&inv => inner => { body })",
            )
            .to_compile_error(),
        };
    let (binding_tokens, body_rest) =
        match split_at_fat_arrow(rest) {
            Some(pair) => pair,
            None => return syn::Error::new(
                proc_macro2::Span::call_site(),
                "open_local_invariant! expects: open_local_invariant!(&inv => inner => { body })",
            )
            .to_compile_error(),
        };

    let inv_stream: proc_macro2::TokenStream = inv_tokens.iter().cloned().collect();
    let binding_stream: proc_macro2::TokenStream = binding_tokens.iter().cloned().collect();
    let body_stream: proc_macro2::TokenStream = body_rest.iter().cloned().collect();
    let binding_ident = match syn::parse2::<syn::Ident>(binding_stream.clone()) {
        Ok(ident) => ident,
        Err(_) => {
            return syn::Error::new_spanned(
                binding_stream,
                "open_local_invariant! binding must be a simple identifier",
            )
            .to_compile_error()
        }
    };
    let body_block = match syn::parse2::<syn::Block>(body_stream.clone()) {
        Ok(block) => block,
        Err(err) => return err.to_compile_error(),
    };

    let inv_str = inv_stream.to_string();
    let binding_str = binding_stream.to_string();
    let suffix = invariant_symbolic_suffix(&inv_str, &binding_str, &body_stream);
    let namespace_ident = format_ident!("__trust_vc_invariant_namespace_{}", suffix);
    let binding_type_ident = format_ident!("__trust_vc_invariant_value_ty_{}", suffix);
    let predicate_fn_ident = format_ident!("__trust_vc_invariant_predicate_{}", suffix);
    let shadow_prefix = format!("__trust_vc_invariant_shadow_{}", suffix);
    let open_shadow_ident = format_ident!("{}_0", shadow_prefix);
    let lowered_body = lower_open_invariant_body(
        &body_block,
        &binding_ident.to_string(),
        &shadow_prefix,
        &binding_type_ident,
    );
    let open_predicate = generate_invariant_predicate_collection(
        &predicate_fn_ident,
        &namespace_ident,
        &open_shadow_ident,
        quote! { #support_root::vc::ObligationKind::Assume },
        "invariant_predicate_open_line_",
    );
    let close_predicate = generate_invariant_predicate_collection(
        &predicate_fn_ident,
        &namespace_ident,
        &lowered_body.final_shadow,
        quote! { #support_root::vc::ObligationKind::Assert },
        "invariant_predicate_close_line_",
    );
    let body_errors = lowered_body.errors;
    let transformed_stmts = lowered_body.transformed_stmts;

    quote! {
        {
            #[cfg(test)]
            {
                #(#body_errors)*
                let #namespace_ident = (#inv_stream).namespace();
                let #binding_type_ident = (#inv_stream).binding_type_name();
                #support_root::register_invariant_predicate_helper(
                    stringify!(#predicate_fn_ident),
                    #binding_type_ident
                );
                #support_root::verify_macro::collect_variable_runtime(
                    stringify!(#namespace_ident),
                    &#namespace_ident
                );
                #support_root::verify_macro::collect_variable(
                    stringify!(#open_shadow_ident).to_string(),
                    #binding_type_ident.to_string()
                );
                #support_root::verify_macro::begin_invariant_open(
                    #inv_str.to_string(),
                    #binding_str.to_string(),
                    Some(#namespace_ident),
                    Some(format!("{}:{}", file!(), line!())),
                );
                #open_predicate
                #(#transformed_stmts)*
                #close_predicate
                #support_root::verify_macro::end_invariant_open(
                    #inv_str.to_string(),
                    Some(#namespace_ident),
                    Some(format!("{}:{}", file!(), line!())),
                );
            }
            #[cfg(not(test))]
            {
                let mut #binding_ident = (#inv_stream).open_binding();
                if false {
                    let _ = || { #body_stream };
                }
            }
        }
    }
}

/// Splits a token slice at the first `=>` fat arrow, returning
/// (before, after) slices. Returns None if no fat arrow found.
#[allow(clippy::indexing_slicing)] // invariant: `tokens[i]`/`tokens[i+1]` bounded by `i < tokens.len() - 1`; slices bounded by computed index
fn split_at_fat_arrow(
    tokens: &[proc_macro2::TokenTree],
) -> Option<(&[proc_macro2::TokenTree], &[proc_macro2::TokenTree])> {
    for i in 0..tokens.len().saturating_sub(1) {
        if let proc_macro2::TokenTree::Punct(p1) = &tokens[i] {
            if p1.as_char() == '=' {
                if let proc_macro2::TokenTree::Punct(p2) = &tokens[i + 1] {
                    if p2.as_char() == '>' {
                        return Some((&tokens[..i], &tokens[i + 2..]));
                    }
                }
            }
        }
    }
    None
}
