//! Attribute handler expansion for various trust_vc attributes.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Handles expansion of: `#[returns]`, `#[external_body]`, equality macros,
//! `#[memoize]`, `#[opens_invariants]`, and `__assume`.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{fold::Fold, parse::Parser, visit::Visit, Expr, FnArg, Item, ItemFn, Lit, Pat, Type};

const SPEC_RETURNS_ERROR: &str = "spec functions cannot have `returns` clause";
const RETURNS_TYPE_MISMATCH_ERROR: &str =
    "type of `returns` clause does not match function return type";
const RETURNS_REF_POSTCONDITION_UNSUPPORTED_ERROR: &str =
    "direct #[trust_vc::returns(x)] reference-return postconditions currently support only \
     shared references to bool and integer referents";

fn attr_has_last_segment(attr: &syn::Attribute, name: &str) -> bool {
    attr.path()
        .segments
        .last()
        .is_some_and(|segment| segment.ident == name)
}

fn primitive_type_name(ty: &Type) -> Option<&'static str> {
    match ty {
        Type::Path(type_path) if type_path.qself.is_none() => {
            let segment = type_path.path.segments.last()?;
            match segment.ident.to_string().as_str() {
                "bool" => Some("bool"),
                "char" => Some("char"),
                "i8" => Some("i8"),
                "i16" => Some("i16"),
                "i32" => Some("i32"),
                "i64" => Some("i64"),
                "i128" => Some("i128"),
                "isize" => Some("isize"),
                "u8" => Some("u8"),
                "u16" => Some("u16"),
                "u32" => Some("u32"),
                "u64" => Some("u64"),
                "u128" => Some("u128"),
                "usize" => Some("usize"),
                "f32" => Some("f32"),
                "f64" => Some("f64"),
                _ => None,
            }
        }
        Type::Tuple(tuple) if tuple.elems.is_empty() => Some("()"),
        Type::Paren(paren) => primitive_type_name(&paren.elem),
        Type::Group(group) => primitive_type_name(&group.elem),
        _ => None,
    }
}

fn function_return_type_name(sig: &syn::Signature) -> Option<&'static str> {
    match &sig.output {
        syn::ReturnType::Default => Some("()"),
        syn::ReturnType::Type(_, ty) => primitive_type_name(ty),
    }
}

fn literal_expr_type_name(expr: &Expr) -> Option<&'static str> {
    match expr {
        Expr::Lit(expr_lit) => match &expr_lit.lit {
            Lit::Bool(_) => Some("bool"),
            Lit::Char(_) => Some("char"),
            Lit::Int(lit) => match lit.suffix() {
                "i8" => Some("i8"),
                "i16" => Some("i16"),
                "i32" => Some("i32"),
                "i64" => Some("i64"),
                "i128" => Some("i128"),
                "isize" => Some("isize"),
                "u8" => Some("u8"),
                "u16" => Some("u16"),
                "u32" => Some("u32"),
                "u64" => Some("u64"),
                "u128" => Some("u128"),
                "usize" => Some("usize"),
                _ => None,
            },
            Lit::Float(lit) => match lit.suffix() {
                "f32" => Some("f32"),
                "f64" => Some("f64"),
                _ => None,
            },
            _ => None,
        },
        Expr::Tuple(tuple) if tuple.elems.is_empty() => Some("()"),
        Expr::Paren(paren) => literal_expr_type_name(&paren.expr),
        Expr::Group(group) => literal_expr_type_name(&group.expr),
        _ => None,
    }
}

fn returns_type_mismatch_error(
    sig: &syn::Signature,
    return_names: TokenStream,
) -> Option<syn::Error> {
    if syn::parse2::<syn::Ident>(return_names.clone()).is_ok() {
        return None;
    }

    let expr = syn::parse2::<Expr>(return_names).ok()?;
    let expected = function_return_type_name(sig)?;
    let actual = literal_expr_type_name(&expr)?;

    (expected != actual).then(|| syn::Error::new_spanned(expr, RETURNS_TYPE_MISMATCH_ERROR))
}

fn single_ident_expr(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Path(expr_path)
            if expr_path.qself.is_none() && expr_path.path.get_ident().is_some()
    )
}

fn tuple_return_names_expr(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Tuple(tuple)
            if !tuple.elems.is_empty() && tuple.elems.iter().all(single_ident_expr)
    )
}

fn returns_postcondition_expr(return_names: TokenStream) -> Option<Expr> {
    if syn::parse2::<syn::Ident>(return_names.clone()).is_ok() {
        return None;
    }

    let expr = syn::parse2::<Expr>(return_names).ok()?;
    (!tuple_return_names_expr(&expr)).then_some(expr)
}

fn is_shared_reference_type(ty: &Type) -> bool {
    match ty {
        Type::Reference(reference) => reference.mutability.is_none(),
        Type::Paren(paren) => is_shared_reference_type(&paren.elem),
        Type::Group(group) => is_shared_reference_type(&group.elem),
        _ => false,
    }
}

fn primitive_runtime_value_capture_type(ty: &Type) -> bool {
    matches!(
        primitive_type_name(ty),
        Some(
            "bool"
                | "i8"
                | "i16"
                | "i32"
                | "i64"
                | "i128"
                | "isize"
                | "u8"
                | "u16"
                | "u32"
                | "u64"
                | "u128"
                | "usize"
        )
    )
}

fn shared_reference_referent_type(ty: &Type) -> Option<&Type> {
    match ty {
        Type::Reference(reference) if reference.mutability.is_none() => Some(&reference.elem),
        Type::Paren(paren) => shared_reference_referent_type(&paren.elem),
        Type::Group(group) => shared_reference_referent_type(&group.elem),
        _ => None,
    }
}

fn signature_shared_reference_referent(sig: &syn::Signature) -> Option<&Type> {
    match &sig.output {
        syn::ReturnType::Type(_, ty) => shared_reference_referent_type(ty),
        syn::ReturnType::Default => None,
    }
}

fn signature_has_supported_shared_reference_return(sig: &syn::Signature) -> bool {
    signature_shared_reference_referent(sig).is_some_and(primitive_runtime_value_capture_type)
}

fn pat_ident(pat: &Pat) -> Option<&syn::Ident> {
    match pat {
        Pat::Ident(pat_ident) => Some(&pat_ident.ident),
        Pat::Type(pat_type) => pat_ident(&pat_type.pat),
        Pat::Reference(pat_ref) => pat_ident(&pat_ref.pat),
        _ => None,
    }
}

fn shared_reference_param_named(sig: &syn::Signature, ident: &syn::Ident) -> bool {
    sig.inputs.iter().any(|input| {
        let FnArg::Typed(pat_type) = input else {
            return false;
        };
        is_shared_reference_type(&pat_type.ty)
            && pat_ident(&pat_type.pat).is_some_and(|param| param == ident)
    })
}

fn direct_shared_reference_ident_expr(sig: &syn::Signature, expr: &Expr) -> Option<syn::Ident> {
    match expr {
        Expr::Path(expr_path)
            if expr_path.qself.is_none()
                && signature_shared_reference_referent(sig).is_some()
                && expr_path
                    .path
                    .get_ident()
                    .is_some_and(|ident| shared_reference_param_named(sig, ident)) =>
        {
            expr_path.path.get_ident().cloned()
        }
        Expr::Paren(paren) => direct_shared_reference_ident_expr(sig, &paren.expr),
        Expr::Group(group) => direct_shared_reference_ident_expr(sig, &group.expr),
        _ => None,
    }
}

struct ReturnsPostcondition {
    expr: Expr,
    shared_reference_param: Option<syn::Ident>,
}

fn returns_postcondition(
    sig: &syn::Signature,
    return_names: TokenStream,
) -> syn::Result<Option<ReturnsPostcondition>> {
    if let Ok(ident) = syn::parse2::<syn::Ident>(return_names.clone()) {
        if signature_shared_reference_referent(sig).is_some()
            && shared_reference_param_named(sig, &ident)
        {
            if !signature_has_supported_shared_reference_return(sig) {
                return Err(syn::Error::new_spanned(
                    ident,
                    RETURNS_REF_POSTCONDITION_UNSUPPORTED_ERROR,
                ));
            }
            return Ok(Some(ReturnsPostcondition {
                expr: syn::parse_quote! { #ident },
                shared_reference_param: Some(ident),
            }));
        }
        return Ok(None);
    }

    let Some(expr) = returns_postcondition_expr(return_names) else {
        return Ok(None);
    };

    let shared_reference_param = direct_shared_reference_ident_expr(sig, &expr);
    if shared_reference_param.is_some() && !signature_has_supported_shared_reference_return(sig) {
        return Err(syn::Error::new_spanned(
            expr,
            RETURNS_REF_POSTCONDITION_UNSUPPORTED_ERROR,
        ));
    }

    Ok(Some(ReturnsPostcondition {
        expr,
        shared_reference_param,
    }))
}

struct ReturnPostconditionRewriter {
    label: syn::Lifetime,
}

impl ReturnPostconditionRewriter {
    fn new() -> Self {
        Self {
            label: syn::Lifetime::new(
                "'__trust_vc_returns_postcondition",
                proc_macro2::Span::call_site(),
            ),
        }
    }
}

impl Fold for ReturnPostconditionRewriter {
    fn fold_expr(&mut self, expr: Expr) -> Expr {
        match expr {
            Expr::Return(expr_return) => {
                let value = expr_return
                    .expr
                    .map(|expr| self.fold_expr(*expr))
                    .unwrap_or_else(|| syn::parse_quote! { () });
                let label = &self.label;
                syn::parse_quote! {
                    break #label #value
                }
            }
            Expr::Closure(expr_closure) => Expr::Closure(expr_closure),
            Expr::Async(expr_async) => Expr::Async(expr_async),
            other => syn::fold::fold_expr(self, other),
        }
    }

    fn fold_item(&mut self, item: Item) -> Item {
        item
    }
}

fn rewrite_returns_postcondition_body(block: syn::Block) -> syn::Block {
    ReturnPostconditionRewriter::new().fold_block(block)
}

struct UnsupportedMacroReturnFinder {
    unsupported_return: Option<proc_macro2::Span>,
}

impl UnsupportedMacroReturnFinder {
    fn new() -> Self {
        Self {
            unsupported_return: None,
        }
    }

    fn into_error(self) -> Option<syn::Error> {
        self.unsupported_return.map(|span| {
            syn::Error::new(
                span,
                "`return` inside a macro invocation is not supported by \
                 #[trust_vc::returns(expr)]; write the return expression directly \
                 so TrustVc can capture it before checking the postcondition",
            )
        })
    }
}

fn token_stream_contains_return(tokens: TokenStream) -> Option<proc_macro2::Span> {
    for token in tokens {
        match token {
            proc_macro2::TokenTree::Ident(ident) if ident == "return" => {
                return Some(ident.span());
            }
            proc_macro2::TokenTree::Group(group) => {
                if let Some(span) = token_stream_contains_return(group.stream()) {
                    return Some(span);
                }
            }
            _ => {}
        }
    }
    None
}

impl<'ast> Visit<'ast> for UnsupportedMacroReturnFinder {
    fn visit_stmt(&mut self, stmt: &'ast syn::Stmt) {
        if self.unsupported_return.is_none() {
            if let syn::Stmt::Macro(stmt_macro) = stmt {
                self.unsupported_return =
                    token_stream_contains_return(stmt_macro.mac.tokens.clone());
            }
        }

        syn::visit::visit_stmt(self, stmt);
    }

    fn visit_expr_macro(&mut self, expr: &'ast syn::ExprMacro) {
        if self.unsupported_return.is_none() {
            self.unsupported_return = token_stream_contains_return(expr.mac.tokens.clone());
        }
    }

    fn visit_expr_closure(&mut self, _expr: &'ast syn::ExprClosure) {}

    fn visit_expr_async(&mut self, _expr: &'ast syn::ExprAsync) {}

    fn visit_item(&mut self, _item: &'ast Item) {}
}

fn reject_macro_hidden_returns(block: &syn::Block) -> syn::Result<()> {
    let mut finder = UnsupportedMacroReturnFinder::new();
    finder.visit_block(block);
    match finder.into_error() {
        Some(err) => Err(err),
        None => Ok(()),
    }
}

/// Expands a `#[returns(name)]` attribute for named return values.
///
/// # Generated Code
///
/// For `#[trust_vc::returns(ret)]`:
/// - Introduces a marker that trust_mc uses to bind the return value
/// - The name can be used in `ensures!` clauses
/// - At runtime, the attribute has no effect
///
/// # ay Encoding
///
/// ```text
/// (declare-const ret <return_type>)
/// ; ... function body ...
/// (assert (= ret <actual_return>))
/// ```
pub fn expand_returns(input: ItemFn, return_names: TokenStream) -> TokenStream {
    let attrs = &input.attrs;
    let vis = &input.vis;
    let sig = &input.sig;
    let block = &input.block;
    let _fn_name = &sig.ident;

    if let Some(attr) = attrs
        .iter()
        .find(|attr| attr_has_last_segment(attr, "spec"))
    {
        return syn::Error::new_spanned(attr, SPEC_RETURNS_ERROR).to_compile_error();
    }

    if let Some(err) = returns_type_mismatch_error(sig, return_names.clone()) {
        return err.to_compile_error();
    }

    let names_str = return_names.to_string();
    let postcondition = match returns_postcondition(sig, return_names.clone()) {
        Ok(Some(postcondition)) => postcondition,
        Ok(None) => {
            return quote! {
                #(#attrs)*
                #[allow(unused_variables)]
                #vis #sig {
                    #[cfg(trust_mc)]
                    {
                        let __trust_vc_return_names = #names_str;
                    }

                    #block
                }
            };
        }
        Err(err) => return err.to_compile_error(),
    };

    if let Err(err) = reject_macro_hidden_returns(block) {
        return err.to_compile_error();
    }

    let support_root = crate::macro_support_root();
    let ReturnsPostcondition {
        expr: postcondition_expr,
        shared_reference_param,
    } = postcondition;
    let rewritten_body = rewrite_returns_postcondition_body((**block).clone());
    let condition = quote! { result == (#postcondition_expr) }.to_string();
    let runtime_check = crate::runtime_check::runtime_check_or_typecheck(
        &quote! { result == (#postcondition_expr) },
        crate::runtime_check::ClauseArithmetic::FixedWidthChecked,
        quote! {
            assert!(
                result == (#postcondition_expr),
                "trust_vc postcondition failed: result == ({})",
                stringify!(#postcondition_expr)
            );
        },
    );
    let result_runtime_capture = if signature_has_supported_shared_reference_return(sig) {
        quote! {
            #support_root::collect_let_binding_runtime_value_from_ref("result", result);
        }
    } else {
        quote! {
            #support_root::collect_let_binding_runtime_value_from_ref("result", &result);
        }
    };
    let shared_reference_param_runtime_capture =
        shared_reference_param
            .as_ref()
            .map_or_else(TokenStream::new, |param| {
                let param_name = param.to_string();
                quote! {
                    #support_root::collect_variable_runtime(#param_name, &#param);
                    #support_root::collect_let_binding_runtime_value_from_ref(#param_name, #param);
                }
            });

    quote! {
        #(#attrs)*
        #[allow(unused_variables)]
        #vis #sig {
            #[cfg(trust_mc)]
            {
                let __trust_vc_return_names = #names_str;
            }

            let result = '__trust_vc_returns_postcondition: #rewritten_body;

            #[cfg(test)]
            {
                #support_root::collect_variable_runtime("result", &result);
                #result_runtime_capture
                #shared_reference_param_runtime_capture
                #support_root::verify_macro::collect_typed_obligation(
                    #support_root::vc::ObligationKind::Ensures,
                    format!("returns_postcondition_line_{}_col_{}", line!(), column!()),
                    #condition.to_string(),
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            }
            #[cfg(not(test))]
            {
                #runtime_check
            }

            result
        }
    }
}

/// Expands a `#[external_body]` attribute for trusted functions.
///
/// # Generated Code
///
/// For `#[trust_vc::external_body]`:
/// - Marks the function body as trusted (not verified)
/// - Contracts (requires/ensures) are still checked at call sites
/// - At runtime, the function executes normally
///
/// # ay Encoding
///
/// The function body is completely skipped during verification.
/// Call sites:
/// - Check preconditions (requires)
/// - Assume postconditions (ensures)
pub fn expand_external_body(input: ItemFn) -> TokenStream {
    let attrs = &input.attrs;
    let vis = &input.vis;
    let sig = &input.sig;
    let block = &input.block;
    let fn_name = &sig.ident;

    quote! {
        #(#attrs)*
        /// External body - implementation trusted, contracts verified at call sites
        #[allow(unused_variables)]
        #vis #sig {
            #[cfg(trust_mc)]
            {
                let __trust_vc_external_body = stringify!(#fn_name);
            }

            #block
        }
    }
}

/// Expands an `ext_eq!(a, b)` call for extensional equality.
///
/// Generates code with trust_mc marker bindings for verification.
pub fn expand_ext_eq(lhs: TokenStream, rhs: TokenStream) -> TokenStream {
    quote! {
        {
            #[cfg(trust_mc)]
            {
                let __trust_vc_ext_eq_lhs = stringify!(#lhs);
                let __trust_vc_ext_eq_rhs = stringify!(#rhs);
                true
            }
            #[cfg(not(trust_mc))]
            {
                (#lhs) == (#rhs)
            }
        }
    }
}

/// Expands an `ext_ne!(a, b)` call for extensional inequality.
///
/// Generates code with trust_mc marker bindings for verification.
pub fn expand_ext_ne(lhs: TokenStream, rhs: TokenStream) -> TokenStream {
    quote! {
        {
            #[cfg(trust_mc)]
            {
                let __trust_vc_ext_ne_lhs = stringify!(#lhs);
                let __trust_vc_ext_ne_rhs = stringify!(#rhs);
                true
            }
            #[cfg(not(trust_mc))]
            {
                (#lhs) != (#rhs)
            }
        }
    }
}

/// Expands a strict equality call (`strict_eq!` / `equal!`).
///
/// Verification lowering recognizes the macro name and emits raw solver
/// equality instead of collection extensional equality.
pub fn expand_strict_eq(lhs: TokenStream, rhs: TokenStream) -> TokenStream {
    quote! {
        {
            #[cfg(trust_mc)]
            {
                let __trust_vc_strict_eq_lhs = stringify!(#lhs);
                let __trust_vc_strict_eq_rhs = stringify!(#rhs);
                true
            }
            #[cfg(not(trust_mc))]
            {
                (#lhs) == (#rhs)
            }
        }
    }
}

/// Runtime assume intrinsic (unsafe, for proof use only).
#[doc(hidden)]
pub fn __assume<T>(_condition: T) {
    // Erased at runtime - only used during verification
}

/// Expands a `#[memoize]` annotation.
///
/// Marks the function for result caching during proof computation.
/// Primarily affects `assert_by_compute!` behavior for recursive functions.
///
/// # Postcondition
///
/// Output contains __trust_vc_memoize marker for verification caching.
pub fn expand_memoize(input: ItemFn) -> TokenStream {
    let attrs = &input.attrs;
    let vis = &input.vis;
    let sig = &input.sig;
    let block = &input.block;
    let fn_name = &sig.ident;

    quote! {
        #(#attrs)*
        #vis #sig {
            #[cfg(trust_mc)]
            let _ = {
                let __trust_vc_memoize = stringify!(#fn_name);
                __trust_vc_memoize
            };

            #block
        }
    }
}

/// Expands an `#[opens_invariants(...)]` annotation.
///
/// Specifies which tracked invariants a function may open, enforcing
/// reentrancy restrictions for concurrent verification.
///
/// # Syntax
///
/// ```text
/// #[trust_vc::opens_invariants(any)]           // Allow any invariant
/// #[trust_vc::opens_invariants(none)]          // Allow no invariants
/// #[trust_vc::opens_invariants(inv1, inv2)]    // Allow specific invariants
/// ```
///
/// # Postcondition
///
/// Output contains __trust_vc_opens_invariants marker.
#[allow(clippy::manual_let_else)]
pub fn expand_opens_invariants(input: ItemFn, attr_tokens: TokenStream) -> TokenStream {
    let attrs = &input.attrs;
    let vis = &input.vis;
    let sig = &input.sig;
    let block = &input.block;
    let fn_name = &sig.ident;

    let parser = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated;
    let parsed = match parser.parse2(attr_tokens.clone()) {
        Ok(parsed) => parsed,
        Err(err) => return err.to_compile_error(),
    };

    let opens_mode_string = attr_tokens.to_string();
    let opens_mode_tokens = quote!(#opens_mode_string);
    let namespace_exprs: Vec<_> = parsed.iter().collect();
    let support_root = crate::macro_support_root();

    let mask_tokens = if let Some(syn::Expr::Path(path)) = parsed.first() {
        if parsed.len() == 1 && path.path.is_ident("any") {
            quote!(#support_root::vc::InvariantMask::Any)
        } else if parsed.len() == 1 && path.path.is_ident("none") {
            quote!(#support_root::vc::InvariantMask::None)
        } else {
            quote!(#support_root::vc::InvariantMask::Namespaces(
                vec![#((#namespace_exprs).namespace()),*]
            ))
        }
    } else {
        quote!(#support_root::vc::InvariantMask::Namespaces(
            vec![#((#namespace_exprs).namespace()),*]
        ))
    };

    quote! {
        #(#attrs)*
        #vis #sig {
            #[cfg(trust_mc)]
            let _ = {
                let __trust_vc_opens_invariants: &str = #opens_mode_tokens;
                let __trust_vc_opens_invariants_fn: &str = stringify!(#fn_name);
                (__trust_vc_opens_invariants, __trust_vc_opens_invariants_fn)
            };

            #[cfg(test)]
            let _trust_vc_invariant_mask_guard =
                #support_root::enter_invariant_mask_scope(#mask_tokens);

            #block
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;

    // --- expand_returns edge cases ---

    #[test]
    fn test_expand_returns_single_name() {
        let names = quote! { result };
        let input: ItemFn = syn::parse2(quote! {
            fn foo() -> i32 { 42 }
        })
        .unwrap();
        let result = expand_returns(input, names);
        let s = result.to_string();
        assert!(
            s.contains("__trust_vc_return_names"),
            "Should have return names marker"
        );
        assert!(s.contains("result"), "Should contain the return name");
    }

    #[test]
    fn test_expand_returns_tuple_names() {
        let names = quote! { (a, b, c) };
        let input: ItemFn = syn::parse2(quote! {
            fn multi() -> (i32, bool, u64) { (1, true, 2) }
        })
        .unwrap();
        let result = expand_returns(input, names);
        let s = result.to_string();
        assert!(s.contains("__trust_vc_return_names"));
        assert!(
            !s.contains("__trust_vc_returns_postcondition"),
            "tuple return names should remain a marker-only binding form: {s}"
        );
    }

    #[test]
    fn test_expand_returns_expression_captures_postcondition() {
        let names = quote! { 20u8 };
        let input: ItemFn = syn::parse2(quote! {
            fn value(flag: bool) -> u8 {
                if flag {
                    return 20u8;
                }
                20u8
            }
        })
        .unwrap();
        let result = expand_returns(input, names);
        let s = result.to_string();

        assert!(
            s.contains("'__trust_vc_returns_postcondition"),
            "expression returns should capture the function body: {s}"
        );
        assert!(
            s.contains("break '__trust_vc_returns_postcondition 20u8"),
            "explicit returns should rewrite to the capture block: {s}"
        );
        assert!(
            s.contains("result == (20u8)"),
            "expression returns should emit a result equality postcondition: {s}"
        );
        assert!(
            s.contains("collect_let_binding_runtime_value_from_ref"),
            "test path should constrain result to the runtime return value: {s}"
        );
    }

    #[test]
    fn test_expand_returns_checks_only_a_call_free_value_at_run_time() {
        let check = "\"trust_vc postcondition failed: result == ({})\"";
        let literal: ItemFn = syn::parse2(quote! {
            fn value() -> u8 { 20u8 }
        })
        .unwrap();
        let kept = expand_returns(literal, quote! { 20u8 }).to_string();
        assert!(
            kept.contains(check),
            "a call-free returns value keeps its run-time check: {kept}"
        );

        let ghost: ItemFn = syn::parse2(quote! {
            fn next(x: u64) -> u64 { x + 1u64 }
        })
        .unwrap();
        let typed_only = expand_returns(ghost, quote! { inc(x) }).to_string();
        assert!(
            !typed_only.contains(check) && typed_only.contains("if false"),
            "a returns value that calls a function is only type-checked: {typed_only}"
        );
    }

    #[test]
    fn test_expand_returns_reference_ident_is_postcondition_for_shared_ref_param() {
        let names = quote! { x };
        let input: ItemFn = syn::parse2(quote! {
            fn same<'a>(x: &'a u64) -> &'a u64 {
                x
            }
        })
        .unwrap();
        let result = expand_returns(input, names);
        let s = result.to_string();

        assert!(
            s.contains("'__trust_vc_returns_postcondition"),
            "shared-reference ident returns should capture the function body: {s}"
        );
        assert!(
            s.contains("result == (x)"),
            "shared-reference ident returns should emit a result equality postcondition: {s}"
        );
        assert!(
            s.contains("collect_variable_runtime (\"x\" , & x)"),
            "test path should collect the shared-reference parameter type: {s}"
        );
        assert!(
            s.contains("collect_let_binding_runtime_value_from_ref (\"x\" , x)"),
            "test path should capture the shared-reference parameter referent: {s}"
        );
        assert!(
            s.contains("collect_let_binding_runtime_value_from_ref (\"result\" , result)"),
            "test path should capture the shared-reference result referent: {s}"
        );
    }

    #[test]
    fn test_expand_returns_ident_keeps_legacy_binding_for_value_param() {
        let names = quote! { x };
        let input: ItemFn = syn::parse2(quote! {
            fn same(x: u64) -> u64 {
                x
            }
        })
        .unwrap();
        let result = expand_returns(input, names);
        let s = result.to_string();

        assert!(s.contains("__trust_vc_return_names"));
        assert!(
            !s.contains("__trust_vc_returns_postcondition"),
            "non-reference single identifiers should remain marker-only bindings: {s}"
        );
    }

    #[test]
    fn test_expand_returns_expression_fails_closed_on_macro_return() {
        let names = quote! { 20u8 };
        let input: ItemFn = syn::parse2(quote! {
            fn hidden_return() -> u8 {
                early!(return 20u8);
                20u8
            }
        })
        .unwrap();
        let result = expand_returns(input, names);
        let s = result.to_string();

        assert!(
            s.contains("compile_error"),
            "macro-hidden returns should fail closed: {s}"
        );
        assert!(
            s.contains("return` inside a macro invocation is not supported"),
            "diagnostic should explain unsupported macro returns: {s}"
        );
    }

    #[test]
    fn test_expand_returns_preserves_visibility() {
        let names = quote! { r };
        let input: ItemFn = syn::parse2(quote! {
            pub fn visible() -> i32 { 0 }
        })
        .unwrap();
        let result = expand_returns(input, names);
        let s = result.to_string();
        assert!(s.contains("pub"), "Should preserve pub visibility");
    }

    #[test]
    fn test_expand_returns_rejects_spec_function() {
        let names = quote! { result };
        let input: ItemFn = syn::parse2(quote! {
            #[trust_vc::spec]
            fn spec_fn() -> bool { true }
        })
        .unwrap();

        let result = expand_returns(input, names);
        let s = result.to_string();

        assert!(
            s.contains("compile_error"),
            "should reject spec returns: {s}"
        );
        assert!(
            s.contains("spec functions cannot have `returns` clause"),
            "should use Verus-compatible diagnostic: {s}"
        );
    }

    #[test]
    fn test_expand_returns_rejects_literal_type_mismatch() {
        let names = quote! { 20u8 };
        let input: ItemFn = syn::parse2(quote! {
            fn wrong_type() -> bool { true }
        })
        .unwrap();

        let result = expand_returns(input, names);
        let s = result.to_string();

        assert!(s.contains("compile_error"), "should reject wrong type: {s}");
        assert!(
            s.contains("type of `returns` clause does not match function return type"),
            "should use Verus-compatible diagnostic: {s}"
        );
    }

    // --- expand_external_body edge cases ---

    #[test]
    fn test_expand_external_body_preserves_attrs() {
        let input: ItemFn = syn::parse2(quote! {
            #[inline]
            fn optimized() -> i32 { 42 }
        })
        .unwrap();
        let result = expand_external_body(input);
        let s = result.to_string();
        assert!(s.contains("__trust_vc_external_body"));
        assert!(s.contains("inline"), "Should preserve existing attributes");
    }

    #[test]
    fn test_expand_external_body_preserves_fn_name() {
        let input: ItemFn = syn::parse2(quote! {
            fn specific_name() {}
        })
        .unwrap();
        let result = expand_external_body(input);
        let s = result.to_string();
        assert!(s.contains("specific_name"));
    }

    // --- expand_ext_eq / expand_ext_ne edge cases ---

    #[test]
    fn test_expand_ext_eq_complex_lhs() {
        let lhs = quote! { a.items[0] };
        let rhs = quote! { b.items[0] };
        let result = expand_ext_eq(lhs, rhs);
        let s = result.to_string();
        assert!(s.contains("__trust_vc_ext_eq_lhs"));
        assert!(s.contains("__trust_vc_ext_eq_rhs"));
    }

    #[test]
    fn test_expand_ext_ne_generates_ne_comparison() {
        let lhs = quote! { x };
        let rhs = quote! { y };
        let result = expand_ext_ne(lhs, rhs);
        let s = result.to_string();
        assert!(s.contains("__trust_vc_ext_ne_lhs"));
        assert!(s.contains("!="), "Non-trust_mc path should use !=");
    }

    // --- expand_memoize edge cases ---

    #[test]
    fn test_expand_memoize_preserves_params() {
        let input: ItemFn = syn::parse2(quote! {
            fn compute(a: i32, b: i32) -> i32 { a + b }
        })
        .unwrap();
        let result = expand_memoize(input);
        let generated: ItemFn = syn::parse2(result).expect("Should produce valid Rust");
        assert_eq!(generated.sig.ident, "compute");
        assert_eq!(generated.sig.inputs.len(), 2);
    }

    // --- expand_opens_invariants edge cases ---

    #[test]
    fn test_expand_opens_invariants_single_any() {
        let attr = quote! { any };
        let input: ItemFn = syn::parse2(quote! {
            fn open_any() {}
        })
        .unwrap();
        let result = expand_opens_invariants(input, attr);
        let s = result.to_string();
        assert!(s.contains("__trust_vc_opens_invariants"));
        assert!(s.contains("any"), "Should contain 'any' mode");
        assert!(
            s.contains("InvariantMask :: Any"),
            "Should install the Any mask at runtime"
        );
    }

    #[test]
    fn test_expand_opens_invariants_single_none() {
        let attr = quote! { none };
        let input: ItemFn = syn::parse2(quote! {
            fn open_none() {}
        })
        .unwrap();
        let result = expand_opens_invariants(input, attr);
        let s = result.to_string();
        assert!(s.contains("none"), "Should contain 'none' mode");
        assert!(
            s.contains("InvariantMask :: None"),
            "Should install the None mask at runtime"
        );
    }

    #[test]
    fn test_expand_opens_invariants_multiple() {
        let attr = quote! { inv1, inv2, inv3 };
        let input: ItemFn = syn::parse2(quote! {
            fn open_specific() {}
        })
        .unwrap();
        let result = expand_opens_invariants(input, attr);
        let s = result.to_string();
        assert!(s.contains("inv1"), "Should contain first invariant");
        assert!(s.contains("inv2"), "Should contain second invariant");
        assert!(s.contains("inv3"), "Should contain third invariant");
        assert!(
            s.contains(". namespace ()"),
            "specific invariants should resolve namespaces at runtime"
        );
    }

    #[test]
    fn test_expand_opens_invariants_empty_list() {
        // Empty attr_tokens should produce an empty list (Ok with len 0 → joined empty string)
        let attr = quote! {};
        let input: ItemFn = syn::parse2(quote! {
            fn open_empty() {}
        })
        .unwrap();
        let result = expand_opens_invariants(input, attr);
        let s = result.to_string();
        // Should still produce valid output (empty invariants string)
        assert!(s.contains("__trust_vc_opens_invariants"));
        assert!(s.contains("open_empty"));
    }

    #[test]
    fn test_expand_opens_invariants_non_path_expression_uses_namespace_branch() {
        let attr = quote! { namespace_for(inv) };
        let input: ItemFn = syn::parse2(quote! {
            fn open_dynamic() {}
        })
        .unwrap();
        let result = expand_opens_invariants(input, attr);
        let s = result.to_string();
        assert!(
            s.contains("namespace_for"),
            "Should preserve expression text"
        );
        assert!(
            s.contains(". namespace ()"),
            "Non-path expressions should still resolve namespaces at runtime"
        );
    }

    #[test]
    fn test_expand_opens_invariants_invalid_tokens_return_compile_error() {
        let attr = quote! { inv + };
        let input: ItemFn = syn::parse2(quote! {
            fn broken_attr() {}
        })
        .unwrap();
        let result = expand_opens_invariants(input, attr);
        let s = result.to_string();
        assert!(
            s.contains("compile_error"),
            "Invalid invariant syntax should fail closed"
        );
    }

    #[test]
    fn test_expand_memoize_emits_marker_for_function_name() {
        let input: ItemFn = syn::parse2(quote! {
            fn compute_cached(value: i32) -> i32 { value }
        })
        .unwrap();
        let result = expand_memoize(input);
        let s = result.to_string();
        assert!(s.contains("__trust_vc_memoize"));
        assert!(s.contains("compute_cached"));
    }

    // --- __assume ---

    #[test]
    fn test_assume_is_noop() {
        // __assume should not panic or have side effects at runtime
        __assume(true);
        __assume(false);
        __assume(42);
        __assume("hello");
    }
}
