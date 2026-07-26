//! Expansion logic for `#[trust_vc::contract]` attribute macro.
//!
//! Parses contract clauses (`requires`, `recommends`, `ensures`, `returns`,
//! `decreases`, `cite`) from the attribute and injects them into the function
//! body or as outer attributes. The `cite` clause registers an explicitly
//! trusted, cited assumption (assumed, never proven). See
//! `designs/2026-03-19-2420-attribute-style-contracts.md`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use proc_macro2::TokenStream;
use quote::quote;
use syn::fold::Fold;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::{Expr, FnArg, Ident, Item, ItemFn, Pat, ReturnType, Token, Type};

use crate::macro_expand;
use crate::postcondition_lowering;

/// A single clause inside `#[trust_vc::contract(...)]`.
///
/// Examples: `requires(x > 0)`, `ensures(ret > x)`, `returns(ret)`,
/// `decreases(n)`, `cite(p(x), "lemma 4.2")`.
struct ContractClause {
    name: Ident,
    args: Vec<Expr>,
}

impl Parse for ContractClause {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let name: Ident = input.parse()?;
        let content;
        syn::parenthesized!(content in input);
        let args = Punctuated::<Expr, Token![,]>::parse_terminated(&content)?;
        Ok(ContractClause {
            name,
            args: args.into_iter().collect(),
        })
    }
}

/// The full parsed content of a `#[trust_vc::contract(...)]` attribute.
struct ContractSpec {
    clauses: Vec<ContractClause>,
}

impl Parse for ContractSpec {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let clauses = Punctuated::<ContractClause, Token![,]>::parse_terminated(input)?;
        Ok(ContractSpec {
            clauses: clauses.into_iter().collect(),
        })
    }
}

fn find_named_attr<'a>(attrs: &'a [syn::Attribute], name: &str) -> Option<&'a syn::Attribute> {
    attrs.iter().find(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == name)
    })
}

struct EarlyReturnRewriter {
    label: syn::Lifetime,
}

impl EarlyReturnRewriter {
    fn new() -> Self {
        Self {
            label: syn::Lifetime::new(
                "'__trust_vc_contract_return",
                proc_macro2::Span::call_site(),
            ),
        }
    }
}

/// Rewrites function-body `return`s, including returns nested in match arms and
/// loop bodies, local initializers, and expression contexts, into exits from
/// the contract return-value capture block.
/// Closure, async-block, and nested-item returns keep their local meaning.
impl Fold for EarlyReturnRewriter {
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

fn rewrite_contract_early_returns(block: syn::Block) -> syn::Block {
    let mut rewriter = EarlyReturnRewriter::new();
    rewriter.fold_block(block)
}

struct UnsupportedReturnFinder {
    unsupported_return: Option<proc_macro2::Span>,
}

impl UnsupportedReturnFinder {
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
                 #[trust_vc::contract(..., returns(...))]; write the return \
                 expression directly so TrustVc can capture it before checking \
                 postconditions",
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

/// Finds explicit `return` tokens in macro invocations that belong to the
/// contract function body. Such returns are invisible to the AST rewriter until
/// after this attribute macro has run, so accepting them would let a macro
/// expansion return from the function before postconditions are checked.
impl<'ast> Visit<'ast> for UnsupportedReturnFinder {
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

fn reject_unsupported_contract_returns(block: &syn::Block) -> syn::Result<()> {
    let mut finder = UnsupportedReturnFinder::new();
    finder.visit_block(block);
    match finder.into_error() {
        Some(err) => Err(err),
        None => Ok(()),
    }
}

fn emit_contract_param_registrations(sig: &syn::Signature) -> Vec<TokenStream> {
    sig.inputs
        .iter()
        .filter_map(|input| match input {
            FnArg::Typed(pat_type) => {
                let Pat::Ident(pat_ident) = &*pat_type.pat else {
                    return None;
                };
                let ident = &pat_ident.ident;
                Some(emit_contract_value_registration(
                    &ident.to_string(),
                    quote!(#ident),
                    &pat_type.ty,
                ))
            }
            FnArg::Receiver(receiver) => Some(emit_contract_value_registration(
                "self",
                quote!(self),
                &receiver.ty,
            )),
        })
        .collect()
}

fn emit_contract_return_registration(name: &Ident, sig: &syn::Signature) -> Option<TokenStream> {
    let ReturnType::Type(_, ty) = &sig.output else {
        return None;
    };
    Some(emit_contract_value_registration(
        &name.to_string(),
        quote!(#name),
        ty,
    ))
}

fn emit_contract_value_registration(name: &str, value_expr: TokenStream, ty: &Type) -> TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let ty_string = quote!(#ty).to_string();
    let value_capture = emit_contract_runtime_value_capture(name, &value_expr, ty);

    quote! {
        #[cfg(test)]
        {
            #support_root::verify_macro::collect_variable(
                #name.to_string(),
                #ty_string.to_string()
            );
            #value_capture
        }
    }
}

fn emit_contract_runtime_value_capture(
    name: &str,
    value_expr: &TokenStream,
    ty: &Type,
) -> TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    match primitive_capture_kind(ty) {
        Some(PrimitiveCaptureKind::Direct) => quote! {
            #support_root::collect_let_binding_runtime_value_from_ref(#name, &#value_expr);
        },
        Some(PrimitiveCaptureKind::SharedRefDeref) => quote! {
            #support_root::collect_let_binding_runtime_value_from_ref(#name, &(*#value_expr));
        },
        None => TokenStream::new(),
    }
}

#[derive(Clone, Copy)]
enum PrimitiveCaptureKind {
    Direct,
    SharedRefDeref,
}

fn primitive_capture_kind(ty: &Type) -> Option<PrimitiveCaptureKind> {
    if let Type::Reference(reference) = ty {
        if reference.mutability.is_none() && is_primitive_value_type(&reference.elem) {
            return Some(PrimitiveCaptureKind::SharedRefDeref);
        }
        return None;
    }
    is_primitive_value_type(ty).then_some(PrimitiveCaptureKind::Direct)
}

fn is_primitive_value_type(ty: &Type) -> bool {
    let Type::Path(type_path) = ty else {
        return false;
    };
    if type_path.qself.is_some() || type_path.path.segments.len() != 1 {
        return false;
    }
    type_path.path.segments.last().is_some_and(|segment| {
        matches!(
            segment.ident.to_string().as_str(),
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
    })
}

/// Expands `#[trust_vc::contract(...)]` on a function.
///
/// `requires` and `ensures` clauses are expanded directly into body obligation
/// calls via `macro_expand::expand_requires` / `expand_ensures`. `returns` and
/// `decreases` are emitted as outer attributes that the existing attribute
/// macros process in a subsequent expansion pass.
pub(crate) fn expand_contract(attr: TokenStream, input: ItemFn) -> TokenStream {
    let spec: ContractSpec = match syn::parse2(attr) {
        Ok(s) => s,
        Err(err) => return err.to_compile_error(),
    };

    // Detect double-expansion: if the body already has trust_vc markers, the
    // user likely put #[contract] below another trust_vc attribute.
    let body_str = input
        .block
        .stmts
        .iter()
        .map(|s| quote!(#s).to_string())
        .collect::<String>();
    if body_str.contains("__trust_vc_return_names") {
        return syn::Error::new_spanned(
            &input.sig.ident,
            "#[trust_vc::contract] must be the outermost trust_vc attribute — \
             it appears this function was already expanded by another trust_vc macro",
        )
        .to_compile_error();
    }

    // Defensive guard: a contract with no clauses is meaningless. The attribute
    // entrypoint already rejects an empty `#[trust_vc::contract]`; this keeps
    // `expand_contract` honest (and unit-testable) on its own.
    if spec.clauses.is_empty() {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "#[trust_vc::contract] requires at least one clause \
             (requires, ensures, returns, decreases, or cite)",
        )
        .to_compile_error();
    }

    let mut requires_exprs: Vec<TokenStream> = Vec::new();
    let mut recommends_exprs: Vec<TokenStream> = Vec::new();
    let mut ensures_exprs: Vec<TokenStream> = Vec::new();
    // Each cited fact: (fact expression tokens, optional citation reference).
    let mut cite_clauses: Vec<(TokenStream, Option<String>)> = Vec::new();
    let mut extra_attrs: Vec<TokenStream> = Vec::new();
    let mut return_name: Option<Ident> = None;
    let mut seen_decreases = false;

    for clause in &spec.clauses {
        let clause_name = clause.name.to_string();
        match clause_name.as_str() {
            "requires" => {
                if clause.args.is_empty() {
                    return syn::Error::new(
                        clause.name.span(),
                        "requires() must have at least one condition",
                    )
                    .to_compile_error();
                }
                for expr in &clause.args {
                    requires_exprs.push(quote!(#expr));
                }
            }
            "recommends" => {
                if clause.args.is_empty() {
                    return syn::Error::new(
                        clause.name.span(),
                        "recommends() must have at least one condition",
                    )
                    .to_compile_error();
                }
                for expr in &clause.args {
                    recommends_exprs.push(quote!(#expr));
                }
            }
            "ensures" => {
                if clause.args.is_empty() {
                    return syn::Error::new(
                        clause.name.span(),
                        "ensures() must have at least one condition",
                    )
                    .to_compile_error();
                }
                for expr in &clause.args {
                    ensures_exprs.push(quote!(#expr));
                }
            }
            "returns" => {
                if return_name.is_some() {
                    return syn::Error::new(
                        clause.name.span(),
                        "duplicate returns clause in contract",
                    )
                    .to_compile_error();
                }
                if clause.args.len() != 1 {
                    return syn::Error::new(
                        clause.name.span(),
                        "returns() takes exactly one identifier",
                    )
                    .to_compile_error();
                }
                #[allow(clippy::indexing_slicing)] // invariant: validated `args.len() == 1` above
                let name_expr = &clause.args[0];
                let name_ident: Ident = match syn::parse2(quote!(#name_expr)) {
                    Ok(id) => id,
                    Err(_) => {
                        return syn::Error::new(
                            clause.name.span(),
                            "returns() argument must be a simple identifier",
                        )
                        .to_compile_error();
                    }
                };
                return_name = Some(name_ident.clone());
                extra_attrs.push(quote! { #[trust_vc::returns(#name_ident)] });
            }
            "decreases" => {
                if seen_decreases {
                    return syn::Error::new(
                        clause.name.span(),
                        "duplicate decreases clause in contract",
                    )
                    .to_compile_error();
                }
                seen_decreases = true;
                if clause.args.is_empty() {
                    return syn::Error::new(
                        clause.name.span(),
                        "decreases() must have at least one measure expression",
                    )
                    .to_compile_error();
                }
                let exprs = &clause.args;
                extra_attrs.push(quote! { #[trust_vc::decreases(#(#exprs),*)] });
            }
            "cite" => {
                // `cite(<fact>)` or `cite(<fact>, <"reference" | path>)`.
                // The cited fact is registered as an explicitly TRUSTED
                // assumption with provenance — assumed, never proven. See
                // `macro_expand::expand_cite`.
                if clause.args.is_empty() {
                    return syn::Error::new(
                        clause.name.span(),
                        "cite() requires a cited fact expression: \
                         cite(expr) or cite(expr, \"reference\")",
                    )
                    .to_compile_error();
                }
                if clause.args.len() > 2 {
                    return syn::Error::new(
                        clause.name.span(),
                        "cite() takes a cited fact and an optional citation \
                         reference: cite(expr) or cite(expr, \"reference\")",
                    )
                    .to_compile_error();
                }
                #[allow(clippy::indexing_slicing)]
                // invariant: validated `1 <= args.len() <= 2` above
                let fact = &clause.args[0];
                let reference = match clause.args.get(1) {
                    Some(reference_expr) => {
                        match macro_expand::cite_reference_string(reference_expr) {
                            Ok(reference) => Some(reference),
                            Err(err) => return err.to_compile_error(),
                        }
                    }
                    None => None,
                };
                cite_clauses.push((quote!(#fact), reference));
            }
            other => {
                return syn::Error::new(
                    clause.name.span(),
                    format!("unknown contract clause: `{other}`"),
                )
                .to_compile_error();
            }
        }
    }

    if let Some(proof_attr) = find_named_attr(&input.attrs, "proof") {
        if !requires_exprs.is_empty() && ensures_exprs.is_empty() && input.block.stmts.is_empty() {
            return syn::Error::new_spanned(
                proof_attr,
                "empty #[trust_vc::proof] bodies cannot use #[trust_vc::contract(requires(...))] without ensures(...); add an ensures(...) clause or a proof assertion",
            )
            .to_compile_error();
        }
    }

    // Ensures without returns is unsound at runtime: expand_ensures() emits
    // runtime assert!() calls that would execute BEFORE the function body,
    // checking postconditions against pre-state values. Require returns()
    // so the body result is captured and ensures checks run after it. (#2475)
    if !ensures_exprs.is_empty() && return_name.is_none() {
        let Some(ensures_clause) = spec.clauses.iter().find(|c| c.name == "ensures") else {
            return syn::Error::new(
                proc_macro2::Span::call_site(),
                "ensures() requires a returns() clause",
            )
            .to_compile_error();
        };
        return syn::Error::new(
            ensures_clause.name.span(),
            "ensures() requires a returns() clause — without returns(), \
             runtime postcondition checks would execute before the function body. \
             Add returns(ret) to capture the return value.",
        )
        .to_compile_error();
    }

    // Reconstruct the function with injected obligations.
    let vis = &input.vis;
    let sig = &input.sig;
    let fn_attrs = &input.attrs;
    let original_stmts = &input.block.stmts;
    let param_registrations = emit_contract_param_registrations(sig);
    let requires_expansions: Vec<TokenStream> = requires_exprs
        .iter()
        .cloned()
        .map(macro_expand::expand_requires)
        .collect();
    let ensures_expansions: Vec<TokenStream> = ensures_exprs
        .iter()
        .cloned()
        .map(macro_expand::expand_ensures)
        .collect();
    let recommends_expansions: Vec<TokenStream> = recommends_exprs
        .iter()
        .cloned()
        .map(macro_expand::expand_recommends)
        .collect();
    // Cited facts: trusted assumptions (assumed, never proven) injected before
    // the body so they are available to subsequent obligations.
    let cite_expansions: Vec<TokenStream> = cite_clauses
        .iter()
        .map(|(fact, reference)| macro_expand::expand_cite(fact.clone(), reference.clone()))
        .collect();

    // When `returns(name)` is present, bind the return value so ensures clauses
    // can reference it at runtime. Without this, `ensures(ret > 0)` would fail
    // with E0425 ("cannot find value `ret`") in non-test builds.
    //
    // Uses shared postcondition lowering so old!() analysis, token rewriting,
    // and emission are consistent with expand_ensures() and closure_expand.
    if let Some(ref ret_ident) = return_name {
        if !ensures_exprs.is_empty() {
            let lowered =
                match postcondition_lowering::lower_postconditions(ensures_exprs.iter().cloned()) {
                    Ok(l) => l,
                    Err(err) => return err.to_compile_error(),
                };
            if let Err(err) = reject_unsupported_contract_returns(&input.block) {
                return err.to_compile_error();
            }
            let rewritten_body = rewrite_contract_early_returns((*input.block).clone());

            let old_bindings = lowered.emit_runtime_old_bindings();
            let test_old_registrations = lowered.emit_test_old_registrations(
                postcondition_lowering::TestOldRegistrationMode::RegisterRuntimeValues,
            );
            let test_obligations = lowered.emit_test_obligations();
            let runtime_asserts = lowered.emit_runtime_asserts();
            // Surface bridge: the `#[trust_vc::contract(..)]` returns path lowers
            // its `ensures` clauses directly (not via `expand_ensures`), so it must
            // ride the SAME bare `ensures(..)` marker emission under
            // `--cfg trust_vc_driver`. The requires clauses already emit markers
            // (via `expand_requires` in `requires_expansions`). Gating the runtime
            // asserts on `not(trust_vc_driver)` makes the arms mutually exclusive:
            // exactly one postcondition form is emitted, never a vacuous `true`
            // alongside a marker (which would be a false-Verify).
            let driver_markers = lowered.emit_driver_markers();
            let return_registration = emit_contract_return_registration(ret_ident, sig);

            return quote! {
                #(#extra_attrs)*
                #(#fn_attrs)*
                #vis #sig {
                    #(#param_registrations)*
                    #(#requires_expansions)*
                    #(#recommends_expansions)*
                    #(#cite_expansions)*
                    #(#old_bindings)*
                    let #ret_ident = '__trust_vc_contract_return: #rewritten_body;
                    #[cfg(test)]
                    {
                        #return_registration
                        #(#test_old_registrations)*
                        #(#test_obligations)*
                    }
                    #[cfg(all(not(test), not(trust_vc_driver)))]
                    {
                        #(#runtime_asserts)*
                    }
                    #(#driver_markers)*
                    #ret_ident
                }
            };
        }
    }

    quote! {
        #(#extra_attrs)*
        #(#fn_attrs)*
        #vis #sig {
            #(#param_registrations)*
            #(#requires_expansions)*
            #(#recommends_expansions)*
            #(#cite_expansions)*
            #(#ensures_expansions)*
            #(#original_stmts)*
        }
    }
}

#[cfg(test)]
#[path = "contract_expand_tests.rs"]
mod tests;
