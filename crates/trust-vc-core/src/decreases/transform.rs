//! Recursive-call scan and decrease obligation injection.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Implements the body transformation that injects `MeasureDecreases`
//! obligations before each recursive call site (#1337, #1353).
//! Extended with qualified-path resolution for automatic SCC detection (#2054).
//! Extended with method call handling for impl block recursion (#2550).

use std::collections::HashSet;
use std::sync::Arc;

use proc_macro2::TokenStream;
use quote::quote;

use super::measure_shape::{
    render_entry_measure, render_recursive_measure, render_unsupported_recursive_measure_condition,
    MeasurePlan,
};
use crate::mode_index::{CanonicalFnPath, CrateModeIndex};
use crate::mode_paths;

/// Context for resolving qualified call paths to canonical crate-relative paths.
/// When present, the transform can match calls like `self::is_odd(...)` or
/// `crate::m::is_even(...)` against SCC members, not just bare ident matching.
pub(crate) struct ResolverContext {
    pub index: Arc<CrateModeIndex>,
    pub caller_module: Vec<String>,
    pub scc_members: HashSet<CanonicalFnPath>,
    pub current: CanonicalFnPath,
}

/// Transforms the function body to inject decrease checks before recursive calls.
/// This implements the fix for #1337 and #1353 - only verifying at recursion points.
///
/// `mutual_peers` contains names of mutually recursive functions. Calls to these
/// peers also get `MeasureDecreases` obligations injected, checking that the
/// peer's arguments (as a measure) are less than the caller's entry measure.
///
/// `resolver` optionally provides qualified-path resolution for automatic SCC
/// detection (#2054). When present, calls like `self::peer(...)` are resolved
/// and matched against SCC members.
pub(super) fn transform_body_with_checks(
    block: &syn::Block,
    fn_name: &syn::Ident,
    entry_measure: &TokenStream,
    measure_plan: Option<&MeasurePlan>,
    when_condition: Option<&TokenStream>,
    mutual_peers: &[String],
    resolver: Option<&ResolverContext>,
) -> TokenStream {
    use syn::fold::{self, Fold};
    use syn::{Expr, ExprCall};

    struct RecursiveCallRewriter<'a> {
        fn_name: &'a syn::Ident,
        entry_measure_str: &'a str,
        measure_plan: Option<&'a MeasurePlan>,
        when_condition_str: Option<&'a str>,
        mutual_peers: &'a [String],
        resolver: Option<&'a ResolverContext>,
        next_call_index: usize,
    }

    impl<'a> RecursiveCallRewriter<'a> {
        fn recursive_argument_string(
            args: &syn::punctuated::Punctuated<Expr, syn::Token![,]>,
        ) -> Option<String> {
            if args.len() == 1 {
                let arg = args.first()?;
                Some(quote!(#arg).to_string())
            } else if !args.is_empty() {
                Some(quote!((#args)).to_string())
            } else {
                None
            }
        }

        fn call_path_tail(path: &syn::ExprPath) -> Option<&syn::Ident> {
            if path.qself.is_some() {
                return None;
            }
            path.path.segments.last().map(|segment| &segment.ident)
        }

        /// Checks if a call path resolves to a function in the same SCC
        /// using the qualified-path resolver. Falls back to tail-name matching
        /// when no resolver is available.
        fn is_scc_peer(&self, path: &syn::ExprPath) -> bool {
            if path.qself.is_some() {
                return false;
            }

            let resolver = match self.resolver {
                Some(r) => r,
                None => return false,
            };

            // Build a CallPath from the syn path.
            let segments: Vec<String> = path
                .path
                .segments
                .iter()
                .map(|s| s.ident.to_string())
                .collect();
            let span = path
                .path
                .segments
                .last()
                .map_or(proc_macro2::Span::call_site(), |s| s.ident.span());
            let call_path = mode_paths::CallPath {
                segments,
                span,
                leading_colon: path.path.leading_colon.is_some(),
            };

            // Try to resolve to a canonical path.
            if let Some(resolved) =
                mode_paths::resolve_call_path(&call_path, &resolver.caller_module, &resolver.index)
            {
                // Check if resolved path is in the SCC (and not the current function).
                if resolved != resolver.current && resolver.scc_members.contains(&resolved) {
                    return true;
                }
                // Also detect self-recursion through qualified paths.
                if resolved == resolver.current {
                    return true;
                }
            }

            false
        }

        /// Generates the decrease condition string for a recursive call.
        /// `is_self_call` indicates whether this is a self-recursive call (same
        /// function). For mutual recursion with `RecursiveAware` measures, we
        /// conservatively emit a rejecting condition because the caller's
        /// `param_index` mapping is unreliable for peers with different
        /// parameter orderings. Fix for #2550 finding F3.
        fn decrease_condition_for_call(
            &self,
            args: &syn::punctuated::Punctuated<Expr, syn::Token![,]>,
            is_self_call: bool,
        ) -> Option<String> {
            match self.measure_plan {
                Some(MeasurePlan::RecursiveAware(components)) => {
                    let old_measure = render_entry_measure(components);
                    let Some(new_measure) =
                        render_recursive_measure(components, args, is_self_call)
                    else {
                        // Mutual recursive peer: we cannot safely map the caller's
                        // measure shape onto the callee's parameter order.
                        // Emit a rejecting obligation instead of silently
                        // eliding MeasureDecreases.
                        return Some("false".to_string());
                    };
                    Some(crate::decreases_lex::lexicographic_decreases_condition(
                        &old_measure,
                        &new_measure,
                    ))
                }
                Some(MeasurePlan::UnsupportedRecursiveDatatype) => Some(
                    render_unsupported_recursive_measure_condition(self.when_condition_str),
                ),
                _ => {
                    let recursive_arg = Self::recursive_argument_string(args)?;
                    Some(crate::decreases_lex::lexicographic_decreases_condition(
                        self.entry_measure_str,
                        &recursive_arg,
                    ))
                }
            }
        }

        /// Builds the obligation TokenStream for a decrease condition.
        fn build_obligation(&self, decrease_condition: String, call_index: usize) -> TokenStream {
            let fn_name_str = self.fn_name.to_string();
            let support_root = crate::macro_support_root();
            let guarded_condition = if let Some(when_condition) = self.when_condition_str {
                if matches!(
                    self.measure_plan,
                    Some(MeasurePlan::UnsupportedRecursiveDatatype)
                ) {
                    decrease_condition
                } else {
                    format!("(!({})) || ({})", when_condition, decrease_condition)
                }
            } else {
                decrease_condition
            };
            let try_builder = syn::parse_str::<syn::Expr>(&guarded_condition)
                .ok()
                .as_ref()
                .and_then(crate::expr_codegen::expr_to_try_builder_tokens);

            if let Some(builder) = try_builder {
                quote! {
                    if let Some(__trust_vc_expr) = { #builder } {
                        #support_root::verify_macro::collect_obligation_expr(
                            #support_root::vc::ObligationKind::MeasureDecreases,
                            format!("{}:recursive_call_{}", #fn_name_str, #call_index),
                            #guarded_condition.to_string(),
                            __trust_vc_expr,
                            Some(format!("{}:{}", file!(), line!()))
                        );
                    } else {
                        #support_root::verify_macro::collect_obligation(
                            #support_root::vc::ObligationKind::MeasureDecreases,
                            format!("{}:recursive_call_{}", #fn_name_str, #call_index),
                            #guarded_condition.to_string(),
                            Some(format!("{}:{}", file!(), line!()))
                        );
                    }
                }
            } else {
                quote! {
                    #support_root::verify_macro::collect_obligation(
                        #support_root::vc::ObligationKind::MeasureDecreases,
                        format!("{}:recursive_call_{}", #fn_name_str, #call_index),
                        #guarded_condition.to_string(),
                        Some(format!("{}:{}", file!(), line!()))
                    );
                }
            }
        }

        fn wrap_recursive_call(&mut self, call: ExprCall, is_self_call: bool) -> Expr {
            let call_index = self.next_call_index;
            self.next_call_index += 1;
            let Some(decrease_condition) =
                self.decrease_condition_for_call(&call.args, is_self_call)
            else {
                return Expr::Call(fold::fold_expr_call(self, call));
            };
            let obligation = self.build_obligation(decrease_condition, call_index);
            let folded_call = fold::fold_expr_call(self, call);
            syn::parse2(quote! {{
                #obligation
                #folded_call
            }})
            .unwrap_or(Expr::Call(folded_call))
        }

        /// Wraps a recursive method call (receiver.method(args)) with decrease
        /// obligations. Prepends the receiver to the args to align with
        /// `param_index` from the function signature (which includes `self`).
        /// Fix for #2550 finding F1 (method call obligation injection).
        fn wrap_recursive_method_call(
            &mut self,
            method_call: syn::ExprMethodCall,
            is_self_call: bool,
        ) -> Expr {
            let call_index = self.next_call_index;
            self.next_call_index += 1;
            // Prepend receiver to args to align with param_index from signature
            // (which counts self/receiver as index 0).
            let mut synthetic_args = syn::punctuated::Punctuated::new();
            synthetic_args.push((*method_call.receiver).clone());
            for arg in &method_call.args {
                synthetic_args.push(arg.clone());
            }
            let Some(decrease_condition) =
                self.decrease_condition_for_call(&synthetic_args, is_self_call)
            else {
                return Expr::MethodCall(fold::fold_expr_method_call(self, method_call));
            };
            let obligation = self.build_obligation(decrease_condition, call_index);
            let folded_call = fold::fold_expr_method_call(self, method_call);
            syn::parse2(quote! {{
                #obligation
                #folded_call
            }})
            .unwrap_or(Expr::MethodCall(folded_call))
        }
    }

    impl Fold for RecursiveCallRewriter<'_> {
        fn fold_expr(&mut self, expr: Expr) -> Expr {
            match expr {
                Expr::Call(call) => {
                    let (tail_ident, is_qualified_scc) = match call.func.as_ref() {
                        Expr::Path(path) => {
                            let tail = Self::call_path_tail(path);
                            let qualified_scc = self.is_scc_peer(path);
                            (tail, qualified_scc)
                        }
                        _ => (None, false),
                    };
                    let is_self_recursive = tail_ident.is_some_and(|ident| ident == self.fn_name);
                    let is_mutual_peer = !is_self_recursive
                        && tail_ident.is_some_and(|ident| {
                            self.mutual_peers.iter().any(|peer| ident == peer)
                        });
                    if is_self_recursive || is_mutual_peer || is_qualified_scc {
                        return self.wrap_recursive_call(call, is_self_recursive);
                    }
                    Expr::Call(fold::fold_expr_call(self, call))
                }
                // Handle method calls (e.g., self.recurse(n-1)) for impl block
                // recursion detection. Fix for #2550 finding F1.
                Expr::MethodCall(method_call) => {
                    let method_name = method_call.method.to_string();
                    let is_self_recursive = method_call.method == *self.fn_name;
                    let is_mutual_peer = !is_self_recursive
                        && self.mutual_peers.iter().any(|peer| peer == &method_name);
                    if is_self_recursive || is_mutual_peer {
                        return self.wrap_recursive_method_call(method_call, is_self_recursive);
                    }
                    Expr::MethodCall(fold::fold_expr_method_call(self, method_call))
                }
                other => fold::fold_expr(self, other),
            }
        }
    }

    let entry_measure_str = quote!(#entry_measure).to_string();
    let when_condition_str = when_condition.map(|condition| quote!(#condition).to_string());
    let mut rewriter = RecursiveCallRewriter {
        fn_name,
        entry_measure_str: &entry_measure_str,
        measure_plan,
        when_condition_str: when_condition_str.as_deref(),
        mutual_peers,
        resolver,
        next_call_index: 0,
    };
    let transformed_block = rewriter.fold_block(block.clone());
    quote! { #transformed_block }
}
