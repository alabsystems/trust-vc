// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared postcondition lowering for contracts and closures.
//!
//! All proc-macro call sites (`expand_ensures`, `expand_contract`,
//! `expand_closure`) consume postcondition expressions through this module
//! instead of independently analyzing, rewriting, and emitting them.
//!
//! The key abstraction is `LoweredPostconditions`: a *plan* that separates
//! analysis from emission, allowing callers to schedule pre-body vs post-body
//! token blocks.
//!
//! Part of #2464.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::BTreeMap;

use proc_macro2::TokenStream;
use quote::quote;
use syn::Ident;

use trust_vc_core::parse_expr_tokens_with_chains;

use crate::macro_expand::generate_obligation_collection;
use crate::old_rewriter::rewrite_old_in_tokens;

/// Distinguishes `old!(x)` (value copy) from `old!(*x)` (dereference copy).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum OldCaptureKind {
    Value,
    Deref,
}

/// Distinguishes `final!(x)` (value copy) from `final!(*x)` (dereference copy).
///
/// The exact symmetric twin of [`OldCaptureKind`] for the new-mut-ref
/// (prophecy) core (design `design-new-mut-ref.md`, Phase 0). `final(x)`
/// names the prophesied final value of a binding; `final(*x)` names the
/// prophesied final value behind a `&mut` place. This is pure plumbing: Phase 0
/// captures the surface syntax but introduces no verification behavior.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FinalCaptureKind {
    Value,
    Deref,
}

/// Controls whether test-path `old!()` lowering should rely on existing
/// symbolic registrations or first infer types from live Rust bindings.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TestOldRegistrationMode {
    SymbolicOnly,
    RegisterRuntimeValues,
}

/// A single lowered postcondition clause.
pub(crate) struct LoweredPostcondition {
    pub(crate) original_expr: TokenStream,
    pub(crate) rewritten_expr: TokenStream,
    pub(crate) rewritten_ast_string: String,
}

/// The result of lowering one or more postcondition expressions.
///
/// Holds the per-clause lowered data plus the deduplicated `old!()` and
/// `final(...)` capture tables. Callers use the `emit_*` methods to place token
/// blocks at the appropriate positions (pre-body vs post-body).
///
/// The `final_captures` table is the symmetric twin of `captures`: it records
/// `final(...)` references (new-mut-ref/prophecy core, Phase 0). It is collected
/// here for plumbing parity but no wired caller emits it yet, so it introduces
/// no verification behavior.
pub(crate) struct LoweredPostconditions {
    pub(crate) clauses: Vec<LoweredPostcondition>,
    pub(crate) captures: BTreeMap<String, OldCaptureKind>,
    // New-mut-ref Phase 0: populated by `lower_postconditions` for plumbing
    // parity but not yet consumed by any wired caller (the emit helpers are
    // exercised only by unit tests until Phase 1 wires the `final` rewriter).
    #[allow(dead_code)]
    pub(crate) final_captures: BTreeMap<String, FinalCaptureKind>,
}

/// Converts expression tokens into a canonicalized AST string at macro expansion
/// time, avoiding runtime `stringify!` collection paths.
fn canonical_expr_ast_string(expr: &TokenStream) -> String {
    parse_expr_tokens_with_chains(expr.clone())
        .map(|parsed| quote!(#parsed).to_string())
        .unwrap_or_else(|_| expr.to_string())
}

fn normalize_expr_tokens(expr: TokenStream) -> syn::Result<TokenStream> {
    parse_expr_tokens_with_chains(expr).map(|parsed| quote!(#parsed))
}

/// Analyzes and lowers postcondition expressions into a plan.
///
/// For each expression:
/// 1. Rewrites `old!(var)` → `__trust_vc_old_var` via `old_rewriter`
/// 2. Collects `old!()` captures into a deduplicated table
/// 3. Records both original and rewritten expressions for emission
///
/// Mixed-use validation: using both `old!(x)` and `old!(*x)` for the same
/// variable across any clause produces an error.
pub(crate) fn lower_postconditions(
    exprs: impl IntoIterator<Item = TokenStream>,
) -> syn::Result<LoweredPostconditions> {
    let mut clauses = Vec::new();
    let mut captures: BTreeMap<String, OldCaptureKind> = BTreeMap::new();
    let mut final_captures: BTreeMap<String, FinalCaptureKind> = BTreeMap::new();

    for original_expr in exprs {
        let (rewritten_expr, _old_vars) = rewrite_old_in_tokens(original_expr.clone())?;
        let rewritten_expr = normalize_expr_tokens(rewritten_expr)?;
        let rewritten_ast_string = canonical_expr_ast_string(&rewritten_expr);

        // Collect captures with mixed-use validation
        collect_old_captures(original_expr.clone(), &mut captures)?;
        // Symmetric twin: collect final!() captures (new-mut-ref Phase 0).
        collect_final_captures(original_expr.clone(), &mut final_captures)?;

        clauses.push(LoweredPostcondition {
            original_expr,
            rewritten_expr,
            rewritten_ast_string,
        });
    }

    Ok(LoweredPostconditions {
        clauses,
        captures,
        final_captures,
    })
}

impl LoweredPostconditions {
    /// Emits `collect_old_value(...)` or `collect_old_value_deref(...)` for the
    /// test path, optionally preceded by runtime variable registration when the
    /// caller has live Rust bindings. Part of #2651: deref captures get distinct
    /// display aliases (`old(*x)` vs `old(x)`) in counterexamples.
    pub(crate) fn emit_test_old_registrations(
        &self,
        mode: TestOldRegistrationMode,
    ) -> Vec<TokenStream> {
        let support_root = trust_vc_core::macro_support_root();
        self.captures
            .iter()
            .flat_map(|(var_name, kind)| {
                let mut registrations = Vec::new();
                if mode == TestOldRegistrationMode::RegisterRuntimeValues {
                    let var_ident = Ident::new(var_name, proc_macro2::Span::call_site());
                    registrations.push(quote! {
                        #support_root::verify_macro::collect_variable_runtime(#var_name, &#var_ident);
                    });
                }
                match kind {
                    OldCaptureKind::Value => {
                        registrations.push(quote! {
                            #support_root::verify_macro::collect_old_value(#var_name.to_string());
                        });
                    }
                    OldCaptureKind::Deref => {
                        registrations.push(quote! {
                            #support_root::verify_macro::collect_old_value_deref(#var_name.to_string());
                        });
                    }
                }
                registrations
            })
            .collect()
    }

    /// Emits runtime `let __trust_vc_old_x = x;` (or `= *x;`) bindings.
    ///
    /// Place these before the function body so postcondition assertions
    /// can reference pre-state values.
    pub(crate) fn emit_runtime_old_bindings(&self) -> Vec<TokenStream> {
        self.captures
            .iter()
            .map(|(name, kind)| {
                let old_ident = Ident::new(
                    &format!("__trust_vc_old_{name}"),
                    proc_macro2::Span::call_site(),
                );
                let var_ident = Ident::new(name, proc_macro2::Span::call_site());
                match kind {
                    OldCaptureKind::Value => quote! {
                        let #old_ident = #var_ident;
                    },
                    OldCaptureKind::Deref => quote! {
                        let #old_ident = *#var_ident;
                    },
                }
            })
            .collect()
    }

    /// Emits `collect_final_value(...)` or `collect_final_value_deref(...)` for
    /// the test path — the exact symmetric twin of
    /// [`Self::emit_test_old_registrations`]. Optionally preceded by runtime
    /// variable registration when the caller has live Rust bindings.
    ///
    /// New-mut-ref/prophecy core Phase 0: pure plumbing. No wired caller invokes
    /// this yet (only unit tests), so it introduces no verification behavior.
    #[allow(dead_code)]
    pub(crate) fn emit_test_final_registrations(
        &self,
        mode: TestOldRegistrationMode,
    ) -> Vec<TokenStream> {
        let support_root = trust_vc_core::macro_support_root();
        self.final_captures
            .iter()
            .flat_map(|(var_name, kind)| {
                let mut registrations = Vec::new();
                if mode == TestOldRegistrationMode::RegisterRuntimeValues {
                    let var_ident = Ident::new(var_name, proc_macro2::Span::call_site());
                    registrations.push(quote! {
                        #support_root::verify_macro::collect_variable_runtime(#var_name, &#var_ident);
                    });
                }
                match kind {
                    FinalCaptureKind::Value => {
                        registrations.push(quote! {
                            #support_root::verify_macro::collect_final_value(#var_name.to_string());
                        });
                    }
                    FinalCaptureKind::Deref => {
                        registrations.push(quote! {
                            #support_root::verify_macro::collect_final_value_deref(#var_name.to_string());
                        });
                    }
                }
                registrations
            })
            .collect()
    }

    /// Emits runtime `let __trust_vc_final_x = x;` (or `= *x;`) bindings — the
    /// exact symmetric twin of [`Self::emit_runtime_old_bindings`].
    ///
    /// Where `old!()` snapshots pre-state at the *entry* boundary, `final(...)`
    /// names post-state at the *exit* boundary. Phase 0 emits the same `let`
    /// shape so the exit binding twin exists; no wired caller places these yet
    /// (only unit tests), so this introduces no verification behavior.
    #[allow(dead_code)]
    pub(crate) fn emit_runtime_final_bindings(&self) -> Vec<TokenStream> {
        self.final_captures
            .iter()
            .map(|(name, kind)| {
                let final_ident = Ident::new(
                    &format!("__trust_vc_final_{name}"),
                    proc_macro2::Span::call_site(),
                );
                let var_ident = Ident::new(name, proc_macro2::Span::call_site());
                match kind {
                    FinalCaptureKind::Value => quote! {
                        let #final_ident = #var_ident;
                    },
                    FinalCaptureKind::Deref => quote! {
                        let #final_ident = *#var_ident;
                    },
                }
            })
            .collect()
    }

    /// Emits obligation collection calls for the test path.
    ///
    /// Each clause produces one `collect_obligation_expr` or
    /// `collect_typed_obligation` call with `ObligationKind::Ensures`.
    pub(crate) fn emit_test_obligations(&self) -> Vec<TokenStream> {
        let support_root = trust_vc_core::macro_support_root();
        self.clauses
            .iter()
            .map(|clause| {
                generate_obligation_collection(
                    &clause.rewritten_expr,
                    &clause.rewritten_ast_string,
                    quote! { #support_root::vc::ObligationKind::Ensures },
                    "ensures_line_",
                )
            })
            .collect()
    }

    /// Emits the rustc-driver surface-bridge postcondition markers: one BARE,
    /// statement-level `::trust_vc_core::__driver_markers::ensures(<cond>);` per
    /// clause, each gated `#[cfg(trust_vc_driver)]`.
    ///
    /// Each marker is a bare statement (not block-wrapped) so the driver's
    /// statement-level marker scan sees a direct `ensures(..)` `FnDef` call and
    /// lowers the REAL postcondition. Uses the *rewritten* expression (the same
    /// one [`Self::emit_runtime_asserts`] checks), so `old!()` snapshots resolve
    /// to their `__trust_vc_old_*` bindings where the caller has emitted them.
    /// The `#[cfg(trust_vc_driver)]` gate is mutually exclusive with the `test`
    /// (collection) and `not(test)` (runtime assert) arms, so under the driver
    /// cfg the postcondition is emitted exactly once and never as a vacuous form.
    pub(crate) fn emit_driver_markers(&self) -> Vec<TokenStream> {
        self.clauses
            .iter()
            .map(|clause| {
                let rewritten = &clause.rewritten_expr;
                quote! {
                    #[cfg(trust_vc_driver)]
                    ::trust_vc_core::__driver_markers::ensures(#rewritten);
                }
            })
            .collect()
    }

    /// Emits runtime `assert!()` checks using the rewritten expressions.
    ///
    /// The assert message uses the *original* expression for readability,
    /// while the checked expression uses `__trust_vc_old_*` bindings.
    pub(crate) fn emit_runtime_asserts(&self) -> Vec<TokenStream> {
        self.clauses
            .iter()
            .map(|clause| {
                let original = &clause.original_expr;
                let rewritten = &clause.rewritten_expr;
                quote! {
                    assert!(
                        #rewritten,
                        "trust_vc postcondition failed: {}",
                        stringify!(#original)
                    );
                }
            })
            .collect()
    }

    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }
}

// --- old!() capture analysis (moved from contract_expand.rs) ---

fn parse_old_capture_group(group: &proc_macro2::Group) -> Option<(String, OldCaptureKind)> {
    let tokens: Vec<proc_macro2::TokenTree> = group.stream().into_iter().collect();
    match tokens.as_slice() {
        [proc_macro2::TokenTree::Ident(ident)] => Some((ident.to_string(), OldCaptureKind::Value)),
        [proc_macro2::TokenTree::Punct(punct), proc_macro2::TokenTree::Ident(ident)]
            if punct.as_char() == '*' =>
        {
            Some((ident.to_string(), OldCaptureKind::Deref))
        }
        _ => None,
    }
}

fn insert_old_capture(
    captures: &mut BTreeMap<String, OldCaptureKind>,
    name: String,
    kind: OldCaptureKind,
    group: &proc_macro2::Group,
) -> syn::Result<()> {
    if let Some(existing) = captures.get(&name) {
        if *existing != kind {
            return Err(syn::Error::new_spanned(
                group.clone(),
                format!(
                    "old!() for `{name}` must use one form consistently; mixing `old!({name})` and `old!(*{name})` is not supported",
                ),
            ));
        }
        return Ok(());
    }

    captures.insert(name, kind);
    Ok(())
}

fn is_double_colon(t1: &proc_macro2::TokenTree, t2: &proc_macro2::TokenTree) -> bool {
    if let (proc_macro2::TokenTree::Punct(p1), proc_macro2::TokenTree::Punct(p2)) = (t1, t2) {
        p1.as_char() == ':' && p2.as_char() == ':'
    } else {
        false
    }
}

#[allow(clippy::indexing_slicing)] // invariant: all indices bounded by `i + N < token_vec.len()` guards
fn collect_old_captures(
    tokens: TokenStream,
    captures: &mut BTreeMap<String, OldCaptureKind>,
) -> syn::Result<()> {
    let token_vec: Vec<proc_macro2::TokenTree> = tokens.into_iter().collect();
    let mut i = 0;

    while i < token_vec.len() {
        if i + 2 < token_vec.len() {
            if let proc_macro2::TokenTree::Ident(ident) = &token_vec[i] {
                if ident == "old" {
                    if let proc_macro2::TokenTree::Punct(punct) = &token_vec[i + 1] {
                        if punct.as_char() == '!' {
                            if let proc_macro2::TokenTree::Group(group) = &token_vec[i + 2] {
                                if let Some((name, kind)) = parse_old_capture_group(group) {
                                    insert_old_capture(captures, name, kind, group)?;
                                    i += 3;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
        }

        if i + 5 < token_vec.len() {
            if let proc_macro2::TokenTree::Ident(ident) = &token_vec[i] {
                if ident == "trust_vc" && is_double_colon(&token_vec[i + 1], &token_vec[i + 2]) {
                    if let proc_macro2::TokenTree::Ident(old_ident) = &token_vec[i + 3] {
                        if old_ident == "old" {
                            if let proc_macro2::TokenTree::Punct(punct) = &token_vec[i + 4] {
                                if punct.as_char() == '!' {
                                    if let proc_macro2::TokenTree::Group(group) = &token_vec[i + 5]
                                    {
                                        if let Some((name, kind)) = parse_old_capture_group(group) {
                                            insert_old_capture(captures, name, kind, group)?;
                                            i += 6;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        if let proc_macro2::TokenTree::Group(group) = &token_vec[i] {
            collect_old_captures(group.stream(), captures)?;
        }
        i += 1;
    }

    Ok(())
}

// --- final(...) capture analysis (symmetric twin of old!() above) ---
//
// New-mut-ref/prophecy core Phase 0 (`design-new-mut-ref.md`). The
// symmetric twin of the `old!()` machinery: `final(x)` -> Value, `final(*x)` ->
// Deref, with mixed-use validation and both bare and `trust_vc::`-qualified
// forms. The surface differs from `old` in one way: `final` is a reserved Rust
// keyword, so the spec op is spelled as a call `final(...)` (no `!`), matching
// the `final(value)` / `*final(x)` boundary syntax in the mut-refs regressions.
// Capture is pure token scanning; rewriting `final(...)` out of the normalized
// expression (so syn does not choke on the keyword) is Phase 1's job.

fn parse_final_capture_group(group: &proc_macro2::Group) -> Option<(String, FinalCaptureKind)> {
    let tokens: Vec<proc_macro2::TokenTree> = group.stream().into_iter().collect();
    match tokens.as_slice() {
        [proc_macro2::TokenTree::Ident(ident)] => {
            Some((ident.to_string(), FinalCaptureKind::Value))
        }
        [proc_macro2::TokenTree::Punct(punct), proc_macro2::TokenTree::Ident(ident)]
            if punct.as_char() == '*' =>
        {
            Some((ident.to_string(), FinalCaptureKind::Deref))
        }
        _ => None,
    }
}

fn insert_final_capture(
    captures: &mut BTreeMap<String, FinalCaptureKind>,
    name: String,
    kind: FinalCaptureKind,
    group: &proc_macro2::Group,
) -> syn::Result<()> {
    if let Some(existing) = captures.get(&name) {
        if *existing != kind {
            return Err(syn::Error::new_spanned(
                group.clone(),
                format!(
                    "final() for `{name}` must use one form consistently; mixing `final({name})` and `final(*{name})` is not supported",
                ),
            ));
        }
        return Ok(());
    }

    captures.insert(name, kind);
    Ok(())
}

#[allow(clippy::indexing_slicing)] // invariant: all indices bounded by `i + N < token_vec.len()` guards
fn collect_final_captures(
    tokens: TokenStream,
    captures: &mut BTreeMap<String, FinalCaptureKind>,
) -> syn::Result<()> {
    let token_vec: Vec<proc_macro2::TokenTree> = tokens.into_iter().collect();
    let mut i = 0;

    while i < token_vec.len() {
        // Bare call form: `final ( ... )`. `final` is a keyword, so the spec op
        // is a call rather than a `final!(...)` macro invocation.
        if i + 1 < token_vec.len() {
            if let proc_macro2::TokenTree::Ident(ident) = &token_vec[i] {
                if ident == "final" {
                    if let proc_macro2::TokenTree::Group(group) = &token_vec[i + 1] {
                        if group.delimiter() == proc_macro2::Delimiter::Parenthesis {
                            if let Some((name, kind)) = parse_final_capture_group(group) {
                                insert_final_capture(captures, name, kind, group)?;
                                i += 2;
                                continue;
                            }
                        }
                    }
                }
            }
        }

        // Qualified call form: `trust_vc :: final ( ... )`.
        if i + 4 < token_vec.len() {
            if let proc_macro2::TokenTree::Ident(ident) = &token_vec[i] {
                if ident == "trust_vc" && is_double_colon(&token_vec[i + 1], &token_vec[i + 2]) {
                    if let proc_macro2::TokenTree::Ident(final_ident) = &token_vec[i + 3] {
                        if final_ident == "final" {
                            if let proc_macro2::TokenTree::Group(group) = &token_vec[i + 4] {
                                if group.delimiter() == proc_macro2::Delimiter::Parenthesis {
                                    if let Some((name, kind)) = parse_final_capture_group(group) {
                                        insert_final_capture(captures, name, kind, group)?;
                                        i += 5;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        if let proc_macro2::TokenTree::Group(group) = &token_vec[i] {
            collect_final_captures(group.stream(), captures)?;
        }
        i += 1;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;

    #[test]
    fn test_lower_single_ensures_without_old() {
        let lowered = lower_postconditions(vec![quote!(x > 0)]).unwrap();
        assert_eq!(lowered.clauses.len(), 1);
        assert!(lowered.captures.is_empty());
        assert!(lowered
            .emit_test_old_registrations(TestOldRegistrationMode::SymbolicOnly)
            .is_empty());
        assert!(lowered.emit_runtime_old_bindings().is_empty());
    }

    #[test]
    fn test_lower_ensures_with_old_value() {
        let lowered = lower_postconditions(vec![quote!(ret == old!(x) + 1)]).unwrap();
        assert_eq!(lowered.clauses.len(), 1);
        assert_eq!(lowered.captures.len(), 1);
        assert_eq!(
            lowered.captures.get("x"),
            Some(&OldCaptureKind::Value),
            "old!(x) should produce Value capture"
        );

        let registrations =
            lowered.emit_test_old_registrations(TestOldRegistrationMode::SymbolicOnly);
        assert_eq!(
            registrations.len(),
            1,
            "symbolic-only mode should only collect old values"
        );
        assert!(
            registrations[0].to_string().contains("collect_old_value"),
            "symbolic-only mode should call collect_old_value, got: {}",
            registrations[0]
        );
    }

    #[test]
    fn test_lower_ensures_with_runtime_old_registration() {
        let lowered = lower_postconditions(vec![quote!(ret == old!(x) + 1)]).unwrap();

        let registrations =
            lowered.emit_test_old_registrations(TestOldRegistrationMode::RegisterRuntimeValues);
        assert_eq!(
            registrations.len(),
            2,
            "runtime mode should register + snapshot"
        );
        assert!(
            registrations[0]
                .to_string()
                .contains("collect_variable_runtime"),
            "first token should register the runtime variable, got: {}",
            registrations[0]
        );
        assert!(
            registrations[1].to_string().contains("collect_old_value"),
            "second token should call collect_old_value, got: {}",
            registrations[1]
        );

        let bindings = lowered.emit_runtime_old_bindings();
        assert_eq!(bindings.len(), 1);
        let binding_str = bindings[0].to_string();
        assert!(
            binding_str.contains("__trust_vc_old_x") && binding_str.contains("let"),
            "runtime binding should be `let __trust_vc_old_x = x`, got: {binding_str}"
        );
    }

    #[test]
    fn test_lower_ensures_with_old_deref() {
        let lowered = lower_postconditions(vec![quote!(ret == old!(*ptr) + 1)]).unwrap();
        assert_eq!(lowered.captures.len(), 1);
        assert_eq!(
            lowered.captures.get("ptr"),
            Some(&OldCaptureKind::Deref),
            "old!(*ptr) should produce Deref capture"
        );

        let bindings = lowered.emit_runtime_old_bindings();
        assert_eq!(bindings.len(), 1);
        let binding_str = bindings[0].to_string();
        assert!(
            binding_str.contains("__trust_vc_old_ptr") && binding_str.contains("* ptr"),
            "deref binding should dereference, got: {binding_str}"
        );
    }

    #[test]
    fn test_lower_multiple_clauses_dedup_captures() {
        let lowered =
            lower_postconditions(vec![quote!(ret == old!(x) + 1), quote!(ret > old!(x))]).unwrap();
        assert_eq!(lowered.clauses.len(), 2);
        assert_eq!(
            lowered.captures.len(),
            1,
            "same variable should be deduped to one capture"
        );
        assert_eq!(
            lowered
                .emit_test_old_registrations(TestOldRegistrationMode::RegisterRuntimeValues)
                .len(),
            2,
            "deduped capture should still produce one register + one old_value"
        );
    }

    #[test]
    fn test_lower_mixed_old_use_rejected() {
        let result = lower_postconditions(vec![quote!(ret == old!(x)), quote!(ret > old!(*x))]);
        let err = match result {
            Err(e) => e,
            Ok(_) => panic!("mixing old!(x) and old!(*x) should fail"),
        };
        assert!(
            err.to_string().contains("one form consistently"),
            "error should explain mixed-use rejection: {err}"
        );
    }

    #[test]
    fn test_lower_multi_variable_captures_ordered() {
        let lowered = lower_postconditions(vec![quote!(old!(b) > old!(a))]).unwrap();
        let keys: Vec<&String> = lowered.captures.keys().collect();
        assert_eq!(
            keys,
            vec!["a", "b"],
            "BTreeMap should order captures alphabetically"
        );
    }

    #[test]
    fn test_emit_test_obligations_contains_ensures_kind() {
        let lowered = lower_postconditions(vec![quote!(x > 0)]).unwrap();
        let obligations = lowered.emit_test_obligations();
        assert_eq!(obligations.len(), 1);
        assert!(
            obligations[0]
                .to_string()
                .contains("ObligationKind :: Ensures"),
            "obligation should have Ensures kind"
        );
    }

    #[test]
    fn test_emit_runtime_asserts_uses_original_for_message() {
        let lowered = lower_postconditions(vec![quote!(ret == old!(x) + 1)]).unwrap();
        let asserts = lowered.emit_runtime_asserts();
        assert_eq!(asserts.len(), 1);
        let assert_str = asserts[0].to_string();
        assert!(
            assert_str.contains("__trust_vc_old_x"),
            "assert condition should use rewritten identifier, got: {assert_str}"
        );
        assert!(
            assert_str.contains("trust_vc postcondition failed"),
            "assert should have failure message, got: {assert_str}"
        );
    }

    #[test]
    fn test_is_empty() {
        let lowered = lower_postconditions(Vec::<TokenStream>::new()).unwrap();
        assert!(lowered.is_empty());
    }

    #[test]
    fn test_qualified_old_captured() {
        let lowered = lower_postconditions(vec![quote!(ret == trust_vc::old!(x) + 1)]).unwrap();
        assert_eq!(lowered.captures.len(), 1);
        assert_eq!(lowered.captures.get("x"), Some(&OldCaptureKind::Value));
    }

    // --- final(...) capture tests (symmetric twins of the old!() tests above) ---
    //
    // `final` is a reserved keyword, so postcondition normalization (which runs
    // syn on the rewritten expression) cannot yet survive `final(...)` — that
    // rewriter is Phase 1. These tests therefore exercise the Phase-0 capture
    // plumbing directly on token streams (`collect_final_captures`) and the
    // emit helpers via a small `LoweredPostconditions` built from the captures,
    // mirroring exactly what the `old!()` tests assert about capture content,
    // kind, dedup, mixed-use rejection, ordering, and emitted tokens.

    /// Test-only: collect `final(...)` captures from a token stream.
    fn collect_finals(tokens: TokenStream) -> syn::Result<BTreeMap<String, FinalCaptureKind>> {
        let mut captures = BTreeMap::new();
        collect_final_captures(tokens, &mut captures)?;
        Ok(captures)
    }

    /// Test-only: build a `LoweredPostconditions` carrying only final captures,
    /// so the `emit_*_final_*` helpers can be exercised in isolation.
    fn lowered_with_finals(
        final_captures: BTreeMap<String, FinalCaptureKind>,
    ) -> LoweredPostconditions {
        LoweredPostconditions {
            clauses: Vec::new(),
            captures: BTreeMap::new(),
            final_captures,
        }
    }

    #[test]
    fn test_collect_no_finals() {
        let captures = collect_finals(quote!(x > 0)).unwrap();
        assert!(captures.is_empty());

        let lowered = lowered_with_finals(captures);
        assert!(lowered
            .emit_test_final_registrations(TestOldRegistrationMode::SymbolicOnly)
            .is_empty());
        assert!(lowered.emit_runtime_final_bindings().is_empty());
    }

    #[test]
    fn test_collect_final_value() {
        let captures = collect_finals(quote!(final(x) == old!(x) + 1)).unwrap();
        assert_eq!(captures.len(), 1);
        assert_eq!(
            captures.get("x"),
            Some(&FinalCaptureKind::Value),
            "final(x) should produce Value capture"
        );

        let lowered = lowered_with_finals(captures);
        let registrations =
            lowered.emit_test_final_registrations(TestOldRegistrationMode::SymbolicOnly);
        assert_eq!(
            registrations.len(),
            1,
            "symbolic-only mode should only collect final values"
        );
        assert!(
            registrations[0].to_string().contains("collect_final_value"),
            "symbolic-only mode should call collect_final_value, got: {}",
            registrations[0]
        );
    }

    #[test]
    fn test_final_runtime_registration_and_binding() {
        let captures = collect_finals(quote!(final(x) == x + 1)).unwrap();
        let lowered = lowered_with_finals(captures);

        let registrations =
            lowered.emit_test_final_registrations(TestOldRegistrationMode::RegisterRuntimeValues);
        assert_eq!(
            registrations.len(),
            2,
            "runtime mode should register + snapshot"
        );
        assert!(
            registrations[0]
                .to_string()
                .contains("collect_variable_runtime"),
            "first token should register the runtime variable, got: {}",
            registrations[0]
        );
        assert!(
            registrations[1].to_string().contains("collect_final_value"),
            "second token should call collect_final_value, got: {}",
            registrations[1]
        );

        let bindings = lowered.emit_runtime_final_bindings();
        assert_eq!(bindings.len(), 1);
        let binding_str = bindings[0].to_string();
        assert!(
            binding_str.contains("__trust_vc_final_x") && binding_str.contains("let"),
            "runtime binding should be `let __trust_vc_final_x = x`, got: {binding_str}"
        );
    }

    #[test]
    fn test_collect_final_deref() {
        let captures = collect_finals(quote!(final(*ptr) == old!(*ptr) + 1)).unwrap();
        assert_eq!(captures.len(), 1);
        assert_eq!(
            captures.get("ptr"),
            Some(&FinalCaptureKind::Deref),
            "final(*ptr) should produce Deref capture"
        );

        let lowered = lowered_with_finals(captures);
        let bindings = lowered.emit_runtime_final_bindings();
        assert_eq!(bindings.len(), 1);
        let binding_str = bindings[0].to_string();
        assert!(
            binding_str.contains("__trust_vc_final_ptr") && binding_str.contains("* ptr"),
            "deref binding should dereference, got: {binding_str}"
        );
    }

    #[test]
    fn test_collect_final_dedup() {
        let captures = collect_finals(quote!(final(x) == x + 1 && final(x) > x)).unwrap();
        assert_eq!(
            captures.len(),
            1,
            "same variable should be deduped to one final capture"
        );
        let lowered = lowered_with_finals(captures);
        assert_eq!(
            lowered
                .emit_test_final_registrations(TestOldRegistrationMode::RegisterRuntimeValues)
                .len(),
            2,
            "deduped capture should still produce one register + one final_value"
        );
    }

    #[test]
    fn test_collect_final_mixed_use_rejected() {
        let result = collect_finals(quote!(final(x) == 0 && final(*x) > 0));
        let err = match result {
            Err(e) => e,
            Ok(_) => panic!("mixing final(x) and final(*x) should fail"),
        };
        assert!(
            err.to_string().contains("one form consistently"),
            "error should explain mixed-use rejection: {err}"
        );
    }

    #[test]
    fn test_collect_final_multi_variable_ordered() {
        let captures = collect_finals(quote!(final(b) > final(a))).unwrap();
        let keys: Vec<&String> = captures.keys().collect();
        assert_eq!(
            keys,
            vec!["a", "b"],
            "BTreeMap should order final captures alphabetically"
        );
    }

    #[test]
    fn test_collect_qualified_final() {
        let captures = collect_finals(quote!(trust_vc::final(x) == x + 1)).unwrap();
        assert_eq!(captures.len(), 1);
        assert_eq!(captures.get("x"), Some(&FinalCaptureKind::Value));
    }

    #[test]
    fn test_collect_final_nested_in_group() {
        // Captures are found when nested inside a delimited group, mirroring the
        // recursive descent the old!() collector performs.
        let captures = collect_finals(quote!(foo(final(y)) == 0)).unwrap();
        assert_eq!(captures.len(), 1);
        assert_eq!(captures.get("y"), Some(&FinalCaptureKind::Value));
    }

    #[test]
    fn test_old_and_final_captures_independent() {
        // A single expression referencing both old!() and final(...) populates
        // both tables independently; the new-mut-ref plumbing does not perturb
        // the existing old!() collection.
        let expr = quote!(final(*x) == old!(*x) + 1);
        let mut old_caps: BTreeMap<String, OldCaptureKind> = BTreeMap::new();
        collect_old_captures(expr.clone(), &mut old_caps).unwrap();
        let final_caps = collect_finals(expr).unwrap();

        assert_eq!(old_caps.len(), 1);
        assert_eq!(old_caps.get("x"), Some(&OldCaptureKind::Deref));
        assert_eq!(final_caps.len(), 1);
        assert_eq!(final_caps.get("x"), Some(&FinalCaptureKind::Deref));
    }
}
