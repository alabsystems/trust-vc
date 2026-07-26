// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::{TraitBound, TrustVcType};
use crate::vc::{FunctionContext, ProofObligation, VerificationContext};
use quote::{format_ident, ToTokens};
use std::collections::{BTreeMap, BTreeSet};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{Expr, File, Ident, ItemFn, Token};

use super::body_extract::TraitMethodCallContract;
use super::{extract_type_name, extract_vars_from_input, SourceStructRegistry};

/// The trait receiver binding name used inside trait-method `requires` clauses.
/// Mirrors `encoder::trait_encoding::TRAIT_RECEIVER_NAME` ("self"); kept as a
/// local literal because that constant is private to the encoder module.
const TRAIT_RECEIVER_NAME: &str = "self";

/// Builds the caller-side `requires` contract map for generic trait-bounded
/// method calls.
///
/// For each `TraitBound { type_param, trait_name }`, finds the matching
/// `TraitDecl`, and for each of that trait's methods with a NON-EMPTY
/// `requires`, produces a `((type_param, method_name), TraitMethodCallContract)`
/// entry. Methods with no `requires` are intentionally omitted (fail-closed
/// scope: there is nothing for the caller to discharge).
///
/// Purely functional: no I/O, no `vc` mutation — independently unit-testable.
pub(super) fn trait_bound_method_requires(
    trait_bounds: &[TraitBound],
    trait_decls: &[crate::ir::TraitDecl],
) -> BTreeMap<(String, String), TraitMethodCallContract> {
    let mut map = BTreeMap::new();
    for bound in trait_bounds {
        // Walk the trait's own methods AND its (transitive) supertraits'
        // methods (unit 6). A method declared on a supertrait `Super` is still
        // callable through a `bound.trait_name`-bounded receiver, so its
        // `requires` must be discharged. `declaring_trait` is the trait that
        // actually DECLARED the method (`Super`, not `bound.trait_name`) — the
        // encoder's linking axiom grounds `Super__super_m`, so the `uf_prefix`
        // MUST use the declaring trait.
        for (declaring_trait, method) in supertrait_closure_methods(trait_decls, &bound.trait_name)
        {
            if method.requires.is_empty() {
                continue;
            }
            let contract = TraitMethodCallContract {
                receiver_binding: TRAIT_RECEIVER_NAME.to_string(),
                param_names: method
                    .params
                    .iter()
                    .map(|(name, _ty)| name.clone())
                    .collect(),
                requires: method.requires.clone(),
                uf_prefix: format!("{}__{}", declaring_trait, method.name),
            };
            map.insert((bound.type_param.clone(), method.name.clone()), contract);
        }
    }
    map
}

/// Returns the supertrait-method closure for `start`: every method reachable
/// from the `start` trait through its (transitive) supertrait chain, paired
/// with the NAME of the trait that DECLARED it.
///
/// Traversal is a start-first BFS over `TraitDecl::supertraits`:
/// - `visited` (by trait name) makes cyclic supertrait graphs total (no
///   infinite loop) — Rust forbids supertrait cycles, but a malformed input
///   must not hang the verifier.
/// - `claimed` (by METHOD name) implements Rust method shadowing: the
///   most-derived declaration (nearest to `start` in BFS order) wins, and a
///   same-named method on a more-distant supertrait is dropped. Because BFS
///   visits `start` first, then its direct supertraits, then their supertraits,
///   the first declaration seen for a given method name is the most-derived.
///
/// An unknown supertrait name (no matching `TraitDecl`) simply contributes
/// nothing (it is enqueued but yields no methods and no further edges) — a
/// missed obligation is conservative.
pub(crate) fn supertrait_closure_methods<'a>(
    trait_decls: &'a [crate::ir::TraitDecl],
    start: &str,
) -> Vec<(String, &'a crate::ir::TraitMethodDecl)> {
    let mut out: Vec<(String, &'a crate::ir::TraitMethodDecl)> = Vec::new();
    let mut visited: BTreeSet<String> = BTreeSet::new();
    let mut claimed: BTreeSet<String> = BTreeSet::new();
    let mut queue: std::collections::VecDeque<String> = std::collections::VecDeque::new();
    queue.push_back(start.to_string());
    visited.insert(start.to_string());

    while let Some(trait_name) = queue.pop_front() {
        let Some(decl) = trait_decls.iter().find(|decl| decl.name == trait_name) else {
            // Unknown trait: no methods, no edges. Conservative.
            continue;
        };
        for method in &decl.methods {
            // Most-derived (nearest-to-`start`) declaration of a given method
            // name wins; a same-named method on a more-distant supertrait is
            // shadowed and dropped.
            if claimed.insert(method.name.clone()) {
                out.push((decl.name.clone(), method));
            }
        }
        for supertrait in &decl.supertraits {
            if visited.insert(supertrait.clone()) {
                queue.push_back(supertrait.clone());
            }
        }
    }
    out
}

/// Returns true if `ty` carries a `TypeParam` NESTED inside a type constructor
/// (e.g. `Seq<P>`, `Wrapper<P>`, `Map<K, V>`) — a genuine GENERIC instantiation
/// that unit 2 skips.
///
/// A BARE top-level `TypeParam` is deliberately NOT treated as "nested": a
/// concrete struct named with a 1-2-char uppercase identifier (e.g. `S`, `T`)
/// is misclassified by `parse_or_opaque`'s short-uppercase heuristic (#2431) as
/// `TypeParam("S")` at impl-parse time even though it is concrete. Skipping such
/// impls would silently drop the obligation (the bug behind unit-2 obstacle 3).
/// Keying a bare `TypeParam` as a concrete type name is sound: the concrete
/// dispatch arm fires ONLY for non-`TypeParam` receivers, so a genuine generic
/// blanket impl `impl<P> T for P` (whose receiver resolves to `TypeParam("P")`)
/// is routed to the unit-1 generic arm and never consults this concrete entry.
fn type_has_nested_type_param(ty: &TrustVcType) -> bool {
    fn contains(ty: &TrustVcType) -> bool {
        match ty {
            TrustVcType::TypeParam(_) => true,
            TrustVcType::Seq(inner)
            | TrustVcType::Array(inner, _)
            | TrustVcType::Set(inner)
            | TrustVcType::Multiset(inner) => contains(inner),
            TrustVcType::Map(key, value) => contains(key) || contains(value),
            TrustVcType::SpecFn(args, ret) => args.iter().any(contains) || contains(ret),
            TrustVcType::Datatype { variants, .. } => variants
                .iter()
                .any(|variant| variant.fields.iter().any(|(_, ty)| contains(ty))),
            _ => false,
        }
    }
    match ty {
        // A bare top-level `TypeParam` is the heuristic-misfire case; not nested.
        TrustVcType::TypeParam(_) => false,
        TrustVcType::Seq(inner)
        | TrustVcType::Array(inner, _)
        | TrustVcType::Set(inner)
        | TrustVcType::Multiset(inner) => contains(inner),
        TrustVcType::Map(key, value) => contains(key) || contains(value),
        TrustVcType::SpecFn(args, ret) => args.iter().any(contains) || contains(ret),
        TrustVcType::Datatype { variants, .. } => variants
            .iter()
            .any(|variant| variant.fields.iter().any(|(_, ty)| contains(ty))),
        _ => false,
    }
}

/// Builds the caller-side `requires` contract map for CONCRETE-receiver
/// trait-method calls `s.f(args)` where `s: S` and `impl T for S`.
///
/// Mirrors `trait_bound_method_requires` (unit 1), keyed by the CONCRETE type
/// name (`impl_decl.concrete_type.to_type_string()`) instead of the type
/// parameter. The receiver side keys on `receiver_ty.to_type_string()`, so a
/// mismatch (e.g. `&S` vs `S`) simply fails closed — a missed obligation,
/// conservative.
///
/// For each registered `impl T for S`, every requires-bearing method of the
/// TRAIT (`trait_decl.methods`) is keyed — not just the physically-written impl
/// bindings (`impl_decl.method_bindings`). A non-overridden inherited DEFAULT
/// method `d` is absent from `method_bindings` yet is still provided by the
/// impl, so `s.d()` must discharge `T::d`'s requires (unit 5). Overridden /
/// bound methods are unchanged: they are also present in `trait_decl.methods`.
///
/// Scope/fail-closed rules:
/// - Skip GENERIC impls (concrete type contains a `TypeParam`) — out of scope.
/// - Skip impls whose `trait_name` has no matching `TraitDecl`.
/// - Skip trait methods with an EMPTY `requires` (nothing to discharge).
/// - AMBIGUITY DROP: if two DIFFERENT traits supply the same `(type, method)`
///   key, drop it entirely and never re-insert — a wrong-trait requires would
///   be a spurious failure; a missed one is conservative. Same-trait
///   re-registration is idempotent (kept).
///
/// `uf_prefix` uses the TRAIT name (`{trait}__{method}`) so the obligation
/// routes through the encoder's linking axiom `T__req(Box_S(s)) == S__req(s)`,
/// exactly as Verus's `assert req%T.f`.
///
/// Purely functional: no I/O, no `vc` mutation — independently unit-testable.
pub(super) fn concrete_impl_method_requires(
    trait_impl_decls: &[crate::ir::TraitImplDecl],
    trait_decls: &[crate::ir::TraitDecl],
) -> BTreeMap<(String, String), TraitMethodCallContract> {
    let mut map: BTreeMap<(String, String), TraitMethodCallContract> = BTreeMap::new();
    // Tracks which trait supplied each key so a DIFFERENT trait supplying the
    // same `(type, method)` triggers an ambiguity drop.
    let mut source_trait: BTreeMap<(String, String), String> = BTreeMap::new();
    // Keys dropped for ambiguity: never re-inserted.
    let mut ambiguous: BTreeSet<(String, String)> = BTreeSet::new();

    for impl_decl in trait_impl_decls {
        // Generic impls (concrete type carries a NESTED type param, e.g.
        // `impl T for Wrapper<P>`) are out of scope. A bare top-level
        // `TypeParam` is the heuristic-misfire case for a concrete struct and
        // is kept (see `type_has_nested_type_param`).
        if type_has_nested_type_param(&impl_decl.concrete_type) {
            continue;
        }
        // Skip impls whose own trait has no registered `TraitDecl` (the closure
        // would yield nothing anyway; this is an explicit fail-closed guard).
        if !trait_decls
            .iter()
            .any(|decl| decl.name == impl_decl.trait_name)
        {
            continue;
        }
        let type_name = impl_decl.concrete_type.to_type_string();
        // Iterate the TRAIT's methods directly (not `impl_decl.method_bindings`)
        // AND its (transitive) supertraits' methods (unit 6). A valid
        // `impl T for S` provides EVERY method of `T`: an overridden method
        // appears as an `ImplItem::Fn` binding, while a non-overridden INHERITED
        // DEFAULT is absent from `method_bindings` (built only from the
        // physically-written impl fns — `parse_trait_impl_decl`). Likewise a
        // method declared on a SUPERTRAIT `Super` is still callable on `s: S`
        // and its `requires` is `Super`'s contract. The `requires` is the
        // DECLARING trait's contract regardless of override / inheritance, so
        // `s.m()` for ANY requires-bearing method `m` reachable from `T` must
        // discharge `m`'s requires (units 5 + 6). `declaring_trait` is the trait
        // that actually declared the method — LOAD-BEARING for both the
        // `uf_prefix` (the encoder's linking axiom grounds
        // `Super__super_m(Box_S(s)) == S__super_m(s)` keyed on the declaring
        // trait) and the `source_trait` ambiguity bookkeeping (so `Super`
        // reached via both `impl T for S` and `impl Super for S` is idempotent,
        // not a spurious cross-trait drop).
        for (declaring_trait, method) in
            supertrait_closure_methods(trait_decls, &impl_decl.trait_name)
        {
            if method.requires.is_empty() {
                continue;
            }
            let key = (type_name.clone(), method.name.clone());
            if ambiguous.contains(&key) {
                continue;
            }
            match source_trait.get(&key) {
                // A DIFFERENT declaring trait already claimed this key:
                // ambiguous, drop. Keyed on the DECLARING trait so the same
                // method reached through two impls of related traits (e.g. `T`
                // and `Super` both impl'd for `S`, `Super` declaring the method)
                // is idempotent rather than a spurious drop.
                Some(existing) if existing != &declaring_trait => {
                    map.remove(&key);
                    ambiguous.insert(key);
                    continue;
                }
                // Same declaring-trait (idempotent) re-registration, or first
                // insertion.
                _ => {
                    source_trait.insert(key.clone(), declaring_trait.clone());
                }
            }
            let contract = TraitMethodCallContract {
                receiver_binding: TRAIT_RECEIVER_NAME.to_string(),
                param_names: method
                    .params
                    .iter()
                    .map(|(name, _ty)| name.clone())
                    .collect(),
                requires: method.requires.clone(),
                uf_prefix: format!("{}__{}", declaring_trait, method.name),
            };
            map.insert(key, contract);
        }
    }
    map
}

/// Builds the caller-side `requires` contract map for INHERENT (non-trait)
/// method calls `x.m(args)` where `x: S` and `impl S { #[trust_vc::proof]
/// #[requires(..)] fn m(&self, ..) }` (unit 3).
///
/// Inherent impls never enter `trait_impl_decls` (`parse_trait_impl_decl` hard-
/// errors on `impl Type` without a trait), so the unit-2 concrete map is
/// structurally empty for them. This walks the raw `syn::Item::Impl` blocks with
/// `trait_.is_none()` directly and produces a `((type_name, method),
/// TraitMethodCallContract)` map keyed by the SAME `to_type_string()` the
/// concrete builder + receiver resolution use, so the existing `other =>`
/// dispatch arm in `record_trait_method_contract_call` resolves inherent
/// receivers with ZERO body_extract change.
///
/// An inherent `requires` references the receiver's OWN concrete fields/spec
/// methods (`self.v > 0` -> ground `s.v > 0`), so — unlike unit 2 — there is no
/// dependence on a `T__req(Box_S(s)) == S__req(s)` linking axiom: the obligation
/// is a plain ground condition once `self := receiver` is substituted.
///
/// Scope/fail-closed rules:
/// - Skip GENERIC inherent impls (self type contains a NESTED type param) — out
///   of scope (a bare top-level `TypeParam` short-uppercase misfire is KEPT, via
///   `type_has_nested_type_param`, matching the concrete builder).
/// - Skip methods with an EMPTY `requires` (nothing to discharge).
/// - Recurse inline modules.
///
/// Hard error (fail-closed): a malformed `#[requires]`/contract attribute, via
/// `extract_contracts`.
///
/// Purely functional: no I/O, no `vc` mutation — independently unit-testable.
pub(super) fn inherent_impl_method_requires(
    items: &[syn::Item],
) -> TrustVcResult<BTreeMap<(String, String), TraitMethodCallContract>> {
    let mut map = BTreeMap::new();
    collect_inherent_impl_method_requires(items, &mut map)?;
    Ok(map)
}

fn collect_inherent_impl_method_requires(
    items: &[syn::Item],
    map: &mut BTreeMap<(String, String), TraitMethodCallContract>,
) -> TrustVcResult<()> {
    for item in items {
        match item {
            // Inherent impl: `impl Type { ... }` (NO trait). Trait impls are
            // handled by the unit-2 concrete builder via `trait_impl_decls`.
            syn::Item::Impl(item_impl) if item_impl.trait_.is_none() => {
                let impl_type_params: BTreeSet<String> = item_impl
                    .generics
                    .type_params()
                    .map(|param| param.ident.to_string())
                    .collect();
                let self_type = self_ty_to_trust_vc_type(&item_impl.self_ty, &impl_type_params);
                // Generic self (nested type param) is out of scope; a bare
                // top-level `TypeParam` short-uppercase misfire is kept.
                if type_has_nested_type_param(&self_type) {
                    continue;
                }
                let type_name = self_type.to_type_string();
                for impl_item in &item_impl.items {
                    let syn::ImplItem::Fn(method) = impl_item else {
                        continue;
                    };
                    // `default_ensures` is not legal on an inherent (non-trait)
                    // impl method; reject before `extract_contracts` silently
                    // drops it (fail closed even for a requires-less method).
                    crate::extern_spec_helpers::forbid_default_ensures(&method.attrs)?;
                    // Surface arg only affects error text on a malformed attr.
                    let (requires, _ensures) =
                        crate::extern_spec_helpers::extract_contracts(&method.attrs, "proof")?;
                    if requires.is_empty() {
                        continue;
                    }
                    let param_names = inherent_method_param_names(&method.sig);
                    let contract = TraitMethodCallContract {
                        receiver_binding: TRAIT_RECEIVER_NAME.to_string(),
                        param_names,
                        requires,
                        uf_prefix: format!("{type_name}__{}", method.sig.ident),
                    };
                    map.insert((type_name.clone(), method.sig.ident.to_string()), contract);
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    collect_inherent_impl_method_requires(inner_items, map)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Derives a `TrustVcType` from an inherent impl's `self_ty` the SAME way
/// `trait_expand::parse_trait_impl_decl` derives a trait impl's `concrete_type`
/// (`parse_trust_vc_type` with the impl's type params), so the resulting
/// `to_type_string()` KEY matches the receiver's `to_type_string()` at the call
/// site. A `self_ty` matching an impl type param becomes `TypeParam`; otherwise
/// `parse_or_opaque` (which yields the same `to_type_string()` regardless of the
/// concrete `Datatype`/`Opaque`/short-uppercase-`TypeParam` shape).
fn self_ty_to_trust_vc_type(ty: &syn::Type, impl_type_params: &BTreeSet<String>) -> TrustVcType {
    let ty_str = crate::local_vars_helpers::extract_type_string(ty);
    if impl_type_params.contains(&ty_str) {
        TrustVcType::TypeParam(ty_str)
    } else {
        TrustVcType::parse_or_opaque(&ty_str)
    }
}

/// The inherent method's declared parameter names (excluding the `self`
/// receiver), in order — substituted positionally by the call arguments.
fn inherent_method_param_names(sig: &syn::Signature) -> Vec<String> {
    sig.inputs
        .iter()
        .enumerate()
        .filter_map(|(index, input)| match input {
            syn::FnArg::Receiver(_) => None,
            syn::FnArg::Typed(pat_type) => Some(match pat_type.pat.as_ref() {
                syn::Pat::Ident(pat_ident) => pat_ident.ident.to_string(),
                _ => format!("arg{index}"),
            }),
        })
        .collect()
}

pub(super) fn apply_source_trait_declarations(
    file: &File,
    vc: &mut VerificationContext,
) -> TrustVcResult<()> {
    let trait_contracts = SourceTraitContractRegistry::from_file(file)?;
    collect_source_trait_declarations(&file.items, vc, &trait_contracts)
}

/// Returns true if `items` declares at least one `#[trust_vc::trait_impl]`
/// block (recursing into inline modules). Used to gate source trait
/// registration for the unit-2 concrete-receiver `requires` discharge.
pub(super) fn file_declares_trait_impls(items: &[syn::Item]) -> bool {
    items.iter().any(|item| match item {
        syn::Item::Impl(item_impl) => has_trust_vc_attr(&item_impl.attrs, "trait_impl"),
        syn::Item::Mod(module) => module
            .content
            .as_ref()
            .is_some_and(|(_, inner_items)| file_declares_trait_impls(inner_items)),
        _ => false,
    })
}

fn collect_source_trait_declarations(
    items: &[syn::Item],
    vc: &mut VerificationContext,
    trait_contracts: &SourceTraitContractRegistry,
) -> TrustVcResult<()> {
    for item in items {
        match item {
            syn::Item::Trait(item_trait) if has_trust_vc_attr(&item_trait.attrs, "trait_spec") => {
                vc.register_trait_decl(crate::trait_expand::parse_trait_decl(item_trait)?);
            }
            // Register `#[trust_vc::trait_impl] impl T for S` blocks so the
            // concrete-receiver `requires` discharge (unit 2) can look up the
            // `(concrete_type, method)` -> `TraitImplDecl` binding from source.
            // Without this arm `vc.trait_impl_decls()` stays empty at extraction
            // time. `register_trait_impl` dedupes by equality, so this is
            // idempotent with the verify-time `apply_registered_traits_to_context`.
            syn::Item::Impl(item_impl) if has_trust_vc_attr(&item_impl.attrs, "trait_impl") => {
                let decl = crate::trait_expand::parse_trait_impl_decl(item_impl)?;
                for impl_item in &item_impl.items {
                    if let syn::ImplItem::Fn(method) = impl_item {
                        // `default_ensures` is legal ONLY on a defaulted trait-method
                        // DECLARATION (harvested + gated in `parse_trait_method_decl`).
                        // On an impl method — whether it redeclares a defaulted
                        // trait method or overrides one — it is ill-formed and must
                        // fail the file CLOSED rather than be silently dropped by the
                        // `extract_contracts` below. (`test_disallow_default_ensures5/6`.)
                        crate::extern_spec_helpers::forbid_default_ensures(&method.attrs)?;
                        let method_name = method.sig.ident.to_string();
                        let Some((_, concrete_fn_name)) = decl
                            .method_bindings
                            .iter()
                            .find(|(trait_method_name, _)| trait_method_name == &method_name)
                        else {
                            continue;
                        };

                        // An impl method that declares its own `returns` while the
                        // trait ALSO declares `returns` is ILL-FORMED and fails
                        // closed with a dedicated error on direct verify
                        // (`inherited_trait_method_contracts` :730, pinned by
                        // returns_postcondition `conflicting_returns_clause`). Mark
                        // THAT case conformance-exempt so the auxiliary pass does not
                        // also Counterexample it (net A already fails the file closed).
                        //
                        // An impl method that declares its OWN `requires` is NOT
                        // exempt. Its dedicated direct-verify error (:722) does NOT
                        // actually fire — `impl_method_matches_item_fn` needs full
                        // token identity INCLUDING attrs, but contract extraction
                        // strips the `requires` attr from the verified `func`, so it
                        // no longer matches the raw method and `inherited_trait_method_contracts`
                        // returns `Ok(None)` → the impl's own no-`ensures` contract →
                        // a false `Verified`. Exempting it from conformance too left
                        // NOTHING checking `body ⊨ trait ensures` (a cardinal
                        // false-verify; `trait_exempt_soundness_probe.rs`). Letting it
                        // through to conformance is fail-closed: an own-`requires`
                        // method is not body-captured (`capture_conformance_method_body`
                        // declines on `requires`), so the obligation runs with an
                        // unconstrained result and Counterexamples — refuting a
                        // violating body and, at worst, over-rejecting a conforming
                        // own-`requires` method (itself ill-formed; Verus rejects an
                        // impl that adds its own requires). A plain inherited-contract
                        // violation likewise conformance-checks and Counterexamples.
                        let trait_declares_returns = trait_contracts
                            .methods
                            .get(&(decl.trait_name.clone(), method_name.clone()))
                            .is_some_and(|contracts| contracts.has_returns);
                        // Validate the `requires` attr is well-formed (fail closed on a
                        // malformed one via `?`); the result no longer gates exemption.
                        has_requires_clause(&method.attrs)?;
                        let impl_declares_returns =
                            has_returns_clause(&method.attrs, Some(&method.sig))?;
                        if impl_declares_returns && trait_declares_returns {
                            vc.register_conformance_exempt_method(concrete_fn_name.clone());
                            continue;
                        }

                        // Otherwise capture the method's single-pure-return body,
                        // keyed by its concrete UF name, so the conformance pass can
                        // bind the method's result to what it ACTUALLY returns even
                        // when the verified function never references it (otherwise
                        // no body axiom is in scope and the contract over-rejects
                        // against an unconstrained UF — the generic/inherited-result
                        // over-rejection this fixes). The capture is soundness-gated
                        // (single pure return, no requires, no shadow) and additive:
                        // an uncaptured method keeps the prior body-axiom path.
                        if let Some(body) = super::capture_conformance_method_body(method) {
                            vc.register_trait_impl_method_body(concrete_fn_name.clone(), body);

                            // Capture the impl method's OWN `#[trust_vc::ensures]`
                            // — the strengthened postcondition it extends onto the
                            // trait contract — but ONLY now that its body was
                            // captured (so the conformance pass can pin
                            // `result == body` and VERIFY `body ⊨ impl_ensures`
                            // before any caller assumes it). `extract_contracts`
                            // drops `returns` and yields plain `ensures`. Gated to
                            // the non-exempt branch: an impl with own `requires` or
                            // a `returns`-on-both conflict is already blocked and
                            // never reaches here, so its unverified `ensures` is
                            // never propagated. Fail-closed on a malformed attr via
                            // the `?`.
                            let (_impl_requires, impl_ensures) =
                                crate::extern_spec_helpers::extract_contracts(
                                    &method.attrs,
                                    "trait_impl",
                                )?;
                            if !impl_ensures.is_empty() {
                                vc.register_trait_impl_method_ensures(
                                    concrete_fn_name.clone(),
                                    impl_ensures,
                                );
                            }
                        }
                    }
                }
                vc.register_trait_impl(decl);
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    collect_source_trait_declarations(inner_items, vc, trait_contracts)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

pub(super) fn apply_function_trait_bounds(
    func: &ItemFn,
    source_structs: Option<&SourceStructRegistry>,
    vc: &mut VerificationContext,
) -> TrustVcResult<()> {
    let trait_bounds = trait_bounds_from_signature(&func.sig);
    if trait_bounds.is_empty() {
        return Ok(());
    }

    let type_params = type_params_from_signature(&func.sig);
    let mut params = Vec::new();
    for input in &func.sig.inputs {
        for (name, ty) in extract_vars_from_input(input)? {
            params.push((
                name,
                trust_vc_type_from_source_string(&ty, source_structs, &type_params),
            ));
        }
    }

    let return_type = match &func.sig.output {
        syn::ReturnType::Type(_, ty) => {
            let ty = extract_type_name(ty);
            trust_vc_type_from_source_string(&ty, source_structs, &type_params)
        }
        syn::ReturnType::Default => TrustVcType::Unit,
    };

    vc.set_function_context(
        FunctionContext::new(
            func.sig.ident.to_string(),
            params,
            return_type,
            crate::mode::FunctionMode::Proof,
        )
        .with_trait_bounds(trait_bounds),
    );
    Ok(())
}

fn trust_vc_type_from_source_string(
    ty: &str,
    source_structs: Option<&SourceStructRegistry>,
    type_params: &BTreeSet<String>,
) -> TrustVcType {
    if type_params.contains(ty) {
        return TrustVcType::TypeParam(ty.to_string());
    }

    source_structs
        .and_then(|registry| registry.resolve_type_string(ty))
        .unwrap_or_else(|| TrustVcType::parse_or_opaque(ty))
}

fn type_params_from_signature(sig: &syn::Signature) -> BTreeSet<String> {
    sig.generics
        .type_params()
        .map(|param| param.ident.to_string())
        .collect()
}

pub(super) fn trait_bounds_from_signature(sig: &syn::Signature) -> Vec<TraitBound> {
    let mut bounds = Vec::new();

    for param in sig.generics.type_params() {
        append_trait_bounds(&mut bounds, &param.ident.to_string(), &param.bounds);
    }

    if let Some(where_clause) = &sig.generics.where_clause {
        for predicate in &where_clause.predicates {
            let syn::WherePredicate::Type(predicate) = predicate else {
                continue;
            };
            let syn::Type::Path(type_path) = &predicate.bounded_ty else {
                continue;
            };
            let Some(type_param) = type_path.path.get_ident() else {
                continue;
            };
            append_trait_bounds(&mut bounds, &type_param.to_string(), &predicate.bounds);
        }
    }

    bounds
}

fn append_trait_bounds(
    bounds: &mut Vec<TraitBound>,
    type_param: &str,
    predicates: &syn::punctuated::Punctuated<syn::TypeParamBound, syn::token::Plus>,
) {
    for bound in predicates {
        let syn::TypeParamBound::Trait(trait_bound) = bound else {
            continue;
        };
        if !matches!(trait_bound.modifier, syn::TraitBoundModifier::None) {
            continue;
        }
        let Some(trait_name) = trait_bound
            .path
            .segments
            .last()
            .map(|segment| segment.ident.to_string())
        else {
            continue;
        };
        let bound = TraitBound::new(type_param, trait_name);
        if !bounds.contains(&bound) {
            bounds.push(bound);
        }
    }
}

pub(super) fn apply_inherited_trait_method_contracts(
    file: &File,
    func: &ItemFn,
    vc: &mut VerificationContext,
    ambient_solver_mode: Option<crate::vc::SolverMode>,
) -> TrustVcResult<()> {
    let Some(contracts) = inherited_trait_method_contracts(file, func)? else {
        return Ok(());
    };

    for condition in contracts.requires {
        vc.push_obligation(with_ambient_solver_mode(
            ProofObligation::assume("precondition", condition),
            ambient_solver_mode,
        ));
    }
    for condition in contracts.ensures {
        vc.push_obligation(with_ambient_solver_mode(
            ProofObligation::assert("postcondition", condition),
            ambient_solver_mode,
        ));
    }
    Ok(())
}

fn with_ambient_solver_mode(
    obligation: ProofObligation,
    ambient_solver_mode: Option<crate::vc::SolverMode>,
) -> ProofObligation {
    match ambient_solver_mode {
        Some(mode) => obligation.with_solver_mode(mode),
        None => obligation,
    }
}

#[derive(Clone)]
struct InheritedTraitMethodContracts {
    requires: Vec<String>,
    ensures: Vec<String>,
}

fn inherited_trait_method_contracts(
    file: &File,
    func: &ItemFn,
) -> TrustVcResult<Option<InheritedTraitMethodContracts>> {
    if source_function_named_in_items(&file.items, &func.sig.ident.to_string()) {
        return Ok(None);
    }

    let mut matches = Vec::new();
    collect_matching_trait_impl_methods(&file.items, func, &mut matches);
    let Some((trait_name, method)) = matches.pop() else {
        return Ok(None);
    };
    if !matches.is_empty() {
        return Err(TrustVcError::Encoding {
            context: "extract inherited trait method contracts",
            detail: format!(
                "ambiguous trait method contract inheritance for `{}`",
                func.sig.ident
            ),
        });
    }

    let registry = SourceTraitContractRegistry::from_file(file)?;
    let Some(contracts) = registry
        .methods
        .get(&(trait_name.clone(), method.sig.ident.to_string()))
    else {
        return Ok(None);
    };

    if has_requires_clause(&method.attrs)? {
        return Err(TrustVcError::Encoding {
            context: "extract inherited trait method contracts",
            detail: "trait method implementation cannot declare requires".to_string(),
        });
    }

    if contracts.has_returns && has_returns_clause(&method.attrs, Some(&method.sig))? {
        return Err(TrustVcError::Encoding {
            context: "extract inherited trait method contracts",
            detail:
                "a `returns` clause cannot be declared on both a trait method impl and its declaration"
                    .to_string(),
        });
    }

    Ok(Some(InheritedTraitMethodContracts {
        requires: contracts.requires.clone(),
        ensures: contracts.ensures.clone(),
    }))
}

/// Returns true if any top-level (or nested-module) free `Item::Fn` in `items`
/// is named `name`. Used to distinguish a genuine free function (the unit-2
/// concrete-receiver caller) from a trait-method body (trait default / impl
/// method), which `find_function` synthesizes from a trait/impl block and which
/// is NOT a top-level `Item::Fn`.
pub(super) fn source_function_named_in_items(items: &[syn::Item], name: &str) -> bool {
    items.iter().any(|item| match item {
        syn::Item::Fn(func) => func.sig.ident == name,
        syn::Item::Mod(module) => module
            .content
            .as_ref()
            .is_some_and(|(_, inner_items)| source_function_named_in_items(inner_items, name)),
        _ => false,
    })
}

/// Returns the top-level (or nested-module) free `Item::Fn` named `name`, if any.
fn find_free_fn_in_items<'a>(items: &'a [syn::Item], name: &str) -> Option<&'a ItemFn> {
    for item in items {
        match item {
            syn::Item::Fn(func) if func.sig.ident == name => return Some(func),
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    if let Some(found) = find_free_fn_in_items(inner_items, name) {
                        return Some(found);
                    }
                }
            }
            _ => {}
        }
    }
    None
}

/// Collects the names of free-function calls (`f(args)` with a single-segment
/// path callee) reachable in `expr`, recursing into every subexpression. Method
/// calls (`recv.m(..)`) are intentionally excluded — those are handled by the
/// sibling-default inliner in the conformance pass.
fn collect_free_call_names(expr: &Expr, out: &mut BTreeSet<String>) {
    use syn::visit::Visit;

    struct CallVisitor<'a> {
        out: &'a mut BTreeSet<String>,
    }
    impl<'ast> Visit<'ast> for CallVisitor<'_> {
        fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
            if let Expr::Path(path_expr) = &*call.func {
                if path_expr.qself.is_none() && path_expr.path.segments.len() == 1 {
                    out_insert(self.out, &path_expr.path.segments[0].ident);
                }
            }
            syn::visit::visit_expr_call(self, call);
        }
    }
    fn out_insert(out: &mut BTreeSet<String>, ident: &Ident) {
        out.insert(ident.to_string());
    }

    CallVisitor { out }.visit_expr(expr);
}

/// Registers the free functions called inside the DEFAULT-method bodies of
/// in-file traits that have NO `#[trait_impl]` block, so the impl-absent
/// default-conformance pass can lower and check those bodies.
///
/// `register_trait` publishes the quantified postcondition axiom `forall self.
/// Trait__m(self) <ensures>` for every trait method unconditionally; a
/// generic-bounded caller `fn g<T: Trait>(t: T) { t.m() }` consumes it directly.
/// `verify_implless_trait_defaults` justifies that axiom by checking the default
/// body against its `ensures` — but only if the body LOWERS. A default body that
/// calls a free function (`fn m(&self) -> u32 { helper() }`) cannot be lowered on
/// the conformance surface because the verified generic caller never references
/// `helper` directly, so it is absent from the context: the conformance build
/// Errs, the Err is swallowed (fail-safe), and the unjustified postcondition
/// axiom is trusted unchecked — a false `Verified`.
///
/// Threading the called free functions into the context closes that hole while
/// preserving Verus-faithful semantics:
///  * a SPEC free function is registered transparently (helper declaration +
///    defining body axiom), so a default whose spec-fn value genuinely
///    establishes the `ensures` still Verifies (no over-rejection) and one that
///    contradicts it Counterexamples;
///  * an EXEC free function is registered as an opaque UF (signature only, no
///    body axiom), so a default relying on its value fails CLOSED — exactly as
///    Verus models a call to a function with no postcondition.
///
/// Restricted to impl-less traits (the implless pass is the sole consumer) and
/// to genuine free `Item::Fn`s in the file, so it never perturbs the impl-present
/// conformance path or registers a method/intrinsic. Purely additive: the
/// registered helpers are unreferenced by the verified function's own body, so
/// its primary verification is unchanged.
pub(super) fn register_default_body_free_function_helpers(
    file: &File,
    source_structs: Option<&SourceStructRegistry>,
    vc: &mut VerificationContext,
) -> TrustVcResult<()> {
    let impl_trait_names: BTreeSet<String> = vc
        .trait_impl_decls()
        .iter()
        .map(|impl_decl| impl_decl.trait_name.clone())
        .collect();
    let default_bodies: Vec<String> = vc
        .trait_decls()
        .iter()
        .filter(|trait_decl| !impl_trait_names.contains(&trait_decl.name))
        .flat_map(|trait_decl| trait_decl.methods.iter())
        .filter_map(|method| method.default_body.clone())
        .collect();
    if default_bodies.is_empty() {
        return Ok(());
    }

    let mut called: BTreeSet<String> = BTreeSet::new();
    for body in &default_bodies {
        if let Ok(expr) = syn::parse_str::<Expr>(body) {
            collect_free_call_names(&expr, &mut called);
        }
    }
    // Keep only genuine free functions declared in the file — never methods,
    // trait siblings, or std intrinsics.
    called.retain(|name| source_function_named_in_items(&file.items, name));
    if called.is_empty() {
        return Ok(());
    }

    let catalog = crate::spec_function_catalog::SpecFunctionCatalog::from_file(file);
    for name in &called {
        // Spec function: register transparently (helper decl + defining body
        // axiom + transitive spec deps).
        match catalog.apply_explicit_spec(name, vc) {
            Ok(true) => continue,
            // Non-spec (exec) free function: fall through to the opaque-signature
            // path below.
            Ok(false) => {}
            // Fail SAFE on a spec-registration error: leave the call unresolved
            // (the conformance build then fails safe, exactly as before), never
            // sink an unrelated verification.
            Err(_) => continue,
        }
        // Exec free function: register its SIGNATURE as an opaque UF, then — when
        // it carries a definitional `#[ensures(result == <rhs>)]` — ALSO publish
        // that postcondition as a body-axiom-shaped broadcast. Registration
        // failure (unsupported return/parameter type) is non-fatal: skip the
        // postcondition (no helper to anchor it on) and let the conformance build
        // Err and fail safe, as before.
        if let Some(item_fn) = find_free_fn_in_items(&file.items, name) {
            if super::register_source_function_signature(name, item_fn, source_structs, vc).is_ok()
            {
                register_exec_callee_postcondition_axioms(name, item_fn, source_structs, vc);
            }
        }
    }
    Ok(())
}

/// Publishes the definitional postcondition of an EXEC free callee (no
/// `#[spec]`, but carrying a `#[ensures(<binding> == <rhs>)]`) as a
/// body-axiom-shaped broadcast `forall params. <callee>(params) == <rhs>`.
///
/// WHY (round-7 over-rejection fix). `register_source_function_signature`
/// declares only the callee's SIGNATURE and DROPS its `#[ensures]`. So a
/// CONFORMING default `fn dm(&self) -> u32 { exec_post() }` whose own `ensures`
/// is `result == 7` could no longer be proved on the conformance surface —
/// `exec_post()` was left an unconstrained UF, free to take any `u32` — and a
/// generic-bounded caller regressed `Verified -> Counterexample`. Carrying the
/// callee's postcondition (here the definitional `exec_post() == 7`) lets the
/// default establish its `ensures`, exactly as the normal-caller path (and
/// Verus) model a call to an exec function WITH a postcondition.
///
/// SOUND, and the round-6 holes stay closed:
///  * The published fact is the callee's OWN contract; the callee is
///    independently verified against that same `#[ensures]`, so assuming it at
///    the (default-body) call site admits no value the callee could not actually
///    return — standard modular-contract reasoning.
///  * Restricted to a top-level `binding == rhs` (definitional) postcondition:
///    the substituted axiom `<callee>(params) == <rhs>` is body-axiom shaped, so
///    the existing [`referenced_body_axiom_broadcasts`] carry grounds it by
///    E-matching the concrete call term — literal- and variable-argument calls
///    alike. A non-definitional `#[ensures]` (inequality, conjunction, …) yields
///    no axiom; the callee stays opaque (sound, just incomplete).
///  * A postcondition-LESS exec callee (`fn bad_exec() -> u32 { 3 }`) produces
///    NO axiom — it remains an opaque UF — so the round-6
///    free-exec-call-in-default false-Verified holes still Counterexample.
///
/// [`referenced_body_axiom_broadcasts`]: crate::encoder::verification
fn register_exec_callee_postcondition_axioms(
    name: &str,
    item_fn: &ItemFn,
    source_structs: Option<&SourceStructRegistry>,
    vc: &mut VerificationContext,
) {
    // SOUNDNESS — requires-guard (the safe fallback for the round-7 false-Verified).
    //
    // The axiom published below is the UNGUARDED `forall params. <callee>(params)
    // == <rhs>`. That equality is the callee's postcondition only WHERE the
    // callee's `#[requires]` holds — the callee is verified against its
    // `#[ensures]` only under that precondition. Publishing it unguarded for a
    // requires-bearing callee is unsound: e.g. `#[requires(a == 5)]
    // #[ensures(result == 100)] fn exec_req(a: u32) -> u32 { a * 20 }` would yield
    // `forall a. exec_req(a) == 100`, letting a default `fn dm(&self) -> u32 {
    // exec_req(7) }` "establish" `result == 100` even though `7` violates
    // `requires(a == 5)` and the real impl returns 140 (and would panic) — a false
    // `Verified` for a generic caller.
    //
    // The Verus-faithful fix is a GUARDED axiom `forall params. requires(params)
    // ==> ensures(params)` PLUS discharging the call-site precondition (the
    // default body's args must satisfy the callee's `#[requires]`). Discharging a
    // free call's precondition is not tractable on this conformance-broadcast
    // surface (broadcasts are assumed facts, with no per-call-site obligation), so
    // we take the safe fallback: carry the definitional postcondition axiom ONLY
    // for a `#[requires]`-FREE exec callee (whose postcondition is unconditional).
    // A requires-bearing exec callee stays OPAQUE (signature only), so a default
    // relying on its value fails CLOSED — exactly the round-6 sound behavior —
    // rather than false-Verifying. Fail closed on a malformed contract attr too.
    if has_requires_clause(&item_fn.attrs).unwrap_or(true) {
        return;
    }
    let Ok((requires, ensures)) =
        super::helper_contract_clauses_from_attrs(&item_fn.attrs, Some(&item_fn.sig))
    else {
        return;
    };
    // Defense in depth: the canonical contract-extraction path must also surface
    // NO precondition before we publish the unguarded postcondition equality.
    if !requires.is_empty() || ensures.is_empty() {
        return;
    }
    let binding = super::attr_extract::extract_return_binding(&item_fn.attrs, Some(&item_fn.sig))
        .ok()
        .flatten()
        .unwrap_or_else(|| "result".to_string());
    // Typed params, each with a pre-freshened bound name (clash-free against the
    // current context). Bail to opaque on any unsupported parameter type/pattern.
    let Ok(Some(params)) = super::helper_params(&item_fn.sig, source_structs, vc) else {
        return;
    };

    // Map each callee param ident to its freshened bound var, and DECLARE the
    // bound var's sort so the quantified axiom lowers — mirroring
    // `SpecFunctionDef::apply_to_context`.
    let param_names: BTreeSet<String> = params.iter().map(|param| param.name.clone()).collect();
    let mut rename: BTreeMap<String, Ident> = BTreeMap::new();
    let mut bound_vars: Vec<String> = Vec::with_capacity(params.len());
    for param in &params {
        if vc.get_variable_type(&param.bound_name).is_none() {
            vc.declare_var_typed(&param.bound_name, param.ty.clone());
        }
        rename.insert(param.name.clone(), format_ident!("{}", param.bound_name));
        bound_vars.push(param.bound_name.clone());
    }
    let trigger = format!("{name}({})", bound_vars.join(", "));

    for (idx, clause) in ensures.iter().enumerate() {
        let Some(rhs) = postcondition_definitional_rhs(&clause.condition, &binding) else {
            continue;
        };
        // Fail SAFE: only carry a `rhs` whose every free ident is a callee
        // parameter (renamed below) and which makes no function/method call. This
        // guarantees the axiom lowers against the conformance context — an `rhs`
        // referencing an undeclared symbol (`result == g()`, an unresolved const,
        // a self-referential `result`) would otherwise fail to lower and sink the
        // WHOLE verification into an Error. Anything excluded just leaves the
        // callee opaque (sound, incomplete), exactly as before.
        if !rhs_is_carryable(rhs, &param_names) {
            continue;
        }
        let mut rhs = rhs.clone();
        syn::visit_mut::VisitMut::visit_expr_mut(
            &mut ExecParamRenamer { rename: &rename },
            &mut rhs,
        );
        let condition = format!("{trigger} == {}", rhs.to_token_stream());
        let axiom_name = format!("__body_axiom_{name}_exec_postcond_{idx}");
        if vc
            .obligations()
            .iter()
            .any(|obligation| obligation.name() == axiom_name)
        {
            continue;
        }
        // Attach the bound-var + trigger scaffolding exactly as the spec-function
        // catalog does (`SpecFunctionDef::apply_to_context`), including the nullary
        // case (empty `bound_vars`, trigger on the constant call term) — that is
        // what a working definitional body axiom looks like, so the broadcast is
        // encoded as an assumed fact rather than mis-encoded into a contradiction.
        vc.push_obligation(
            ProofObligation::broadcast_assume(axiom_name, condition)
                .with_bound_vars(bound_vars.clone())
                .with_trigger_patterns(vec![vec![trigger.clone()]]),
        );
    }
}

/// If `expr` is a top-level `binding == rhs` (or `rhs == binding`), returns the
/// `rhs` side — the value the postcondition pins the result to. Any other shape
/// (inequality, conjunction, a comparison not against the result binding, …)
/// returns `None`, leaving the callee opaque.
fn postcondition_definitional_rhs<'a>(expr: &'a Expr, binding: &str) -> Option<&'a Expr> {
    let Expr::Binary(bin) = expr else {
        return None;
    };
    if !matches!(bin.op, syn::BinOp::Eq(_)) {
        return None;
    }
    if expr_is_path_ident(&bin.left, binding) {
        return Some(&bin.right);
    }
    if expr_is_path_ident(&bin.right, binding) {
        return Some(&bin.left);
    }
    None
}

fn expr_is_path_ident(expr: &Expr, name: &str) -> bool {
    matches!(expr, Expr::Path(path) if path.qself.is_none() && path.path.is_ident(name))
}

/// True iff every leaf of `rhs` is safe to lower against the conformance context:
/// every single-segment path ident is one of the callee's `params`, and the
/// expression makes no function/method/macro call (which could reference an
/// unregistered symbol). Multi-segment paths (associated consts, qualified
/// names) are rejected conservatively. Guarantees the published postcondition
/// axiom cannot fail to lower and Error out an otherwise-fine verification.
fn rhs_is_carryable(rhs: &Expr, params: &BTreeSet<String>) -> bool {
    use syn::visit::Visit;

    struct Checker<'a> {
        params: &'a BTreeSet<String>,
        safe: bool,
    }
    impl<'ast> Visit<'ast> for Checker<'_> {
        fn visit_expr(&mut self, expr: &'ast Expr) {
            match expr {
                Expr::Call(_) | Expr::MethodCall(_) | Expr::Macro(_) | Expr::Closure(_) => {
                    self.safe = false;
                    return;
                }
                Expr::Path(path) => {
                    let is_param = path.qself.is_none()
                        && path.path.segments.len() == 1
                        && self
                            .params
                            .contains(&path.path.segments[0].ident.to_string());
                    if !is_param {
                        self.safe = false;
                        return;
                    }
                }
                _ => {}
            }
            syn::visit::visit_expr(self, expr);
        }
    }
    let mut checker = Checker { params, safe: true };
    checker.visit_expr(rhs);
    checker.safe
}

/// Rewrites a callee's parameter idents to their freshened bound-var names inside
/// a postcondition `rhs`, so the published quantified axiom binds cleanly.
struct ExecParamRenamer<'a> {
    rename: &'a BTreeMap<String, Ident>,
}

impl syn::visit_mut::VisitMut for ExecParamRenamer<'_> {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        if let Expr::Path(path) = expr {
            if path.qself.is_none() && path.path.segments.len() == 1 {
                if let Some(fresh) = self.rename.get(&path.path.segments[0].ident.to_string()) {
                    path.path.segments[0].ident = fresh.clone();
                    return;
                }
            }
        }
        syn::visit_mut::visit_expr_mut(self, expr);
    }
}

fn collect_matching_trait_impl_methods<'a>(
    items: &'a [syn::Item],
    func: &ItemFn,
    matches: &mut Vec<(String, &'a syn::ImplItemFn)>,
) {
    for item in items {
        match item {
            syn::Item::Impl(item_impl)
                if has_trust_vc_attr(&item_impl.attrs, "trait_impl")
                    && item_impl.trait_.is_some() =>
            {
                let trait_name = item_impl
                    .trait_
                    .as_ref()
                    .and_then(|(_, path, _)| path.segments.last())
                    .map(|segment| segment.ident.to_string());
                let Some(trait_name) = trait_name else {
                    continue;
                };
                for impl_item in &item_impl.items {
                    let syn::ImplItem::Fn(method) = impl_item else {
                        continue;
                    };
                    if impl_method_matches_item_fn(method, func) {
                        matches.push((trait_name.clone(), method));
                    }
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    collect_matching_trait_impl_methods(inner_items, func, matches);
                }
            }
            _ => {}
        }
    }
}

fn impl_method_matches_item_fn(method: &syn::ImplItemFn, func: &ItemFn) -> bool {
    method.sig.ident == func.sig.ident
        && method.sig.to_token_stream().to_string() == func.sig.to_token_stream().to_string()
        && method.block.to_token_stream().to_string() == func.block.to_token_stream().to_string()
        && attrs_to_string(&method.attrs) == attrs_to_string(&func.attrs)
}

fn attrs_to_string(attrs: &[syn::Attribute]) -> String {
    attrs
        .iter()
        .map(ToTokens::to_token_stream)
        .map(|tokens| tokens.to_string())
        .collect::<Vec<_>>()
        .join("\n")
}

#[derive(Clone, Default)]
struct SourceTraitContractRegistry {
    methods: BTreeMap<(String, String), SourceTraitMethodContracts>,
}

#[derive(Clone)]
struct SourceTraitMethodContracts {
    requires: Vec<String>,
    ensures: Vec<String>,
    has_returns: bool,
}

impl SourceTraitContractRegistry {
    fn from_file(file: &File) -> TrustVcResult<Self> {
        let mut registry = Self::default();
        collect_source_trait_contracts(&file.items, &mut registry)?;
        Ok(registry)
    }
}

fn collect_source_trait_contracts(
    items: &[syn::Item],
    registry: &mut SourceTraitContractRegistry,
) -> TrustVcResult<()> {
    for item in items {
        match item {
            syn::Item::Trait(item_trait) if has_trust_vc_attr(&item_trait.attrs, "trait_spec") => {
                let decl = crate::trait_expand::parse_trait_decl(item_trait)?;
                for method in decl.methods {
                    let mut has_returns = false;
                    for trait_item in &item_trait.items {
                        let matches_method = matches!(trait_item, syn::TraitItem::Fn(raw) if raw.sig.ident == method.name);
                        if matches_method && trait_item_returns_clause(trait_item)? {
                            has_returns = true;
                            break;
                        }
                    }
                    registry.methods.insert(
                        (decl.name.clone(), method.name),
                        SourceTraitMethodContracts {
                            requires: method.requires,
                            ensures: method.ensures,
                            has_returns,
                        },
                    );
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    collect_source_trait_contracts(inner_items, registry)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn has_trust_vc_attr(attrs: &[syn::Attribute], marker: &str) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == marker)
    })
}

fn trait_item_returns_clause(item: &syn::TraitItem) -> TrustVcResult<bool> {
    let syn::TraitItem::Fn(method) = item else {
        return Ok(false);
    };
    has_returns_clause(&method.attrs, Some(&method.sig))
}

struct ContractClause {
    name: Ident,
    _args: Vec<Expr>,
}

impl Parse for ContractClause {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let name: Ident = input.parse()?;
        let content;
        syn::parenthesized!(content in input);
        let args = Punctuated::<Expr, Token![,]>::parse_terminated(&content)?;
        Ok(Self {
            name,
            _args: args.into_iter().collect(),
        })
    }
}

fn contract_clauses(attr: &syn::Attribute) -> TrustVcResult<Vec<ContractClause>> {
    attr.parse_args_with(Punctuated::<ContractClause, Token![,]>::parse_terminated)
        .map(|clauses| clauses.into_iter().collect())
        .map_err(|source| TrustVcError::Encoding {
            context: "extract inherited trait method contracts",
            detail: format!("Failed to parse #[contract] attribute: {source}"),
        })
}

fn has_requires_clause(attrs: &[syn::Attribute]) -> TrustVcResult<bool> {
    for attr in attrs {
        #[allow(clippy::collapsible_match)]
        match super::path_last_segment(attr.path()).as_deref() {
            Some("requires") => return Ok(true),
            Some("contract") => {
                if contract_clauses(attr)?
                    .iter()
                    .any(|clause| clause.name == "requires")
                {
                    return Ok(true);
                }
            }
            _ => {}
        }
    }
    Ok(false)
}

fn has_returns_clause(
    attrs: &[syn::Attribute],
    sig: Option<&syn::Signature>,
) -> TrustVcResult<bool> {
    Ok(
        super::attr_extract::extract_return_binding(attrs, sig)?.is_some()
            || super::attr_extract::has_direct_returns_postcondition(attrs, sig)?,
    )
}

#[cfg(test)]
mod tests {
    use super::{
        concrete_impl_method_requires, inherent_impl_method_requires, supertrait_closure_methods,
        trait_bound_method_requires,
    };
    use crate::ir::{TraitBound, TraitDecl, TraitImplDecl, TraitMethodDecl, TrustVcType};

    #[test]
    fn test_trait_bound_method_requires_maps_requires_bearing_methods() {
        // Trait `T` with a requires-bearing `f` and a requires-free `req`.
        let trait_decl = TraitDecl::new(
            "T",
            vec![
                TraitMethodDecl::new(
                    "f",
                    Vec::new(),
                    TrustVcType::Unit,
                    vec!["self.req()".to_string()],
                    Vec::new(),
                    false,
                    None,
                ),
                TraitMethodDecl::new(
                    "req",
                    Vec::new(),
                    TrustVcType::Bool,
                    Vec::new(),
                    Vec::new(),
                    false,
                    None,
                ),
            ],
        );
        let bounds = vec![TraitBound::new("A", "T")];

        let map = trait_bound_method_requires(&bounds, std::slice::from_ref(&trait_decl));

        // The requires-bearing method `f` is mapped under (A, f).
        let contract = map
            .get(&("A".to_string(), "f".to_string()))
            .expect("requires-bearing trait method `f` should be mapped");
        assert_eq!(contract.receiver_binding, "self");
        assert_eq!(contract.uf_prefix, "T__f");
        assert!(
            contract.param_names.is_empty(),
            "`f` declares no non-self params: {:?}",
            contract.param_names
        );
        assert_eq!(
            contract.requires,
            vec!["self.req()".to_string()],
            "the raw requires string must be carried verbatim"
        );

        // The requires-free method `req` must NOT be mapped (fail-closed scope).
        assert!(
            !map.contains_key(&("A".to_string(), "req".to_string())),
            "requires-free trait method `req` must not produce an obligation entry: {:?}",
            map.keys().collect::<Vec<_>>()
        );
    }

    fn trait_t_with_requires_bearing_f() -> TraitDecl {
        TraitDecl::new(
            "T",
            vec![
                TraitMethodDecl::new(
                    "f",
                    Vec::new(),
                    TrustVcType::Unit,
                    vec!["self.req()".to_string()],
                    Vec::new(),
                    false,
                    None,
                ),
                TraitMethodDecl::new(
                    "req",
                    Vec::new(),
                    TrustVcType::Bool,
                    Vec::new(),
                    Vec::new(),
                    false,
                    None,
                ),
            ],
        )
    }

    #[test]
    fn test_concrete_impl_method_requires_maps_requires_bearing_method() {
        // `impl T for S` where `T::f` has a non-empty requires and `T::req` is
        // requires-free. The concrete map keys on the concrete type name `S`.
        // A concrete `S` parses to `Opaque("S")` here (no short-uppercase
        // misclassification because the test builds the type directly).
        let trait_decl = trait_t_with_requires_bearing_f();
        let impl_decl = TraitImplDecl::new(
            "T",
            TrustVcType::Opaque("S".to_string()),
            vec![
                ("f".to_string(), "S__f".to_string()),
                ("req".to_string(), "S__req".to_string()),
            ],
        );

        let map = concrete_impl_method_requires(
            std::slice::from_ref(&impl_decl),
            std::slice::from_ref(&trait_decl),
        );

        let contract = map
            .get(&("S".to_string(), "f".to_string()))
            .expect("requires-bearing concrete impl method `f` should be mapped under (S, f)");
        assert_eq!(contract.receiver_binding, "self");
        assert_eq!(contract.uf_prefix, "T__f");
        assert!(
            contract.param_names.is_empty(),
            "`f` declares no non-self params: {:?}",
            contract.param_names
        );
        assert_eq!(
            contract.requires,
            vec!["self.req()".to_string()],
            "the raw requires string must be carried verbatim"
        );

        // The requires-free method `req` must NOT be mapped (fail-closed scope).
        assert!(
            !map.contains_key(&("S".to_string(), "req".to_string())),
            "requires-free concrete impl method `req` must not produce an entry: {:?}",
            map.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_concrete_impl_method_requires_keys_bare_typeparam_concrete_type() {
        // A concrete struct named `S` is misclassified by `parse_or_opaque`'s
        // short-uppercase heuristic (#2431) as `TypeParam("S")` at impl-parse
        // time. The builder must STILL key it as the concrete type `S` (its
        // `to_type_string()`), not skip it as a generic impl — this is the
        // unit-2 obstacle-3 regression guard.
        let trait_decl = trait_t_with_requires_bearing_f();
        let impl_decl = TraitImplDecl::new(
            "T",
            TrustVcType::TypeParam("S".to_string()),
            vec![("f".to_string(), "S__f".to_string())],
        );

        let map = concrete_impl_method_requires(
            std::slice::from_ref(&impl_decl),
            std::slice::from_ref(&trait_decl),
        );

        assert!(
            map.contains_key(&("S".to_string(), "f".to_string())),
            "a bare-`TypeParam` concrete type (heuristic misfire) must key as concrete `S`: {:?}",
            map.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_concrete_impl_method_requires_skips_generic_impl() {
        // A GENERIC impl whose concrete type carries a NESTED type param
        // (`Seq<P>`) is out of unit-2 scope and produces NO entry.
        let trait_decl = trait_t_with_requires_bearing_f();
        let impl_decl = TraitImplDecl::new(
            "T",
            TrustVcType::Seq(Box::new(TrustVcType::TypeParam("P".to_string()))),
            vec![("f".to_string(), "Wrapper__f".to_string())],
        );

        let map = concrete_impl_method_requires(
            std::slice::from_ref(&impl_decl),
            std::slice::from_ref(&trait_decl),
        );

        assert!(
            map.is_empty(),
            "a generic impl (nested TypeParam) must be skipped: {:?}",
            map.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_concrete_impl_method_requires_drops_ambiguous_trait_selection() {
        // Two DIFFERENT traits `T` and `U` each declare a requires-bearing `f`,
        // and `S` impls BOTH. The `(S, f)` key is AMBIGUOUS (which trait's
        // requires?) and must be dropped entirely — a missed obligation is
        // conservative; a wrong-trait one is a spurious failure.
        let trait_t = trait_t_with_requires_bearing_f();
        let trait_u = TraitDecl::new(
            "U",
            vec![TraitMethodDecl::new(
                "f",
                Vec::new(),
                TrustVcType::Unit,
                vec!["self.other()".to_string()],
                Vec::new(),
                false,
                None,
            )],
        );
        let impl_t = TraitImplDecl::new(
            "T",
            TrustVcType::Opaque("S".to_string()),
            vec![("f".to_string(), "S__f".to_string())],
        );
        let impl_u = TraitImplDecl::new(
            "U",
            TrustVcType::Opaque("S".to_string()),
            vec![("f".to_string(), "S__f".to_string())],
        );

        let map = concrete_impl_method_requires(&[impl_t, impl_u], &[trait_t, trait_u]);

        assert!(
            !map.contains_key(&("S".to_string(), "f".to_string())),
            "an ambiguous (two-trait) (S, f) key must be dropped: {:?}",
            map.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_inherent_impl_method_requires_maps_requires_bearing_method() {
        // An inherent (non-trait) impl with a requires-bearing `m` and a
        // requires-free `n`. The builder keys on the concrete type name `S`
        // (its `to_type_string()`), carries the raw `requires`, the `self`
        // receiver binding, and a `{type}__{method}` uf_prefix. The
        // requires-free `n` must NOT be mapped (fail-closed scope), and a trait
        // impl in the same file is IGNORED (it routes through the unit-2
        // concrete builder, not this one).
        let code = r#"
            struct S { v: i32 }

            impl S {
                #[trust_vc::proof]
                #[requires(self.v > 0)]
                fn m(&self, k: i32) {}

                fn n(&self) {}
            }

            #[trust_vc::trait_spec]
            trait T {
                #[trust_vc::requires(self.req())]
                fn f(&self);
            }

            #[trust_vc::trait_impl]
            impl T for S {
                fn f(&self) {}
            }
        "#;
        let file = syn::parse_str::<syn::File>(code).unwrap();
        let map = inherent_impl_method_requires(&file.items).unwrap();

        let contract = map
            .get(&("S".to_string(), "m".to_string()))
            .expect("requires-bearing inherent method `m` should be mapped under (S, m)");
        assert_eq!(contract.receiver_binding, "self");
        assert_eq!(contract.uf_prefix, "S__m");
        assert_eq!(
            contract.param_names,
            vec!["k".to_string()],
            "non-self param `k` must be carried in order: {:?}",
            contract.param_names
        );
        assert_eq!(
            contract.requires,
            vec!["self . v > 0".to_string()],
            "the raw requires string must be carried verbatim: {:?}",
            contract.requires
        );

        // The requires-free inherent method `n` must NOT be mapped.
        assert!(
            !map.contains_key(&("S".to_string(), "n".to_string())),
            "requires-free inherent method `n` must not produce an entry: {:?}",
            map.keys().collect::<Vec<_>>()
        );
        // The TRAIT method `f` must NOT be mapped by the inherent builder.
        assert!(
            !map.contains_key(&("S".to_string(), "f".to_string())),
            "a trait-impl method must not be picked up by the inherent builder: {:?}",
            map.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_inherent_impl_method_requires_skips_generic_self() {
        // A GENERIC inherent impl whose self type parses to a NESTED type param
        // (`Vec<P>` -> `Seq(TypeParam("P"))`) is out of unit-3 scope and
        // produces NO entry. (A bare top-level `TypeParam` short-uppercase
        // misfire is kept — see the concrete builder's regression guard.) This
        // mirrors `test_concrete_impl_method_requires_skips_generic_impl`'s
        // `Seq<P>` shape, the case `type_has_nested_type_param` recognizes.
        let code = r#"
            impl<P> Vec<P> {
                #[trust_vc::proof]
                #[requires(true)]
                fn m(&self) {}
            }
        "#;
        let file = syn::parse_str::<syn::File>(code).unwrap();
        let map = inherent_impl_method_requires(&file.items).unwrap();

        assert!(
            map.is_empty(),
            "a generic inherent impl (nested TypeParam self) must be skipped: {:?}",
            map.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_inherent_impl_method_requires_recurses_modules() {
        // Inherent impls nested inside an inline module must be discovered.
        let code = r#"
            mod inner {
                struct S { v: i32 }
                impl S {
                    #[trust_vc::proof]
                    #[requires(self.v > 0)]
                    fn m(&self) {}
                }
            }
        "#;
        let file = syn::parse_str::<syn::File>(code).unwrap();
        let map = inherent_impl_method_requires(&file.items).unwrap();

        assert!(
            map.contains_key(&("S".to_string(), "m".to_string())),
            "an inherent impl inside an inline module must be discovered: {:?}",
            map.keys().collect::<Vec<_>>()
        );
    }

    // -- Unit 6: supertrait-method closure ------------------------------------

    fn super_with_super_m() -> TraitDecl {
        TraitDecl::new(
            "Super",
            vec![TraitMethodDecl::new(
                "super_m",
                vec![("n".to_string(), TrustVcType::Uint { width: 64 })],
                TrustVcType::Unit,
                vec!["n > 10".to_string()],
                Vec::new(),
                false,
                None,
            )],
        )
    }

    #[test]
    fn test_supertrait_closure_methods_collects_inherited_with_declaring_trait() {
        // `trait T: Super {}` with `Super::super_m`. The closure from `T` must
        // reach `super_m` and pair it with its DECLARING trait `Super` (NOT the
        // starting trait `T`) — the encoder linking axiom grounds `Super__super_m`.
        let super_decl = super_with_super_m();
        let t_decl = TraitDecl::new("T", Vec::new()).with_supertraits(vec!["Super".to_string()]);
        let decls = [t_decl, super_decl];

        let closure = supertrait_closure_methods(&decls, "T");
        let found: Vec<_> = closure
            .iter()
            .map(|(decl_trait, m)| (decl_trait.clone(), m.name.clone()))
            .collect();
        assert!(
            found.contains(&("Super".to_string(), "super_m".to_string())),
            "the closure from `T` must reach `Super::super_m` keyed by the declaring trait `Super`: {found:?}"
        );
    }

    #[test]
    fn test_trait_bound_method_requires_keys_supertrait_method_by_declaring_trait() {
        // GENERIC bound `Z: T`, `trait T: Super`, `Super::super_m` requires-bearing.
        // The map must carry `(Z, super_m)` with `uf_prefix == "Super__super_m"`
        // (the DECLARING trait — LOAD-BEARING for the encoder linking axiom).
        let super_decl = super_with_super_m();
        let t_decl = TraitDecl::new("T", Vec::new()).with_supertraits(vec!["Super".to_string()]);
        let bounds = [TraitBound::new("Z", "T")];
        let decls = [t_decl, super_decl];

        let map = trait_bound_method_requires(&bounds, &decls);
        let contract = map
            .get(&("Z".to_string(), "super_m".to_string()))
            .expect("supertrait method `super_m` must be mapped under (Z, super_m)");
        assert_eq!(
            contract.uf_prefix, "Super__super_m",
            "uf_prefix must use the DECLARING trait `Super`, not the bound trait `T`"
        );
        assert_eq!(contract.receiver_binding, "self");
        assert_eq!(contract.param_names, vec!["n".to_string()]);
        assert_eq!(contract.requires, vec!["n > 10".to_string()]);
    }

    #[test]
    fn test_concrete_impl_method_requires_keys_supertrait_method_by_declaring_trait() {
        // CONCRETE `impl T for S`, `trait T: Super`, `Super::super_m` requires.
        // The concrete map must carry `(S, super_m)` with `uf_prefix ==
        // "Super__super_m"`. Only `impl T for S` is registered (the supertrait
        // impl `impl Super for S` need not be a separate registration for the
        // closure to fire).
        let super_decl = super_with_super_m();
        let t_decl = TraitDecl::new("T", Vec::new()).with_supertraits(vec!["Super".to_string()]);
        let impl_t = TraitImplDecl::new("T", TrustVcType::Opaque("S".to_string()), Vec::new());
        let decls = [t_decl, super_decl];

        let map = concrete_impl_method_requires(std::slice::from_ref(&impl_t), &decls);
        let contract = map
            .get(&("S".to_string(), "super_m".to_string()))
            .expect("supertrait method `super_m` must be mapped under (S, super_m)");
        assert_eq!(
            contract.uf_prefix, "Super__super_m",
            "uf_prefix must use the DECLARING trait `Super`, not the impl trait `T`"
        );
    }

    #[test]
    fn test_concrete_impl_method_requires_supertrait_reached_two_ways_is_idempotent() {
        // `S` impls BOTH `T` (`trait T: Super`) and `Super` directly. The
        // `(S, super_m)` key is supplied by `Super` (the DECLARING trait) via
        // BOTH impls. Because the ambiguity bookkeeping keys on the declaring
        // trait, this is idempotent — NOT a spurious cross-trait drop.
        let super_decl = super_with_super_m();
        let t_decl = TraitDecl::new("T", Vec::new()).with_supertraits(vec!["Super".to_string()]);
        let impl_t = TraitImplDecl::new("T", TrustVcType::Opaque("S".to_string()), Vec::new());
        let impl_super = TraitImplDecl::new(
            "Super",
            TrustVcType::Opaque("S".to_string()),
            vec![("super_m".to_string(), "S__super_m".to_string())],
        );
        let decls = [t_decl, super_decl];

        let map = concrete_impl_method_requires(&[impl_t, impl_super], &decls);
        assert!(
            map.contains_key(&("S".to_string(), "super_m".to_string())),
            "a supertrait method reached via two impls of related traits must stay (idempotent), not drop: {:?}",
            map.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_supertrait_closure_methods_most_derived_shadows() {
        // `T: Super`, both declare `m`. The most-derived (nearest-to-start) `T::m`
        // shadows `Super::m`, mirroring Rust method resolution.
        let super_decl = TraitDecl::new(
            "Super",
            vec![TraitMethodDecl::new(
                "m",
                Vec::new(),
                TrustVcType::Unit,
                vec!["super_req".to_string()],
                Vec::new(),
                false,
                None,
            )],
        );
        let t_decl = TraitDecl::new(
            "T",
            vec![TraitMethodDecl::new(
                "m",
                Vec::new(),
                TrustVcType::Unit,
                vec!["t_req".to_string()],
                Vec::new(),
                false,
                None,
            )],
        )
        .with_supertraits(vec!["Super".to_string()]);
        let decls = [t_decl, super_decl];

        let closure = supertrait_closure_methods(&decls, "T");
        let m_entries: Vec<_> = closure
            .iter()
            .filter(|(_, method)| method.name == "m")
            .collect();
        assert_eq!(
            m_entries.len(),
            1,
            "exactly ONE `m` survives shadowing: {:?}",
            m_entries.iter().map(|(t, _)| t).collect::<Vec<_>>()
        );
        assert_eq!(
            m_entries[0].0, "T",
            "the most-derived declaration `T::m` must shadow `Super::m`"
        );
    }

    #[test]
    fn test_supertrait_closure_methods_cycle_is_total() {
        // A malformed cyclic supertrait graph (`A: B`, `B: A`) must terminate via
        // the `visited` guard rather than hang. (Rust forbids such cycles, but the
        // verifier must be total on malformed input.)
        let a = TraitDecl::new(
            "A",
            vec![TraitMethodDecl::new(
                "am",
                Vec::new(),
                TrustVcType::Unit,
                vec!["a_req".to_string()],
                Vec::new(),
                false,
                None,
            )],
        )
        .with_supertraits(vec!["B".to_string()]);
        let b = TraitDecl::new(
            "B",
            vec![TraitMethodDecl::new(
                "bm",
                Vec::new(),
                TrustVcType::Unit,
                vec!["b_req".to_string()],
                Vec::new(),
                false,
                None,
            )],
        )
        .with_supertraits(vec!["A".to_string()]);
        let decls = [a, b];

        let closure = supertrait_closure_methods(&decls, "A");
        let names: Vec<_> = closure.iter().map(|(_, m)| m.name.clone()).collect();
        assert!(names.contains(&"am".to_string()) && names.contains(&"bm".to_string()));
        assert_eq!(
            closure.len(),
            2,
            "each method appears once despite the cycle"
        );
    }

    #[test]
    fn test_supertrait_closure_methods_no_supertraits_is_self_only() {
        // A trait with NO supertraits yields exactly its own methods — the
        // byte-identical fall-through that preserves all pre-unit-6 behaviour.
        let decls = [super_with_super_m()];
        let closure = supertrait_closure_methods(&decls, "Super");
        assert_eq!(closure.len(), 1);
        assert_eq!(closure[0].0, "Super");
        assert_eq!(closure[0].1.name, "super_m");
    }
}
