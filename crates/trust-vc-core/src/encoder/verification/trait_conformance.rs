//! Auxiliary trait-impl conformance verification.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{HashMap, HashSet};

use quote::ToTokens;
use syn::visit_mut::VisitMut;

use crate::encoder::{types::VerifyResult, AYEncoder};
use crate::error::TrustVcError;
use crate::ir::{TraitBound, TraitDecl, TraitImplDecl, TraitMethodDecl, TrustVcType};
use crate::ir_lowering::{MethodMeta, TypeEnv};
use crate::prepared_context::PreparedVerificationContext;
use crate::vc::{FunctionContext, VerificationMode};

#[path = "trait_conformance_contracts.rs"]
mod contracts;
use contracts::{
    build_contract_obligations, build_default_contract_obligations,
    build_impl_body_definition_obligation, build_impl_ensures_assert_obligations,
    clone_base_conformance_obligations, collect_helper_function_contexts,
    conformance_obligation_name, conformance_trait_display, instantiate_current_body_axioms,
    instantiate_referenced_body_axioms, normalize_conformance_result,
    referenced_body_axiom_broadcasts,
};

#[path = "trait_conformance_specialize.rs"]
mod specialize;
use specialize::{
    specialize_self_type, validate_concrete_function_signature, ContractBindings, IdentifierRenamer,
};

const CONFORMANCE_CONTEXT: &str = "trait impl conformance verification";
const CONFORMANCE_SELF: &str = "__trust_vc_impl_self";
const CONFORMANCE_RESULT: &str = "__trust_vc_impl_result";
const CONFORMANCE_STACK_RED_ZONE: usize = 8 * 1024 * 1024;
const CONFORMANCE_STACK_SIZE: usize = 128 * 1024 * 1024;

/// How a conformance walk treats each obligation it reaches.
///
/// The SAME walk drives both modes, so the set of obligations `List` reports is
/// exactly the set `VerifyOne` can check — a listing can never silently drift
/// from what is verifiable, which is the property that makes conformance safe to
/// attribute to individual obligations (an impl that is listed is an impl that
/// is checked, and vice versa).
enum ConformanceWalk<'a> {
    /// Verify ONLY the named obligation; skip the rest.
    VerifyOne { target: &'a str, matched: bool },
    /// Verify nothing; collect every obligation name.
    List { names: &'a mut Vec<String> },
}

impl ConformanceWalk<'_> {
    /// Records/selects the obligation `name`. Returns `true` when this walk must
    /// build and verify it.
    fn select(&mut self, name: &str) -> bool {
        match self {
            ConformanceWalk::VerifyOne { target, matched } => {
                if *target == name {
                    *matched = true;
                    true
                } else {
                    false
                }
            }
            ConformanceWalk::List { names } => {
                names.push(name.to_string());
                false
            }
        }
    }

    /// Policy for an obligation whose conformance context cannot be BUILT (a
    /// body that does not lower onto the conformance surface).
    ///
    /// Fail CLOSED with `Unknown`: the obligation was ADDRESSED BY NAME, and it
    /// is this impl's only report channel — answering `Verified` for an impl we
    /// did not actually check would report success where Verus errors. The old
    /// whole-file pass could silently skip such a body ("no worse than the prior
    /// no-check state") precisely because the failure had nowhere to be
    /// attributed; an addressable obligation has one, so it must never be
    /// silently skipped.
    fn unbuildable(&self, name: &str) -> Option<VerifyResult> {
        match self {
            ConformanceWalk::List { .. } => None,
            ConformanceWalk::VerifyOne { .. } => Some(VerifyResult::unknown(
                format!(
                    "{name}: the impl body does not lower onto the conformance surface, so this \
                     obligation could not be checked"
                ),
                // `Incompleteness` is the fail-CLOSED category: it is surfaced as
                // a verification FAILURE, never as a soft pass.
                Some(crate::encoder::UnknownCategory::Incompleteness),
            )),
        }
    }
}

/// Every conformance obligation in `base`, named exactly as the verification
/// path names it. Includes impls with NO method items (`impl Tr for bool {}`),
/// whose inherited default body is still conformance-checked — those have no
/// syn method item to enumerate, so the list is derived from the trait/impl
/// decls, not from the AST.
pub(in crate::encoder) fn list_trait_conformance_obligations(
    base: &PreparedVerificationContext,
) -> Result<Vec<String>, TrustVcError> {
    let mut names = Vec::new();
    let result = stacker::maybe_grow(CONFORMANCE_STACK_RED_ZONE, CONFORMANCE_STACK_SIZE, || {
        verify_trait_conformance_inner(base, &mut ConformanceWalk::List { names: &mut names })
    });
    // `List` never verifies, so the only non-`Verified` outcome is a hard
    // ill-formedness error (e.g. a missing trait declaration). Surface it rather
    // than returning a silently truncated list.
    match result {
        VerifyResult::Verified => Ok(names),
        other => Err(super::encoding_error(
            CONFORMANCE_CONTEXT,
            format!("cannot enumerate trait conformance obligations: {other:?}"),
        )),
    }
}

/// Verifies exactly ONE conformance obligation, addressed by name.
///
/// This is the impl's own report channel: a non-conforming impl is refuted here
/// whether or not anything in the file calls it. An unknown name fails CLOSED
/// (`Error`) — never `Verified` — so a mis-addressed obligation can never be
/// mistaken for a discharged one.
pub(in crate::encoder) fn verify_trait_conformance_obligation(
    base: &PreparedVerificationContext,
    obligation_name: &str,
) -> VerifyResult {
    let mut walk = ConformanceWalk::VerifyOne {
        target: obligation_name,
        matched: false,
    };
    let result = stacker::maybe_grow(CONFORMANCE_STACK_RED_ZONE, CONFORMANCE_STACK_SIZE, || {
        verify_trait_conformance_inner(base, &mut walk)
    });
    let matched = matches!(walk, ConformanceWalk::VerifyOne { matched: true, .. });
    if matches!(result, VerifyResult::Verified) && !matched {
        return VerifyResult::Error {
            message: format!(
                "{CONFORMANCE_CONTEXT}: no such trait conformance obligation '{obligation_name}'"
            ),
        };
    }
    result
}

fn verify_trait_conformance_inner(
    base: &PreparedVerificationContext,
    walk: &mut ConformanceWalk<'_>,
) -> VerifyResult {
    // Computed ONCE per walk from the decls alone, so `List` and `VerifyOne`
    // refuse exactly the same impls and the listed set stays the checked set.
    let shared_symbols = shared_impl_method_symbols(&base.trait_impl_decls);
    for (impl_decl, shared_symbol) in base.trait_impl_decls.iter().zip(&shared_symbols) {
        let shared_symbol = shared_symbol.as_deref();
        // `#[trust_vc::external]` impl: the Verus external_trait_specification
        // trust model — the impl's method bodies are TRUSTED, not verified, so
        // body conformance must not run (a deliberately-divergent external body
        // would otherwise Counterexample and sink every unrelated function in
        // the file). Callers still consume the trait contract; NON-external
        // impls keep full fail-closed conformance below.
        if impl_decl.is_external {
            continue;
        }
        let Some(trait_decl) = base
            .trait_decls
            .iter()
            .find(|decl| decl.name == impl_decl.trait_name)
        else {
            // A generic-struct impl (`impl<P> Tr for W<P>`, Opaque self) with no
            // in-file trait decl cannot be checked — preserve the prior opaque
            // skip. A concrete impl with a missing trait decl keeps its hard
            // error (an ill-formed file, not a silent skip).
            if impl_decl.concrete_type.contains_opaque() {
                continue;
            }
            return VerifyResult::Error {
                message: format!(
                    "trait impl conformance verification: missing trait declaration '{}' for {}",
                    impl_decl.trait_name,
                    impl_decl.concrete_type.to_type_string()
                ),
            };
        };

        // Generic-struct impl: the concrete self type lowers to an Opaque/`Poly`
        // sort with no ay datatype, so the concrete-surface per-impl path below
        // cannot run and previously SKIPPED the impl wholesale (the
        // `contains_opaque()` guard). That left the global trait postcondition
        // axiom published-but-unchecked, so a generic-bounded caller
        // `fn g<T: Tr>(t: T) { t.m() }` false-Verified an unestablished `ensures`
        // (round-8 trait findings 18/19). Check each method's effective body
        // against the trait `ensures` on an abstract (`Poly`) self instead.
        if impl_decl.concrete_type.contains_opaque() {
            let result = verify_generic_struct_impl_conformance(
                base,
                trait_decl,
                impl_decl,
                shared_symbol,
                walk,
            );
            if !matches!(result, VerifyResult::Verified) {
                return result;
            }
            continue;
        }

        for method in &trait_decl.methods {
            let concrete_fn_binding = impl_decl
                .method_bindings
                .iter()
                .find(|(trait_method_name, _)| trait_method_name == &method.name);

            // Conformance must ALSO run when only the IMPL declares an `ensures`
            // (the trait method may have none): the strengthened impl
            // postcondition still has to be verified against the body before it
            // can be propagated to callers. `trait_impl_method_ensures` is keyed
            // by the DECLARING TRAIT plus the concrete UF name and is populated
            // only for a captured, non-exempt impl body. The trait half is
            // load-bearing: keyed by the concrete name alone, `impl A1 for S` and
            // `impl A2 for S` share `S__v` and this lookup answers with the wrong
            // impl's clauses.
            let impl_declares_ensures = concrete_fn_binding.is_some_and(|(_, concrete_fn_name)| {
                base.trait_impl_method_ensures
                    .get(&crate::ir::ImplMethodKey::new(
                        &impl_decl.trait_name,
                        concrete_fn_name,
                    ))
                    .is_some_and(|ensures| !ensures.is_empty())
            });
            if method.ensures.is_empty() && !impl_declares_ensures {
                continue;
            }

            // TRAIT-ARGUMENT COLLISION: fail CLOSED before anything below can
            // read a registry keyed without the impl's trait arguments. The
            // captured body and impl `ensures` (`ImplMethodKey`, first
            // registration wins), the function context (bare `S__m`) and the
            // exempt set (bare `S__m`) all answer for whichever sibling impl
            // registered first, so building this obligation would check the
            // WRONG body: `impl Wc<bool> for S { 1 }` answered for
            // `impl Wc<u32> for S { 2 }` against `ensures(result == 1)` and both
            // rows Verified. `select` still runs FIRST, so the refused
            // obligation is listed and the file cannot report green. The emission
            // gate above is conservative for a collided group: any member's
            // registered impl `ensures` populate the shared key, so every member
            // that binds it emits.
            if let Some(shared_symbol) = shared_symbol {
                let obligation_name = conformance_obligation_name(trait_decl, method, impl_decl);
                if !walk.select(&obligation_name) {
                    continue;
                }
                return shared_symbol_refusal(
                    &obligation_name,
                    trait_decl,
                    impl_decl,
                    shared_symbol,
                );
            }

            // Non-overridden default method: VERIFY that the default body
            // establishes the trait `ensures` (given the trait `requires`),
            // exactly as an overridden impl method is verified. The global
            // trait-postcondition axiom emitted by `register_trait` asserts an
            // `ensures` that no impl body would otherwise be checked against —
            // a latent false-`Verified` the moment caller-side trait dispatch
            // instantiates a ground `Trait::method(..)` term (the default-body
            // axiom emitted by `register_trait_impl` then contradicts the
            // postcondition axiom). Verifying the body here justifies the axiom
            // by a checked body, just like an override. Part of #2442.
            if method.has_default && concrete_fn_binding.is_none() {
                // Declaration-only defaults (no body text) cannot be checked;
                // preserve the prior skip — caller dispatch still fails closed.
                let Some(default_body) = method.default_body.as_deref() else {
                    continue;
                };

                // Inline non-overridden sibling default-method calls onto the
                // concrete surface BEFORE lowering. An all-defaults impl whose
                // default body calls an inherited sibling (`self.g()`) otherwise
                // hits an unknown method, the lowering Errs, and the conformance
                // check is silently skipped — leaving the global trait
                // postcondition axiom published but unjustified (a false
                // `Verified` through generic dispatch). The sibling's behavior in
                // THIS impl is exactly its default body, so the substitution is
                // sound and precise: a non-conforming default still Counterexamples
                // and a conforming one still Verifies. Part of the round-3 trait
                // surface fix (residual of #2442 sibling-call default gap).
                let inlined_body =
                    inline_sibling_default_calls(default_body, trait_decl, impl_decl);

                let obligation_name = conformance_obligation_name(trait_decl, method, impl_decl);
                if !walk.select(&obligation_name) {
                    continue;
                }
                let conformance_ctx = match build_default_conformance_context(
                    base,
                    trait_decl,
                    impl_decl,
                    method,
                    &inlined_body,
                    &obligation_name,
                ) {
                    Ok(ctx) => ctx,
                    // Fail SAFE, not closed: a default body we cannot lower onto
                    // the concrete conformance surface is left unchecked here
                    // (no worse than the prior skip — soundness is unchanged
                    // because caller dispatch still fails closed), rather than
                    // tainting every unrelated function in the file with a
                    // spurious conformance error. Simple literal/arithmetic
                    // default bodies (the common case) always build. When the
                    // obligation is ADDRESSED BY NAME the skip becomes a
                    // fail-CLOSED `Unknown` (see `ConformanceWalk::unbuildable`).
                    Err(_) => match walk.unbuildable(&obligation_name) {
                        Some(result) => return result,
                        None => continue,
                    },
                };

                let result = AYEncoder::verify_typed(&conformance_ctx);
                if !matches!(result, VerifyResult::Verified) {
                    return normalize_conformance_result(result, &obligation_name);
                }
                continue;
            }

            let Some(concrete_fn_name) =
                concrete_fn_binding.map(|(_, concrete_fn_name)| concrete_fn_name.as_str())
            else {
                return VerifyResult::Error {
                    message: format!(
                        "trait impl conformance verification: missing method binding for '{}::{}' on {}",
                        trait_decl.name,
                        method.name,
                        impl_decl.concrete_type.to_type_string()
                    ),
                };
            };

            // Skip impl methods blocked by a dedicated ill-formedness error (own
            // `requires`, or a `returns`-on-both conflict): they are already
            // rejected via that error when verified directly, so conformance must
            // not ALSO Counterexample them while verifying an UNRELATED function
            // (which would let a blocked impl sink the whole file). This never
            // accepts a plain inherited-contract violation — those carry no own
            // clause, are not exempt, and still Counterexample below.
            if base.conformance_exempt_methods.contains(concrete_fn_name) {
                continue;
            }

            let obligation_name = conformance_obligation_name(trait_decl, method, impl_decl);
            if !walk.select(&obligation_name) {
                continue;
            }
            let conformance_ctx = match build_impl_conformance_context(
                base,
                trait_decl,
                impl_decl,
                method,
                concrete_fn_name,
                &obligation_name,
            ) {
                Ok(ctx) => ctx,
                Err(err) => return VerifyResult::from(err),
            };

            let result = AYEncoder::verify_typed(&conformance_ctx);
            if !matches!(result, VerifyResult::Verified) {
                return normalize_conformance_result(result, &obligation_name);
            }
        }
    }

    // The per-impl loop above only checks a default body when an impl for that
    // trait exists (the `method.has_default && concrete_fn_binding.is_none()`
    // arm lives INSIDE `for impl_decl in &base.trait_impl_decls`). But
    // `register_trait` publishes the quantified postcondition axiom
    // `forall self. Trait__m(self) <ensures>` for EVERY trait method
    // unconditionally, and a generic-bounded caller `fn g<T: Trait>(t: T) {
    // t.m() }` consumes that axiom directly. With ZERO impls the default body is
    // never checked, so a caller relying on an unestablished/contradictory
    // default `ensures` false-Verifies. Close that no-impl residual.
    verify_implless_trait_defaults(base, walk)
}

/// Verifies trait DEFAULT-method bodies against their declared `ensures` for
/// traits that have NO impl in the file (the impl-absent residual of the
/// #2442 / round-3 #60 default-conformance class).
///
/// The default body is checked on an abstract (`Poly`) self standing for an
/// arbitrary `T: Trait`, inlining non-overridden sibling defaults exactly as the
/// impl-present path does (with no impl, every sibling default is
/// non-overridden), and modeling any un-inlined sibling through the trait method
/// UF plus its postcondition axiom. A body that does not establish the `ensures`
/// — a literal that violates it, or a call to a contract-less declaration-only
/// sibling whose UF is unconstrained — Counterexamples, failing closed so the
/// unjustified global postcondition axiom is not silently trusted by a generic
/// caller. A CONFORMING default (a literal / sibling-default chain / a sibling
/// whose own `ensures` establishes the result) still Verifies — no
/// over-rejection.
fn verify_implless_trait_defaults(
    base: &PreparedVerificationContext,
    walk: &mut ConformanceWalk<'_>,
) -> VerifyResult {
    for trait_decl in &base.trait_decls {
        // Traits WITH an impl in the file are checked per-impl above (concrete
        // self type); skip them here so this pass never disturbs that path.
        if base
            .trait_impl_decls
            .iter()
            .any(|impl_decl| impl_decl.trait_name == trait_decl.name)
        {
            continue;
        }

        for method in &trait_decl.methods {
            // Only DEFAULT methods carry a body an impl can inherit WITHOUT
            // re-proving, so only their `ensures` can be published unchecked. A
            // declaration-only (abstract) method's `ensures` is a per-impl
            // obligation every impl must discharge, so its axiom is sound to
            // publish even with no in-file impl — leave it alone.
            if method.ensures.is_empty() || !method.has_default {
                continue;
            }
            let Some(default_body) = method.default_body.as_deref() else {
                continue;
            };

            // With no impl, EVERY sibling default is non-overridden: a synthetic
            // all-defaults impl over the abstract receiver drives the existing
            // inliner unchanged.
            let abstract_impl =
                TraitImplDecl::new(trait_decl.name.clone(), TrustVcType::Poly, Vec::new());
            let inlined_body =
                inline_sibling_default_calls(default_body, trait_decl, &abstract_impl);

            let obligation_name = implless_default_obligation_name(trait_decl, method);
            if !walk.select(&obligation_name) {
                continue;
            }
            let conformance_ctx = match build_implless_default_conformance_context(
                base,
                trait_decl,
                method,
                &abstract_impl,
                &inlined_body,
                &obligation_name,
            ) {
                Ok(ctx) => ctx,
                // Fail SAFE on a default body we cannot lower onto the abstract
                // surface, and never an over-rejection of an unrelated function.
                // The round-4 holes (literal bodies, contract-less
                // declaration-only sibling) all build and fail CLOSED via a
                // genuine Counterexample below. Addressed by name, the skip
                // becomes a fail-CLOSED `Unknown`.
                //
                // "NO WORSE THAN THE PRIOR (NO-CHECK) STATE" WAS THE OLD
                // JUSTIFICATION HERE AND IT DOES NOT ESTABLISH SOUNDNESS. A
                // skipped conformance check leaves `register_trait`'s published
                // `forall self. Trait__m(self) <ensures>` UNJUSTIFIED, and a
                // generic-bounded caller consumes it directly. What actually
                // makes this arm safe is an ORDERING invariant: `select` records
                // the obligation name BEFORE this build is attempted, so an
                // unbuildable obligation is still enumerated and any
                // list-then-verify-each driver reaches `VerifyOne`, where
                // `unbuildable` fails closed. `None` here is therefore only
                // reachable under `List`, where continuing is correct.
                //
                // Move `select` after the build and that collapses silently:
                // unbuildable obligations vanish from the list, nothing ever
                // addresses them by name, and this `continue` becomes the
                // unjustified-axiom hole. Adding a walk variant is
                // compiler-enforced (`unbuildable` matches exhaustively); the
                // ordering is NOT, so it is pinned by
                // `tests/unbuildable_conformance_obligation_is_still_listed.rs`.
                Err(_) => match walk.unbuildable(&obligation_name) {
                    Some(result) => return result,
                    None => continue,
                },
            };

            let result = AYEncoder::verify_typed(&conformance_ctx);
            if !matches!(result, VerifyResult::Verified) {
                return normalize_conformance_result(result, &obligation_name);
            }
        }
    }

    VerifyResult::Verified
}

/// For each entry of `impl_decls` (same order), the first concrete method
/// symbol it shares with ANOTHER impl decl of the SAME trait, or `None`.
///
/// SOUNDNESS-CRITICAL. Every per-impl registry the conformance lane reads is
/// keyed without the impl's trait type arguments: `parse_trait_impl_decl` mints
/// `format!("{type}__{method}")`, [`crate::ir::ImplMethodKey`] is (trait name,
/// that symbol) and keys the captured bodies and impl `ensures` first-
/// registration-wins, and `resolve_function_context` and
/// `conformance_exempt_methods` look up the bare symbol. So `impl Wc<bool> for
/// S` and `impl Wc<u32> for S` are ONE impl to all of them, and checking the
/// second impl read the first impl's body — a non-conforming second impl
/// Verified and its trait postcondition axiom was published unjustified.
///
/// A second decl claiming the same (trait, symbol) pair is a genuinely different
/// impl: other trait arguments, or a same-spelled self type. But the decl list
/// UNDER-counts: `register_trait_impl` merges decls whose ERASED fields compare
/// equal, so `impl Wc<u8> for S` and `impl<'x> Wc<&'x u8> for S` (and
/// `impl Tm for S` / `impl Tm for &S`) reach this walk as ONE decl — measured, a
/// single Verified row while the `&u8` impl returned 2 against
/// `ensures(result == 1)`. The source census carried on the decl
/// (`ImplGroupCensus::shared_method_names`, `crate::trait_impl_groups`) is taken
/// before that merge and is consulted as well. External decls COUNT as
/// claimants — their bodies are captured under the same key — even though they
/// emit no obligation of their own. Impls that share no symbol (a
/// default beside an override, all-defaults impls, the same trait for another
/// self type, a different trait with a same-named method) are untouched: their
/// checks read only their own keys.
fn shared_impl_method_symbols(impl_decls: &[TraitImplDecl]) -> Vec<Option<String>> {
    let mut claimants: HashMap<(&str, &str), usize> = HashMap::new();
    for impl_decl in impl_decls {
        let symbols: HashSet<&str> = impl_decl
            .method_bindings
            .iter()
            .map(|(_, concrete_fn)| concrete_fn.as_str())
            .collect();
        for symbol in symbols {
            *claimants
                .entry((impl_decl.trait_name.as_str(), symbol))
                .or_default() += 1;
        }
    }
    impl_decls
        .iter()
        .map(|impl_decl| {
            impl_decl
                .method_bindings
                .iter()
                .find(|(trait_method, concrete_fn)| {
                    claimants
                        .get(&(impl_decl.trait_name.as_str(), concrete_fn.as_str()))
                        .is_some_and(|count| *count > 1)
                        // The SOURCE census (`crate::trait_impl_groups`): a
                        // sibling impl of this trait for this self type declares
                        // the same method, even when the two decls merged
                        // before this walk could count them.
                        || impl_decl
                            .impl_group
                            .shared_method_names
                            .contains(trait_method)
                })
                .map(|(_, concrete_fn)| concrete_fn.clone())
        })
        .collect()
}

/// The fail-CLOSED verdict for a conformance obligation of an impl that shares
/// its (trait, concrete symbol) key with another impl
/// (see [`shared_impl_method_symbols`]). `Incompleteness` is surfaced as a
/// verification FAILURE: the impl was not checked, so it must not read as a
/// pass. A conforming collided impl is over-rejected until the registries are
/// keyed by trait arguments.
fn shared_symbol_refusal(
    obligation_name: &str,
    trait_decl: &TraitDecl,
    impl_decl: &TraitImplDecl,
    shared_symbol: &str,
) -> VerifyResult {
    VerifyResult::unknown(
        format!(
            "{obligation_name}: `{}` is implemented for `{}` by more than one impl sharing the \
             concrete method symbol `{shared_symbol}`; captured bodies, impl ensures and the \
             function context are keyed by trait name and that symbol without the impl's trait \
             arguments, so they cannot tell these impls apart and this impl's conformance is \
             not modelled",
            trait_decl.name,
            impl_decl.concrete_type.to_type_string()
        ),
        Some(crate::encoder::UnknownCategory::Incompleteness),
    )
}

fn implless_default_obligation_name(trait_decl: &TraitDecl, method: &TraitMethodDecl) -> String {
    format!(
        "trait default conformance {}::{} (no impl)",
        trait_decl.name, method.name
    )
}

/// Verifies a GENERIC-struct trait impl (`impl<P> Tr for W<P>`, whose concrete
/// self type lowers to an `Opaque` sort with no ay datatype) against the trait
/// `ensures`, checking each method's EFFECTIVE body on an abstract (`Poly`)
/// self — the same surface the impl-absent default pass uses.
///
/// The concrete-surface per-impl path ([`build_impl_conformance_context`])
/// cannot run here (no ay sort for `W<P>`), so the impl was previously SKIPPED
/// wholesale, leaving the global trait postcondition axiom published-but-checked
/// against no body and a generic-bounded caller false-Verifying (round-8 trait
/// findings 18/19). For each trait method with an `ensures`:
/// * an OVERRIDDEN method is checked against its CAPTURED impl body;
/// * a non-overridden method is checked against its inherited DEFAULT body.
///
/// Both bind `result == (<body>)` on a `Poly` self and assert the trait
/// `ensures`, inlining non-overridden sibling defaults exactly as the impl-absent
/// path does (an OVERRIDDEN sibling is left as its trait UF — checked modularly
/// through its own override conformance — never wrongly replaced by its default).
///
/// Keeping the trait registered is sound precisely because `register_trait_impl`
/// emits NO `UF == body` linking axiom for an Opaque self, so the postcondition
/// axiom stands alone and the body is checked on its own merits (same reasoning
/// as [`build_implless_default_conformance_context`]).
///
/// A body that does not establish the `ensures` Counterexamples (fail closed); a
/// conforming body still Verifies (no over-rejection). Honest partial: a body
/// that cannot be lowered onto the abstract surface (references the generic
/// field, declares its own `requires`, or is not a single pure return) is left
/// unchecked — no worse than the prior wholesale skip, never an over-rejection.
fn verify_generic_struct_impl_conformance(
    base: &PreparedVerificationContext,
    trait_decl: &TraitDecl,
    impl_decl: &TraitImplDecl,
    shared_symbol: Option<&str>,
    walk: &mut ConformanceWalk<'_>,
) -> VerifyResult {
    // Abstract `Poly` self standing for an arbitrary monomorphization of the
    // generic struct. Empty bindings: every trait method UF is registered via
    // the synthetic fn's `Self: Trait` bound, and sibling-default inlining uses
    // the REAL impl below to decide what is overridden.
    let abstract_impl = TraitImplDecl::new(trait_decl.name.clone(), TrustVcType::Poly, Vec::new());

    for method in &trait_decl.methods {
        if method.ensures.is_empty() {
            continue;
        }

        // TRAIT-ARGUMENT COLLISION: refuse BEFORE the exempt skip and the
        // body-capture `continue`s below — those run ahead of `select`, so a
        // collided impl reaching them could silently vanish from the listing,
        // and the captured body they read belongs to whichever sibling
        // registered first (`impl<P> Wc<bool> for G<P> { 1 }` answered for
        // `impl<P> Wc<u32> for G<P> { 2 }`). Same rule as the concrete path.
        if let Some(shared_symbol) = shared_symbol {
            let obligation_name = generic_struct_obligation_name(trait_decl, method, impl_decl);
            if !walk.select(&obligation_name) {
                continue;
            }
            return shared_symbol_refusal(&obligation_name, trait_decl, impl_decl, shared_symbol);
        }

        let binding = impl_decl
            .method_bindings
            .iter()
            .find(|(trait_method_name, _)| trait_method_name == &method.name);

        // The effective body text, on the `self` + source-param-name surface the
        // default-body conformance path expects.
        let effective_body = match binding {
            Some((_, concrete_fn_name)) => {
                // Ill-formed impl methods (own `requires`, or `returns`-on-both)
                // are rejected via their dedicated error when verified directly;
                // do not ALSO Counterexample them here (mirrors the concrete
                // path's `conformance_exempt_methods` skip).
                if base.conformance_exempt_methods.contains(concrete_fn_name) {
                    continue;
                }
                // Body not captured (complex / has-requires / not a single pure
                // return), or an arity mismatch that would make the positional
                // restore unsound: fail SAFE — no worse than the prior skip.
                let Some(body) = base
                    .trait_impl_method_bodies
                    .get(&crate::ir::ImplMethodKey::new(
                        &impl_decl.trait_name,
                        concrete_fn_name,
                    ))
                else {
                    continue;
                };
                if body.param_count != method.params.len() {
                    continue;
                }
                let Some(restored) = restore_conformance_body_param_names(&body.body_text, method)
                else {
                    continue;
                };
                restored
            }
            None => {
                // Inherited default: only a default WITH a body is checkable. A
                // declaration-only abstract method that the impl fails to provide
                // is an ill-formed file caught elsewhere; nothing to check here.
                if !method.has_default {
                    continue;
                }
                let Some(default_body) = method.default_body.as_deref() else {
                    continue;
                };
                default_body.to_string()
            }
        };

        // Inline non-overridden sibling defaults using the REAL impl's bindings
        // so an OVERRIDDEN sibling is excluded (it lowers to its trait UF, which
        // its own override conformance check discharges).
        let inlined_body = inline_sibling_default_calls(&effective_body, trait_decl, impl_decl);

        let obligation_name = generic_struct_obligation_name(trait_decl, method, impl_decl);
        if !walk.select(&obligation_name) {
            continue;
        }
        let conformance_ctx = match build_implless_default_conformance_context(
            base,
            trait_decl,
            method,
            &abstract_impl,
            &inlined_body,
            &obligation_name,
        ) {
            Ok(ctx) => ctx,
            // Fail SAFE: a body we cannot lower onto the abstract surface is left
            // unchecked (prior behavior), never an over-rejection. Addressed by
            // name, the skip becomes a fail-CLOSED `Unknown`.
            Err(_) => match walk.unbuildable(&obligation_name) {
                Some(result) => return result,
                None => continue,
            },
        };

        let result = AYEncoder::verify_typed(&conformance_ctx);
        if !matches!(result, VerifyResult::Verified) {
            return normalize_conformance_result(result, &obligation_name);
        }
    }

    VerifyResult::Verified
}

fn generic_struct_obligation_name(
    trait_decl: &TraitDecl,
    method: &TraitMethodDecl,
    impl_decl: &TraitImplDecl,
) -> String {
    format!(
        "trait impl conformance {}::{} for {} (generic struct)",
        conformance_trait_display(trait_decl, impl_decl),
        method.name,
        impl_decl.concrete_type.to_type_string()
    )
}

/// Restores a CAPTURED conformance body (whose non-receiver params were renamed
/// to positional `__trust_vc_conf_arg_{i}` placeholders at extraction) back to
/// the trait method's declared source parameter names, so it shares the
/// `self`/source-name convention the default-body conformance path renames from.
/// Returns `None` on a parse failure (fail SAFE — leave the method unchecked).
fn restore_conformance_body_param_names(
    body_text: &str,
    method: &TraitMethodDecl,
) -> Option<String> {
    if method.params.is_empty() {
        return Some(body_text.to_string());
    }
    let mut expr = syn::parse_str::<syn::Expr>(body_text).ok()?;
    let renames: HashMap<String, String> = method
        .params
        .iter()
        .enumerate()
        .map(|(index, (name, _))| (format!("__trust_vc_conf_arg_{index}"), name.clone()))
        .collect();
    IdentifierRenamer::new(&renames).visit_expr_mut(&mut expr);
    Some(expr.to_token_stream().to_string())
}

/// Fixpoint cap for nested sibling-default inlining (mutually-recursive defaults
/// cannot loop forever; any residual unresolved sibling call simply fails to
/// lower later, preserving the prior safe skip).
const SIBLING_INLINE_DEPTH: usize = 8;

/// Rewrites a trait default-method body, replacing calls to non-overridden
/// sibling trait DEFAULT methods (`self.g(args)`) with their (parenthesized)
/// default body, substituting the sibling body's `self`/params with the call's
/// receiver/args. Returns the original text unchanged on a parse failure or when
/// there is nothing to inline.
///
/// For an all-defaults impl the inherited sibling's behavior IS its default
/// body, so this is sound and precise — it neither admits a non-conforming
/// default (the inlined body still contradicts a violated `ensures`) nor
/// over-rejects a conforming one. Overridden siblings are excluded: they carry
/// their own concrete UF and are checked through the impl path.
fn inline_sibling_default_calls(
    body_text: &str,
    trait_decl: &TraitDecl,
    impl_decl: &TraitImplDecl,
) -> String {
    let Ok(mut expr) = syn::parse_str::<syn::Expr>(body_text) else {
        return body_text.to_string();
    };

    let overridden: HashSet<&str> = impl_decl
        .method_bindings
        .iter()
        .map(|(name, _)| name.as_str())
        .collect();
    let defaults: HashMap<String, &TraitMethodDecl> = trait_decl
        .methods
        .iter()
        .filter(|method| {
            method.default_body.is_some() && !overridden.contains(method.name.as_str())
        })
        .map(|method| (method.name.clone(), method))
        .collect();
    if defaults.is_empty() {
        return body_text.to_string();
    }

    let mut inliner = SiblingDefaultInliner {
        defaults: &defaults,
        changed: false,
    };
    for _ in 0..SIBLING_INLINE_DEPTH {
        inliner.changed = false;
        inliner.visit_expr_mut(&mut expr);
        if !inliner.changed {
            break;
        }
    }

    expr.to_token_stream().to_string()
}

/// Post-order visitor that inlines one layer of sibling default-method calls per
/// `visit_expr_mut` sweep (the enclosing fixpoint loop handles nested layers).
struct SiblingDefaultInliner<'a> {
    defaults: &'a HashMap<String, &'a TraitMethodDecl>,
    changed: bool,
}

impl VisitMut for SiblingDefaultInliner<'_> {
    fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
        // Recurse first so the receiver/args (which may themselves contain
        // sibling calls) are inlined before this node is considered.
        syn::visit_mut::visit_expr_mut(self, expr);

        let syn::Expr::MethodCall(method_call) = expr else {
            return;
        };
        let method_name = method_call.method.to_string();
        let Some(method) = self.defaults.get(&method_name) else {
            return;
        };
        // Arity must match the sibling's declared params, else a positional
        // substitution would be unsound — leave the call untouched.
        if method_call.args.len() != method.params.len() {
            return;
        }
        let Some(body_text) = method.default_body.as_deref() else {
            return;
        };
        let Ok(mut body_expr) = syn::parse_str::<syn::Expr>(body_text) else {
            return;
        };

        let mut subs: HashMap<String, syn::Expr> = HashMap::new();
        subs.insert("self".to_string(), (*method_call.receiver).clone());
        for ((param_name, _), arg) in method.params.iter().zip(method_call.args.iter()) {
            subs.insert(param_name.clone(), arg.clone());
        }
        ExprSubstituter { subs: &subs }.visit_expr_mut(&mut body_expr);

        *expr = syn::Expr::Paren(syn::ExprParen {
            attrs: Vec::new(),
            paren_token: syn::token::Paren::default(),
            expr: Box::new(body_expr),
        });
        self.changed = true;
    }
}

/// Replaces single-segment path identifiers (`self`, a param name) with their
/// substituted expression. Does not recurse into a replacement, so a receiver
/// that itself names `self` is left as-is.
struct ExprSubstituter<'a> {
    subs: &'a HashMap<String, syn::Expr>,
}

impl VisitMut for ExprSubstituter<'_> {
    fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
        if let syn::Expr::Path(path_expr) = expr {
            if path_expr.qself.is_none() && path_expr.path.segments.len() == 1 {
                let ident = path_expr.path.segments[0].ident.to_string();
                if let Some(replacement) = self.subs.get(&ident) {
                    *expr = replacement.clone();
                    return;
                }
            }
        }
        syn::visit_mut::visit_expr_mut(self, expr);
    }
}

fn build_impl_conformance_context(
    base: &PreparedVerificationContext,
    trait_decl: &TraitDecl,
    impl_decl: &TraitImplDecl,
    method: &TraitMethodDecl,
    concrete_fn_name: &str,
    obligation_name: &str,
) -> Result<PreparedVerificationContext, TrustVcError> {
    let concrete_fn_ctx = resolve_function_context(base, concrete_fn_name)?;
    let obligation_template = base.obligations.first().cloned().ok_or_else(|| {
        super::encoding_error(
            CONFORMANCE_CONTEXT,
            "trait impl conformance requires at least one prepared obligation",
        )
    })?;
    let bindings = ContractBindings::new(method, impl_decl, &trait_decl.generics);
    validate_concrete_function_signature(
        &concrete_fn_ctx,
        &bindings,
        impl_decl,
        trait_decl,
        method,
    )?;

    let env = build_impl_contract_env(base, trait_decl, impl_decl, &concrete_fn_ctx, &bindings)?;
    let concrete_body_axioms = instantiate_current_body_axioms(
        base,
        concrete_fn_name,
        obligation_name,
        &bindings,
        &env,
        &obligation_template,
    )?;
    let contract_obligations = build_contract_obligations(
        method,
        concrete_fn_name,
        obligation_name,
        &bindings,
        &env,
        &obligation_template,
    )?;

    // CONFORMANCE-EXTENSION (cardinal): also verify the impl body against the
    // impl method's OWN declared `ensures`. The map is populated (at extraction)
    // ONLY for a non-exempt impl whose single-pure-return body was captured, so
    // the `impl_body_definition` below pins `__trust_vc_impl_result` to the true
    // body value and this assert genuinely checks `body ⊨ impl_ensures`. A
    // violating body Counterexamples here, which is the sole justification that
    // makes the caller-side propagation axiom sound.
    //
    // The clauses are POSITIONAL (`__trust_vc_conf_arg_{i}`, the captured body's
    // numbering), so they are bound through that body's arity; a missing body or
    // an arity disagreement is an Err (fail closed), never a trait-name reading.
    let impl_method_key = crate::ir::ImplMethodKey::new(&impl_decl.trait_name, concrete_fn_name);
    let impl_ensures_obligations = match base.trait_impl_method_ensures.get(&impl_method_key) {
        Some(impl_ensures) if !impl_ensures.is_empty() => build_impl_ensures_assert_obligations(
            impl_ensures,
            base.trait_impl_method_bodies.get(&impl_method_key),
            obligation_name,
            &bindings,
            &env,
            &obligation_template,
        )?,
        _ => Vec::new(),
    };

    // When the impl method's body was captured from source, assume its
    // definitional fact `concrete_fn(self, args..) == body` so the trait
    // contract is checked against the body's ACTUAL return value — not an
    // unconstrained UF result that over-rejects a conforming impl whenever the
    // verified function does not itself reference the impl method (so its body
    // axiom is absent from the base context). Sound: the captured body is the
    // method's true single-return value, so a non-conforming body still
    // contradicts the asserted `ensures`. Absent capture (or on lowering
    // failure), the prior body-axiom path is preserved unchanged.
    let impl_body_definition = base
        .trait_impl_method_bodies
        .get(&impl_method_key)
        .and_then(|body| {
            build_impl_body_definition_obligation(
                concrete_fn_name,
                body,
                obligation_name,
                &bindings,
                &env,
                &obligation_template,
            )
        });

    let mut obligations = clone_base_conformance_obligations(base);
    obligations.extend(instantiate_referenced_body_axioms(
        base,
        &concrete_body_axioms,
        &contract_obligations,
        &env,
        obligation_name,
        concrete_fn_name,
    )?);
    obligations.extend(concrete_body_axioms);
    obligations.extend(impl_body_definition);
    obligations.extend(contract_obligations);
    obligations.extend(impl_ensures_obligations);

    let mut variables = base.variables.clone();
    variables.extend(bindings.variables());

    let helper_function_contexts = collect_helper_function_contexts(base, concrete_fn_name);
    let has_collection_context = base.has_collection_context
        || variables.iter().any(|var| var.ty.is_collection())
        || obligations
            .iter()
            .any(|obligation| obligation.expr.references_collection());

    let mut conformance_ctx = base.clone();
    conformance_ctx.obligations = obligations;
    conformance_ctx.variables = variables;
    conformance_ctx.function_context = Some(concrete_fn_ctx);
    // Lowering already translated the contract onto the concrete surface,
    // so the auxiliary pass does not need the quantified trait UF axioms or
    // any impl-linking axioms at setup time.
    conformance_ctx.trait_decls = Vec::new();
    conformance_ctx.trait_impl_decls = Vec::new();
    conformance_ctx.verification_mode = VerificationMode::BodyLevel;
    conformance_ctx.overflow_behavior = base.overflow_behavior;
    conformance_ctx.assert_by_scopes = HashMap::new();
    conformance_ctx.loop_guards = HashMap::new();
    conformance_ctx.loop_modified_vars = HashMap::new();
    conformance_ctx.loop_body_transitions = HashMap::new();
    conformance_ctx.has_collection_context = has_collection_context;
    conformance_ctx.revealed_fns = base.revealed_fns.clone();
    conformance_ctx.hidden_fns = base.hidden_fns.clone();
    conformance_ctx.helper_function_contexts = helper_function_contexts;
    conformance_ctx.struct_types = base.struct_types.clone();
    conformance_ctx.type_invariants = base.type_invariants.clone();
    Ok(conformance_ctx)
}

/// Builds the conformance context for a NON-overridden trait default method.
///
/// Same shape as [`build_impl_conformance_context`], but the result variable is
/// bound to the *inlined default body* rather than to a concrete impl function
/// call (see [`build_default_contract_obligations`]). The trait UF axioms are
/// NOT re-emitted (trait_decls / trait_impl_decls cleared), so this context is
/// free of the dormant default-body-vs-postcondition contradiction that the
/// primary verification carries; the body is checked against the `ensures` on
/// its own merits.
fn build_default_conformance_context(
    base: &PreparedVerificationContext,
    trait_decl: &TraitDecl,
    impl_decl: &TraitImplDecl,
    method: &TraitMethodDecl,
    default_body: &str,
    obligation_name: &str,
) -> Result<PreparedVerificationContext, TrustVcError> {
    let obligation_template = base.obligations.first().cloned().ok_or_else(|| {
        super::encoding_error(
            CONFORMANCE_CONTEXT,
            "trait impl conformance requires at least one prepared obligation",
        )
    })?;
    let bindings = ContractBindings::new(method, impl_decl, &trait_decl.generics);

    // Stand-in function context for the default body, with the specialized
    // self/param/return types on the concrete conformance surface. setup
    // declares it as a (dead) UF that is never applied — the body is inlined
    // into the result binding — but it gives the env and verification pass a
    // current function exactly as the overridden-impl path has.
    let synthetic_fn_ctx =
        synthesize_default_function_context(trait_decl, impl_decl, method, &bindings);

    let env = build_impl_contract_env(base, trait_decl, impl_decl, &synthetic_fn_ctx, &bindings)?;
    let contract_obligations = build_default_contract_obligations(
        method,
        default_body,
        obligation_name,
        &bindings,
        &env,
        &obligation_template,
    )?;

    let mut obligations = clone_base_conformance_obligations(base);
    // The default body may call helper functions / overridden impl methods; pull
    // in their body axioms (the result binding carries those calls). There is no
    // concrete-fn body axiom to seed, so the seed set is empty.
    obligations.extend(instantiate_referenced_body_axioms(
        base,
        &[],
        &contract_obligations,
        &env,
        obligation_name,
        &synthetic_fn_ctx.name,
    )?);
    obligations.extend(contract_obligations);

    let mut variables = base.variables.clone();
    variables.extend(bindings.variables());

    let helper_function_contexts = collect_helper_function_contexts(base, &synthetic_fn_ctx.name);
    let has_collection_context = base.has_collection_context
        || variables.iter().any(|var| var.ty.is_collection())
        || obligations
            .iter()
            .any(|obligation| obligation.expr.references_collection());

    let mut conformance_ctx = base.clone();
    conformance_ctx.obligations = obligations;
    conformance_ctx.variables = variables;
    conformance_ctx.function_context = Some(synthetic_fn_ctx);
    conformance_ctx.trait_decls = Vec::new();
    conformance_ctx.trait_impl_decls = Vec::new();
    conformance_ctx.verification_mode = VerificationMode::BodyLevel;
    conformance_ctx.overflow_behavior = base.overflow_behavior;
    conformance_ctx.assert_by_scopes = HashMap::new();
    conformance_ctx.loop_guards = HashMap::new();
    conformance_ctx.loop_modified_vars = HashMap::new();
    conformance_ctx.loop_body_transitions = HashMap::new();
    conformance_ctx.has_collection_context = has_collection_context;
    conformance_ctx.revealed_fns = base.revealed_fns.clone();
    conformance_ctx.hidden_fns = base.hidden_fns.clone();
    conformance_ctx.helper_function_contexts = helper_function_contexts;
    conformance_ctx.struct_types = base.struct_types.clone();
    conformance_ctx.type_invariants = base.type_invariants.clone();
    Ok(conformance_ctx)
}

/// Synthesizes the stand-in [`FunctionContext`] for a default-method body. The
/// parameter list mirrors the conformance bindings (specialized receiver first,
/// then specialized method params); the name is unique per trait/method/impl so
/// the dead UF never collides with a real function.
fn synthesize_default_function_context(
    trait_decl: &TraitDecl,
    impl_decl: &TraitImplDecl,
    method: &TraitMethodDecl,
    bindings: &ContractBindings,
) -> FunctionContext {
    let mut params = Vec::with_capacity(bindings.params.len() + 1);
    params.push((bindings.receiver_name.clone(), bindings.receiver_ty.clone()));
    for param in &bindings.params {
        params.push((param.lowered_name.clone(), param.ty.clone()));
    }

    let name = format!(
        "__trust_vc_default_impl_{}_{}_{}",
        crate::encoder::sanitize_symbol(&trait_decl.name),
        crate::encoder::sanitize_symbol(&method.name),
        crate::encoder::sanitize_symbol(&impl_decl.concrete_type.to_type_string()),
    );

    FunctionContext::new(
        name,
        params,
        bindings.result_ty.clone(),
        crate::mode::FunctionMode::Proof,
    )
}

/// Builds the conformance context for a trait default method whose trait has NO
/// impl in the file (the impl-absent residual).
///
/// Unlike [`build_default_conformance_context`] (which specializes onto a
/// concrete impl type and clears the trait registration because an impl is
/// present), this checks the default body on an abstract (`Poly`) self and KEEPS
/// exactly this trait registered, for two reasons:
///
///  * its method UFs must be declared so a `self.sibling()` call left in the
///    (un-inlined) body lowers to `Trait__sibling(self)`; and
///  * its sibling postcondition axioms must be in scope so a CONFORMING default
///    that relies on a contract-bearing sibling still Verifies.
///
/// CARDINAL — the trait is registered with the METHOD-UNDER-CHECK's OWN `ensures`
/// STRIPPED ([`trait_decl_without_own_postcondition`]). Asserting
/// `∀ self, args. ensures[result := Trait__m(self, args)]` while trying to prove
/// that a body establishes that very `ensures` is assuming the conclusion, and it
/// is not merely redundant — it is a PROOF HOLE whenever the postcondition is
/// unsatisfiable as a universal. `ensures(result > x)` over `u32` is exactly such
/// a case (nothing is `bvult`-above `u32::MAX`, so NO total interpretation of
/// `Tr__p` exists), which makes the premise set CONTRADICTORY and the conformance
/// obligation vacuously valid; the violating impl would then be reported as
/// conforming, and its published trait contract would let every generic-bounded
/// caller prove anything. Only ay's BV-quantifier incompleteness (a deferral, not
/// a decision) stood between that encoding and a false verify. Stripping the
/// method's own postcondition removes the circular premise; the body is checked
/// against the `ensures` on its own merits and the violating case now yields a
/// concrete counterexample.
///
/// SIBLING axioms are KEPT, and are justified as before: each sibling's own
/// conformance obligation discharges it (and for a contract-less
/// declaration-only sibling there is no axiom at all, leaving its UF
/// unconstrained — exactly the underivability that fails a default closed).
/// Keeping the trait registered at all is sound here precisely BECAUSE no impl
/// linking axiom is emitted: `register_trait_impl` (whose `UF == default_body`
/// axiom would contradict a violated postcondition) never runs on this surface.
fn build_implless_default_conformance_context(
    base: &PreparedVerificationContext,
    trait_decl: &TraitDecl,
    method: &TraitMethodDecl,
    abstract_impl: &TraitImplDecl,
    default_body: &str,
    obligation_name: &str,
) -> Result<PreparedVerificationContext, TrustVcError> {
    let obligation_template = base.obligations.first().cloned().ok_or_else(|| {
        super::encoding_error(
            CONFORMANCE_CONTEXT,
            "trait impl conformance requires at least one prepared obligation",
        )
    })?;
    // `abstract_impl.concrete_type == Poly`, so `specialize_self_type` is the
    // identity over the trait's own (Poly) signature — the bindings carry the
    // abstract receiver/param/result types unchanged.
    let bindings = ContractBindings::new(method, abstract_impl, &trait_decl.generics);

    let synthetic_fn_ctx =
        synthesize_implless_default_function_context(trait_decl, method, &bindings);

    let mut env = build_impl_contract_env(
        base,
        trait_decl,
        abstract_impl,
        &synthetic_fn_ctx,
        &bindings,
    )?;
    let poly_self_fields = crate::encoder::trait_self_fields::poly_self_field_projections(
        &trait_decl.name,
        method,
        &[default_body],
    )?;
    for projection in &poly_self_fields {
        insert_poly_self_field_metadata_checked(&mut env, projection)?;
    }
    let contract_obligations = build_default_contract_obligations(
        method,
        default_body,
        obligation_name,
        &bindings,
        &env,
        &obligation_template,
    )?;

    let mut obligations = clone_base_conformance_obligations(base);
    // Carry the body axioms of free functions the default body calls, as
    // broadcasts, so E-matching grounds them for literal/constant-argument calls
    // (e.g. `{ add(2, 5) }`) that `instantiate_referenced_body_axioms` — limited
    // to variable-argument ground calls — cannot instantiate. Without this a
    // CONFORMING default calling such a free fn over-rejects.
    obligations.extend(referenced_body_axiom_broadcasts(
        base,
        &contract_obligations,
    ));
    obligations.extend(instantiate_referenced_body_axioms(
        base,
        &[],
        &contract_obligations,
        &env,
        obligation_name,
        &synthetic_fn_ctx.name,
    )?);
    obligations.extend(contract_obligations);

    let mut variables = base.variables.clone();
    variables.extend(bindings.variables());

    let mut helper_function_contexts =
        collect_helper_function_contexts(base, &synthetic_fn_ctx.name);
    for projection in &poly_self_fields {
        insert_poly_self_field_helper_checked(&mut helper_function_contexts, projection)?;
    }
    let has_collection_context = base.has_collection_context
        || variables.iter().any(|var| var.ty.is_collection())
        || obligations
            .iter()
            .any(|obligation| obligation.expr.references_collection());

    let mut conformance_ctx = base.clone();
    conformance_ctx.obligations = obligations;
    conformance_ctx.variables = variables;
    conformance_ctx.function_context = Some(synthetic_fn_ctx);
    // Keep ONLY this trait registered (UFs + sibling postcondition axioms);
    // drop all impls (there are none for this trait) and every OTHER trait (the
    // default body references only THIS trait's methods on `self`, and isolating
    // it avoids any unrelated trait's axioms perturbing the check).
    conformance_ctx.trait_decls = vec![trait_decl_without_own_postcondition(trait_decl, method)];
    conformance_ctx.trait_impl_decls = Vec::new();
    conformance_ctx.verification_mode = VerificationMode::BodyLevel;
    conformance_ctx.overflow_behavior = base.overflow_behavior;
    conformance_ctx.assert_by_scopes = HashMap::new();
    conformance_ctx.loop_guards = HashMap::new();
    conformance_ctx.loop_modified_vars = HashMap::new();
    conformance_ctx.loop_body_transitions = HashMap::new();
    conformance_ctx.has_collection_context = has_collection_context;
    conformance_ctx.revealed_fns = base.revealed_fns.clone();
    conformance_ctx.hidden_fns = base.hidden_fns.clone();
    conformance_ctx.helper_function_contexts = helper_function_contexts;
    conformance_ctx.struct_types = base.struct_types.clone();
    conformance_ctx.type_invariants = base.type_invariants.clone();
    Ok(conformance_ctx)
}

fn insert_poly_self_field_metadata_checked(
    env: &mut TypeEnv,
    projection: &crate::encoder::trait_self_fields::PolySelfFieldProjection,
) -> Result<(), TrustVcError> {
    let receiver = TrustVcType::Poly.to_type_string();
    if let Some(existing) = env.lookup_field(&receiver, &projection.field_name) {
        if existing.uf_name == projection.uf_name && existing.field_type == projection.field_type {
            return Ok(());
        }
        return Err(super::encoding_error(
            CONFORMANCE_CONTEXT,
            format!(
                "conflicting abstract receiver field metadata for '{}.{}'",
                receiver, projection.field_name
            ),
        ));
    }
    env.insert_field_metadata(
        receiver,
        projection.field_name.clone(),
        projection.uf_name.clone(),
        projection.field_type.clone(),
    );
    Ok(())
}

fn insert_poly_self_field_helper_checked(
    helpers: &mut Vec<FunctionContext>,
    projection: &crate::encoder::trait_self_fields::PolySelfFieldProjection,
) -> Result<(), TrustVcError> {
    if let Some(existing) = helpers
        .iter()
        .find(|helper| helper.name == projection.uf_name)
    {
        let expected_params = [("__trust_vc_poly_self".to_string(), TrustVcType::Poly)];
        if existing.params == expected_params && existing.return_type == projection.field_type {
            return Ok(());
        }
        return Err(super::encoding_error(
            CONFORMANCE_CONTEXT,
            format!(
                "conflicting helper signature for abstract receiver projection '{}'",
                projection.uf_name
            ),
        ));
    }
    helpers.push(FunctionContext::new(
        projection.uf_name.clone(),
        vec![("__trust_vc_poly_self".to_string(), TrustVcType::Poly)],
        projection.field_type.clone(),
        crate::mode::FunctionMode::Spec,
    ));
    Ok(())
}

/// Clones `trait_decl` with `method`'s OWN `ensures` (and `default_ensures`)
/// removed, so [`AYEncoder::register_trait`] declares every method UF but emits
/// NO postcondition axiom for the method whose conformance is under check.
///
/// This is the "do not assume the conclusion" rule for the abstract-self
/// conformance surface. The obligation being solved is
/// `body_definition ∧ ¬ensures` — SAT means "refuted, here is the witness".
/// Adding `∀ self, args. ensures[result := Trait__m(self, args)]` to that premise
/// set can only (a) do nothing, when the body's result is a fresh variable the
/// axiom never mentions, or (b) POISON it, when the axiom is unsatisfiable, in
/// which case the query is UNSAT for reasons that have nothing to do with the
/// body and the obligation is discharged VACUOUSLY. Case (b) is not
/// hypothetical: `ensures(result > x)` over `u32` is unsatisfiable as a universal.
/// (a) is why the satisfiable-postcondition fixtures never exposed this.
///
/// Method UFs stay declared (only the axiom is suppressed), so a body that still
/// mentions `self.m()` lowers exactly as before. Sibling methods keep their
/// axioms — each is discharged by its own conformance obligation.
fn trait_decl_without_own_postcondition(
    trait_decl: &TraitDecl,
    method: &TraitMethodDecl,
) -> TraitDecl {
    let mut scrubbed = trait_decl.clone();
    for decl_method in &mut scrubbed.methods {
        if decl_method.name == method.name {
            decl_method.ensures.clear();
            decl_method.default_ensures.clear();
        }
    }
    scrubbed
}

/// Synthesizes the stand-in [`FunctionContext`] for an impl-absent default-method
/// body. Mirrors [`synthesize_default_function_context`] but carries a `Self:
/// Trait` bound over the abstract (`Poly`) receiver so that EVERY trait method —
/// including contract-less declaration-only siblings — registers as its
/// quantified UF `Trait__method` in the env, letting an un-inlined `self.m()`
/// call lower onto the abstract surface.
fn synthesize_implless_default_function_context(
    trait_decl: &TraitDecl,
    method: &TraitMethodDecl,
    bindings: &ContractBindings,
) -> FunctionContext {
    let mut params = Vec::with_capacity(bindings.params.len() + 1);
    params.push((bindings.receiver_name.clone(), bindings.receiver_ty.clone()));
    for param in &bindings.params {
        params.push((param.lowered_name.clone(), param.ty.clone()));
    }

    let name = format!(
        "__trust_vc_implless_default_{}_{}",
        crate::encoder::sanitize_symbol(&trait_decl.name),
        crate::encoder::sanitize_symbol(&method.name),
    );

    FunctionContext::new(
        name,
        params,
        bindings.result_ty.clone(),
        crate::mode::FunctionMode::Proof,
    )
    .with_trait_bounds(vec![TraitBound::new(
        TrustVcType::Poly.to_type_string(),
        trait_decl.name.clone(),
    )])
}

fn resolve_function_context(
    base: &PreparedVerificationContext,
    function_name: &str,
) -> Result<FunctionContext, TrustVcError> {
    if let Some(func_ctx) = base
        .function_context
        .as_ref()
        .filter(|func_ctx| func_ctx.name == function_name)
    {
        return Ok(func_ctx.clone());
    }

    base.helper_function_contexts
        .iter()
        .find(|func_ctx| func_ctx.name == function_name)
        .cloned()
        .ok_or_else(|| {
            super::encoding_error(
                CONFORMANCE_CONTEXT,
                format!(
                    "missing function context for concrete impl function '{}'",
                    function_name
                ),
            )
        })
}

fn build_impl_contract_env(
    base: &PreparedVerificationContext,
    trait_decl: &TraitDecl,
    impl_decl: &TraitImplDecl,
    concrete_fn_ctx: &FunctionContext,
    bindings: &ContractBindings,
) -> Result<TypeEnv, TrustVcError> {
    let mut env = TypeEnv::new();

    for var in &base.variables {
        env.insert(var.name.clone(), var.ty.clone());
    }
    for var in bindings.variables() {
        env.insert(var.name, var.ty);
    }

    let mut seen_function_contexts = HashSet::new();
    if let Some(func_ctx) = &base.function_context {
        register_function_context_in_env(
            &mut env,
            &base.trait_decls,
            func_ctx,
            &mut seen_function_contexts,
        )?;
    }
    for helper_ctx in &base.helper_function_contexts {
        register_function_context_in_env(
            &mut env,
            &base.trait_decls,
            helper_ctx,
            &mut seen_function_contexts,
        )?;
    }
    register_function_context_in_env(
        &mut env,
        &base.trait_decls,
        concrete_fn_ctx,
        &mut seen_function_contexts,
    )?;

    register_impl_method_metadata(&mut env, trait_decl, impl_decl)?;
    Ok(env)
}

fn register_function_context_in_env(
    env: &mut TypeEnv,
    trait_decls: &[TraitDecl],
    func_ctx: &FunctionContext,
    seen_function_contexts: &mut HashSet<String>,
) -> Result<(), TrustVcError> {
    if !seen_function_contexts.insert(func_ctx.name.clone()) {
        return Ok(());
    }

    env.insert_fn(func_ctx.name.clone(), func_ctx.return_type.clone());
    env.insert_fn_params(
        func_ctx.name.clone(),
        func_ctx.params.iter().map(|(_, ty)| ty.clone()).collect(),
    );
    register_trait_bound_methods_for_bounds(env, trait_decls, &func_ctx.trait_bounds)
}

fn register_trait_bound_methods_for_bounds(
    env: &mut TypeEnv,
    trait_decls: &[TraitDecl],
    bounds: &[crate::ir::TraitBound],
) -> Result<(), TrustVcError> {
    for bound in bounds {
        let Some(trait_decl) = trait_decls
            .iter()
            .find(|trait_decl| trait_decl.name == bound.trait_name)
        else {
            continue;
        };

        for method in &trait_decl.methods {
            insert_method_metadata_checked(
                env,
                &bound.type_param,
                &method.name,
                MethodMeta {
                    uf_name: format!("{}__{}", trait_decl.name, method.name),
                    return_type: method.return_type.clone(),
                    param_types: method.params.iter().map(|(_, ty)| ty.clone()).collect(),
                    box_receiver: None,
                },
            )?;
            // H10 (method half): see `ir_lowering::dispatch::methods`.
            env.insert_method_generic_params(
                bound.type_param.clone(),
                method.name.clone(),
                method.generic_params.clone(),
            );
        }
    }

    Ok(())
}

fn register_impl_method_metadata(
    env: &mut TypeEnv,
    trait_decl: &TraitDecl,
    impl_decl: &TraitImplDecl,
) -> Result<(), TrustVcError> {
    let receiver_type_name = impl_decl.concrete_type.to_type_string();

    for (trait_method_name, concrete_fn_name) in &impl_decl.method_bindings {
        let Some(method) = trait_decl
            .methods
            .iter()
            .find(|method| method.name == *trait_method_name)
        else {
            return Err(super::encoding_error(
                CONFORMANCE_CONTEXT,
                format!(
                    "missing trait method '{}::{}' while building conformance metadata",
                    trait_decl.name, trait_method_name
                ),
            ));
        };

        insert_method_metadata_checked(
            env,
            &receiver_type_name,
            trait_method_name,
            MethodMeta {
                uf_name: concrete_fn_name.clone(),
                // Normalize `Self::X` projections to the impl's associated-type
                // binding before Self-specialization (unresolved stays Opaque,
                // fail-closed downstream).
                return_type: specialize_self_type(
                    &impl_decl.resolve_assoc_projections(&method.return_type),
                    &impl_decl.concrete_type,
                ),
                param_types: method
                    .params
                    .iter()
                    .map(|(_, ty)| {
                        specialize_self_type(
                            &impl_decl.resolve_assoc_projections(ty),
                            &impl_decl.concrete_type,
                        )
                    })
                    .collect(),
                box_receiver: None,
            },
        )?;
        // H10 (method half): see `ir_lowering::dispatch::methods`.
        env.insert_method_generic_params(
            receiver_type_name.clone(),
            trait_method_name.clone(),
            method.generic_params.clone(),
        );
    }

    Ok(())
}

fn insert_method_metadata_checked(
    env: &mut TypeEnv,
    receiver_type_name: &str,
    method_name: &str,
    meta: MethodMeta,
) -> Result<(), TrustVcError> {
    if let Some(existing) = env.lookup_method(receiver_type_name, method_name) {
        if existing == &meta {
            return Ok(());
        }

        return Err(super::encoding_error(
            CONFORMANCE_CONTEXT,
            format!(
                "conflicting method metadata for '{}.{}'",
                receiver_type_name, method_name
            ),
        ));
    }

    env.insert_method_metadata(
        receiver_type_name.to_string(),
        method_name.to_string(),
        meta,
    );
    Ok(())
}

#[cfg(test)]
#[path = "trait_conformance_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "trait_conformance_slice6_tests.rs"]
mod slice6_tests;
