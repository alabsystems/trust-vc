// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verification condition extraction from Rust AST.
//!
//! This module bridges the gap between proc-macro expanded code and the ay encoder.
//! It parses Rust function bodies to extract verification conditions.

use crate::encoder::VerifyResult;
use crate::ir::{DatatypeVariant, StructDef, TrustVcType};
use crate::ir_lowering::expr_path_to_string;
use crate::vc::{ObligationKind, ProofObligation, VerificationContext};
use crate::{TrustVcError, TrustVcResult};
use proc_macro2::Span;
use quote::{quote, ToTokens};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
#[cfg(test)]
use syn::parse_file;
use syn::punctuated::Punctuated;
use syn::{visit::Visit, visit_mut::VisitMut};
use syn::{Block, Expr, File, FnArg, ItemFn, Pat, Path, Token, Type};

type AssociatedHelperSignature = (TrustVcType, Vec<(String, TrustVcType)>);
type AssociatedHelperSignatures = BTreeMap<String, AssociatedHelperSignature>;

mod attr_extract;
mod body_extract;
mod function_discovery;
mod mut_ref_prophecy;
mod param_extract;
mod return_extract;
pub(crate) mod trait_contracts;

#[cfg(test)]
#[path = "vc_extraction/tests.rs"]
mod tests;

/// Extracts the last segment name from a syn::Path.
/// Handles both simple identifiers (`assert`) and qualified paths (`trust_vc::assert`).
fn path_last_segment(path: &Path) -> Option<String> {
    function_discovery::path_last_segment(path)
}

/// Finds a function by name in the AST.
fn find_function<'a>(file: &'a File, name: &str) -> Option<&'a ItemFn> {
    function_discovery::find_function(file, name)
}

/// Extracts declared verification variables from a function input.
fn extract_vars_from_input(input: &FnArg) -> TrustVcResult<Vec<(String, String)>> {
    param_extract::extract_vars_from_input(input)
}

/// Extracts assertions from expressions (looking for assertion-like macros).
/// Only used by tests; production code enters through body extraction with
/// function-signature context.
#[cfg(test)]
fn extract_expr_assertions(
    expr: &Expr,
    vc: &mut VerificationContext,
    stmt_index: usize,
) -> TrustVcResult<()> {
    body_extract::extract_expr_assertions(expr, vc, stmt_index)
}

/// Classifies the function body's return flow for result modeling.
///
/// `params` supplies the function's parameter identifiers, consulted only to
/// admit a loop-invariant `return param` from inside a `loop`/`while`/`for`.
/// Pass an empty set to keep every loop-return fail-closed.
fn classify_return_expression<'a>(
    block: &'a Block,
    allow_unit_bare_return: bool,
    params: &BTreeSet<String>,
) -> return_extract::ReturnExtraction<'a> {
    return_extract::classify_return_expression(block, allow_unit_bare_return, params)
}

/// Collects the identifier of every simple `name: T` parameter of `func`.
/// Non-identifier parameter patterns and the receiver are skipped (they are
/// never candidates for a loop-invariant `return param`).
fn function_parameter_idents(inputs: &Punctuated<FnArg, Token![,]>) -> BTreeSet<String> {
    inputs
        .iter()
        .filter_map(|arg| match arg {
            FnArg::Typed(pat_type) => match pat_type.pat.as_ref() {
                Pat::Ident(pat_ident) => Some(pat_ident.ident.to_string()),
                _ => None,
            },
            FnArg::Receiver(_) => None,
        })
        .collect()
}

/// Extracts a type name as a string.
///
/// Preserves exact Rust type names so the encoder can map them to the correct
/// bitvector widths. For example, `u8` stays `"u8"` (8-bit BV), not collapsed
/// to `"u32"` (32-bit BV), which would change overflow semantics.
fn extract_type_name(ty: &Type) -> String {
    param_extract::extract_type_name(ty)
}

/// Extracts an expression as a string for the string-based parser.
fn extract_expr_string(expr: &Expr) -> String {
    use quote::quote;
    quote!(#expr).to_string()
}

/// Extracts and verifies a single function from a file.
///
/// The verdict covers the function's OWN obligations. Trait-impl conformance is
/// NOT folded in — it is an obligation of the IMPL, addressed by
/// [`list_trait_conformance_obligations`] / [`verify_trait_conformance_obligation`].
/// A file is verified only when its functions AND its conformance obligations
/// all discharge (`cargo trust-vc check` enumerates both).
pub fn verify_function_from_file(file_path: &str, func_name: &str) -> TrustVcResult<VerifyResult> {
    verify_function_from_file_inner(file_path, func_name)
}

/// Every trait-impl conformance obligation declared by `file_path`, named
/// exactly as the verification path names them
/// (`"trait impl conformance {Trait}::{method} for {Type}"`).
///
/// Conformance obligations are FIRST-CLASS, ADDRESSABLE cases: an impl is
/// checked whether or not anything in the file calls it, so a non-conforming
/// impl with no in-file caller is still reported (upstream Verus errors on it
/// too). Includes impls with NO method items — `impl Tr for bool {}` inherits a
/// default body that IS conformance-checked, and there is no syn method item to
/// enumerate, so the list comes from the trait/impl decls rather than the AST.
///
/// Every listed obligation is checkable by
/// [`verify_trait_conformance_obligation`], and the listing is produced by the
/// SAME walk that verifies them, so it can never drift from the set that is
/// checked.
pub fn list_trait_conformance_obligations(file_path: &str) -> TrustVcResult<Vec<String>> {
    let (pinned_width, ctx) = prepare_file_conformance_context(file_path)?;
    let _guard = pinned_width.map(crate::ir::PointerWidthGuard::install);
    let prepared = crate::prepared_context::prepare_context(&ctx)?;
    crate::encoder::AYEncoder::list_conformance_obligations(&prepared)
}

/// Verifies exactly ONE trait-impl conformance obligation of `file_path`,
/// addressed by the name [`list_trait_conformance_obligations`] reports.
///
/// This is the impl's own report channel. An unknown name fails CLOSED
/// (`Error`) and an impl body that cannot be lowered onto the conformance
/// surface fails CLOSED (`Unknown`) — neither may be mistaken for a discharged
/// obligation.
pub fn verify_trait_conformance_obligation(
    file_path: &str,
    obligation_name: &str,
) -> TrustVcResult<VerifyResult> {
    let (pinned_width, ctx) = prepare_file_conformance_context(file_path)?;
    let _guard = pinned_width.map(crate::ir::PointerWidthGuard::install);
    let prepared = crate::prepared_context::prepare_context(&ctx)?;
    Ok(crate::encoder::AYEncoder::verify_conformance_obligation(
        &prepared,
        obligation_name,
    ))
}

/// The name of the synthetic function used to carry a file's conformance
/// context. It declares no contracts and has an empty body, so it contributes no
/// obligations of its own — it exists only so the file-level registration
/// (traits, impls, structs, spec catalog, helper signatures) runs exactly as it
/// does when a real function in the file is verified.
const CONFORMANCE_PROBE_FN: &str = "__trust_vc_conformance_probe";

/// Builds the FILE-level verification context that trait conformance is checked
/// against, independent of any particular function in the file.
///
/// Conformance obligations belong to the file's impls, not to a function, so
/// they must be checkable even when the file contains no function at all (an
/// `impl Tr for bool {}` with a violating inherited default is still an error).
/// A synthetic, contract-free probe function stands in as the "current"
/// function; every trait/impl/struct/helper registration is driven off the FILE,
/// exactly as in [`verify_function_from_file`].
fn prepare_file_conformance_context(
    file_path: &str,
) -> TrustVcResult<(Option<u32>, VerificationContext)> {
    let content = fs::read_to_string(file_path).map_err(|source| TrustVcError::Io {
        context: "read verification source file",
        source,
    })?;
    let pinned_width = match crate::ir::scan_pointer_width_directive(&content) {
        Ok(guard) => crate::ir::pinned_width_from_guard(guard),
        Err(detail) => {
            return Err(TrustVcError::Encoding {
                context: "scan global size_of usize directive",
                detail,
            })
        }
    };
    let content = crate::ir::strip_pointer_width_directives(&content);
    let content = crate::spec_function_catalog::normalize_open_spec_source(&content);
    let ast = crate::parse_file_allow_tracked(&content).map_err(|source| TrustVcError::Parse {
        context: "parse verification source file",
        source,
    })?;

    let probe_ident = syn::Ident::new(CONFORMANCE_PROBE_FN, Span::call_site());
    let probe: ItemFn = syn::parse_quote! {
        fn #probe_ident() {}
    };

    let _guard = pinned_width.map(crate::ir::PointerWidthGuard::install);
    let mut ctx = extract_verification_conditions_from_parts_inner(
        Some(&ast),
        Some(std::path::Path::new(file_path)),
        &probe,
        // The probe is not itself an item of the file, so the narrow
        // "function is named in the file" gate would skip source-trait
        // registration and leave the context with ZERO impls — every
        // conformance obligation would silently vanish from the listing.
        true,
    )?;
    // The conformance machinery derives every sub-query from an obligation
    // TEMPLATE (`base.obligations.first()`), so the context must carry at least
    // one obligation. The probe declares no contracts, so supply a trivially
    // true one — it is an `Assert`, never an `Assume`, so it cannot weaken any
    // conformance check derived from it.
    if ctx.obligations.is_empty() {
        ctx.push_obligation(ProofObligation::assert(CONFORMANCE_PROBE_FN, "true"));
    }
    Ok((pinned_width, ctx))
}

/// Part of #1690: typed inner path for crate-internal callers.
pub(crate) fn try_verify_function_from_file(
    file_path: &str,
    func_name: &str,
) -> TrustVcResult<VerifyResult> {
    verify_function_from_file_inner(file_path, func_name)
}

fn verify_function_from_file_inner(
    file_path: &str,
    func_name: &str,
) -> TrustVcResult<VerifyResult> {
    // Read the file
    let content = fs::read_to_string(file_path).map_err(|source| TrustVcError::Io {
        context: "read verification source file",
        source,
    })?;

    // Detect (and validate) any `global size_of usize == N` target pointer-width
    // directive (#2778) BEFORE extracting VCs, because `declare_var_typed`
    // resolves usize/isize bit widths via `pointer_width()` at declaration time,
    // and the encoder's shift and bit-vector bounds read the same width during
    // `verify()`. We scan the raw, pre-normalization source so the directive line
    // is observed exactly as authored (`normalize_open_spec_source` rewrites
    // `spec fn`, not globals). The scan also fails closed on malformed/conflicting
    // directives — so we run it here unconditionally even when we will re-derive
    // the width(s) ourselves below.
    let pinned_width = match crate::ir::scan_pointer_width_directive(&content) {
        Ok(guard) => crate::ir::pinned_width_from_guard(guard),
        Err(detail) => {
            return Err(TrustVcError::Encoding {
                context: "scan global size_of usize directive",
                detail,
            })
        }
    };

    // The directive is a unit-level pragma, not a Rust item, so remove it before
    // parsing. The width(s) it declared are re-installed per verification pass.
    let content = crate::ir::strip_pointer_width_directives(&content);
    let content = crate::spec_function_catalog::normalize_open_spec_source(&content);

    // Parse the file once — parsing is pointer-width independent. Only extraction
    // (which bakes usize/isize widths into the IR) and verification depend on the
    // installed width, so each pass below re-runs *those* under its own guard.
    let ast = crate::parse_file_allow_tracked(&content).map_err(|source| TrustVcError::Parse {
        context: "parse verification source file",
        source,
    })?;

    // Find the target function
    let func = find_function(&ast, func_name).ok_or_else(|| TrustVcError::Internal {
        context: "find function in verification source",
        detail: format!("Function '{}' not found in {}", func_name, file_path),
    })?;

    // The source file path lets the spec catalog resolve `use crate::…`-imported
    // spec functions from sibling modules of the SAME crate (cross-file). Cross-
    // crate imports are not resolved here (they stay uninterpreted — fail closed).
    let source_path = std::path::Path::new(file_path);
    match pinned_width {
        // A pinned `global size_of usize == N` directive fixes the target arch:
        // verify exactly once at that width (unchanged behavior).
        Some(width) => verify_unit_at_width(&ast, func, width, Some(source_path)),
        // No directive. If the unit's verification depends on the pointer width
        // (mentions `usize`/`isize`/`usize::BITS`), Rust permits BOTH a 32-bit and
        // a 64-bit `usize`, so a proof is sound only if it holds at BOTH. Emit the
        // obligation set twice and require both to discharge (#2778 dual-arch).
        // Width-invariant units are verified once at the host width, as before.
        None if unit_is_pointer_width_polymorphic(func) => {
            verify_unit_dual_width(&ast, func, Some(source_path))
        }
        None => {
            // Host width, no guard needed (pointer_width() already returns it).
            extract_verification_conditions_with_source_file(&ast, func, Some(source_path))
                .map(|vc| vc.verify())
        }
    }
}

/// Extracts and verifies `func` with the given target pointer width installed.
///
/// Both VC extraction (which bakes usize/isize widths into the IR) and `verify()`
/// run under the same [`crate::ir::PointerWidthGuard`], so the obligation set and
/// the solver's bit-vector bounds agree on the target width.
fn verify_unit_at_width(
    ast: &File,
    func: &ItemFn,
    width_bits: u32,
    source_file: Option<&std::path::Path>,
) -> TrustVcResult<VerifyResult> {
    let _guard = crate::ir::PointerWidthGuard::install(width_bits);
    extract_verification_conditions_with_source_file(ast, func, source_file).map(|vc| vc.verify())
}

/// Verifies a pointer-width-polymorphic unit at BOTH 32-bit and 64-bit `usize`,
/// requiring both to discharge for an overall `Verified` verdict (#2778).
///
/// Rust's `usize`/`isize` are 32-bit on some targets and 64-bit on others. When a
/// unit carries no `global size_of usize` directive pinning the target, a proof
/// that mentions `usize`/`isize` is sound only if it holds for *every* width Rust
/// supports for the polymorphic case. We verify the obligation set under each
/// width and combine:
///
/// * Both `Verified`  → `Verified`.
/// * Otherwise        → the failing result, tagged with the arch(es) on which it
///   failed (`_32bit`, `_64bit`, or `_32bit_64bit`), mirroring upstream Verus's
///   `assert_fails_bv_*` arch-specific reporting.
///
/// A non-`Counterexample`/`Verified` outcome (`Unknown`/`Error`) on either width
/// is surfaced as-is (also arch-tagged) rather than being masked by the other
/// width's success — fail-closed.
fn verify_unit_dual_width(
    ast: &File,
    func: &ItemFn,
    source_file: Option<&std::path::Path>,
) -> TrustVcResult<VerifyResult> {
    let result_32 = verify_unit_at_width(ast, func, 32, source_file)?;
    let result_64 = verify_unit_at_width(ast, func, 64, source_file)?;
    Ok(combine_dual_width_results(result_32, result_64))
}

/// Architecture tag for a dual-width verification failure.
fn arch_suffix(failed_32: bool, failed_64: bool) -> &'static str {
    match (failed_32, failed_64) {
        (true, true) => "_32bit_64bit",
        (true, false) => "_32bit",
        (false, true) => "_64bit",
        // Caller only constructs a suffix when at least one width failed.
        (false, false) => "",
    }
}

/// Combines the 32-bit and 64-bit verification results for a polymorphic unit.
///
/// `Verified` requires BOTH widths to verify. Any non-verifying width makes the
/// combined verdict non-`Verified`; the surfaced result is the failing one, with
/// its obligation name suffixed by the arch(es) on which the proof failed so
/// downstream reporting can distinguish a 32-bit-only failure from a 64-bit-only
/// one from a both-arch failure (parity with upstream `assert_fails_bv_32bit` /
/// `_64bit` / `_32bit_64bit`).
fn combine_dual_width_results(result_32: VerifyResult, result_64: VerifyResult) -> VerifyResult {
    let failed_32 = !result_32.is_verified();
    let failed_64 = !result_64.is_verified();
    if !failed_32 && !failed_64 {
        return VerifyResult::Verified;
    }
    let suffix = arch_suffix(failed_32, failed_64);
    // Prefer a concrete counterexample over an Unknown/Error so the user sees the
    // witnessing model; if only one width is a counterexample, surface that one.
    let chosen = match (failed_32, &result_32, failed_64, &result_64) {
        // Both failed: prefer whichever is a counterexample; if both are, the
        // 32-bit witness is reported (the suffix already records both archs).
        (true, VerifyResult::Counterexample { .. }, _, _) => result_32,
        (_, _, true, VerifyResult::Counterexample { .. }) => result_64,
        // Neither width produced a counterexample (Unknown/Error): surface the
        // failing width's result; prefer 32-bit when both failed.
        (true, _, _, _) => result_32,
        (_, _, true, _) => result_64,
        // Unreachable: at least one of failed_32/failed_64 is true here.
        (false, _, false, _) => VerifyResult::Verified,
    };
    tag_result_with_arch(chosen, suffix)
}

/// Appends an architecture suffix to a non-verifying result's obligation name.
fn tag_result_with_arch(result: VerifyResult, suffix: &str) -> VerifyResult {
    if suffix.is_empty() {
        return result;
    }
    match result {
        VerifyResult::Counterexample {
            obligation_name,
            model,
            bindings,
        } => VerifyResult::Counterexample {
            obligation_name: format!("{obligation_name}{suffix}"),
            model,
            bindings,
        },
        VerifyResult::NotProved { reason, category } => VerifyResult::NotProved {
            reason: format!("{reason} (arch{suffix})"),
            category,
        },
        VerifyResult::Unknown { reason, category } => VerifyResult::Unknown {
            reason: format!("{reason} (arch{suffix})"),
            category,
        },
        // Verified/Error are passed through unchanged: Verified carries no
        // obligation name to tag, and Error is already a hard stop.
        other => other,
    }
}

/// Conservatively decides whether verifying `func` depends on the target pointer
/// width, i.e. whether it mentions `usize`/`isize` (including `usize::BITS`).
///
/// This is a syntactic over-approximation: any unit that *names* `usize`/`isize`
/// is treated as width-polymorphic and verified at both widths. Over-approximating
/// is sound — a width-invariant unit that happens to mention `usize` simply
/// verifies identically at both widths (both pass, combined verdict `Verified`),
/// at the cost of one extra solver pass. Under-approximating would be unsound (a
/// genuinely width-dependent proof verified at only one width), so we err toward
/// inclusion. We scan the function's own token stream (signature + body) so the
/// decision is independent of how widths are later baked into the IR.
fn unit_is_pointer_width_polymorphic(func: &ItemFn) -> bool {
    fn tokens_mention_pointer_width(tokens: proc_macro2::TokenStream) -> bool {
        use proc_macro2::TokenTree;
        for tree in tokens {
            match tree {
                TokenTree::Ident(ident) => {
                    let s = ident.to_string();
                    if s == "usize" || s == "isize" {
                        return true;
                    }
                }
                TokenTree::Group(group) if tokens_mention_pointer_width(group.stream()) => {
                    return true;
                }
                _ => {}
            }
        }
        false
    }
    tokens_mention_pointer_width(func.to_token_stream())
}

/// INCREMENT 1 (Fn-bound closure typing foundation). Recognizes `Fn(A..) -> B`
/// parenthesized trait bounds on the function's own type parameters and maps each
/// such type-parameter NAME to its `SpecFn(arg_tys, ret)` model, so a value
/// parameter `f: F` (with `F: Fn(A..) -> B`) is typed as a first-class `SpecFn`
/// value and a call `f(x)` reaches the existing opaque, congruent `spec_fn_apply`
/// UF arm (`ir_lowering/dispatch/calls.rs`).
///
/// SOUNDNESS — `Fn`-ONLY (the deterministic case):
/// * `Fn` captures immutably, so it is DETERMINISTIC across calls: modeling `f`
///   with one congruent uninterpreted function (`spec_fn_apply(f, x)`) is sound —
///   equal arguments yield the equal result (`f(3) == f(3)`), the real capability
///   this typing unlocks. The result stays otherwise UNCONSTRAINED (`f(3) == 3` is
///   NOT provable — the UF says nothing about its value).
/// * `FnMut` / `FnOnce` are NOT deterministic across calls (mutable / consumed
///   captures); a single congruent UF would UNSOUNDLY prove `f(3) == f(3)`. They
///   are therefore left UNMODELED — the type parameter keeps its bare `TypeParam`
///   typing, so a call through such a parameter fails closed exactly as before.
///   Only a `Fn` bound is recognized here.
///
/// The parameter is typed as a PURELY UNCONSTRAINED `SpecFn` value: this ONLY sets
/// the variable's type. It registers NO reflection contract, so the call-site
/// obligation seam (`record_closure_application_obligations`, gated on
/// `closure_reflection_contracts`) emits nothing, and it runs NO def-side
/// obligation (`record_closure_def_side_failure` is reachable only from a
/// `trust_vc::closure!` literal). Nothing is assumed about the result. This is why
/// the cardinal direct-application invariant (SpecFn-typed ⟺
/// registered-with-checked-def-side) is NOT weakened: a def-side-less `Fn`
/// parameter never enters the registered/assumed lane — its result term is opaque
/// and behaviour-dependent reads fail closed.
///
/// Fails closed (omits the type parameter, leaving its original `TypeParam`
/// typing) whenever any argument or the return type is not fully concrete /
/// modelable (opaque or a residual type parameter), so an `Fn(T) -> T` or
/// `Fn(UnknownStruct) -> u64` bound never produces an unsound `SpecFn` sort.
fn fn_bound_spec_fn_param_types(
    sig: &syn::Signature,
    source_structs: Option<&SourceStructRegistry>,
) -> BTreeMap<String, TrustVcType> {
    let mut map = BTreeMap::new();
    let mut record =
        |type_param: &str, bounds: &Punctuated<syn::TypeParamBound, syn::token::Plus>| {
            if let Some(spec_fn) = fn_bound_spec_fn_type(bounds, source_structs) {
                map.insert(type_param.to_string(), spec_fn);
            }
        };
    for param in sig.generics.type_params() {
        record(&param.ident.to_string(), &param.bounds);
    }
    if let Some(where_clause) = &sig.generics.where_clause {
        for predicate in &where_clause.predicates {
            if let syn::WherePredicate::Type(predicate) = predicate {
                if let syn::Type::Path(type_path) = &predicate.bounded_ty {
                    if let Some(ident) = type_path.path.get_ident() {
                        record(&ident.to_string(), &predicate.bounds);
                    }
                }
            }
        }
    }
    map
}

/// The `SpecFn(arg_tys, ret)` model of a single type parameter's `bounds`, when
/// they carry a DETERMINISTIC `Fn(A..) -> B` parenthesized bound over fully
/// concrete argument/return types. A `FnMut`/`FnOnce` bound, a non-parenthesized
/// `Fn` mention, or any non-concrete signature yields `None` (fail closed — see
/// [`fn_bound_spec_fn_param_types`]).
fn fn_bound_spec_fn_type(
    bounds: &Punctuated<syn::TypeParamBound, syn::token::Plus>,
    source_structs: Option<&SourceStructRegistry>,
) -> Option<TrustVcType> {
    for bound in bounds {
        let syn::TypeParamBound::Trait(trait_bound) = bound else {
            continue;
        };
        if !matches!(trait_bound.modifier, syn::TraitBoundModifier::None) {
            continue;
        }
        let Some(segment) = trait_bound.path.segments.last() else {
            continue;
        };
        // Increment 1 is `Fn`-ONLY: `FnMut`/`FnOnce` are non-deterministic across
        // calls, so a congruent UF would be UNSOUND for them — leave them fail
        // closed by declining to recognize the bound.
        if segment.ident != "Fn" {
            continue;
        }
        let syn::PathArguments::Parenthesized(args) = &segment.arguments else {
            continue;
        };
        let mut arg_tys = Vec::with_capacity(args.inputs.len());
        for input in &args.inputs {
            arg_tys.push(resolve_concrete_type(input, source_structs)?);
        }
        let ret_ty = match &args.output {
            syn::ReturnType::Default => TrustVcType::Unit,
            syn::ReturnType::Type(_, ty) => resolve_concrete_type(ty, source_structs)?,
        };
        return Some(TrustVcType::SpecFn(arg_tys, Box::new(ret_ty)));
    }
    None
}

/// Resolve a `syn::Type` to a FULLY CONCRETE `TrustVcType` via the same
/// registry-then-`parse_or_opaque` path the parameter loop uses. Returns `None`
/// for anything not fully concrete (opaque, or a residual type parameter), so a
/// non-modelable `Fn` signature fails closed rather than producing an unsound
/// `SpecFn` sort.
fn resolve_concrete_type(
    ty: &Type,
    source_structs: Option<&SourceStructRegistry>,
) -> Option<TrustVcType> {
    let ty_str = extract_type_name(ty);
    let resolved = source_structs
        .and_then(|registry| registry.resolve_type_string(&ty_str))
        .unwrap_or_else(|| TrustVcType::parse_or_opaque(&ty_str));
    if resolved.contains_opaque() || resolved.contains_type_param() {
        return None;
    }
    Some(resolved)
}

/// Extracts verification conditions from a function.
pub fn extract_verification_conditions(func: &ItemFn) -> TrustVcResult<VerificationContext> {
    extract_verification_conditions_inner(func)
}

fn extract_verification_conditions_inner(func: &ItemFn) -> TrustVcResult<VerificationContext> {
    extract_verification_conditions_from_parts(None, None, func)
}

pub fn extract_verification_conditions_with_file_context(
    file: &File,
    func: &ItemFn,
) -> TrustVcResult<VerificationContext> {
    extract_verification_conditions_from_parts(Some(file), None, func)
}

/// Like [`extract_verification_conditions_with_file_context`], but also threads
/// the on-disk path of the source file so the spec catalog can resolve
/// `use crate::…`-imported spec functions from sibling modules of the same crate
/// (cross-file). Used by the proc-macro `verify_function_from_file` path.
pub(crate) fn extract_verification_conditions_with_source_file(
    file: &File,
    func: &ItemFn,
    source_file: Option<&std::path::Path>,
) -> TrustVcResult<VerificationContext> {
    extract_verification_conditions_from_parts(Some(file), source_file, func)
}

fn extract_verification_conditions_from_parts(
    file: Option<&File>,
    source_file: Option<&std::path::Path>,
    func: &ItemFn,
) -> TrustVcResult<VerificationContext> {
    extract_verification_conditions_from_parts_inner(file, source_file, func, false)
}

/// `force_source_trait_registration` registers the file's trait decls + impls
/// regardless of the verified function's shape. It is set ONLY for the synthetic
/// conformance probe (see [`prepare_file_conformance_context`]), whose whole
/// purpose is to carry the file's trait/impl decls; every real function keeps the
/// narrow gate below byte-for-byte.
fn extract_verification_conditions_from_parts_inner(
    file: Option<&File>,
    source_file: Option<&std::path::Path>,
    func: &ItemFn,
    force_source_trait_registration: bool,
) -> TrustVcResult<VerificationContext> {
    // Capture exact source provenance before binder inference rewrites the body.
    let source_identity_func = func;
    let source_file_is_crate_root = match source_file {
        Some(path) => crate::mode_index::discover_crate_root(path).map(|root| {
            let source = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
            let root = root.canonicalize().unwrap_or(root);
            source == root
        }),
        None => Some(true),
    };
    let enclosing_inline_module =
        file.and_then(
            |file| match function_discovery::enclosing_inline_module_path(file, func) {
                function_discovery::EnclosingModuleResolution::Unique(path) => Some(path),
                function_discovery::EnclosingModuleResolution::Ambiguous => None,
            },
        );
    let enclosing_self_ty = match file {
        Some(file) => match function_discovery::enclosing_impl_self_ty(file, func) {
            function_discovery::EnclosingImplResolution::NotImpl => None,
            function_discovery::EnclosingImplResolution::Unique(self_ty) => Some(self_ty),
            function_discovery::EnclosingImplResolution::Ambiguous => {
                return Err(TrustVcError::Encoding {
                    context: "resolve enclosing impl method",
                    detail: format!(
                        "cannot resolve `{}` to one exact source method; same-named or token-identical candidates make `Self` substitution ambiguous",
                        func.sig.ident
                    ),
                });
            }
        },
        None => None,
    };

    // Verus infers the type of an `assert forall|x| …` binder from its use
    // (upstream assert_forall_by.rs `test_forallstmt1` pairs the typed form with
    // the inferred one in a single case). Resolve those binders against the
    // file's SPEC-fn signatures before anything else looks at the body; binders
    // whose type is not forced by the program are left untyped on purpose and
    // still fail closed in `parse_assert_forall_by`. Needs the file context, so
    // the proc-macro (no-file) path keeps rejecting untyped binders outright.
    let binder_inferred;
    let func = match file {
        Some(file) => {
            match crate::assert_forall_binder_inference::infer_untyped_assert_forall_binders(
                file, func,
            ) {
                Some(rewritten) => {
                    binder_inferred = rewritten;
                    &binder_inferred
                }
                None => func,
            }
        }
        None => func,
    };

    // Resolve `Self` to the enclosing impl's concrete type. An impl method
    // lifted to a standalone `ItemFn` (by either the gate's `find_function` or
    // the file-context test harness) loses its impl context, so a bare `self`
    // receiver, a `-> Self` return, or a `Self::method(..)` associated call
    // would otherwise carry the literal keyword `Self` and fail to lower. This
    // is the single point every extraction caller shares, so both paths resolve
    // `Self` identically. Sound: `Self` IS the impl's self type — the rewrite
    // only makes types more concrete, never weaker. Free functions and
    // trait-method defaults are left untouched (`enclosing_impl_self_ty` reports
    // `NotImpl`).
    let self_substituted;
    let func = match enclosing_self_ty {
        Some(self_ty) => {
            let mut owned = func.clone();
            let mut sub = function_discovery::SelfTypeSubstituter::new(self_ty);
            syn::visit_mut::visit_signature_mut(&mut sub, &mut owned.sig);
            syn::visit_mut::visit_block_mut(&mut sub, &mut owned.block);
            self_substituted = owned;
            &self_substituted
        }
        None => func,
    };

    // A3: resolve fully-qualified associated-type projections
    // `<Concrete as Trait>::Assoc` in the SIGNATURE to the concrete type bound
    // by the file's matching `#[trust_vc::trait_impl]` (`type Assoc = T;`). A
    // parameter or return typed by such a projection (e.g. `x: <S as Tr>::X`
    // where `impl Tr for S { type X = u8; }`) would otherwise reach the string
    // parser as `Opaque("<S as Tr>::X")` — the `as` word boundary collapsed by
    // token re-rendering — and sink the whole file closed even though the impl
    // binds the projection to a fully concrete type. Resolving structurally at
    // the syn seam, BEFORE the string parser, sidesteps that mangling and lands
    // the concrete type in the lifted variable's OWN sort. SOUND: it only makes
    // a type more concrete, and only to what the impl binds; an unmatched or
    // bare-generic (`T::X`) projection is left as-is and still fails closed
    // downstream. Applied to the signature only — local `let`-typed projections
    // in the body already resolve via initializer inference and stay on that
    // path.
    let projection_resolved;
    let func = match file {
        Some(file) => {
            let bindings = function_discovery::collect_assoc_projection_bindings(file);
            if bindings.is_empty() {
                func
            } else {
                let mut owned = func.clone();
                let mut resolver = function_discovery::AssocProjectionResolver::new(&bindings);
                syn::visit_mut::visit_signature_mut(&mut resolver, &mut owned.sig);
                projection_resolved = owned;
                &projection_resolved
            }
        }
        None => func,
    };

    // Desugar the `?` (Try) operator into an equivalent tail `match` BEFORE the
    // control-flow gates and extraction. `let PAT = g()?; REST` becomes
    // `match g() { Some(PAT) => { REST }, None => None }` (Ok/Err for a Result
    // fn) — a tail match with no early return, which the extractor checks on
    // every arm. Behavior-preserving; only supported shapes are rewritten
    // (others keep their existing `Expr::Try` fail-close). See try_desugar.rs.
    let try_desugared;
    let func = match crate::try_desugar::desugar_try_operator(
        func,
        file,
        enclosing_inline_module.as_deref(),
    ) {
        Some(owned) => {
            try_desugared = owned;
            &try_desugared
        }
        None => func,
    };

    // Desugar ARGUMENT-position `impl Trait` (`fn f(x: impl Tr)`) into a
    // synthetic generic type parameter (`fn f<__TrustVcAPIT0: Tr>(x: __TrustVcAPIT0)`)
    // BEFORE trait-bound/signature extraction, so `x.spec_method()` resolves via
    // the already-sound generic-bound path. Behavior-preserving; emits no axioms.
    // Return-position `-> impl Trait` is deliberately left untouched. See
    // impl_trait_desugar.rs.
    let apit_desugared;
    let func = match crate::impl_trait_desugar::desugar_impl_trait_args(func) {
        Some(owned) => {
            apit_desugared = owned;
            &apit_desugared
        }
        None => func,
    };

    // Desugar `let S { a, b, .. } = obj;` (a struct pattern with a rest) into
    // per-field `let a = obj.a; let b = obj.b;` — reusing the field-projection
    // path the extractor already lowers. Only fires for plain-ident field
    // bindings and a side-effect-free identifier initializer; can only ADD
    // sound field bindings, never false-verify. See struct_rest_pattern_desugar.rs.
    let rest_pat_desugared;
    let func = match crate::struct_rest_pattern_desugar::desugar_struct_rest_pattern(func) {
        Some(owned) => {
            rest_pat_desugared = owned;
            &rest_pat_desugared
        }
        None => func,
    };

    // Desugar `matches!(EXPR, PAT [if GUARD])` into `match EXPR { PAT => true,
    // _ => false }` — its exact expansion — so it lowers like any `match`.
    // Behavior-preserving; handles body, `assert!` bodies, and contract
    // attributes. See matches_macro_desugar.rs.
    let matches_desugared;
    let func = match crate::matches_macro_desugar::desugar_matches_macro(func) {
        Some(owned) => {
            matches_desugared = owned;
            &matches_desugared
        }
        None => func,
    };

    // Desugar `if COND { A } else { panic!() }` (a diverging FAILURE arm) into
    // `{ let fresh = COND; trust_vc::assert!(fresh); A }`. The ordinary local
    // preserves single evaluation, side effects, and exec panic obligations;
    // the assert is the arm's unreachability obligation and the surviving
    // branch supplies the value. Only fires when EXACTLY one branch is a bare
    // diverging-failure block and COND has no branch-scoped `let` binding; all
    // other panic shapes keep failing closed. See diverging_if_desugar.rs.
    let diverging_desugared;
    let func = match crate::diverging_if_desugar::desugar_diverging_if(func) {
        Some(owned) => {
            diverging_desugared = owned;
            &diverging_desugared
        }
        None => func,
    };

    // Desugar `<fieldless-decl-order-enum> as <int>` (`Color::Green as u64`,
    // `c as int` for `c: Color`) into an equal integer expression — a variant's
    // declaration-order discriminant — keeping the `as TARGET` so the existing
    // int→TARGET cast finishes the job. Only enums whose declaration order IS
    // Rust's discriminant (fieldless + no explicit discriminants) are rewritten;
    // everything else keeps its fail-closed cast. See enum_int_cast_desugar.rs.
    let enum_cast_desugared;
    let func = match crate::enum_int_cast_desugar::desugar_enum_int_cast(func, file) {
        Some(owned) => {
            enum_cast_desugared = owned;
            &enum_cast_desugared
        }
        None => func,
    };

    // Desugar a bounded, FLAT `for i in LO..HI { BODY }` range loop into the
    // counter-driven `while i < HI { invariant!(LO<=i); BODY; i = i+1; }` that the
    // loop machinery already reasons about soundly (base + inductive-step invariant
    // checks + negated-guard exit fact). Fires only for a plain loop var, simple
    // (literal/ident) bounds, a body that neither reassigns the loop var nor the
    // upper bound, and a flat (spec-macro + pure-arith-assign) body — every other
    // `for` keeps its current fail-closed behavior. The injected `LO<=i` invariant
    // is inductive and re-checked by the machinery, so this can only turn a
    // previously fail-closed range `for` into a soundly verified/refuted `while`,
    // never a false `Verified`. See for_range_desugar.rs.
    let for_range_desugared;
    let func = match crate::for_range_desugar::desugar_for_range(func) {
        Some(owned) => {
            for_range_desugared = owned;
            &for_range_desugared
        }
        None => func,
    };

    let mut vc = VerificationContext::new();
    let function_mode = crate::mode_attrs::classify_item_fn(func);
    // Faithful to Verus: exec functions get overflow / div-by-zero / bit-shift
    // safety obligations; spec & proof functions do not. Without this wiring the
    // encoder never emits exec arithmetic checks, so trust-vc unsoundly accepts
    // overflowing exec code that Verus rejects (#2778).
    vc = vc.with_mode_overflow(function_mode);
    let function_solver_mode = crate::mode_attrs::extract_function_solver_mode(&func.attrs)?;
    // Verus-style per-function solver budget: `#[verifier::rlimit(N)]` /
    // `#[verifier::rlimit(infinity)]` (upstream basic.rs test_rlimit_20 /
    // test_rlimit_inf). N is in upstream rlimit units (~seconds of reference
    // solver work, verifier.rs RLIMIT_PER_SECOND) and maps onto the
    // per-obligation `rlimit_ms` nominal budget; malformed arguments fail
    // closed with the verbatim upstream message. See
    // `mode_attrs::extract_function_rlimit_ms`.
    if let Some(rlimit_ms) = crate::mode_attrs::extract_function_rlimit_ms(&func.attrs)? {
        vc.set_rlimit(rlimit_ms);
    }
    if !matches!(function_mode, crate::mode::FunctionMode::Exec)
        && block_contains_let_else(&func.block)
    {
        return Err(TrustVcError::Encoding {
            context: "extract verification conditions",
            detail: "The verifier does not yet support the following Rust feature: let-else in spec/proof".to_string(),
        });
    }
    // Verus mode/signature misuse rejections (upstream basic.rs / modes.rs
    // parity). Verus fires signature-lowering errors before body mode-checking,
    // and the by-value `mut self` unsupported_err (rust_to_vir_func.rs, any
    // mode) before the spec-mode parameter check — match that order. All rules
    // are reject-only (fail-closed): they can never make a program verify that
    // did not already.
    if let Some(err) = mut_self_receiver_error(func) {
        return Err(err);
    }
    // Verus parity (upstream assert_forall_by.rs `test_assertby1_fail3` /
    // `test_forallstmt1_fail3`): inside an `assert … by` / `assert forall … by`
    // block, an outer PROOF-mode variable reads at mode `spec`
    // (`vir/src/modes.rs` pushes `in_forall_stmt` for both flavours), so passing
    // it to a `tracked` (proof-mode) parameter is a mode error. Needs the file
    // context for the callee's parameter modes, so the proc-macro (no-file) path
    // is unaffected. Reject-only — see `crate::proof_var_mode`.
    if let Some(file) = file {
        crate::proof_var_mode::check_by_block_proof_var_modes(file, func)?;
    }
    // Verus parity (upstream inline.rs `test_nonspec_fails`): `#[verifier(inline)]`
    // is only permitted on SPEC functions — an `#[inline]` proof/exec fn is
    // rejected at the VIR level with this verbatim message. Fail-closed:
    // rejecting the definition can never wrongly verify.
    if crate::spec_function_catalog::has_inline_attr(&func.attrs)
        && !matches!(function_mode, crate::mode::FunctionMode::Spec)
    {
        return Err(TrustVcError::Encoding {
            context: "extract verification conditions",
            detail: "'inline' is only allowed for 'spec' functions".to_string(),
        });
    }
    match function_mode {
        crate::mode::FunctionMode::Spec => {
            if let Some(err) = spec_mut_param_error(func) {
                return Err(err);
            }
            if block_contains_assignment(&func.block) {
                // Upstream: vir/src/modes.rs — ANY assignment typed in a pure
                // (spec) context is rejected, including deferred-init locals
                // (`let x: u64; x = 23;`, modes.rs spec_let_decl_init_fail)
                // and `let mut` locals. Exec/proof deferred init stays legal.
                return Err(TrustVcError::Encoding {
                    context: "extract verification conditions",
                    detail: "assignment is not allowed inside pure context".to_string(),
                });
            }
            if block_contains_return(&func.block) {
                // Upstream: vir/src/modes.rs — spec-fn bodies are checked
                // with `in_pure` set (`push_in_pure(pure_spec_fn)`), so ANY
                // `return` typed in a spec body — including inside closures
                // (spec closures are pure too) — is rejected. No upstream
                // test pins the bare spec-body shape (the closure shape is
                // pinned by closures.rs `return_in_closure`); the modes.rs
                // source check (ExprX::Return + in_pure) is unambiguous.
                return Err(TrustVcError::Encoding {
                    context: "extract verification conditions",
                    detail: "return is not allowed in pure context".to_string(),
                });
            }
        }
        crate::mode::FunctionMode::Proof => {
            if let Some(err) = proof_non_mut_param_assignment_error(func) {
                return Err(err);
            }
            if block_closures_contain_return(&func.block) {
                // Upstream witness: closures.rs `return_in_closure` —
                // `proof fn p() { let _f = |x:int| -> int { return x; }; }`.
                // A closure in a proof fn is a spec closure; its body is
                // checked with `in_pure` set, so `return` inside it is
                // rejected. A top-level `return` in a proof-fn BODY is legal
                // (the `(Mode::Proof, _)` arm of ExprX::Return) and must not
                // fire — the finder is closure-scoped.
                return Err(TrustVcError::Encoding {
                    context: "extract verification conditions",
                    detail: "return is not allowed in pure context".to_string(),
                });
            }
        }
        _ => {}
    }
    // Ghost-argument control-flow rejections (all modes): the arguments of
    // assert!/assume! and the proof block of `assert forall … by` are
    // ghost/pure contexts upstream, but they live inside macro token streams
    // that `syn::visit` never descends — so the body-level finders above
    // cannot see them. This walker parses those token streams with the SAME
    // parsers the real extraction path uses and rejects
    // return/break/continue/loops with the upstream messages.
    if let Some(err) = ghost_macro_control_flow_error(&func.block, function_mode) {
        return Err(err);
    }
    // Upstream at-most-one `proof_note` rule: a translation-time reject that
    // fires BEFORE any solving, regardless of proof outcome (FAMILY C).
    if let Some(err) = proof_note_at_most_one_error(&func.block) {
        return Err(err);
    }
    let source_structs = file.map(SourceStructRegistry::from_file);
    if let Some(registry) = &source_structs {
        registry.register_struct_defs(&mut vc);
        registry.register_type_aliases(&mut vc);
    }
    let source_consts = file.map(SourceConstRegistry::from_file);
    let source_traits = file.map(SourceTraitRegistry::from_file);
    let return_binding = attr_extract::extract_return_binding(&func.attrs, Some(&func.sig))?;
    let has_direct_returns_postcondition =
        attr_extract::has_direct_returns_postcondition(&func.attrs, Some(&func.sig))?;
    let result_var = return_binding.as_deref().unwrap_or("result");

    let mut supported_mut_ref_param_targets = BTreeSet::new();

    // Extract parameters as variables, handling complex patterns
    let const_generic_len_names = function_const_generic_names(func);
    // Const-generic array length params modeled symbolically: each entry is
    // `(param_name, length_ident)`. We declare each distinct length ident as a
    // `usize` variable and bind `param@.len() == ident`, so a symbolic array
    // length `[T; N]` proves `ar@.len() == N` exactly as Verus does — without
    // assuming any concrete length (which would be unsound).
    let mut const_generic_array_bindings: Vec<(String, String)> = Vec::new();
    // Declared parameter types for the spec-eq compatibility rule (FAMILY D):
    // name -> (source type string, resolved TrustVcType). Same resolution as
    // the declarations below (registry aliases resolve; unknowns stay Opaque),
    // with upstream-transparent decorations (&, Box/Rc/Arc/Ghost/Tracked)
    // stripped before resolution so `Arc<Option<u64>>` classifies as the
    // datatype it decorates.
    let mut spec_eq_param_types: BTreeMap<String, (String, TrustVcType)> = BTreeMap::new();
    // INCREMENT 1: `Fn(A..) -> B`-bounded type parameters modeled as `SpecFn`
    // (deterministic, `Fn`-only; `FnMut`/`FnOnce` stay fail-closed). A value
    // parameter `f: F` whose type string is exactly such a type-param name is
    // typed as the mapped `SpecFn` value below. See
    // [`fn_bound_spec_fn_param_types`] for the soundness argument.
    let fn_bound_spec_fn_params = fn_bound_spec_fn_param_types(&func.sig, source_structs.as_ref());
    // The names this signature DECLARES as generic type parameters. A parameter
    // typed by exactly one of these is that type parameter, whatever its name's
    // shape — this is context-aware (unlike the context-free ≤2-char-uppercase
    // heuristic in `TrustVcType::parse_or_opaque`), so it never misclassifies a
    // concrete type as a type parameter yet still recognizes descriptively-named
    // generics (`Item`, `Key`) and desugared argument-position `impl Trait`
    // parameters (`__TrustVcAPIT0`). Fn-bounded params are still modeled as the
    // more-specific `SpecFn` above, so they take precedence over this fallback.
    let declared_type_params: BTreeSet<String> = func
        .sig
        .generics
        .type_params()
        .map(|param| param.ident.to_string())
        .collect();
    // INCREMENT 2a: the VALUE-parameter names `f` whose type is an `F: Fn(A) -> B`
    // bound modeled as a first-class `SpecFn` above (`fn_bound_spec_fn_params` is
    // keyed by the TYPE-parameter name `F`; this set is keyed by the value name `f`
    // the call site `f(a)` uses). Collected in the parameter loop below and threaded
    // to the body-assertion collector so the callee-side call-site obligation seam
    // (`emit_fn_bound_param_application_obligations`) fires ONLY for a genuine
    // Fn-bound parameter application `f(a)`, never a `closure!` literal or a ghost
    // `SpecFn<A,B>` value.
    let mut fn_bound_spec_fn_param_names: BTreeSet<String> = BTreeSet::new();
    for input in &func.sig.inputs {
        let erased_shared_ref_vars = param_extract::extract_erased_shared_ref_vars_from_input(
            input,
            &const_generic_len_names,
        )?
        .into_iter()
        .collect::<BTreeSet<_>>();
        let erased_ghost_vars = param_extract::extract_erased_ghost_vars_from_input(input)?
            .into_iter()
            .collect::<BTreeSet<_>>();
        supported_mut_ref_param_targets
            .extend(param_extract::extract_supported_mut_ref_scalar_vars_from_input(input)?);
        let const_array_len_resolver = |name: &str| {
            source_consts
                .as_ref()
                .and_then(|registry| registry.usize_const_len(name, &const_generic_len_names))
        };
        if let Some(binding) = param_extract::const_generic_array_length_binding(
            input,
            &const_array_len_resolver,
            &const_generic_len_names,
        ) {
            const_generic_array_bindings.push(binding);
        }
        for (var_name, var_type) in param_extract::extract_vars_from_input_resolving_array_lengths(
            input,
            &const_array_len_resolver,
            &const_generic_len_names,
        )? {
            let fn_bound_spec_fn_ty = fn_bound_spec_fn_params.get(var_type.trim()).cloned();
            if fn_bound_spec_fn_ty.is_some() {
                // INCREMENT 2a: record the VALUE-parameter name (`f`) so the
                // callee-side application seam can recognize `f(a)`.
                fn_bound_spec_fn_param_names.insert(var_name.clone());
            }
            let trust_vc_ty = fn_bound_spec_fn_ty
                .or_else(|| {
                    declared_type_params
                        .contains(var_type.trim())
                        .then(|| TrustVcType::TypeParam(var_type.trim().to_string()))
                })
                .or_else(|| {
                    source_structs
                        .as_ref()
                        .and_then(|registry| registry.resolve_type_string(&var_type))
                })
                .unwrap_or_else(|| TrustVcType::parse_or_opaque(&var_type));
            {
                // Spec-eq rule input: resolve the UNDECORATED source type so a
                // decorated declaration (`Arc<Option<u64>>`) classifies as its
                // decorated datatype, exactly as upstream `undecorate_typ`.
                let compact = var_type.replace(' ', "");
                let undecorated = undecorate_type_string(&compact).to_string();
                let resolved = source_structs
                    .as_ref()
                    .and_then(|registry| registry.resolve_type_string(&undecorated))
                    .unwrap_or_else(|| TrustVcType::parse_or_opaque(&undecorated));
                spec_eq_param_types.insert(var_name.clone(), (var_type.clone(), resolved));
            }
            // Vec/Seq length-boundedness: capture whether the ORIGIN syn type is
            // a `usize`-bounded exec collection (`Vec`/slice/array) HERE, from the
            // per-binding origin type string, BEFORE `parse_or_opaque` collapses
            // `Vec` and `Seq` alike to `TrustVcType::Seq`. A spec `Seq<T>` MUST
            // classify as unbounded (`false`) — see
            // `param_extract::syn_type_string_is_bounded_len_collection` for the
            // soundness boundary. `var_type` is the per-element origin spelling,
            // so tuple params classify each binding independently.
            let bounded_len = param_extract::syn_type_string_is_bounded_len_collection(&var_type);
            vc.declare_var_typed_bounded(&var_name, trust_vc_ty, bounded_len);
            if erased_shared_ref_vars.contains(&var_name) {
                vc.mark_erased_shared_ref_var(&var_name);
            }
            if erased_ghost_vars.contains(&var_name) {
                vc.mark_erased_ghost_var(&var_name);
            }
        }
    }
    // FAMILY D: spec `==`/`!=` between incompatible declared parameter types
    // in a contract clause — the upstream primary translation-time error
    // "mismatched types; types must be compatible to use == or !=".
    if let Some(err) = spec_eq_type_mismatch_error(func, &spec_eq_param_types) {
        return Err(err);
    }

    // Declare each referenced const-generic length param as a `usize` variable
    // and bind the modeled (symbolic) array view length to it. Declaring `N`
    // makes it available to specs/asserts (`ar@.len() == N`), and the binding
    // assumption ties the otherwise-free seq length to that parameter.
    let mut declared_const_generic_lens: BTreeSet<String> = BTreeSet::new();
    for (param_name, len_ident) in &const_generic_array_bindings {
        if declared_const_generic_lens.insert(len_ident.clone()) {
            // `usize` const-generic length; a free nonneg parameter (the usize
            // type already constrains it to `[0, usize::MAX]`).
            vc.declare_var_typed(
                len_ident,
                TrustVcType::Uint {
                    width: crate::ir::pointer_width(),
                },
            );
        }
        vc.push_obligation(ProofObligation::assume(
            format!("__const_generic_array_len_{param_name}"),
            // `.view().len()` is the engine-level spelling of the surface `@.len()`
            // (the `@` view sigil is desugared in the macro frontend, not here).
            format!("{param_name}.view().len() == {len_ident}"),
        ));
    }

    // Register source trait decls + impls when EITHER:
    //  (a) the verified function carries a trait bound (existing behavior — the
    //      generic-dispatch / unit-1 path needs the trait decl), OR
    //  (b) the file declares `#[trait_impl]` blocks AND the verified function is
    //      a genuine top-level/module free function (unit 2: a concrete-receiver
    //      caller such as `fn caller(s: S){ s.f(); }`).
    //
    // Case (b) is deliberately NARROW: it excludes trait-method bodies (trait
    // default bodies and impl-method bodies, which are synthesized via
    // `find_function`'s `Box::leak` and are NOT present as a top-level
    // `Item::Fn`). Registering the trait postcondition axiom while verifying
    // such a body flips its verdict from Counterexample to a fail-closed
    // `Unknown (quantifier-unhandled)` — see
    // `trait_default_returns_postcondition_rejects_wrong_body_from_file`. Gating
    // on `source_function_named_in_items` keeps that body on the unchanged path.
    let register_source_traits = force_source_trait_registration
        || file.is_some_and(|f| {
            !trait_contracts::trait_bounds_from_signature(&func.sig).is_empty()
                || (trait_contracts::file_declares_trait_impls(&f.items)
                    && trait_contracts::source_function_named_in_items(
                        &f.items,
                        &func.sig.ident.to_string(),
                    ))
        });
    if let Some(file) = file.filter(|_| register_source_traits) {
        trait_contracts::apply_source_trait_declarations(file, &mut vc)?;
    }

    // Add the postcondition return binding if function has a return type.
    let mut return_value_ty = None;
    match &func.sig.output {
        syn::ReturnType::Type(_, ty) => {
            let result_type = extract_type_name(ty);
            let result_ty = source_structs
                .as_ref()
                .and_then(|registry| registry.resolve_type_string(&result_type))
                .unwrap_or_else(|| TrustVcType::parse_or_opaque(&result_type));
            vc.declare_var_typed(result_var, result_ty.clone());
            if param_extract::is_erased_shared_ref_type(ty) {
                vc.mark_erased_shared_ref_var(result_var);
            }
            return_value_ty = Some(result_ty);
        }
        syn::ReturnType::Default if has_direct_returns_postcondition => {
            vc.declare_var_typed(result_var, TrustVcType::Unit);
            return_value_ty = Some(TrustVcType::Unit);
        }
        syn::ReturnType::Default => {}
    }

    trait_contracts::apply_function_trait_bounds(func, source_structs.as_ref(), &mut vc)?;
    if let Some(registry) = &source_consts {
        registry.apply_referenced_scalar_consts(func, &mut vc);
    }

    // Register sibling source-only spec functions referenced from contracts.
    let mut sibling_helper_contracts = BTreeMap::new();
    // Exact spec aliases admitted for THIS function body's outer lexical block.
    // Kept until body extraction so `reveal!`/`hide!` metadata can be rewritten
    // to the canonical body-axiom name without exposing aliases to attributes.
    let mut exact_spec_aliases = HashMap::new();
    // Per-call `&mut`-argument positions for every free function called in the
    // body (signature-derived; empty without a file). Drives the free-call
    // `&mut`-referent havoc that closes the dropped-mutation false `Verified`.
    let mut mut_ref_call_args = BTreeMap::new();
    if let Some(file) = file {
        validate_block_use_alias_resolution(
            file,
            func,
            source_identity_func,
            enclosing_inline_module.as_deref(),
            source_file_is_crate_root,
        )?;
        sibling_helper_contracts = collect_referenced_sibling_helper_contracts(file, func, &vc)?;
        mut_ref_call_args = collect_referenced_sibling_mut_ref_call_args(file, func);
        reject_helper_contract_calls_in_target_contracts(func, &sibling_helper_contracts)?;
        apply_when_used_as_spec_contract_functions(file, func, source_structs.as_ref(), &mut vc)?;
        apply_block_use_alias_helper_functions(file, func, source_structs.as_ref(), &mut vc)?;
        apply_sibling_helper_functions(
            file,
            func,
            source_structs.as_ref(),
            source_file_is_crate_root,
            &mut vc,
        )?;
        apply_inherent_impl_methods(file, func, source_structs.as_ref(), &mut vc)?;
        register_impl_method_self_receiver_kinds(&file.items, &mut vc);
        if let Some(registry) = &source_traits {
            registry.apply_referenced_associated_fns(func, source_structs.as_ref(), &mut vc);
        }
        // When the on-disk source path is known, additionally resolve spec
        // functions imported from sibling modules of the same crate
        // (`use crate::m::f;`); otherwise fall back to file-local specs only.
        let mut spec_catalog = match source_file {
            Some(path) => {
                crate::spec_function_catalog::SpecFunctionCatalog::from_file_with_crate_imports(
                    file, path,
                )
            }
            None => crate::spec_function_catalog::SpecFunctionCatalog::from_file(file),
        };
        spec_catalog.register_exact_aliases(&block_use_function_aliases(&func.block))?;
        exact_spec_aliases.extend(spec_catalog.exact_alias_targets().clone());
        spec_catalog.apply_referenced_specs(func, &mut vc)?;
        // Publish file-local `#[trust_vc::broadcast]` lemmas as grouped/global
        // BroadcastAssume axioms so `broadcast_use!{ group }` can activate them on
        // the file path (the runtime path publishes these by executing lemma
        // bodies). requires->guard folding is enforced inside. Grouped axioms are
        // gated FORWARD-ONLY by the body-ordered `broadcast_use!` markers via the
        // position-aware encoder gate. Part of the file-path broadcast_use! wiring.
        collect_source_broadcast_lemmas(file, &spec_catalog, &mut vc)?;
        apply_source_spec_recommends_in_target_contracts(
            file,
            func,
            source_structs.as_ref(),
            source_traits.as_ref(),
            &mut vc,
        )?;
        // Make free functions called inside impl-less trait DEFAULT-method bodies
        // resolvable to the impl-absent default-conformance pass. Without this a
        // default body `fn dm(&self) -> u32 { helper() }` cannot lower on the
        // conformance surface (the generic caller never references `helper`), the
        // conformance build Errs and is swallowed as fail-safe, and the
        // unjustified trait postcondition axiom is trusted unchecked — a false
        // `Verified`. Registers spec callees transparently (body axiom) and exec
        // callees as opaque UFs (fail closed). Part of the round-6 trait surface
        // fix (free-function-call-in-default-body residual of the #2442 class).
        trait_contracts::register_default_body_free_function_helpers(
            file,
            source_structs.as_ref(),
            &mut vc,
        )?;
    }

    // `default_ensures` is legal ONLY on a defaulted trait-method declaration;
    // on a free function (or any function verified directly) it is ill-formed
    // and must fail CLOSED rather than be silently ignored by the attribute
    // extraction below. (`test_disallow_default_ensures3`.)
    crate::extern_spec_helpers::forbid_default_ensures(&func.attrs)?;

    // Extract requires/ensures from attributes
    attr_extract::extract_contract_attributes(
        &func.attrs,
        &mut vc,
        function_solver_mode,
        Some(&func.sig),
    )?;
    if let Some(file) = file {
        trait_contracts::apply_inherited_trait_method_contracts(
            file,
            func,
            &mut vc,
            function_solver_mode,
        )?;
    }

    // Build caller-side trait-bounded method-call `requires` contracts. Clone
    // the `TraitBound`/`TraitDecl` data out of `vc` first so the borrow ends
    // before the `&mut vc` body-extract borrow below (unit 1 of the
    // trait-`requires` discharge). Methods without a `requires` produce no
    // entry (fail-closed scope).
    let trait_bounds_owned: Vec<crate::ir::TraitBound> = vc
        .function_context()
        .map(|fc| fc.trait_bounds().to_vec())
        .unwrap_or_default();
    let trait_decls_owned: Vec<crate::ir::TraitDecl> = vc.trait_decls().to_vec();
    let trait_method_call_contracts =
        trait_contracts::trait_bound_method_requires(&trait_bounds_owned, &trait_decls_owned);

    // Build caller-side CONCRETE-receiver trait-method `requires` contracts
    // (unit 2): `s.f(args)` where `s: S` and `impl T for S`. Clone the impl
    // decls out of `vc` first (same borrow discipline as above). Keyed by the
    // concrete type name; empty when no requires-bearing concrete impl exists.
    let trait_impl_decls_owned: Vec<crate::ir::TraitImplDecl> = vc.trait_impl_decls().to_vec();
    let mut concrete_method_call_contracts =
        trait_contracts::concrete_impl_method_requires(&trait_impl_decls_owned, &trait_decls_owned);

    // Build caller-side INHERENT (non-trait) method `requires` contracts (unit
    // 3): `x.m(args)` where `x: S` and `impl S { #[requires(..)] fn m(&self) }`.
    // Inherent impls never enter `trait_impl_decls` (they hard-error in
    // `parse_trait_impl_decl`), so this is built directly from `file.items`,
    // INDEPENDENT of the trait-registration gate. Both maps are keyed by the
    // same `to_type_string()` and consumed by the same `other =>` concrete
    // dispatch arm, so they MERGE into `concrete_method_call_contracts` (zero
    // body_extract change). COLLISION HANDLING (an inherent `(S, m)` key
    // colliding with a concrete-trait `(S, m)` — a method that is somehow both
    // inherent and trait-supplied): DROP the key entirely (remove the existing
    // concrete entry, skip the inherent one) so NEITHER fires. A missed
    // obligation is always sound; emitting either member's `requires` risks
    // attributing the wrong contract — never emit a wrong `requires`.
    if let Some(file) = file {
        let inherent_method_call_contracts =
            trait_contracts::inherent_impl_method_requires(&file.items)?;
        for (key, contract) in inherent_method_call_contracts {
            if concrete_method_call_contracts.contains_key(&key) {
                // Ambiguous (S, m): a concrete-trait entry already owns this
                // key. Drop both so neither contributes a (possibly wrong)
                // obligation.
                concrete_method_call_contracts.remove(&key);
                continue;
            }
            concrete_method_call_contracts.insert(key, contract);
        }
    }

    // Extract assertions from function body
    let mut_ref_post_state = if sibling_helper_contracts.is_empty()
        && trait_method_call_contracts.is_empty()
        && concrete_method_call_contracts.is_empty()
    {
        body_extract::extract_body_assertions_with_mut_ref_param_targets(
            &func.block,
            &mut vc,
            function_solver_mode,
            &supported_mut_ref_param_targets,
            &mut_ref_call_args,
            &fn_bound_spec_fn_param_names,
        )?
    } else {
        let helper_contracts =
            (!sibling_helper_contracts.is_empty()).then_some(&sibling_helper_contracts);
        let trait_method_contracts =
            (!trait_method_call_contracts.is_empty()).then_some(&trait_method_call_contracts);
        let concrete_method_contracts =
            (!concrete_method_call_contracts.is_empty()).then_some(&concrete_method_call_contracts);
        body_extract::extract_body_assertions_with_helper_and_trait_method_contracts(
            &func.block,
            &mut vc,
            function_solver_mode,
            helper_contracts,
            trait_method_contracts,
            concrete_method_contracts,
            &supported_mut_ref_param_targets,
            &mut_ref_call_args,
            &fn_bound_spec_fn_param_names,
        )?
    };

    canonicalize_visibility_aliases(&mut vc, &exact_spec_aliases);

    // Two-state fix for scalar `&mut` parameters: a *bare* `&mut` parameter in a
    // postcondition denotes its FINAL (post-body) value (Verus semantics +
    // `design-new-mut-ref.md`), not the entry snapshot. The string-model
    // body extraction above already computed the final value; rewrite the
    // postcondition obligations onto it, failing closed where the final value is
    // uncertain. MUST run before the return-value binding below so a `&mut` param
    // referenced alongside `result` is resolved consistently.
    apply_mut_ref_final_state_to_postconditions(
        &mut vc,
        &supported_mut_ref_param_targets,
        &mut_ref_post_state,
    )?;

    // Classic-old expressiveness (slice A of the mut-ref two-state keystone):
    // `old(P)` / `*old(P)` in `requires` ALSO denotes the ENTRY value —
    // identical to bare `P` in requires, which is already live — but must
    // PARSE to the entry symbol rather than error, so callee contracts like
    // `requires(*old(a) < 10)` (upstream refs.rs `add1`) are expressible.
    apply_mut_ref_old_state_to_preconditions(&mut vc, &supported_mut_ref_param_targets)?;

    // Straight-line sibling of the catastrophic loop collection-mutation gap: a
    // `&mut Vec`/`&mut HashMap`/… parameter is NOT a `supported_mut_ref` scalar,
    // so the two-state final-value rewrite above never runs for it and a bare
    // occurrence in a postcondition resolves to the ENTRY snapshot. When such a
    // parameter is mutated in place by a method call (`clear`/`push`/`retain`/
    // `drain`/`extend`/`sort`/…), its FINAL value is not threaded into the
    // model, so checking the postcondition against the pre-call snapshot would
    // be a false `Verified`. Fail closed instead. By-value `mut v: Vec` params
    // are NOT references, so their entry-value postcondition (Verus-faithful for
    // an owned parameter) is untouched.
    reject_mut_ref_collection_method_mutation_postconditions(&vc, func)?;

    // User-struct sibling of the straight-line `&mut`-collection postcondition
    // gap: a bare `&mut S` struct/enum parameter in a postcondition resolves to
    // its ENTRY snapshot, but a `&mut self` (or unresolved non-pure) method call
    // mutates it in place without threading the FINAL value, so checking the
    // postcondition against the pre-call state would be a false `Verified`. Fail
    // closed. A pure `&self`/by-value reader is never flagged (NO over-rejection);
    // by-value `mut s: S` params keep their Verus-faithful entry-value semantics.
    reject_mut_ref_struct_method_mutation_postconditions(&vc, func)?;

    // Direct-write sibling of the two method-mutation rejects above: a non-scalar
    // `&mut` parameter (struct/enum/collection/array) mutated by a DIRECT place
    // write (`P.field = …`, `P[i] = …`, `*P = …`, compound + nested forms) or
    // whose `&mut` reference is REBORROWED (`let r = &mut *P; r.push(..)`) has a
    // FINAL value the postcondition rewrite does not thread (the bare parameter
    // still reads its ENTRY snapshot). The body model reflects the write for
    // in-body reads, but a postcondition over the parameter would be checked
    // against the pre-write state — a false `Verified`. Fail closed (P0-A).
    reject_mut_ref_param_place_mutation_postconditions(&vc, func)?;

    // Connect function body return value to result variable
    if !matches!(func.sig.output, syn::ReturnType::Default) || has_direct_returns_postcondition {
        let allow_unit_bare_return = matches!(return_value_ty, Some(TrustVcType::Unit));
        let loop_return_params = function_parameter_idents(&func.sig.inputs);
        match classify_return_expression(&func.block, allow_unit_bare_return, &loop_return_params) {
            return_extract::ReturnExtraction::Single(return_value) => {
                let return_str =
                    scoped_return_value_expression(&func.block, return_value, &vc.struct_types);
                // For a `match`-returning body, the canonical return value is an
                // `ite` over a datatype discriminant. Binding `result` to it with
                // an opaque `result == match …` ASSUME poisons the solver's
                // SAT-model search when the arms contain Seq-/datatype-valued
                // uninterpreted-fn leaves (e.g. the REAL `eval_constraint`:
                // `match c.rel { Ge => eval_terms(t,a) >= rhs, Eq => … }`): the
                // solver returns Unknown instead of a counterexample, so a
                // deliberately-WRONG arm (`>` for `>=`) cannot be refuted with a
                // witness — defeating the non-vacuity control. INLINE the return
                // value into the obligations that reference `result` and drop the
                // assume so the postcondition becomes the self-contained,
                // decidable goal `match_body == match_spec` (the same shape a
                // proof-fn `assert!` already produces). This is sound — `result`
                // IS the return expression — and only the assume is removed once
                // `result` no longer occurs anywhere. Non-match returns keep the
                // established assume path byte-for-byte.
                let inlined = (return_value_is_match(return_value)
                    || return_value_is_seq_quantifier(return_value))
                    && inline_result_binding(&mut vc, result_var, &return_str);
                if !inlined {
                    // Add an assumption that the return binding equals the return
                    // expression. This is only sound when VC extraction proved
                    // there is exactly one canonical return value for the body.
                    // Parenthesize the return expression ONLY when its tail is a
                    // comparison/logical binary, so a lower-precedence body tail
                    // (`a <= b && c`) binds inside the `==`. Without the parens
                    // `result == value <= floor && vig_all(..)` parses as the
                    // illegal chained comparison `result == value <= floor`
                    // ("comparison operators cannot be chained") — exactly the
                    // shape of the real `optimum_upgrade_guard` body. The guard
                    // keeps every non-chaining return (`result == false`,
                    // `result == foo()`, `result == ()`) byte-identical.
                    let condition = if return_value_tail_is_chainable_binary(return_value) {
                        format!("{result_var} == ({return_str})")
                    } else {
                        format!("{result_var} == {return_str}")
                    };
                    // When the return expression reads a loop-MODIFIED variable
                    // (`fn f(n){ let mut i=0; while i<n { invariant!(i<=n); i+=1 } i }`),
                    // bind `result` as a POST-LOOP assume: a `PostLoopAssume` is
                    // exempt from the post-loop pre-state rewrite (setup.rs), so
                    // `result` binds to the POST-loop `i` (constrained by inv ∧
                    // ¬guard), not the pre-loop `i__pre` — closing the let-local
                    // returned-as-result over-rejection AND preventing the dual
                    // false-verify (a plain assume rewrites to `result == i__pre`,
                    // which could satisfy an `ensures(result == <entry value>)`).
                    // Every OTHER return (non-loop function, or a return that reads
                    // no loop-modified var) keeps the plain assume byte-identical —
                    // PostLoopAssume would otherwise change the obligation kind for
                    // returns that do not need the exemption.
                    let returns_loop_modified = vc
                        .loop_modified_vars()
                        .values()
                        .flatten()
                        .any(|var| condition_references_word(&return_str, var));
                    let mut obligation = if returns_loop_modified {
                        ProofObligation::post_loop_assume("return_value", condition)
                    } else {
                        ProofObligation::assume("return_value", condition)
                    };
                    if let Some(mode) = function_solver_mode {
                        obligation = obligation.with_solver_mode(mode);
                    }
                    vc.push_obligation(obligation);
                }
            }
            return_extract::ReturnExtraction::Multiple(return_exprs) => {
                // Nested explicit returns are modeled as a conservative set of
                // possible return values. This over-approximates path-sensitive
                // control flow, so it may reject valid programs, but it cannot
                // prove a postcondition that fails for one of these values.
                let clauses = return_exprs
                    .iter()
                    .map(|return_value| {
                        let return_str = scoped_return_value_expression(
                            &func.block,
                            *return_value,
                            &vc.struct_types,
                        );
                        format!("({result_var} == {return_str})")
                    })
                    .collect::<Vec<_>>();
                let mut obligation = ProofObligation::assume("return_value", clauses.join(" || "));
                if let Some(mode) = function_solver_mode {
                    obligation = obligation.with_solver_mode(mode);
                }
                vc.push_obligation(obligation);
            }
            return_extract::ReturnExtraction::Missing => {
                // Fail-closed: a return type with no detectable return expression
                // leaves the return binding unconstrained. Postconditions
                // referencing it would be trivially satisfiable (unsound).
                // Return an error so the caller knows the VC is incomplete. #2251.
                return Err(TrustVcError::Internal {
                    context: "extract verification conditions",
                    detail: format!(
                        "Function '{}' has return type but no detectable return expression — \
                         postconditions referencing `{}` would be unsound",
                        func.sig.ident, result_var
                    ),
                });
            }
            return_extract::ReturnExtraction::Ambiguous(reason) => {
                return Err(TrustVcError::Internal {
                    context: "extract verification conditions",
                    detail: format!(
                        "Function '{}' has ambiguous multi-path return extraction ({reason}) — \
                         postconditions referencing `{}` would be unsound",
                        func.sig.ident, result_var
                    ),
                });
            }
        }
    }

    // Resolve struct-name PARAMETER types in trait method signatures before
    // verification. A single-uppercase struct name in a trait method parameter
    // (`fn merge(&self, o: Other)`) is classified `TypeParam("Other")` at
    // macro-expand time (no struct registry there) — the SAME heuristic that gave
    // the self type `TypeParam("S")` before 2a53711. Unresolved, that param is not
    // `is_concrete_boxable_type`, so the concrete-receiver UF path skips the method
    // ("unsupported method") and the synthesized context's function registration
    // rejects it ("Unsupported param type"). Resolving it to the registered
    // struct's `Datatype` here — while `vc` is still owned mutably and every trait
    // + struct is registered — makes ALL downstream consumers (`build_type_env`,
    // `synthesize_impl_method_contexts`, and the encoder's `register_trait`, which
    // all read `vc.trait_decls`) see one ay-encodable param sort. Mirrors
    // `resolve_trait_impl_concrete_types` for the self type. Return types are left
    // alone (a non-primitive return is routed through the definitional body axiom,
    // not the UF path). A genuine blanket type param (not a registered struct)
    // matches nothing and stays unchanged, fail-closed.
    resolve_trait_decl_param_types(&mut vc);

    Ok(vc)
}

/// Resolves each trait method PARAMETER whose type is a struct-name
/// `TypeParam`/`Opaque` to the registered struct's `Datatype`. See the call site
/// in `extract_verification_conditions_from_parts_inner` for the rationale.
fn resolve_trait_decl_param_types(vc: &mut VerificationContext) {
    if vc.trait_decls.is_empty() || vc.struct_types.is_empty() {
        return;
    }
    let struct_types = vc.struct_types.clone();
    let resolve = |ty: &crate::ir::TrustVcType| -> crate::ir::TrustVcType {
        use crate::ir::TrustVcType;
        let (TrustVcType::Opaque(name) | TrustVcType::TypeParam(name)) = ty else {
            return ty.clone();
        };
        let Some(struct_def) = struct_types.iter().find(|def| &def.name == name) else {
            return ty.clone();
        };
        let datatype = struct_def.to_datatype_type();
        // Only a fully-concrete datatype (no opaque field) has an ay sort; a
        // partially-opaque one must stay unresolved and fail closed.
        if datatype.contains_opaque() {
            return ty.clone();
        }
        datatype
    };
    for decl in &mut vc.trait_decls {
        for method in &mut decl.methods {
            for (_, ty) in &mut method.params {
                *ty = resolve(ty);
            }
        }
    }
}

/// Rewrites postcondition obligations so a *bare* scalar `&mut` parameter `P`
/// (or `*P`) denotes its FINAL (post-body) value, the two-state semantics Verus
/// and `design-new-mut-ref.md` mandate. Without this, the string body model
/// resolves `P` to the entry-snapshot variable, so a postcondition is checked
/// against the PRE-call state — a catastrophic false `Verified` for any clause a
/// body mutation falsifies.
///
/// Soundness contract (must never produce a false `Verified` on a `&mut`
/// postcondition):
/// - When `P` is cleanly tracked to the single fall-through exit, substitute its
///   exact final value. (Sound + complete.)
/// - When the body has an early `return`/`?`, the fall-through value need not
///   hold on every exit path → fail closed.
/// - When `P`'s reference escapes (passed to a call/method, aliased, reborrowed),
///   its referent may be mutated outside the tracked value → fail closed.
/// - When `P` is referenced but not soundly resolvable: it is safe to keep the
///   entry value ONLY if `P` is neither mutated nor escaped in the body (so
///   entry == final — e.g. a pure `*P` read); otherwise its final value is
///   uncertain (havoc through a branch/loop join) → fail closed.
/// - When a quantifier/closure body in the postcondition references `P`, the
///   rewriter cannot safely substitute under a binder → fail closed.
///
/// Only scalar `&mut` *reference* params (`supported_mut_ref_params`) are
/// affected; by-value `mut x: T` params keep their entry-value postcondition
/// semantics (also Verus-faithful) untouched.
fn apply_mut_ref_final_state_to_postconditions(
    vc: &mut VerificationContext,
    supported_mut_ref_params: &BTreeSet<String>,
    post_state: &body_extract::MutRefPostState,
) -> TrustVcResult<()> {
    if supported_mut_ref_params.is_empty() {
        return Ok(());
    }

    let mut pending: Vec<(usize, String)> = Vec::new();
    for (index, obligation) in vc.obligations.iter().enumerate() {
        if obligation.kind != ObligationKind::Assert || obligation.name != "postcondition" {
            continue;
        }
        // Typed obligations carry their condition as a lowered IR expression, not
        // a re-parseable string; the string body model never produces them, so
        // leave them untouched.
        if obligation.typed_expr.is_some() {
            continue;
        }

        let outcome = rewrite_mut_ref_postcondition(
            &obligation.condition,
            supported_mut_ref_params,
            &post_state.clean_finals,
        )?;

        if outcome.closure_mentions_param {
            return Err(mut_ref_two_state_error(
                &obligation.condition,
                "a quantifier/closure body references a `&mut` parameter",
            ));
        }
        if outcome.referenced_params.is_empty() && outcome.old_referenced_params.is_empty() {
            continue;
        }
        // Validate, per referenced `&mut` param, that its post-body value can be
        // resolved soundly. A param is soundly resolved to its FINAL value iff it
        // is cleanly tracked to the exit (`clean_finals`), its reference never
        // escaped (so no untracked call/alias mutation), and the body has no early
        // exit (so the fall-through value is the only exit value).
        //
        // THE TWO-STATE SPLIT: this validation applies ONLY to params referenced
        // BARE (`P` / `*P` — FINAL semantics, `outcome.referenced_params`; the
        // substituted value must hold on every exit path). A param referenced
        // only via `old(P)` (`outcome.old_referenced_params`) needs NO
        // validation: it was rewritten to the ENTRY symbol, whose value is
        // path-independent — early exits, escapes and branch havocs change the
        // FINAL value, never the entry snapshot. Validating old-only refs would
        // be sound but needlessly incomplete (`ensures(old(x) < 100)` on an
        // early-exit body must not fail closed); skipping validation for bare
        // refs would be the catastrophic false-`Verified` this resolver exists
        // to prevent. A param referenced BOTH ways keeps the validation for its
        // bare (final-semantics) occurrences.
        for name in &outcome.referenced_params {
            let soundly_resolved = post_state.clean_finals.contains_key(name)
                && !post_state.escapes_in_body.contains(name)
                && !post_state.has_early_exit;
            if soundly_resolved {
                continue;
            }
            // Not soundly resolvable to a final value. Reading the entry value is
            // sound ONLY if the parameter is neither mutated nor escaped, so that
            // entry == final on every path (e.g. a pure `*P` read). Otherwise its
            // final value is uncertain and we fail closed.
            let mutated = post_state.mutated_in_body.contains(name);
            let escaped = post_state.escapes_in_body.contains(name);
            if mutated || escaped {
                let reason = if escaped {
                    "the parameter's reference escapes the body (passed to a \
                     call/method, aliased, or reborrowed), so its referent may be \
                     mutated outside the tracked value"
                } else if post_state.has_early_exit {
                    "the body has an early `return`/`?`, so a mutated parameter's \
                     fall-through final value need not hold on every exit path"
                } else {
                    "the parameter is mutated but its final value is uncertain \
                     (havoced by a branch/loop join)"
                };
                return Err(mut_ref_two_state_error(&obligation.condition, reason));
            }
            // Otherwise: `name` is never mutated and never escapes, hence is
            // unchanged by the body, so its bare occurrence is its entry value ==
            // final value — sound to leave as-is (the substituter left it
            // untouched because it had no clean final value).
        }
        pending.push((index, outcome.rewritten));
    }

    for (index, rewritten) in pending {
        vc.obligations[index].condition = rewritten;
    }
    Ok(())
}

/// Rewrites `old(P)` / `*old(P)` in `requires` (precondition) obligations to
/// the ENTRY symbol `P` for scalar `&mut` parameters.
///
/// In a precondition the declared parameter variable IS the entry value (bare
/// `P` in `requires` already reads entry state; Verus's "in requires, use
/// `old(a)`" diagnostic for bare `&mut` mentions is a future slice), so
/// `old(P)` and bare `P` coincide here — `old(P)` must parse to the same
/// symbol rather than error. No final-value substitution is performed
/// (`finals` = ∅) and, unlike the postcondition pass, no per-param resolution
/// validation is needed: entry values are path-independent.
///
/// Fail-closed boundaries: `old()` over a non-`&mut` param or over anything
/// but a bare parameter path is a hard error (silently reading the current
/// value would over-prove); an `old(P)` under a quantifier/closure binder is
/// never rewritten (the visitor does not descend under binders) and stays
/// fail-closed downstream at encoding. A closure merely *mentioning* a `&mut`
/// param is NOT an error here — with no substitution possible, bare `P` under
/// a requires-binder keeps its already-live entry semantics.
fn apply_mut_ref_old_state_to_preconditions(
    vc: &mut VerificationContext,
    supported_mut_ref_params: &BTreeSet<String>,
) -> TrustVcResult<()> {
    if supported_mut_ref_params.is_empty() {
        return Ok(());
    }

    let no_finals = BTreeMap::new();
    let mut pending: Vec<(usize, String)> = Vec::new();
    for (index, obligation) in vc.obligations.iter().enumerate() {
        if obligation.kind != ObligationKind::Assume || obligation.name != "precondition" {
            continue;
        }
        // Typed obligations carry a lowered IR expression, not a re-parseable
        // string — same skip as the postcondition pass.
        if obligation.typed_expr.is_some() {
            continue;
        }
        // Cheap token pre-filter: only re-parse (and possibly re-stringify)
        // conditions that can contain an `old(..)` form, so unrelated
        // preconditions never drift in formatting.
        if !condition_mentions_ident(&obligation.condition, "old") {
            continue;
        }

        let outcome = rewrite_mut_ref_postcondition(
            &obligation.condition,
            supported_mut_ref_params,
            &no_finals,
        )
        .map_err(|err| match err {
            TrustVcError::Encoding { detail, .. } => TrustVcError::Encoding {
                context: "resolve `&mut` parameter precondition `old()` entry state",
                detail,
            },
            other => other,
        })?;
        if outcome.old_referenced_params.is_empty() {
            continue;
        }
        pending.push((index, outcome.rewritten));
    }

    for (index, rewritten) in pending {
        vc.obligations[index].condition = rewritten;
    }
    Ok(())
}

fn mut_ref_two_state_error(condition: &str, reason: &str) -> TrustVcError {
    TrustVcError::Encoding {
        context: "resolve `&mut` parameter two-state postcondition",
        detail: format!(
            "Postcondition `{condition}` reads a scalar `&mut` parameter whose \
             FINAL value cannot be soundly resolved: {reason}. A bare `&mut` \
             parameter in a postcondition denotes its post-body value (Verus \
             two-state semantics); this shape is rejected rather than risk \
             checking the postcondition against the pre-call state.",
        ),
    }
}

/// Fail closed when a postcondition reads a `&mut <collection>` parameter
/// (`Vec`/`[T]`/`HashSet`/`HashMap`/…, modeled as `Seq`/`Set`/`Map`/`Multiset`)
/// that is mutated in place by a method call in the body.
///
/// Such a parameter is NOT a `supported_mut_ref` scalar, so the two-state final
/// value rewrite never ran for it: a bare occurrence in the postcondition still
/// resolves to the ENTRY-snapshot variable. A method mutation (`clear`/`push`/
/// `retain`/`drain`/`extend`/`sort`/…) is not threaded into that snapshot, so
/// the postcondition would be checked against the pre-call state — a false
/// `Verified`. We reject the function rather than risk that. Owned (by-value)
/// `mut v: Vec` parameters are not `&mut` references, so their entry-value
/// postconditions (Verus-faithful for an owned parameter) are left untouched.
fn reject_mut_ref_collection_method_mutation_postconditions(
    vc: &VerificationContext,
    func: &ItemFn,
) -> TrustVcResult<()> {
    let mut_ref_collection_params: BTreeSet<String> = func
        .sig
        .inputs
        .iter()
        .filter_map(param_extract::extract_mut_ref_var_from_input)
        .filter(|name| {
            matches!(
                vc.get_variable_type(name),
                Some(
                    TrustVcType::Set(_)
                        | TrustVcType::Seq(_)
                        | TrustVcType::Map(_, _)
                        | TrustVcType::Multiset(_)
                )
            )
        })
        .collect();
    if mut_ref_collection_params.is_empty() {
        return Ok(());
    }

    let method_mutated = body_extract::mut_ref_collection_params_method_mutated_in_body(
        &func.block,
        &mut_ref_collection_params,
    );
    if method_mutated.is_empty() {
        return Ok(());
    }

    for obligation in &vc.obligations {
        if obligation.kind != ObligationKind::Assert || obligation.name != "postcondition" {
            continue;
        }
        for name in &method_mutated {
            if condition_mentions_ident(&obligation.condition, name) {
                return Err(mut_ref_collection_two_state_error(
                    &obligation.condition,
                    name,
                ));
            }
        }
    }
    Ok(())
}

/// Fail closed when a `&mut S` struct/enum parameter that is mutated in place by
/// a `&mut self` (or unresolved non-pure) method call is read in a postcondition.
/// The user-struct sibling of `reject_mut_ref_collection_method_mutation_postconditions`:
/// the bare `&mut S` parameter resolves to its ENTRY snapshot and the method's
/// post-state effect is not threaded, so checking the postcondition against the
/// pre-call state would be unsound (a false `Verified`).
fn reject_mut_ref_struct_method_mutation_postconditions(
    vc: &VerificationContext,
    func: &ItemFn,
) -> TrustVcResult<()> {
    let param_struct_types: BTreeMap<String, String> = func
        .sig
        .inputs
        .iter()
        .filter_map(param_extract::extract_mut_ref_var_from_input)
        .filter_map(|name| match vc.get_variable_type(&name) {
            Some(TrustVcType::Datatype { name: ty, .. }) => Some((name, ty.clone())),
            _ => None,
        })
        .collect();
    if param_struct_types.is_empty() {
        return Ok(());
    }

    let kinds = vc.struct_self_receiver_kinds_clone();
    let method_mutated = body_extract::mut_ref_struct_params_method_mutated_in_body(
        &func.block,
        &param_struct_types,
        &kinds,
        &vc.struct_types,
    );
    if method_mutated.is_empty() {
        return Ok(());
    }

    for obligation in &vc.obligations {
        if obligation.kind != ObligationKind::Assert || obligation.name != "postcondition" {
            continue;
        }
        for name in &method_mutated {
            if condition_mentions_ident(&obligation.condition, name) {
                return Err(mut_ref_struct_two_state_error(&obligation.condition, name));
            }
        }
    }
    Ok(())
}

/// Fail closed when a postcondition reads a non-scalar `&mut` parameter
/// (struct/enum/collection/array) that is mutated by a DIRECT place write
/// (`P.field = …`, `P[i] = …`, `*P = …`, compound + nested forms) or whose `&mut`
/// reference is reborrowed (`let r = &mut *P; r.push(..)`). The direct-write
/// sibling of the two method-mutation rejects: such a parameter resolves to its
/// ENTRY snapshot in a postcondition (it is not a `supported_mut_ref` scalar, so
/// the two-state final-value rewrite never runs), and the post-body final value
/// is not threaded into that snapshot — so checking the postcondition against the
/// pre-write state would be a false `Verified` (P0-A). Scalar `&mut` params
/// (handled by the two-state rewrite) are excluded.
fn reject_mut_ref_param_place_mutation_postconditions(
    vc: &VerificationContext,
    func: &ItemFn,
) -> TrustVcResult<()> {
    let non_scalar_mut_ref_params: BTreeSet<String> = func
        .sig
        .inputs
        .iter()
        .filter_map(param_extract::extract_mut_ref_var_from_input)
        .filter(|name| {
            matches!(
                vc.get_variable_type(name),
                Some(
                    TrustVcType::Datatype { .. }
                        | TrustVcType::Set(_)
                        | TrustVcType::Seq(_)
                        | TrustVcType::Map(_, _)
                        | TrustVcType::Multiset(_)
                        | TrustVcType::Array(_, _)
                )
            )
        })
        .collect();
    if non_scalar_mut_ref_params.is_empty() {
        return Ok(());
    }

    let mutated = body_extract::mut_ref_params_place_mutated_or_reborrowed_in_body(
        &func.block,
        &non_scalar_mut_ref_params,
    );
    if mutated.is_empty() {
        return Ok(());
    }

    for obligation in &vc.obligations {
        if obligation.kind != ObligationKind::Assert || obligation.name != "postcondition" {
            continue;
        }
        for name in &mutated {
            if condition_mentions_ident(&obligation.condition, name) {
                return Err(mut_ref_place_mutation_two_state_error(
                    &obligation.condition,
                    name,
                ));
            }
        }
    }
    Ok(())
}

fn mut_ref_place_mutation_two_state_error(condition: &str, name: &str) -> TrustVcError {
    TrustVcError::Encoding {
        context: "resolve `&mut` parameter two-state postcondition",
        detail: format!(
            "Postcondition `{condition}` reads `&mut` parameter `{name}`, which is \
             mutated by a direct field/index/deref write (e.g. `{name}.f = ..`, \
             `{name}[i] = ..`) or whose reference is reborrowed (`&mut *{name}`) in \
             the body. A bare `&mut` parameter in a postcondition denotes its \
             post-body (FINAL) value (Verus two-state semantics), but the body model \
             does not thread that final value into the entry snapshot the \
             postcondition reads; checking it against the pre-write state would be \
             unsound, so this shape is rejected (fail closed) rather than risk a \
             false `Verified`.",
        ),
    }
}

fn mut_ref_struct_two_state_error(condition: &str, name: &str) -> TrustVcError {
    TrustVcError::Encoding {
        context: "resolve `&mut` struct parameter two-state postcondition",
        detail: format!(
            "Postcondition `{condition}` reads `&mut` struct/enum parameter `{name}`, \
             which is mutated in place by a `&mut self` (or unresolved) method call \
             in the body (e.g. `{name}.bump()`). A bare `&mut` parameter in a \
             postcondition denotes its post-body (FINAL) value (Verus two-state \
             semantics), but the struct body model does not thread that final value \
             through the method call; checking the postcondition against the \
             pre-call snapshot would be unsound, so this shape is rejected (fail \
             closed) rather than risk a false `Verified`.",
        ),
    }
}

fn mut_ref_collection_two_state_error(condition: &str, name: &str) -> TrustVcError {
    TrustVcError::Encoding {
        context: "resolve `&mut` collection parameter two-state postcondition",
        detail: format!(
            "Postcondition `{condition}` reads `&mut` collection parameter `{name}`, \
             which is mutated in place by a method call in the body (e.g. \
             `clear`/`push`/`retain`/`drain`/`extend`/`sort`). A bare `&mut` \
             parameter in a postcondition denotes its post-body (FINAL) value \
             (Verus two-state semantics), but the collection body model does not \
             thread that final value; checking the postcondition against the \
             pre-call snapshot would be unsound, so this shape is rejected (fail \
             closed) rather than risk a false `Verified`.",
        ),
    }
}

/// Result of rewriting a single postcondition's `&mut`-parameter references.
struct MutRefRewriteOutcome {
    /// The condition string after substituting cleanly-resolved `&mut` params.
    rewritten: String,
    /// `&mut` scalar params referenced (bare `P` or `*P`) outside any closure.
    /// FINAL-value semantics — the caller's per-param resolution validation
    /// applies to exactly this set.
    referenced_params: BTreeSet<String>,
    /// `&mut` scalar params referenced via `old(P)` / `*old(P)` outside any
    /// closure. ENTRY-value semantics — rewritten to the declared param symbol,
    /// which is path-independent, so these need NO resolution validation.
    old_referenced_params: BTreeSet<String>,
    /// A closure (quantifier) body mentions a `&mut` param — fail-closed shape.
    closure_mentions_param: bool,
}

fn rewrite_mut_ref_postcondition(
    condition: &str,
    mut_ref_params: &BTreeSet<String>,
    finals: &BTreeMap<String, String>,
) -> TrustVcResult<MutRefRewriteOutcome> {
    // Conditions originate from `quote!(#expr)`, so they re-parse as an `Expr`.
    // A parse failure here would mean we cannot reason about whether a `&mut`
    // param is referenced; fail closed by reporting every textually-present param
    // as referenced (the caller then resolves or rejects each).
    let mut expr: Expr = match syn::parse_str(condition) {
        Ok(expr) => expr,
        Err(_) => {
            let referenced_params = mut_ref_params
                .iter()
                .filter(|name| condition_mentions_ident(condition, name))
                .cloned()
                .collect();
            return Ok(MutRefRewriteOutcome {
                rewritten: condition.to_string(),
                referenced_params,
                old_referenced_params: BTreeSet::new(),
                closure_mentions_param: false,
            });
        }
    };

    let mut substituter = FinalValueSubstituter {
        mut_ref_params,
        finals,
        referenced_params: BTreeSet::new(),
        old_referenced_params: BTreeSet::new(),
        closure_mentions_param: false,
        parse_error: None,
    };
    substituter.visit_expr_mut(&mut expr);

    if let Some(detail) = substituter.parse_error {
        return Err(TrustVcError::Encoding {
            context: "resolve `&mut` parameter two-state postcondition",
            detail,
        });
    }

    let referenced_params = substituter.referenced_params;
    let old_referenced_params = substituter.old_referenced_params;
    let closure_mentions_param = substituter.closure_mentions_param;
    // Re-stringify only when a `&mut` param was actually referenced (and thus the
    // expression may have been substituted); otherwise preserve the exact
    // original string so unrelated postconditions never drift in formatting.
    let rewritten = if referenced_params.is_empty() && old_referenced_params.is_empty() {
        condition.to_string()
    } else {
        quote!(#expr).to_string()
    };
    Ok(MutRefRewriteOutcome {
        rewritten,
        referenced_params,
        old_referenced_params,
        closure_mentions_param,
    })
}

/// True when `ident` appears as a whole-word identifier token in `condition`.
fn condition_mentions_ident(condition: &str, ident: &str) -> bool {
    condition
        .split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .any(|tok| tok == ident)
}

struct FinalValueSubstituter<'a> {
    mut_ref_params: &'a BTreeSet<String>,
    finals: &'a BTreeMap<String, String>,
    /// Every `&mut` scalar param referenced (bare `P` or `*P`) outside a closure.
    referenced_params: BTreeSet<String>,
    /// Every `&mut` scalar param referenced via `old(P)` / `*old(P)` outside a
    /// closure. These were rewritten to the ENTRY symbol (the declared param
    /// var) — never final-substituted.
    old_referenced_params: BTreeSet<String>,
    closure_mentions_param: bool,
    parse_error: Option<String>,
}

/// Shape of a candidate `old(..)` two-state call form (see
/// [`classify_old_call`]).
enum OldCallShape {
    /// Not an `old(..)` call form at all — normal visiting applies.
    NotOld,
    /// An `old(..)` call whose argument is not a bare parameter path
    /// (`old(P)` / `old(*P)`), e.g. `old(x + 1)`, `old(s.f)`, `old()`,
    /// `old(a, b)` — fail closed.
    BadArg,
    /// `old(P)` / `old(*P)` (optionally under one outer deref: `*old(P)` /
    /// `*old(*P)`) targeting the single-ident parameter `P`.
    Param(String),
}

/// Classifies `expr` as a two-state `old(..)` call form. Recognizes the call
/// itself (`old(P)`, `old(*P)`) and the outer-deref spelling (`*old(P)`,
/// `*old(*P)` — the whole `Unary(Deref)` node is then the form). Anything
/// whose callee is not the bare path `old` is `NotOld`.
fn classify_old_call(expr: &Expr) -> OldCallShape {
    let call = match expr {
        Expr::Call(call) => call,
        Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Deref(_)) => {
            match unary.expr.as_ref() {
                Expr::Call(call) => call,
                _ => return OldCallShape::NotOld,
            }
        }
        _ => return OldCallShape::NotOld,
    };
    let Expr::Path(func_path) = call.func.as_ref() else {
        return OldCallShape::NotOld;
    };
    if expr_path_single_ident(func_path).as_deref() != Some("old") {
        return OldCallShape::NotOld;
    }
    if call.args.len() != 1 {
        return OldCallShape::BadArg;
    }
    match old_call_arg_param_name(&call.args[0]) {
        Some(name) => OldCallShape::Param(name),
        None => OldCallShape::BadArg,
    }
}

/// The parameter name when an `old(..)` argument is a bare single-ident path
/// `P` or its deref `*P`; `None` for any other shape (fields, indexing,
/// arithmetic, nested calls, …) — those fail closed in slice A.
fn old_call_arg_param_name(arg: &Expr) -> Option<String> {
    match arg {
        Expr::Path(path) => expr_path_single_ident(path),
        Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Deref(_)) => {
            match unary.expr.as_ref() {
                Expr::Path(path) => expr_path_single_ident(path),
                _ => None,
            }
        }
        _ => None,
    }
}

impl FinalValueSubstituter<'_> {
    /// Records a reference to `&mut` param `name` and, when a clean final value
    /// exists, replaces `*expr` with it. Never recurses into the replacement, so
    /// an entry-level reference inside a final value (e.g. `x + 1` for `*x = *x +
    /// 1`) keeps its entry meaning. (Whether the substitution is *sound* — no
    /// escape / early exit — is validated per-param by the caller, which discards
    /// `rewritten` and fails closed otherwise.)
    fn substitute(&mut self, expr: &mut Expr, name: &str) {
        self.referenced_params.insert(name.to_string());
        if let Some(value) = self.finals.get(name) {
            match syn::parse_str::<Expr>(value) {
                Ok(replacement) => *expr = replacement,
                Err(err) => {
                    self.parse_error = Some(format!(
                        "final value `{value}` for `&mut` parameter `{name}` did not \
                         re-parse as an expression: {err}"
                    ));
                }
            }
        }
    }
}

impl VisitMut for FinalValueSubstituter<'_> {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        // Two-state `old(..)` forms FIRST (they wrap a `Call`, which the bare
        // `Path` / `Unary(Deref)`-of-path arms below never match): `old(P)`,
        // `old(*P)`, `*old(P)`, `*old(*P)` denote the ENTRY (pre-state) value
        // of a scalar `&mut` param, which in the string model is exactly the
        // declared param symbol. Replace the ENTIRE node (including any outer
        // deref) with the bare path `P` and record it in
        // `old_referenced_params`, then return WITHOUT recursing — the same
        // never-recurse-into-replacement discipline as `substitute`: visiting
        // the inserted `P` would final-substitute it, silently turning the
        // entry reference into the post-state value (directionality landmine).
        match classify_old_call(expr) {
            OldCallShape::Param(name) if self.mut_ref_params.contains(&name) => {
                self.old_referenced_params.insert(name.clone());
                let ident = syn::Ident::new(&name, proc_macro2::Span::call_site());
                *expr = Expr::Path(syn::ExprPath {
                    attrs: Vec::new(),
                    qself: None,
                    path: syn::Path::from(ident),
                });
                return;
            }
            OldCallShape::Param(name) => {
                // `old()` over anything that is not a supported scalar `&mut`
                // parameter is a HARD error: silently reading the current
                // value would treat `old(y)` as `y` and over-prove.
                self.parse_error = Some(format!(
                    "old() is only supported on scalar &mut parameters: `{name}` \
                     is not a supported scalar `&mut` parameter (bool/integer \
                     referent)"
                ));
                return;
            }
            OldCallShape::BadArg => {
                let snippet = quote!(#expr).to_string();
                self.parse_error = Some(format!(
                    "old() is only supported on scalar &mut parameters: the \
                     argument must be a bare parameter (`old(P)` or `*old(P)`), \
                     got `{snippet}`"
                ));
                return;
            }
            OldCallShape::NotOld => {}
        }
        if let Expr::Path(path) = expr {
            if let Some(name) = expr_path_single_ident(path) {
                if self.mut_ref_params.contains(&name) {
                    self.substitute(expr, &name);
                    return;
                }
            }
        }
        if let Expr::Unary(unary) = expr {
            if matches!(unary.op, syn::UnOp::Deref(_)) {
                if let Expr::Path(path) = unary.expr.as_ref() {
                    if let Some(name) = expr_path_single_ident(path) {
                        if self.mut_ref_params.contains(&name) {
                            self.substitute(expr, &name);
                            return;
                        }
                    }
                }
            }
        }
        syn::visit_mut::visit_expr_mut(self, expr);
    }

    // Do NOT descend into closures (quantifier bodies): a binder may shadow a
    // `&mut` parameter name, and substituting under it would be wrong. Record
    // whether a `&mut` parameter is mentioned so the caller can fail closed.
    fn visit_expr_closure_mut(&mut self, closure: &mut syn::ExprClosure) {
        if closure_mentions_mut_ref_param(closure, self.mut_ref_params) {
            self.closure_mentions_param = true;
        }
    }

    fn visit_item_mut(&mut self, _item: &mut syn::Item) {}
}

fn expr_path_single_ident(path: &syn::ExprPath) -> Option<String> {
    if path.qself.is_some() {
        return None;
    }
    path.path.get_ident().map(ToString::to_string)
}

fn closure_mentions_mut_ref_param(
    closure: &syn::ExprClosure,
    mut_ref_params: &BTreeSet<String>,
) -> bool {
    struct IdentVisitor<'a> {
        params: &'a BTreeSet<String>,
        found: bool,
    }
    impl<'ast> Visit<'ast> for IdentVisitor<'_> {
        fn visit_ident(&mut self, ident: &'ast proc_macro2::Ident) {
            if self.params.contains(&ident.to_string()) {
                self.found = true;
            }
        }
    }
    let mut visitor = IdentVisitor {
        params: mut_ref_params,
        found: false,
    };
    visitor.visit_expr_closure(closure);
    visitor.found
}

/// Whether the single canonical return value is a `match` expression (modulo
/// transparent `Paren`/`Group`/block-tail wrapping). Gates the `result`-inlining
/// that keeps a `match`-returning body's postcondition decidable (see the call
/// site). `Conditional`/`Unit` returns are never match-shaped.
fn return_value_is_match(return_value: return_extract::ReturnValue<'_>) -> bool {
    match return_value {
        return_extract::ReturnValue::Expr(expr) => expr_tail_is_match(expr),
        _ => false,
    }
}

fn expr_tail_is_match(expr: &Expr) -> bool {
    match expr {
        Expr::Match(_) => true,
        Expr::Paren(p) => expr_tail_is_match(&p.expr),
        Expr::Group(g) => expr_tail_is_match(&g.expr),
        Expr::Block(b) => match b.block.stmts.last() {
            Some(syn::Stmt::Expr(tail, None)) => expr_tail_is_match(tail),
            _ => false,
        },
        _ => false,
    }
}

/// A body whose tail is `seq.all(|x| ..)` / `seq.any(|x| ..)` (over a slice/Vec,
/// optionally via `.iter()`) lowers to a bounded quantifier. Binding `result` to
/// such a quantifier with an opaque `result == forall …` ASSUME poisons the ay
/// e-matching search — the contract equivalence `result == forall …` then
/// degrades to `Unknown (quantifier-unhandled)` instead of discharging. Inlining
/// the quantifier into the `result`-referencing obligations (and dropping the
/// assume) turns the postcondition into the self-contained, e-matchable goal
/// `forall_body == forall_spec`, exactly as the match-return path does. Sound:
/// `result` IS the return expression.
fn return_value_is_seq_quantifier(return_value: return_extract::ReturnValue<'_>) -> bool {
    match return_value {
        return_extract::ReturnValue::Expr(expr) => expr_tail_is_seq_quantifier(expr),
        _ => false,
    }
}

/// True iff the return tail is a comparison or short-circuit-logical binary
/// (`<`, `<=`, `>`, `>=`, `==`, `!=`, `&&`, `||`) whose presence directly to the
/// right of the synthesized `result ==` would form an illegal chained comparison
/// (or mis-bind a `&&`). Such a tail must be parenthesized in the `return_value`
/// assume; every other tail is left byte-identical.
fn return_value_tail_is_chainable_binary(return_value: return_extract::ReturnValue<'_>) -> bool {
    match return_value {
        return_extract::ReturnValue::Expr(expr) => expr_tail_is_chainable_binary(expr),
        _ => false,
    }
}

fn expr_tail_is_chainable_binary(expr: &Expr) -> bool {
    match expr {
        Expr::Binary(binary) => matches!(
            binary.op,
            syn::BinOp::Lt(_)
                | syn::BinOp::Le(_)
                | syn::BinOp::Gt(_)
                | syn::BinOp::Ge(_)
                | syn::BinOp::Eq(_)
                | syn::BinOp::Ne(_)
                | syn::BinOp::And(_)
                | syn::BinOp::Or(_)
        ),
        Expr::Paren(p) => expr_tail_is_chainable_binary(&p.expr),
        Expr::Group(g) => expr_tail_is_chainable_binary(&g.expr),
        Expr::Block(b) => match b.block.stmts.last() {
            Some(syn::Stmt::Expr(tail, None)) => expr_tail_is_chainable_binary(tail),
            _ => false,
        },
        _ => false,
    }
}

fn expr_tail_is_seq_quantifier(expr: &Expr) -> bool {
    match expr {
        Expr::MethodCall(mc) => {
            (mc.method == "all" || mc.method == "any")
                && mc.args.len() == 1
                && matches!(mc.args.first(), Some(Expr::Closure(_)))
        }
        Expr::Paren(p) => expr_tail_is_seq_quantifier(&p.expr),
        Expr::Group(g) => expr_tail_is_seq_quantifier(&g.expr),
        Expr::Block(b) => match b.block.stmts.last() {
            Some(syn::Stmt::Expr(tail, None)) => expr_tail_is_seq_quantifier(tail),
            _ => false,
        },
        _ => false,
    }
}

/// Inlines the canonical return expression `return_str` into every obligation
/// that references `result_var`, replacing each whole-word occurrence with
/// `(return_str)`. Returns `true` iff, after the substitution, NO obligation
/// references `result_var` any more — only then is it sound for the caller to
/// drop the `result == return_str` assume (the binding is fully eliminated). If
/// any reference remains (e.g. `result` used in a spot the textual inliner does
/// not reach), returns `false` and leaves the conditions rewritten but the
/// caller keeps the assume, so the result binding is still constrained.
fn inline_result_binding(vc: &mut VerificationContext, result_var: &str, return_str: &str) -> bool {
    let replacement = format!("({return_str})");
    for obligation in &mut vc.obligations {
        if condition_references_word(&obligation.condition, result_var) {
            obligation.condition =
                replace_whole_word(&obligation.condition, result_var, &replacement);
        }
    }
    !vc.obligations
        .iter()
        .any(|obligation| condition_references_word(&obligation.condition, result_var))
}

/// True if `word` occurs in `haystack` as a complete identifier (not bordered by
/// `[A-Za-z0-9_]`), so `result` matches `result` / `result.x` but not
/// `result_value` or `my_result`.
fn condition_references_word(haystack: &str, word: &str) -> bool {
    word_match_indices(haystack, word).next().is_some()
}

fn replace_whole_word(haystack: &str, word: &str, replacement: &str) -> String {
    let mut out = String::with_capacity(haystack.len());
    let mut last = 0usize;
    for start in word_match_indices(haystack, word).collect::<Vec<_>>() {
        out.push_str(&haystack[last..start]);
        out.push_str(replacement);
        last = start + word.len();
    }
    out.push_str(&haystack[last..]);
    out
}

/// Yields the byte offsets at which `word` appears in `haystack` as a standalone
/// identifier (ident-boundary on both sides).
fn word_match_indices<'a>(haystack: &'a str, word: &'a str) -> impl Iterator<Item = usize> + 'a {
    fn is_ident_char(c: char) -> bool {
        c.is_ascii_alphanumeric() || c == '_'
    }
    let word_len = word.len();
    haystack
        .match_indices(word)
        .filter(move |&(start, _)| {
            let before_ok = start == 0
                || !haystack[..start]
                    .chars()
                    .next_back()
                    .is_some_and(is_ident_char);
            let after = start + word_len;
            let after_ok = after >= haystack.len()
                || !haystack[after..].chars().next().is_some_and(is_ident_char);
            before_ok && after_ok
        })
        .map(|(start, _)| start)
}

fn scoped_return_value_expression(
    block: &Block,
    return_value: return_extract::ReturnValue<'_>,
    struct_types: &[StructDef],
) -> String {
    match return_value {
        return_extract::ReturnValue::Expr(return_expr) => {
            scoped_return_expression(block, return_expr, struct_types)
        }
        return_extract::ReturnValue::Conditional {
            pattern,
            scrutinee,
            then_value,
            else_value,
        } => {
            let scrutinee =
                body_extract::extract_scoped_return_expression(block, scrutinee, struct_types)
                    .unwrap_or_else(|| extract_expr_string(scrutinee));
            let condition = let_else_match_condition(pattern, &scrutinee);
            let then_value = scoped_return_expression(block, then_value, struct_types);
            let else_value = scoped_return_expression(block, else_value, struct_types);
            format!("if {condition} {{ {then_value} }} else {{ {else_value} }}")
        }
        return_extract::ReturnValue::Unit => "()".to_string(),
    }
}

fn scoped_return_expression(
    block: &Block,
    return_expr: &Expr,
    struct_types: &[StructDef],
) -> String {
    body_extract::extract_scoped_return_expression(block, return_expr, struct_types)
        .unwrap_or_else(|| extract_expr_string(return_expr))
}

fn let_else_match_condition(pattern: &Pat, scrutinee: &str) -> String {
    match pattern {
        Pat::TupleStruct(tuple_struct) => tuple_struct
            .path
            .segments
            .last()
            .map(|segment| variant_match_condition(scrutinee, &segment.ident.to_string()))
            .unwrap_or_else(|| "true".to_string()),
        Pat::Path(path) => path
            .path
            .segments
            .last()
            .map(|segment| variant_match_condition(scrutinee, &segment.ident.to_string()))
            .unwrap_or_else(|| "true".to_string()),
        Pat::Struct(_) => "true".to_string(),
        Pat::Type(pat_type) => let_else_match_condition(&pat_type.pat, scrutinee),
        Pat::Paren(paren) => let_else_match_condition(&paren.pat, scrutinee),
        Pat::Ident(_) | Pat::Wild(_) => "true".to_string(),
        _ => "true".to_string(),
    }
}

fn variant_match_condition(scrutinee: &str, variant_name: &str) -> String {
    match variant_name {
        "Some" => format!("({scrutinee}).is_some()"),
        "None" => format!("({scrutinee}).is_none()"),
        _ => format!("({scrutinee}).is_{variant_name}()"),
    }
}

fn block_contains_let_else(block: &Block) -> bool {
    #[derive(Default)]
    struct Finder {
        found: bool,
    }

    impl<'ast> Visit<'ast> for Finder {
        fn visit_local(&mut self, local: &'ast syn::Local) {
            if self.found {
                return;
            }
            if local
                .init
                .as_ref()
                .is_some_and(|init| init.diverge.is_some())
            {
                self.found = true;
                return;
            }
            syn::visit::visit_local(self, local);
        }
    }

    let mut finder = Finder::default();
    finder.visit_block(block);
    finder.found
}

/// Verus rejects a by-value `mut self` receiver at signature lowering
/// (`rust_verify/src/rust_to_vir_func.rs` `ImplicitSelfKind::Mut` →
/// `unsupported_err`), in ANY mode, before any parameter mode checks. Upstream
/// witness: basic.rs `test_mut_self_disallowed`. `&mut self` (`RefMut`) and
/// plain `self` / `&self` are legal and must not fire. Applies only to the
/// function under extraction (sibling helper-contract registration never goes
/// through this entry), so ordinary Rust `mut self` builder methods elsewhere
/// in a crate are unaffected. Fail-closed; the diagnostic contains the
/// upstream message verbatim.
fn mut_self_receiver_error(func: &ItemFn) -> Option<TrustVcError> {
    for input in &func.sig.inputs {
        if let FnArg::Receiver(receiver) = input {
            if receiver.reference.is_none() && receiver.mutability.is_some() {
                return Some(TrustVcError::Encoding {
                    context: "extract verification conditions",
                    detail:
                        "The verifier does not yet support the following Rust feature: mut self"
                            .to_string(),
                });
            }
        }
    }
    None
}

/// Verus rejects a `mut x` binding in a SPEC function signature at lowering
/// (`rust_verify/src/rust_to_vir_func.rs`, `is_mut_var` + mode == Spec),
/// independent of the body and not gated on new-mut-ref. Upstream witness:
/// basic.rs `test_mut_param_spec_fail` (`spec fn f(mut x: i32) -> i32;`).
/// `mut` params in exec/proof functions are legal and unaffected (caller gates
/// on mode). Fail-closed; the diagnostic contains the upstream message
/// verbatim.
fn spec_mut_param_error(func: &ItemFn) -> Option<TrustVcError> {
    for input in &func.sig.inputs {
        if let FnArg::Typed(pat_type) = input {
            if let Pat::Ident(pat_ident) = pat_type.pat.as_ref() {
                if pat_ident.mutability.is_some() {
                    return Some(TrustVcError::Encoding {
                        context: "extract verification conditions",
                        detail: "mut argument not allowed for spec functions".to_string(),
                    });
                }
            }
        }
    }
    None
}

/// True if the block contains any assignment expression (`x = e`) or compound
/// assignment (`x += e`, …) anywhere, including nested blocks and closures
/// (spec closures are pure too) but NOT nested item definitions (a nested `fn`
/// item has its own mode). Macro token streams are not descended into by
/// `syn::visit`, so `assert!(a == b)` and friends can never misfire. Used for
/// the Verus pure-context rule: any assignment in a spec-mode body is
/// "assignment is not allowed inside pure context" (upstream basic.rs
/// `test_init_spec_param_fail_2`, modes.rs `spec_let_decl_init_fail`).
fn block_contains_assignment(block: &Block) -> bool {
    #[derive(Default)]
    struct Finder {
        found: bool,
    }

    impl<'ast> Visit<'ast> for Finder {
        fn visit_expr_assign(&mut self, _: &'ast syn::ExprAssign) {
            self.found = true;
        }

        fn visit_expr_binary(&mut self, binary: &'ast syn::ExprBinary) {
            if self.found {
                return;
            }
            if binop_is_assignment(&binary.op) {
                self.found = true;
                return;
            }
            syn::visit::visit_expr_binary(self, binary);
        }

        fn visit_item(&mut self, _: &'ast syn::Item) {
            // A nested item (fn/const/…) has its own mode; do not descend.
        }
    }

    let mut finder = Finder::default();
    finder.visit_block(block);
    finder.found
}

/// True for the compound-assignment binary operators (`+=`, `-=`, …).
fn binop_is_assignment(op: &syn::BinOp) -> bool {
    matches!(
        op,
        syn::BinOp::AddAssign(_)
            | syn::BinOp::SubAssign(_)
            | syn::BinOp::MulAssign(_)
            | syn::BinOp::DivAssign(_)
            | syn::BinOp::RemAssign(_)
            | syn::BinOp::BitXorAssign(_)
            | syn::BinOp::BitAndAssign(_)
            | syn::BinOp::BitOrAssign(_)
            | syn::BinOp::ShlAssign(_)
            | syn::BinOp::ShrAssign(_)
    )
}

/// True if the block contains a `return` expression anywhere, including
/// closure bodies (spec closures are pure too) but NOT nested item
/// definitions (a nested `fn` has its own mode). Macro token streams are not
/// descended by `syn::visit`, so return-in-assert-arg shapes are handled by
/// the mode-keyed [`ghost_macro_control_flow_error`] walker instead. Used for
/// the Verus pure-context rule: any `return` typed in a spec-mode body is
/// "return is not allowed in pure context" (vir/src/modes.rs ExprX::Return +
/// `in_pure`, set for spec-fn bodies by `push_in_pure(pure_spec_fn)`).
fn block_contains_return(block: &Block) -> bool {
    #[derive(Default)]
    struct Finder {
        found: bool,
    }

    impl<'ast> Visit<'ast> for Finder {
        fn visit_expr_return(&mut self, _: &'ast syn::ExprReturn) {
            self.found = true;
        }

        fn visit_item(&mut self, _: &'ast syn::Item) {
            // A nested item (fn/const/…) has its own mode; do not descend.
        }
    }

    let mut finder = Finder::default();
    finder.visit_block(block);
    finder.found
}

/// True if the block contains a `return` expression inside a CLOSURE subtree
/// (closure-depth scoped: a top-level `return` does not fire). Nested items
/// are not descended. Used for the proof-mode pure-context rule: closures in
/// proof fns are spec closures, whose bodies are pure — upstream witness
/// closures.rs `return_in_closure` ("return is not allowed in pure context").
/// trust-vc's contract-bearing `closure!` surface is a macro call, invisible
/// to `syn::visit`, so it cannot be over-rejected here.
fn block_closures_contain_return(block: &Block) -> bool {
    #[derive(Default)]
    struct Finder {
        closure_depth: usize,
        found: bool,
    }

    impl<'ast> Visit<'ast> for Finder {
        fn visit_expr_closure(&mut self, closure: &'ast syn::ExprClosure) {
            if self.found {
                return;
            }
            self.closure_depth += 1;
            syn::visit::visit_expr_closure(self, closure);
            self.closure_depth -= 1;
        }

        fn visit_expr_return(&mut self, ret: &'ast syn::ExprReturn) {
            if self.closure_depth > 0 {
                self.found = true;
                return;
            }
            syn::visit::visit_expr_return(self, ret);
        }

        fn visit_item(&mut self, _: &'ast syn::Item) {
            // A nested item has its own mode; do not descend.
        }
    }

    let mut finder = Finder::default();
    finder.visit_block(block);
    finder.found
}

/// Which ghost-context control-flow construct a walk found FIRST, in
/// pre-order (outer-to-inner, left-to-right) — matching upstream's
/// expression-recursion order, where the error of an ENCLOSING construct
/// fires before any check on its children (e.g. a ghost-context loop is
/// rejected with "cannot use while in proof or spec mode" before a `break`
/// inside it is ever mode-checked).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GhostControlFlow {
    Loop,
    Return,
    BreakOrContinue,
}

/// First loop/`return`/`break`/`continue` in the expression, pre-order,
/// descending closures (quantifier/spec-closure bodies are pure too) but not
/// nested items.
fn first_ghost_control_flow_in_expr(expr: &Expr) -> Option<GhostControlFlow> {
    let mut finder = GhostControlFlowFinder::default();
    finder.visit_expr(expr);
    finder.found
}

/// Block-shaped variant of [`first_ghost_control_flow_in_expr`].
fn first_ghost_control_flow_in_block(block: &Block) -> Option<GhostControlFlow> {
    let mut finder = GhostControlFlowFinder::default();
    finder.visit_block(block);
    finder.found
}

#[derive(Default)]
struct GhostControlFlowFinder {
    found: Option<GhostControlFlow>,
}

impl<'ast> Visit<'ast> for GhostControlFlowFinder {
    fn visit_expr(&mut self, expr: &'ast Expr) {
        if self.found.is_some() {
            return;
        }
        match expr {
            Expr::While(_) | Expr::ForLoop(_) | Expr::Loop(_) => {
                self.found = Some(GhostControlFlow::Loop);
            }
            Expr::Return(_) => self.found = Some(GhostControlFlow::Return),
            Expr::Break(_) | Expr::Continue(_) => {
                self.found = Some(GhostControlFlow::BreakOrContinue);
            }
            _ => syn::visit::visit_expr(self, expr),
        }
    }

    fn visit_item(&mut self, _: &'ast syn::Item) {
        // A nested item has its own mode; do not descend.
    }
}

/// Upstream diagnostic for a control-flow construct typed in a PURE argument
/// position (assert!/assume! arguments, quantifier bodies). Message table
/// grounded in vir/src/modes.rs check ORDER:
///   * loops: ghost-context loops are rejected first — "cannot use while in
///     proof or spec mode" (modes.rs ExprX::Loop, `block_ghostness != Exec`).
///   * `return`: the exec-fn ghost-context check PRECEDES all pure-context
///     checks, so in an exec fn the message is "cannot return from non-exec
///     code in exec function"; in proof/spec fns that check passes
///     (`(Mode::Proof, _)` / `(Mode::Spec, _)` arms) and `in_pure` fires —
///     "return is not allowed in pure context".
///   * `break`/`continue`: ExprX::BreakOrContinue has NO exec-ghost check —
///     "break/continue is not allowed in pure context" in every mode.
fn pure_arg_control_flow_detail(kind: GhostControlFlow, mode: crate::mode::FunctionMode) -> String {
    match kind {
        GhostControlFlow::Loop => "cannot use while in proof or spec mode".to_string(),
        GhostControlFlow::Return => match mode {
            crate::mode::FunctionMode::Exec => {
                "cannot return from non-exec code in exec function".to_string()
            }
            _ => "return is not allowed in pure context".to_string(),
        },
        GhostControlFlow::BreakOrContinue => {
            "break/continue is not allowed in pure context".to_string()
        }
    }
}

/// Upstream diagnostic for a control-flow construct typed in the PROOF BLOCK
/// of an `assert forall … by` statement (`in_forall_stmt` upstream). Same
/// check-order grounding as [`pure_arg_control_flow_detail`]: the exec-fn
/// ghost-context return check still precedes `in_forall_stmt`; for
/// proof/spec fns the `in_forall_stmt` messages fire (modes.rs :3123/:3155).
/// No upstream test pins these two strings (grepped rust_verify_test/tests);
/// they are source-grounded only.
fn assert_by_control_flow_detail(
    kind: GhostControlFlow,
    mode: crate::mode::FunctionMode,
) -> String {
    match kind {
        GhostControlFlow::Loop => "cannot use while in proof or spec mode".to_string(),
        GhostControlFlow::Return => match mode {
            crate::mode::FunctionMode::Exec => {
                "cannot return from non-exec code in exec function".to_string()
            }
            _ => "return is not allowed in 'assert ... by' statements".to_string(),
        },
        GhostControlFlow::BreakOrContinue => {
            "break/continue is not allowed in 'assert ... by' statements".to_string()
        }
    }
}

/// Verus-parity rejection of `return`/`break`/`continue`/loops typed inside
/// the GHOST argument of an assert!/assume! macro or inside the proof block
/// of an `assert forall … by`, which the body-level finders cannot see
/// (`syn::visit` never descends macro token streams). The token streams are
/// parsed with the SAME parsers the real extraction path uses
/// (`parse_assert_forall_by`, `parse_expr_tokens_with_chains`); parse
/// failures are ignored here — the existing extraction path errors on those
/// later. Reject-only: every fired shape is rejected upstream (assert/assume
/// arguments are `in_pure`, assert-by proof blocks are `in_forall_stmt`,
/// ghost-context loops are rejected outright), so no legal program is lost —
/// `return` in exec/proof fn bodies and `break`/`continue` in exec loops
/// OUTSIDE the macro arguments never enter this walker.
fn ghost_macro_control_flow_error(
    block: &Block,
    mode: crate::mode::FunctionMode,
) -> Option<TrustVcError> {
    struct Walker {
        mode: crate::mode::FunctionMode,
        detail: Option<String>,
    }

    impl Walker {
        fn check_pure_arg(&mut self, expr: &Expr) {
            if self.detail.is_some() {
                return;
            }
            if let Some(kind) = first_ghost_control_flow_in_expr(expr) {
                self.detail = Some(pure_arg_control_flow_detail(kind, self.mode));
            }
        }
    }

    impl<'ast> Visit<'ast> for Walker {
        fn visit_macro(&mut self, mac: &'ast syn::Macro) {
            if self.detail.is_some() {
                return;
            }
            let Some(name) = path_last_segment(&mac.path) else {
                return;
            };
            match name.as_str() {
                "assert" | "trust_vc_assert" | "assert_forall_by" => {
                    if let Ok(parsed) = crate::parse_assert_forall_by(mac.tokens.clone()) {
                        // `assert forall |x| cond by { proof }`: upstream sets
                        // `in_forall_stmt` for the WHOLE statement — condition
                        // AND proof block — and that check precedes `in_pure`
                        // (modes.rs :3123/:3155 before :3130/:3162), so BOTH
                        // positions get the 'assert ... by' message variant
                        // (the exec-fn ghost-return check still precedes, and
                        // ghost-loop rejection fires first for loops — both
                        // encoded in `assert_by_control_flow_detail`).
                        if let Some(kind) = first_ghost_control_flow_in_expr(&parsed.closure.body) {
                            self.detail = Some(assert_by_control_flow_detail(kind, self.mode));
                        }
                        if self.detail.is_none() {
                            if let Some(kind) =
                                first_ghost_control_flow_in_block(&parsed.proof_block)
                            {
                                self.detail = Some(assert_by_control_flow_detail(kind, self.mode));
                            }
                        }
                        return;
                    }
                    if let Ok(expr) = crate::chained_comparisons::parse_expr_tokens_with_chains(
                        mac.tokens.clone(),
                    ) {
                        self.check_pure_arg(&expr);
                    }
                }
                "assume" | "trust_vc_assume" => {
                    if let Ok(expr) = crate::chained_comparisons::parse_expr_tokens_with_chains(
                        mac.tokens.clone(),
                    ) {
                        self.check_pure_arg(&expr);
                    }
                }
                _ => {}
            }
        }

        fn visit_item(&mut self, _: &'ast syn::Item) {
            // A nested item has its own mode; do not descend.
        }
    }

    let mut walker = Walker { mode, detail: None };
    walker.visit_block(block);
    walker.detail.map(|detail| TrustVcError::Encoding {
        context: "extract verification conditions",
        detail,
    })
}

/// Translation-time enforcement of the upstream at-most-one `proof_note`
/// rule over `assert!`/`assume!` macros in the function body (basic.rs
/// FAMILY C: `test_multiple_proof_notes_on_assert`/`_on_assume`,
/// `test_multiple_custom_errs_on_assert`). Upstream
/// `get_proof_note_annotation` (rust_verify/src/attributes.rs:1010-1023)
/// fires during HIR→VIR translation, BEFORE verification, regardless of the
/// proof outcome — so this entry prepass rejects duplicates even on paths
/// where the body extractor would not parse the macro (e.g. value-only
/// evaluation). Labels pool per macro: statement/expression-level attrs on
/// the macro node PLUS leading expression-level attrs inside the token
/// stream (upstream moves statement attrs inside onto the argument
/// expression). `proof_note` and `custom_err` pool TOGETHER, matching
/// upstream (both parse to `Attr::ProofNote`).
///
/// Reject-only: a single label never fires; unparseable token streams are
/// skipped here (the real extraction path errors on those later); macros
/// other than assert/assume are untouched.
fn proof_note_at_most_one_error(block: &Block) -> Option<TrustVcError> {
    struct Walker {
        error: Option<TrustVcError>,
    }

    impl Walker {
        fn check_macro(&mut self, mac: &syn::Macro, node_attrs: &[syn::Attribute]) {
            if self.error.is_some() {
                return;
            }
            let Some(name) = path_last_segment(&mac.path) else {
                return;
            };
            if !matches!(
                name.as_str(),
                "assert" | "trust_vc_assert" | "assume" | "trust_vc_assume"
            ) {
                return;
            }
            let mut labels = match crate::proof_note::proof_note_labels_from_attrs(node_attrs) {
                Ok(labels) => labels,
                Err(err) => {
                    self.error = Some(err);
                    return;
                }
            };
            if let Ok(mut expr) =
                crate::chained_comparisons::parse_expr_tokens_with_chains(mac.tokens.clone())
            {
                match crate::proof_note::take_leading_proof_note_labels(&mut expr) {
                    Ok(more) => labels.extend(more),
                    Err(err) => {
                        self.error = Some(err);
                        return;
                    }
                }
            }
            if let Err(err) = crate::proof_note::at_most_one_proof_note(labels) {
                self.error = Some(err);
            }
        }
    }

    impl<'ast> Visit<'ast> for Walker {
        fn visit_stmt(&mut self, stmt: &'ast syn::Stmt) {
            if self.error.is_some() {
                return;
            }
            if let syn::Stmt::Macro(stmt_macro) = stmt {
                self.check_macro(&stmt_macro.mac, &stmt_macro.attrs);
            }
            syn::visit::visit_stmt(self, stmt);
        }

        fn visit_expr_macro(&mut self, expr_macro: &'ast syn::ExprMacro) {
            if self.error.is_some() {
                return;
            }
            self.check_macro(&expr_macro.mac, &expr_macro.attrs);
            syn::visit::visit_expr_macro(self, expr_macro);
        }
    }

    let mut walker = Walker { error: None };
    walker.visit_block(block);
    walker.error
}

/// Which side of a spec `==`/`!=` a declared parameter type falls on for the
/// upstream compatibility rule (`rust_verify/src/fn_call_to_vir.rs:1761-1786`:
/// allowed iff `types_equal || is_smt_arith` — every int-class mix is
/// arithmetic-compatible, anything else must be the SAME type).
enum SpecEqOperandClass {
    /// Integer-class (u*/i*/int/nat): compatible with every other int-class.
    IntClass,
    /// A positively-known NON-integer concrete type (datatype, collection,
    /// bool, spec_fn, …): incompatible with an int-class operand.
    NonIntConcrete,
    /// Anything the syn frontend cannot positively classify (opaque,
    /// type-param, char/float/real, …): the rule NEVER fires — fail toward
    /// the existing behavior, no over-rejection.
    Unknown,
}

fn spec_eq_operand_class(ty: &TrustVcType) -> SpecEqOperandClass {
    match ty {
        TrustVcType::Int { .. }
        | TrustVcType::Uint { .. }
        | TrustVcType::MathInt
        | TrustVcType::Nat => SpecEqOperandClass::IntClass,
        TrustVcType::Bool
        | TrustVcType::Unit
        | TrustVcType::Seq(_)
        | TrustVcType::Array(_, _)
        | TrustVcType::Set(_)
        | TrustVcType::Multiset(_)
        | TrustVcType::Map(_, _)
        | TrustVcType::SpecFn(_, _)
        | TrustVcType::Datatype { .. }
        | TrustVcType::String
        | TrustVcType::StrSlice => SpecEqOperandClass::NonIntConcrete,
        _ => SpecEqOperandClass::Unknown,
    }
}

/// Syntactic operand shapes for the tuple × generic-projection spec-eq
/// rejection (`test_spec_eq_type_error_4`) — the pair whose Verus-verbatim span
/// rendering requires the `syn::Type`, not the compacted source string.
enum SpecEqSynShape {
    /// A tuple type `(A, B, ..)` (≥ 2 elements).
    Tuple,
    /// An associated-type projection `<X as Trait>::Assoc` whose `Self` (`X`) is
    /// a DECLARED function type-generic — abstract, so unnormalizable, so
    /// upstream can never prove it equal to a concrete tuple.
    GenericProjection,
    Other,
}

fn spec_eq_syn_shape(ty: &syn::Type, generic_idents: &BTreeSet<String>) -> SpecEqSynShape {
    match ty {
        syn::Type::Tuple(tuple) if tuple.elems.len() >= 2 => SpecEqSynShape::Tuple,
        syn::Type::Path(type_path) => {
            let Some(qself) = &type_path.qself else {
                return SpecEqSynShape::Other;
            };
            // `<X as Trait>::Assoc`: require `X` to be a bare declared generic
            // ident (abstract). A concrete `Self` type could normalize, so
            // firing there would risk over-rejecting a case upstream accepts.
            if let syn::Type::Path(self_path) = qself.ty.as_ref() {
                if self_path.qself.is_none() {
                    if let Some(ident) = self_path.path.get_ident() {
                        if generic_idents.contains(&ident.to_string()) {
                            return SpecEqSynShape::GenericProjection;
                        }
                    }
                }
            }
            SpecEqSynShape::Other
        }
        _ => SpecEqSynShape::Other,
    }
}

/// Renders a `syn::Type` with Verus's span-label spacing: `(A, B)` for tuples
/// (comma-space), ` as ` around a projection's trait, `::`-joined path segments
/// with NO surrounding spaces. Only the shapes reached by the tuple ×
/// generic-projection rejection need be exact; anything else falls back to the
/// compact `extract_type_name` (never gate-matched on those paths).
fn render_type_verus(ty: &syn::Type) -> String {
    match ty {
        syn::Type::Tuple(tuple) => {
            let elems: Vec<String> = tuple.elems.iter().map(render_type_verus).collect();
            format!("({})", elems.join(", "))
        }
        syn::Type::Reference(reference) => {
            let inner = render_type_verus(&reference.elem);
            if reference.mutability.is_some() {
                format!("&mut {inner}")
            } else {
                format!("&{inner}")
            }
        }
        syn::Type::Path(type_path) => {
            let segments: Vec<String> = type_path
                .path
                .segments
                .iter()
                .map(render_path_segment_verus)
                .collect();
            let leading = if type_path.path.leading_colon.is_some() {
                "::"
            } else {
                ""
            };
            match &type_path.qself {
                Some(qself) => {
                    let self_ty = render_type_verus(&qself.ty);
                    let position = qself.position.min(segments.len());
                    let (trait_part, assoc_part) = segments.split_at(position);
                    format!(
                        "<{} as {}{}>::{}",
                        self_ty,
                        leading,
                        trait_part.join("::"),
                        assoc_part.join("::")
                    )
                }
                None => format!("{leading}{}", segments.join("::")),
            }
        }
        other => param_extract::extract_type_name(other),
    }
}

fn render_path_segment_verus(segment: &syn::PathSegment) -> String {
    match &segment.arguments {
        syn::PathArguments::None => segment.ident.to_string(),
        // Generic/parenthesized args are not reached by the tuple × projection
        // pair on the basic.rs case; render them via the compact fallback so a
        // future shape stays sound (display-only, reject-only).
        _ => param_extract::extract_type_name(&syn::Type::Path(syn::TypePath {
            qself: None,
            path: syn::Path::from(segment.clone()),
        })),
    }
}

/// Strips upstream-transparent type decorations from a compacted type string:
/// leading `&`/`&mut` and the `Box`/`Rc`/`Arc`/`Ghost`/`Tracked` wrappers
/// (with any module qualification), mirroring Verus `undecorate_typ` — the
/// upstream spec-eq check compares the UNDECORATED types
/// (`test_spec_eq_type_error_2`: `std::sync::Arc<Option<u64>>` reports
/// `::Option<u64>`).
fn undecorate_type_string(compact: &str) -> &str {
    let mut current = compact;
    loop {
        let stripped = current
            .strip_prefix("&mut")
            .or_else(|| current.strip_prefix('&'))
            .unwrap_or(current);
        let mut next = stripped;
        for wrapper in ["Box", "Rc", "Arc", "Ghost", "Tracked"] {
            if let Some(open) = next.find('<') {
                let head = &next[..open];
                let is_wrapper = head == wrapper || head.ends_with(&format!("::{wrapper}"));
                if is_wrapper && next.ends_with('>') {
                    next = &next[open + 1..next.len() - 1];
                    break;
                }
            }
        }
        if next == current {
            return current;
        }
        current = next;
    }
}

/// Verus-parity rejection of a spec `==`/`!=` between INCOMPATIBLE declared
/// parameter types in a contract clause (basic.rs FAMILY D,
/// `test_spec_eq_type_error_1`/`_2`). Upstream
/// (`rust_verify/src/fn_call_to_vir.rs:1761-1786`) allows the comparison iff
/// the undecorated types are equal or both integer-class (`is_smt_arith` —
/// `u64 == int` is LEGAL); everything else is the primary translation-time
/// error "mismatched types; types must be compatible to use == or !=" with
/// both type renderings attached.
///
/// Syn-frontend decidable subset, deliberately narrow (no over-rejection):
/// * both operands must be BARE parameter identifiers of the verified
///   function (locals/calls/fields/`result` are skipped — no flow analysis);
/// * only CONTRACT clause expressions are scanned (requires/ensures/
///   recommends, standalone or `#[contract]`-grouped) — body asserts can
///   shadow parameter names, so they are out of scope here;
/// * closure sub-expressions are skipped (quantifier binders may shadow
///   parameter names);
/// * the rule fires only for an int-class operand against a POSITIVELY
///   non-integer concrete operand; any unresolved/opaque side means silence
///   (alias controls stay legal: an unresolved alias classifies `Unknown`, a
///   registry-resolved alias classifies as its target).
///
/// Rendering: the source-declared type, compacted and undecorated; a
/// datatype rendering gets a leading `::` (upstream renders the FULL path —
/// `core::option::Option<u64>` — of which the pinned upstream pattern
/// `::Option<u64>` is a suffix).
fn spec_eq_type_mismatch_error(
    func: &ItemFn,
    param_types: &BTreeMap<String, (String, TrustVcType)>,
) -> Option<TrustVcError> {
    if param_types.is_empty() {
        return None;
    }

    struct EqWalker<'a> {
        param_types: &'a BTreeMap<String, (String, TrustVcType)>,
        /// The declared `syn::Type` per parameter, used for the shape-based
        /// (tuple × generic-projection) rejection whose Verus-verbatim span
        /// rendering the compacted `param_types` source string cannot reproduce
        /// (`<Xastest_crate::A>::AT` loses the `as` word boundary).
        param_syn_types: &'a BTreeMap<String, syn::Type>,
        /// The function's declared type-generic idents (`fn f<X: ..>`) — a
        /// projection `<X as Trait>::Assoc` over one of these is abstract, so
        /// unnormalizable, so upstream ALWAYS rejects it against a tuple.
        generic_idents: &'a BTreeSet<String>,
        error: Option<TrustVcError>,
        /// Clause-local binders (let / match arms / if-let / while-let /
        /// for-loops) that SHADOW a parameter name. A shadowed ident must not
        /// be classified with the parameter's type — upstream evaluates it
        /// with the binder's type (e.g. `{ let b = 10u64; a == b }` with
        /// `b: Option<u64>` in the signature is a legal u64 == u64 upstream).
        /// Conservative direction: shadowed -> skip classification (silent),
        /// mirroring the existing unresolved-ident silence; never a reject.
        shadow_stack: Vec<BTreeSet<String>>,
    }

    fn bare_param_ident(expr: &Expr) -> Option<String> {
        let mut current = expr;
        loop {
            match current {
                Expr::Paren(paren) => current = &paren.expr,
                Expr::Group(group) => current = &group.expr,
                Expr::Reference(reference) => current = &reference.expr,
                Expr::Path(path) if path.qself.is_none() => {
                    return path.path.get_ident().map(ToString::to_string);
                }
                _ => return None,
            }
        }
    }

    fn render_spec_eq_type(source: &str, ty: &TrustVcType) -> String {
        let compact = source.replace(' ', "");
        let undecorated = undecorate_type_string(&compact);
        if matches!(ty, TrustVcType::Datatype { .. }) && !undecorated.starts_with("::") {
            format!("::{undecorated}")
        } else if let TrustVcType::SpecFn(args, _ret) = ty {
            // Verus renders trust-vc's ghost-closure type `SpecFn<P1, .., Pn,
            // Ret>` as `spec_fn(P1, .., Pn) -> Ret` in its span labels, so the
            // spec-eq type-mismatch diagnostic must carry that surface verbatim
            // (upstream basic.rs test_spec_eq_type_error_3 pattern
            // `spec_fn(u64) -> nat`). The source's first `args.len()` generic
            // arguments are the parameters, the last is the return. Fall back to
            // the raw rendering if the source shape is unexpected (still an
            // `error` verdict either way — this is display text only).
            spec_fn_verus_rendering(&undecorated, args.len())
                .unwrap_or_else(|| undecorated.to_string())
        } else {
            undecorated.to_string()
        }
    }

    /// Renders an (already space-stripped, undecorated) `SpecFn<..>` source type
    /// as Verus's `spec_fn(params) -> ret` surface. `arg_count` is the parameter
    /// arity from the `TrustVcType::SpecFn`, so the last of the `arg_count + 1`
    /// top-level generic arguments is the return type. Returns `None` (caller
    /// keeps the raw rendering) when the source is not the expected
    /// `SpecFn<..>` shape or its top-level generic count disagrees with the type.
    fn spec_fn_verus_rendering(undecorated: &str, arg_count: usize) -> Option<String> {
        let open = undecorated.find('<')?;
        let name = undecorated[..open].trim_start_matches("::");
        if name != "SpecFn" {
            return None;
        }
        let inner = undecorated.strip_suffix('>')?.get(open + 1..)?;
        let parts = split_top_level_type_list(inner);
        if parts.len() != arg_count + 1 {
            return None;
        }
        let (params, ret) = parts.split_at(arg_count);
        Some(format!("spec_fn({}) -> {}", params.join(", "), ret[0]))
    }

    /// Splits a comma-separated type list on TOP-LEVEL commas only, keeping
    /// nested generic / tuple / array groups (`<>`, `()`, `[]`) intact.
    fn split_top_level_type_list(inner: &str) -> Vec<String> {
        let mut parts = Vec::new();
        let mut depth = 0i32;
        let mut current = String::new();
        for ch in inner.chars() {
            match ch {
                '<' | '(' | '[' => {
                    depth += 1;
                    current.push(ch);
                }
                '>' | ')' | ']' => {
                    depth -= 1;
                    current.push(ch);
                }
                ',' if depth == 0 => {
                    parts.push(current.trim().to_string());
                    current.clear();
                }
                _ => current.push(ch),
            }
        }
        if !current.trim().is_empty() {
            parts.push(current.trim().to_string());
        }
        parts
    }

    impl EqWalker<'_> {
        fn is_shadowed(&self, name: &str) -> bool {
            self.shadow_stack.iter().any(|scope| scope.contains(name))
        }

        fn bind_pattern(&mut self, pat: &syn::Pat) {
            let mut names = Vec::new();
            collect_pat_binding_names(pat, &mut names);
            if let Some(scope) = self.shadow_stack.last_mut() {
                scope.extend(names);
            }
        }

        /// `if`/`while` conditions: bind `let` pattern names (let-chains
        /// included) into the current freshly-pushed scope; visit non-let
        /// operands normally. Mirrors the slice-1 Finder.
        fn visit_cond_binding_lets(&mut self, cond: &Expr) {
            match cond {
                Expr::Let(expr_let) => {
                    self.visit_expr(&expr_let.expr);
                    self.bind_pattern(&expr_let.pat);
                }
                Expr::Binary(binary) if matches!(binary.op, syn::BinOp::And(_)) => {
                    self.visit_cond_binding_lets(&binary.left);
                    self.visit_cond_binding_lets(&binary.right);
                }
                Expr::Paren(paren) => self.visit_cond_binding_lets(&paren.expr),
                Expr::Group(group) => self.visit_cond_binding_lets(&group.expr),
                other => self.visit_expr(other),
            }
        }

        fn check_binary(&mut self, binary: &syn::ExprBinary) {
            if self.error.is_some() {
                return;
            }
            if !matches!(binary.op, syn::BinOp::Eq(_) | syn::BinOp::Ne(_)) {
                return;
            }
            let (Some(left), Some(right)) = (
                bare_param_ident(&binary.left),
                bare_param_ident(&binary.right),
            ) else {
                return;
            };
            if self.is_shadowed(&left) || self.is_shadowed(&right) {
                return;
            }
            let (Some((left_src, left_ty)), Some((right_src, right_ty))) =
                (self.param_types.get(&left), self.param_types.get(&right))
            else {
                return;
            };
            let incompatible = matches!(
                (
                    spec_eq_operand_class(left_ty),
                    spec_eq_operand_class(right_ty)
                ),
                (
                    SpecEqOperandClass::IntClass,
                    SpecEqOperandClass::NonIntConcrete
                ) | (
                    SpecEqOperandClass::NonIntConcrete,
                    SpecEqOperandClass::IntClass
                )
            );
            if incompatible {
                self.error = Some(TrustVcError::Encoding {
                    context: "extract verification conditions",
                    detail: format!(
                        "mismatched types; types must be compatible to use == or != \
                         (this is `{}`, this is `{}`)",
                        render_spec_eq_type(left_src, left_ty),
                        render_spec_eq_type(right_src, right_ty),
                    ),
                });
                return;
            }
            // FAMILY D (shape subset): a tuple compared with an associated-type
            // projection over a declared fn generic (`<X as Trait>::Assoc`).
            // Both are positively-known NON-arith and can NEVER be `types_equal`
            // (the projection over an abstract generic is unnormalizable), so
            // upstream ALWAYS errors on the pair — a faithful, reject-only
            // extension. Rendered from the `syn::Type` (not the compacted source)
            // so the span labels carry Verus's exact spacing, e.g. `(u64, nat)`
            // and `<X as test_crate::A>::AT` (upstream basic.rs
            // test_spec_eq_type_error_4).
            let (Some(left_syn), Some(right_syn)) = (
                self.param_syn_types.get(&left),
                self.param_syn_types.get(&right),
            ) else {
                return;
            };
            let shapes = (
                spec_eq_syn_shape(left_syn, self.generic_idents),
                spec_eq_syn_shape(right_syn, self.generic_idents),
            );
            if matches!(
                shapes,
                (SpecEqSynShape::Tuple, SpecEqSynShape::GenericProjection)
                    | (SpecEqSynShape::GenericProjection, SpecEqSynShape::Tuple)
            ) {
                self.error = Some(TrustVcError::Encoding {
                    context: "extract verification conditions",
                    detail: format!(
                        "mismatched types; types must be compatible to use == or != \
                         (this is `{}`, this is `{}`)",
                        render_type_verus(left_syn),
                        render_type_verus(right_syn),
                    ),
                });
            }
        }
    }

    impl<'ast> Visit<'ast> for EqWalker<'_> {
        fn visit_expr(&mut self, expr: &'ast Expr) {
            if self.error.is_some() {
                return;
            }
            // Quantifier/closure binders may shadow parameter names; skip.
            if matches!(expr, Expr::Closure(_)) {
                return;
            }
            if let Expr::Binary(binary) = expr {
                self.check_binary(binary);
            }
            syn::visit::visit_expr(self, expr);
        }

        fn visit_block(&mut self, block: &'ast syn::Block) {
            self.shadow_stack.push(BTreeSet::new());
            for stmt in &block.stmts {
                self.visit_stmt(stmt);
            }
            self.shadow_stack.pop();
        }

        fn visit_local(&mut self, local: &'ast syn::Local) {
            // Initializer first: in `let b = b + 1;` the RHS still refers to
            // the parameter.
            if let Some(init) = &local.init {
                self.visit_expr(&init.expr);
                if let Some((_, diverge)) = &init.diverge {
                    self.visit_expr(diverge);
                }
            }
            self.bind_pattern(&local.pat);
        }

        fn visit_arm(&mut self, arm: &'ast syn::Arm) {
            self.shadow_stack.push(BTreeSet::new());
            self.bind_pattern(&arm.pat);
            if let Some((_, guard)) = &arm.guard {
                self.visit_expr(guard);
            }
            self.visit_expr(&arm.body);
            self.shadow_stack.pop();
        }

        fn visit_expr_for_loop(&mut self, for_loop: &'ast syn::ExprForLoop) {
            self.visit_expr(&for_loop.expr);
            self.shadow_stack.push(BTreeSet::new());
            self.bind_pattern(&for_loop.pat);
            self.visit_block(&for_loop.body);
            self.shadow_stack.pop();
        }

        fn visit_expr_if(&mut self, expr_if: &'ast syn::ExprIf) {
            // `if let PAT = RHS { .. }` (incl. let-chains): bindings scope to
            // the THEN branch.
            self.shadow_stack.push(BTreeSet::new());
            self.visit_cond_binding_lets(&expr_if.cond);
            self.visit_block(&expr_if.then_branch);
            self.shadow_stack.pop();
            if let Some((_, else_expr)) = &expr_if.else_branch {
                self.visit_expr(else_expr);
            }
        }

        fn visit_expr_while(&mut self, expr_while: &'ast syn::ExprWhile) {
            self.shadow_stack.push(BTreeSet::new());
            self.visit_cond_binding_lets(&expr_while.cond);
            self.visit_block(&expr_while.body);
            self.shadow_stack.pop();
        }

        fn visit_item(&mut self, _: &'ast syn::Item) {
            // A nested item has its own scope; do not descend.
        }
    }

    let mut param_syn_types: BTreeMap<String, syn::Type> = BTreeMap::new();
    for input in &func.sig.inputs {
        if let FnArg::Typed(pat_type) = input {
            if let syn::Pat::Ident(pat_ident) = pat_type.pat.as_ref() {
                param_syn_types.insert(pat_ident.ident.to_string(), (*pat_type.ty).clone());
            }
        }
    }
    let generic_idents: BTreeSet<String> = func
        .sig
        .generics
        .params
        .iter()
        .filter_map(|param| match param {
            syn::GenericParam::Type(type_param) => Some(type_param.ident.to_string()),
            _ => None,
        })
        .collect();
    let mut walker = EqWalker {
        param_types,
        param_syn_types: &param_syn_types,
        generic_idents: &generic_idents,
        error: None,
        shadow_stack: Vec::new(),
    };
    for attr in &func.attrs {
        match path_last_segment(attr.path()).as_deref() {
            Some("requires" | "ensures" | "recommends") => {
                if let Ok(expr) = contract_attribute_expr(attr) {
                    walker.visit_expr(&expr);
                }
            }
            Some("contract") => {
                if let Ok(clauses) = parse_target_contract_clauses(attr) {
                    for clause in clauses {
                        if matches!(
                            clause.name.to_string().as_str(),
                            "requires" | "ensures" | "recommends"
                        ) {
                            for expr in &clause.args {
                                walker.visit_expr(expr);
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        if walker.error.is_some() {
            break;
        }
    }
    walker.error
}

/// Verus rejects an assignment to a non-`mut` PARAMETER in a proof function
/// with "variable `{name}` is not marked mutable" (`vir/src/ast_simplify.rs`).
/// Upstream witness: basic.rs `test_init_spec_param_fail_1`
/// (`proof fn test1(x: u64) { x = 5; }`). Scope is deliberately param-only and
/// shadow-aware: `proof fn f(mut x: int) { x += 1; }` is legal (mut param),
/// assignments to `let mut` locals are legal, and a param name re-bound by an
/// intervening `let` / closure param / match or for-loop pattern is no longer
/// the parameter — none of those fire. Exec functions are unaffected (caller
/// gates on mode); spec functions hit the pure-context rule first. Nested
/// items are not descended into. Fail-closed; the diagnostic contains the
/// upstream message (with the interpolated name) verbatim.
fn proof_non_mut_param_assignment_error(func: &ItemFn) -> Option<TrustVcError> {
    let mut non_mut_params: BTreeSet<String> = BTreeSet::new();
    for input in &func.sig.inputs {
        if let FnArg::Typed(pat_type) = input {
            if let Pat::Ident(pat_ident) = pat_type.pat.as_ref() {
                if pat_ident.mutability.is_none() {
                    non_mut_params.insert(pat_ident.ident.to_string());
                }
            }
        }
    }
    if non_mut_params.is_empty() {
        return None;
    }

    struct Finder {
        params: BTreeSet<String>,
        shadow_stack: Vec<BTreeSet<String>>,
        found: Option<String>,
    }

    impl Finder {
        fn is_shadowed(&self, name: &str) -> bool {
            self.shadow_stack.iter().any(|scope| scope.contains(name))
        }

        fn check_assignment_target(&mut self, target: &Expr) {
            if self.found.is_some() {
                return;
            }
            let mut expr = target;
            loop {
                match expr {
                    Expr::Paren(paren) => expr = &paren.expr,
                    Expr::Group(group) => expr = &group.expr,
                    _ => break,
                }
            }
            let Expr::Path(path) = expr else {
                return;
            };
            if path.qself.is_some() || path.path.segments.len() != 1 {
                return;
            }
            let name = path.path.segments[0].ident.to_string();
            if self.params.contains(&name) && !self.is_shadowed(&name) {
                self.found = Some(name);
            }
        }

        fn bind_pattern_names(&mut self, pat: &Pat) {
            let mut names = Vec::new();
            collect_pat_binding_names(pat, &mut names);
            if let Some(scope) = self.shadow_stack.last_mut() {
                scope.extend(names);
            }
        }

        /// Walk an `if`/`while` condition: visit every non-`let`
        /// subexpression normally (assignment checks still apply there) and
        /// bind the pattern names of every `let` operand — let-chains
        /// (`let A(x) = e && let B(y) = f`) included — into the CURRENT
        /// (freshly pushed) scope so they cover the guarded branch/body.
        /// Left-to-right recursion means later chain operands already see
        /// earlier bindings, matching Rust's scoping.
        fn visit_cond_binding_lets(&mut self, cond: &syn::Expr) {
            match cond {
                syn::Expr::Let(expr_let) => {
                    // RHS is evaluated before the binding exists.
                    self.visit_expr(&expr_let.expr);
                    self.bind_pattern_names(&expr_let.pat);
                }
                syn::Expr::Binary(binary) if matches!(binary.op, syn::BinOp::And(_)) => {
                    self.visit_cond_binding_lets(&binary.left);
                    self.visit_cond_binding_lets(&binary.right);
                }
                syn::Expr::Paren(paren) => self.visit_cond_binding_lets(&paren.expr),
                syn::Expr::Group(group) => self.visit_cond_binding_lets(&group.expr),
                other => self.visit_expr(other),
            }
        }
    }

    impl<'ast> Visit<'ast> for Finder {
        fn visit_block(&mut self, block: &'ast Block) {
            self.shadow_stack.push(BTreeSet::new());
            for stmt in &block.stmts {
                self.visit_stmt(stmt);
            }
            self.shadow_stack.pop();
        }

        fn visit_local(&mut self, local: &'ast syn::Local) {
            // Visit the initializer BEFORE recording the binding: in
            // `let x = x + 1;` the RHS still refers to the parameter.
            if let Some(init) = &local.init {
                self.visit_expr(&init.expr);
                if let Some((_, diverge)) = &init.diverge {
                    self.visit_expr(diverge);
                }
            }
            self.bind_pattern_names(&local.pat);
        }

        fn visit_expr_closure(&mut self, closure: &'ast syn::ExprClosure) {
            self.shadow_stack.push(BTreeSet::new());
            for input in &closure.inputs {
                self.bind_pattern_names(input);
            }
            self.visit_expr(&closure.body);
            self.shadow_stack.pop();
        }

        fn visit_arm(&mut self, arm: &'ast syn::Arm) {
            self.shadow_stack.push(BTreeSet::new());
            self.bind_pattern_names(&arm.pat);
            if let Some((_, guard)) = &arm.guard {
                self.visit_expr(guard);
            }
            self.visit_expr(&arm.body);
            self.shadow_stack.pop();
        }

        fn visit_expr_for_loop(&mut self, for_loop: &'ast syn::ExprForLoop) {
            self.visit_expr(&for_loop.expr);
            self.shadow_stack.push(BTreeSet::new());
            self.bind_pattern_names(&for_loop.pat);
            self.visit_block(&for_loop.body);
            self.shadow_stack.pop();
        }

        fn visit_expr_if(&mut self, expr_if: &'ast syn::ExprIf) {
            // `if let PAT = RHS { .. }` (incl. let-chains): the pattern
            // bindings scope to the THEN branch only. Without this override
            // an `if let Some(mut o) = o { o = 5; }` rebind of a non-mut
            // param was invisible to the shadow tracker and the rule falsely
            // fired on upstream-legal code (Verus accepts mut pattern-bound
            // rebinds — rust_verify_test/tests/match.rs test3/test4).
            self.shadow_stack.push(BTreeSet::new());
            self.visit_cond_binding_lets(&expr_if.cond);
            self.visit_block(&expr_if.then_branch);
            self.shadow_stack.pop();
            if let Some((_, else_expr)) = &expr_if.else_branch {
                self.visit_expr(else_expr);
            }
        }

        fn visit_expr_while(&mut self, expr_while: &'ast syn::ExprWhile) {
            // `while let PAT = RHS { .. }`: bindings scope to the loop body.
            self.shadow_stack.push(BTreeSet::new());
            self.visit_cond_binding_lets(&expr_while.cond);
            self.visit_block(&expr_while.body);
            self.shadow_stack.pop();
        }

        fn visit_expr_assign(&mut self, assign: &'ast syn::ExprAssign) {
            self.check_assignment_target(&assign.left);
            syn::visit::visit_expr_assign(self, assign);
        }

        fn visit_expr_binary(&mut self, binary: &'ast syn::ExprBinary) {
            if binop_is_assignment(&binary.op) {
                self.check_assignment_target(&binary.left);
            }
            syn::visit::visit_expr_binary(self, binary);
        }

        fn visit_item(&mut self, _: &'ast syn::Item) {
            // A nested item has its own signature/mode; do not descend.
        }
    }

    let mut finder = Finder {
        params: non_mut_params,
        shadow_stack: Vec::new(),
        found: None,
    };
    finder.visit_block(&func.block);
    finder.found.map(|name| TrustVcError::Encoding {
        context: "extract verification conditions",
        detail: format!("variable `{name}` is not marked mutable"),
    })
}

/// Collects every identifier bound by a pattern (any mutability — a rebound
/// name shadows the parameter either way). Used for shadow tracking in
/// [`proof_non_mut_param_assignment_error`].
fn collect_pat_binding_names(pat: &Pat, names: &mut Vec<String>) {
    struct Collector<'a> {
        names: &'a mut Vec<String>,
    }
    impl<'a, 'ast> Visit<'ast> for Collector<'a> {
        fn visit_pat_ident(&mut self, pat_ident: &'ast syn::PatIdent) {
            self.names.push(pat_ident.ident.to_string());
            syn::visit::visit_pat_ident(self, pat_ident);
        }
    }
    let mut collector = Collector { names };
    collector.visit_pat(pat);
}

#[derive(Clone)]
struct SourceStructTemplate {
    name: String,
    generic_params: Vec<String>,
    fields: Vec<(String, Type)>,
    derived_partial_eq: bool,
    derived_clone: bool,
}

/// True when `attrs` contain `#[derive(.., Trait, ..)]` naming `trait_name` (by
/// its final path segment, so `PartialEq` and `std::cmp::PartialEq` both match).
fn attrs_derive_trait(attrs: &[syn::Attribute], trait_name: &str) -> bool {
    attrs.iter().any(|attr| {
        if !attr.path().is_ident("derive") {
            return false;
        }
        let mut found = false;
        let _ = attr.parse_nested_meta(|meta| {
            if meta
                .path
                .segments
                .last()
                .is_some_and(|segment| segment.ident == trait_name)
            {
                found = true;
            }
            Ok(())
        });
        found
    })
}

#[derive(Clone)]
struct SourceEnumTemplate {
    name: String,
    generic_params: Vec<String>,
    variants: Vec<SourceEnumVariantTemplate>,
    derived_partial_eq: bool,
    derived_clone: bool,
}

#[derive(Clone)]
struct SourceEnumVariantTemplate {
    name: String,
    fields: Vec<(String, Type)>,
}

#[derive(Clone)]
struct SourceTypeAliasTemplate {
    name: String,
    generic_params: Vec<String>,
    target: Type,
}

#[derive(Clone, Default)]
struct SourceFunctionRegistry {
    functions: BTreeMap<String, ItemFn>,
}

impl SourceFunctionRegistry {
    fn from_file(file: &File) -> Self {
        let mut registry = Self::default();
        collect_source_functions_from_items(&file.items, &mut Vec::new(), &mut registry.functions);
        registry
    }

    fn get(&self, path: &str) -> Option<&ItemFn> {
        self.functions.get(path)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct SourceCallReference {
    source_path: String,
    call_symbol: String,
}

/// Resolve one call edge through the aliases of the Rust block that CONTAINS
/// that edge. Keeping the call symbol unchanged preserves the spelling used by
/// the body axiom, while canonicalizing `source_path` fixes the source item
/// identity carried through transitive sibling discovery.
fn source_reference_with_aliases(
    mut reference: SourceCallReference,
    aliases: &BTreeMap<String, String>,
) -> SourceCallReference {
    if let Some(source_path) = aliases.get(&reference.source_path) {
        reference.source_path.clone_from(source_path);
    }
    reference
}

fn source_call_reference(call: &syn::ExprCall) -> Option<SourceCallReference> {
    let Expr::Path(path) = &*call.func else {
        return None;
    };
    source_call_reference_from_expr_path(path)
}

fn source_call_reference_from_expr_path(path: &syn::ExprPath) -> Option<SourceCallReference> {
    if path.qself.is_some() || path.path.leading_colon.is_some() {
        return None;
    }
    let call_symbol = expr_path_to_string(path);
    let mut segments = path
        .path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>();
    while segments
        .first()
        .is_some_and(|segment| segment == "crate" || segment == "self")
    {
        segments.remove(0);
    }
    if segments.is_empty() {
        return None;
    }
    Some(SourceCallReference {
        source_path: segments.join("::"),
        call_symbol,
    })
}

fn call_function_symbol(call: &syn::ExprCall) -> Option<String> {
    source_call_reference(call).map(|reference| reference.call_symbol)
}

fn collect_source_functions_from_items(
    items: &[syn::Item],
    prefix: &mut Vec<String>,
    functions: &mut BTreeMap<String, ItemFn>,
) {
    for item in items {
        match item {
            syn::Item::Fn(item_fn) => {
                let mut path = prefix.clone();
                path.push(item_fn.sig.ident.to_string());
                functions
                    .entry(path.join("::"))
                    .or_insert_with(|| item_fn.clone());
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    prefix.push(module.ident.to_string());
                    collect_source_functions_from_items(inner_items, prefix, functions);
                    prefix.pop();
                }
            }
            _ => {}
        }
    }
}

#[derive(Clone, Default)]
struct SourceStructRegistry {
    structs: BTreeMap<String, SourceStructTemplate>,
    enums: BTreeMap<String, SourceEnumTemplate>,
    type_aliases: BTreeMap<String, SourceTypeAliasTemplate>,
    /// Datatype names with a hand-written `impl PartialEq for T` in the source
    /// (a `#[derive(PartialEq)]` is NOT an `Item::Impl` in the syn AST, so only
    /// genuinely-custom impls land here). Their exec `==` may be non-structural.
    manual_partial_eq_types: BTreeSet<String>,
}

impl SourceStructRegistry {
    fn from_file(file: &File) -> Self {
        let mut registry = Self::default();
        collect_source_types_from_items(
            &file.items,
            &mut registry.structs,
            &mut registry.enums,
            &mut registry.type_aliases,
        );
        collect_manual_partial_eq_impls(&file.items, &mut registry.manual_partial_eq_types);
        registry
    }

    /// True when `method_name` is the name of an auto-generated datatype
    /// accessor that the type environment synthesizes for the datatype named
    /// `self_type` — a variant tester `is_<Variant>` or a field selector
    /// `get_<Variant>_<field>`. These mirror exactly the helper methods
    /// `TypeEnv::register_variant_helper_methods` registers for every datatype
    /// variant (a struct is a single variant whose name equals the type).
    ///
    /// A user may write an inherent method that re-declares such an accessor
    /// (e.g. a hand-written `fn is_A(&self) -> bool` or `fn get_A_0(&self)` on
    /// an enum with variant `A`). Registering it as an ordinary inherent method
    /// would (a) collide with the canonical accessor's metadata and (b) emit a
    /// body axiom over the method's body (often a `match`/`matches!`/`panic!`
    /// that is not lowerable as a pure spec expression). Because the canonical,
    /// encoder-backed accessor already provides the correct selector/tester
    /// semantics for `recv.is_A()` / `recv.get_A_0()` — and is what the
    /// pattern-binding extractor emits for `let` / `let-else` / `match` field
    /// projection — the redundant user declaration is skipped. Skipping only
    /// ever falls back to the true datatype accessor, so it is sound.
    fn is_synthesized_datatype_accessor(&self, self_type: &str, method_name: &str) -> bool {
        let matches_variant = |variant_name: &str, fields: &[(String, Type)]| {
            if method_name == format!("is_{variant_name}") {
                return true;
            }
            fields
                .iter()
                .any(|(field_name, _)| method_name == format!("get_{variant_name}_{field_name}"))
        };

        if let Some(enum_template) = self.enums.get(self_type) {
            if enum_template
                .variants
                .iter()
                .any(|variant| matches_variant(&variant.name, &variant.fields))
            {
                return true;
            }
        }

        // A struct lowers to a single-variant datatype whose variant name is the
        // struct name, so its accessors are `is_<Struct>` / `get_<Struct>_<f>`.
        if let Some(struct_template) = self.structs.get(self_type) {
            if matches_variant(self_type, &struct_template.fields) {
                return true;
            }
        }

        false
    }

    /// The declared type-parameter names of the datatype named `base`, IN ORDER
    /// (`struct W<P>` → `["P"]`, `enum GOpt<K, V>` → `["K", "V"]`). Used to remap a
    /// generic impl's own type-param names onto the carrier's declared ones when a
    /// generic impl RENAMES them (`impl<A> W<A>` over `struct W<P>`).
    fn datatype_generic_params(&self, base: &str) -> Option<&[String]> {
        if let Some(template) = self.structs.get(base) {
            return Some(&template.generic_params);
        }
        if let Some(template) = self.enums.get(base) {
            return Some(&template.generic_params);
        }
        None
    }

    fn register_struct_defs(&self, vc: &mut VerificationContext) {
        // Datatypes with a hand-written `impl PartialEq` — thread to the context so
        // the `==`/`!=` operator gate (ir_lowering::operators) can decline them.
        for name in &self.manual_partial_eq_types {
            vc.manual_partial_eq_types.insert(name.clone());
        }
        for template in self.structs.values() {
            let substitutions = template
                .generic_params
                .iter()
                .map(|param| (param.clone(), TrustVcType::TypeParam(param.clone())))
                .collect::<HashMap<_, _>>();
            let fields = template.resolve_fields(&substitutions, self);
            vc.register_struct_type(
                StructDef::new(template.name.clone(), fields)
                    .with_derives(template.derived_partial_eq, template.derived_clone),
            );
            if template.derived_partial_eq {
                vc.derived_partial_eq_types.insert(template.name.clone());
            }
            if template.derived_clone {
                vc.derived_clone_types.insert(template.name.clone());
            }
        }
    }

    fn register_type_aliases(&self, vc: &mut VerificationContext) {
        for template in self.enums.values() {
            if template.derived_partial_eq {
                vc.derived_partial_eq_types.insert(template.name.clone());
            }
            if template.derived_clone {
                vc.derived_clone_types.insert(template.name.clone());
            }
            if let Some(ty) = template.to_datatype_type(self) {
                // Register the carrier under the bare name (`GList`) AND, for a
                // generic enum, under its canonical generic spelling
                // (`GList<T>`), with the SAME `TypeParam`-bearing template
                // carrier. The bare key serves monomorphic enums and qualified
                // constructor lookups; the canonical-spelling key lets a generic
                // spec fn's parameter `xs: GList<T>` resolve through
                // `source_type_from_context` (a flat string lookup) to the
                // template carrier instead of failing closed as an opaque
                // `GList<T>`. Per-instantiation monomorphization to a concrete
                // `GList<i32>` happens later, at the use site.
                if !template.generic_params.is_empty() {
                    let canonical =
                        format!("{}<{}>", template.name, template.generic_params.join(", "))
                            .replace(' ', "");
                    vc.register_source_type_alias(&canonical, ty.clone());
                }
                vc.register_source_type_alias(&template.name, ty);
            }
        }
        for template in self.type_aliases.values() {
            if !template.generic_params.is_empty() {
                continue;
            }
            let ty = self
                .resolve_type(&template.target, &HashMap::new())
                .unwrap_or_else(|| {
                    TrustVcType::parse_or_opaque(&extract_type_name(&template.target))
                });
            vc.register_source_type_alias(&template.name, ty);
        }
    }

    fn resolve_type_string(&self, ty: &str) -> Option<TrustVcType> {
        syn::parse_str::<Type>(ty)
            .ok()
            .and_then(|ty| self.resolve_type(&ty, &HashMap::new()))
    }

    fn resolve_type(
        &self,
        ty: &Type,
        substitutions: &HashMap<String, TrustVcType>,
    ) -> Option<TrustVcType> {
        self.resolve_type_inner(
            ty,
            substitutions,
            &mut BTreeSet::new(),
            &mut BTreeSet::new(),
        )
    }

    fn resolve_type_inner(
        &self,
        ty: &Type,
        substitutions: &HashMap<String, TrustVcType>,
        seen_aliases: &mut BTreeSet<String>,
        seen_enums: &mut BTreeSet<String>,
    ) -> Option<TrustVcType> {
        if let Type::Reference(reference) = ty {
            return self.resolve_type_inner(
                &reference.elem,
                substitutions,
                seen_aliases,
                seen_enums,
            );
        }
        // A slice `[T]` (the element type behind a `&[T]` parameter) models as a
        // `Seq(T)`. Resolving the element registry-aware here — instead of falling
        // back to the registry-blind `parse_or_opaque`, which leaves a user
        // struct/enum element as `Opaque` and trips the `contains_opaque` reject —
        // lets a `&[PbConstraint]` parameter (e.g. `verify_all_constraints` / the
        // OPTIMUM gate) resolve to the SAME `Seq(Datatype …)` carrier the body and
        // contract use. Falls back to `parse_or_opaque` when the element is itself
        // unresolved (e.g. a bare primitive `&[bool]`), preserving the prior
        // behavior for those. (Fixed-size arrays `[T; N]` keep their existing
        // `parse_or_opaque` path so their length modeling is unchanged.)
        if let Type::Slice(slice) = ty {
            let resolved =
                self.resolve_type_inner(&slice.elem, substitutions, seen_aliases, seen_enums)?;
            return Some(TrustVcType::Seq(Box::new(resolved)));
        }
        let Type::Path(type_path) = ty else {
            return None;
        };
        if type_path.qself.is_some() {
            return None;
        }
        let segment = type_path.path.segments.last()?;
        let name = segment.ident.to_string();
        if let Some(substitution) = substitutions.get(&name) {
            return Some(substitution.clone());
        }

        if let Some(alias) = self.type_aliases.get(&name) {
            let generic_args = generic_type_args(&segment.arguments)?;
            if !generic_args.is_empty() && generic_args.len() != alias.generic_params.len() {
                return None;
            }
            if !seen_aliases.insert(name.clone()) {
                return None;
            }
            let mut alias_substitutions = substitutions.clone();
            for (param, arg_ty) in alias.generic_params.iter().zip(generic_args.iter()) {
                let resolved = self
                    .resolve_type_inner(arg_ty, substitutions, seen_aliases, seen_enums)
                    .unwrap_or_else(|| TrustVcType::parse_or_opaque(&extract_type_name(arg_ty)));
                alias_substitutions.insert(param.clone(), resolved);
            }
            let resolved = self.resolve_type_inner(
                &alias.target,
                &alias_substitutions,
                seen_aliases,
                seen_enums,
            );
            seen_aliases.remove(&name);
            return resolved.or_else(|| {
                Some(TrustVcType::parse_or_opaque(
                    &type_string_with_substitutions(&alias.target, &alias_substitutions),
                ))
            });
        }

        let generic_args = generic_type_args(&segment.arguments)?;
        if let Some(template) = self.structs.get(&name) {
            if !generic_args.is_empty() && generic_args.len() != template.generic_params.len() {
                return None;
            }

            let mut nested_substitutions = HashMap::new();
            let mut concrete_arg_names = Vec::with_capacity(generic_args.len());
            for (param, arg_ty) in template.generic_params.iter().zip(generic_args.iter()) {
                let resolved = self
                    .resolve_type_inner(arg_ty, substitutions, seen_aliases, seen_enums)
                    .unwrap_or_else(|| TrustVcType::parse_or_opaque(&extract_type_name(arg_ty)));
                concrete_arg_names.push(resolved.to_type_string());
                nested_substitutions.insert(param.clone(), resolved);
            }

            let datatype_name = if concrete_arg_names.is_empty() {
                template.name.clone()
            } else {
                format!("{}<{}>", template.name, concrete_arg_names.join(", "))
            };
            // Recursion guard for a recursive STRUCT (e.g. `Tree { children:
            // Vec<Tree> }`). The enum path already guards re-entry with
            // `seen_enums` (and lifts a direct `Box<Self>` edge to a
            // `RecursiveRef`); the struct path had NO guard, so a struct that
            // reaches itself through a container field — `Vec<Self>`, which is NOT
            // a direct `Box<Self>` self-reference — unfolded forever and overflowed
            // the stack. `seen_enums` is the only resolution set threaded across
            // the field-resolution boundary (`seen_aliases` is reset per field), so
            // it doubles as the datatype-recursion guard for structs here; struct
            // and enum names never collide in the registry. The guard wraps ONLY
            // the field resolution (the unbounded edge), NOT the generic-argument
            // loop above (finite, explicitly-written nesting such as
            // `Wrapper<Wrapper<i32>>`), so non-recursive nesting still resolves.
            // Re-entry fails closed (`None` → the field lowers opaque → the owning
            // datatype is rejected downstream), matching the enum guard.
            if !seen_enums.insert(template.name.clone()) {
                return None;
            }
            let fields = template.resolve_fields_inner(&nested_substitutions, self, seen_enums);
            seen_enums.remove(&template.name);
            return Some(TrustVcType::Datatype {
                name: datatype_name,
                variants: vec![DatatypeVariant::new(template.name.clone(), fields)],
            });
        }

        if let Some(template) = self.enums.get(&name) {
            if !generic_args.is_empty() && generic_args.len() != template.generic_params.len() {
                return None;
            }

            let mut nested_substitutions = HashMap::new();
            let mut concrete_arg_names = Vec::with_capacity(generic_args.len());
            for (param, arg_ty) in template.generic_params.iter().zip(generic_args.iter()) {
                let resolved = self
                    .resolve_type_inner(arg_ty, substitutions, seen_aliases, seen_enums)
                    .unwrap_or_else(|| TrustVcType::parse_or_opaque(&extract_type_name(arg_ty)));
                concrete_arg_names.push(resolved.to_type_string());
                nested_substitutions.insert(param.clone(), resolved);
            }

            let datatype_name = if concrete_arg_names.is_empty() {
                template.name.clone()
            } else {
                format!("{}<{}>", template.name, concrete_arg_names.join(", "))
            };
            return template.to_datatype_type_inner(
                &datatype_name,
                &nested_substitutions,
                self,
                seen_enums,
            );
        }

        // Built-in container/wrapper types whose element types may be
        // user-defined structs/enums. `resolve_type_inner` is registry-aware,
        // so resolving the element here (instead of falling back to the
        // registry-blind string parser `parse_or_opaque`) lets a `Vec<UserT>`
        // field — e.g. `PbConstraint.terms: Vec<PbTerm>` — resolve to a
        // `Seq(Datatype …)` rather than `Seq(Unrecognized …)`, which is what
        // made the whole owning struct opaque. (#trust-vc: container element
        // resolution must consult the source-type registry.)
        match name.as_str() {
            "Vec" | "VecDeque" => {
                let element = generic_args.first()?;
                let resolved =
                    self.resolve_type_inner(element, substitutions, seen_aliases, seen_enums)?;
                return Some(TrustVcType::Seq(Box::new(resolved)));
            }
            // Transparent ownership/heap wrappers: a `Box<T>`/`Rc<T>`/`Arc<T>`
            // field has exactly the verification surface of its `T`.
            "Box" | "Rc" | "Arc" => {
                let element = generic_args.first()?;
                return self.resolve_type_inner(element, substitutions, seen_aliases, seen_enums);
            }
            // Builtin `Option<T>` / `Result<T, E>` whose payload types may be
            // user-defined structs/enums. The registry-blind `parse_or_opaque`
            // leaves a user payload as `Opaque` (e.g. the `ObjectiveEvalError`
            // in `Result<i128, ObjectiveEvalError>`), which makes the whole
            // `result`/parameter unrecognized and skips verification. Resolving
            // the payload(s) registry-aware here yields the SAME `Option`/
            // `Result` datatype carrier the constructor lowering (`Ok(..)`/
            // `Some(..)`) and `parse_or_opaque` build, so a function returning
            // `Result<i128, ObjectiveEvalError>` (e.g. `eval_objective_exact`)
            // and a spec fn over the same type share one carrier. (User
            // `Option`/`Result` enums are caught by the struct/enum lookups
            // above, so this only fires for the builtins.)
            "Option" if generic_args.len() == 1 => {
                let inner = self
                    .resolve_type_inner(&generic_args[0], substitutions, seen_aliases, seen_enums)
                    .unwrap_or_else(|| {
                        TrustVcType::parse_or_opaque(&extract_type_name(&generic_args[0]))
                    });
                return Some(TrustVcType::Datatype {
                    name: format!("Option<{}>", inner.to_type_string()),
                    variants: vec![
                        DatatypeVariant::new("None", vec![]),
                        DatatypeVariant::new("Some", vec![("0".to_string(), inner)]),
                    ],
                });
            }
            "Result" if generic_args.len() == 2 => {
                let ok = self
                    .resolve_type_inner(&generic_args[0], substitutions, seen_aliases, seen_enums)
                    .unwrap_or_else(|| {
                        TrustVcType::parse_or_opaque(&extract_type_name(&generic_args[0]))
                    });
                let err = self
                    .resolve_type_inner(&generic_args[1], substitutions, seen_aliases, seen_enums)
                    .unwrap_or_else(|| {
                        TrustVcType::parse_or_opaque(&extract_type_name(&generic_args[1]))
                    });
                return Some(TrustVcType::Datatype {
                    name: format!("Result<{}, {}>", ok.to_type_string(), err.to_type_string()),
                    variants: vec![
                        DatatypeVariant::new("Ok", vec![("0".to_string(), ok)]),
                        DatatypeVariant::new("Err", vec![("0".to_string(), err)]),
                    ],
                });
            }
            _ => {}
        }

        None
    }
}

impl SourceStructTemplate {
    fn resolve_fields(
        &self,
        substitutions: &HashMap<String, TrustVcType>,
        registry: &SourceStructRegistry,
    ) -> Vec<(String, TrustVcType)> {
        // Pre-seed the recursion guard with THIS struct's own name so a
        // self-referential field (`Tree { children: Vec<Tree> }`) fails closed
        // immediately — mirroring `resolve_type_inner`'s struct branch, which
        // inserts the name before resolving fields. Without this, the
        // `register_struct_defs` entry (which calls `resolve_fields` directly,
        // bypassing that branch) would resolve one extra self-nesting level and
        // materialise an INNER `Tree` datatype whose (opaque-field) shape differs
        // from the outer one, tripping the encoder's "conflicting variant
        // metadata" check and poisoning verification of every function in the
        // file. Seeding here makes both entry paths yield the SAME single-level,
        // opaque-field carrier, exactly as before container-element resolution
        // existed. (`seen_enums` doubles as the datatype-recursion guard for
        // structs — see the struct branch of `resolve_type_inner`.)
        let mut seen_enums = BTreeSet::new();
        seen_enums.insert(self.name.clone());
        self.resolve_fields_inner(substitutions, registry, &mut seen_enums)
    }

    fn resolve_fields_inner(
        &self,
        substitutions: &HashMap<String, TrustVcType>,
        registry: &SourceStructRegistry,
        seen_enums: &mut BTreeSet<String>,
    ) -> Vec<(String, TrustVcType)> {
        self.fields
            .iter()
            .map(|(name, ty)| {
                let field_ty = registry
                    .resolve_type_inner(ty, substitutions, &mut BTreeSet::new(), seen_enums)
                    .unwrap_or_else(|| TrustVcType::parse_or_opaque(&extract_type_name(ty)));
                (name.clone(), field_ty)
            })
            .collect()
    }
}

impl SourceEnumTemplate {
    fn to_datatype_type(&self, registry: &SourceStructRegistry) -> Option<TrustVcType> {
        let substitutions = self
            .generic_params
            .iter()
            .map(|param| (param.clone(), TrustVcType::TypeParam(param.clone())))
            .collect::<HashMap<_, _>>();
        self.to_datatype_type_inner(&self.name, &substitutions, registry, &mut BTreeSet::new())
    }

    fn to_datatype_type_inner(
        &self,
        datatype_name: &str,
        substitutions: &HashMap<String, TrustVcType>,
        registry: &SourceStructRegistry,
        seen_enums: &mut BTreeSet<String>,
    ) -> Option<TrustVcType> {
        if !seen_enums.insert(self.name.clone()) {
            return None;
        }
        let variants = self
            .variants
            .iter()
            .map(|variant| {
                let fields = variant
                    .fields
                    .iter()
                    .map(|(name, ty)| {
                        // Direct self-recursion (`Succ(Box<Nat>)`, `Cons(.., Box<Self>)`,
                        // `Branch(Box<Tree>, Box<Tree>)`): materialise the recursion
                        // edge as a `RecursiveRef` pointing at the datatype currently
                        // being built, instead of recursing back through resolution
                        // (which would re-enter the seen-set guard and fail closed).
                        // Using `datatype_name` as the target guarantees the
                        // `RecursiveRef` names the owning carrier — exactly what the
                        // encoder's well-foundedness validation and the `dt_size`
                        // acyclicity invariant key on. This fires ONLY for the
                        // datatype's own name (after stripping `&`/`Box`/`Rc`/`Arc`);
                        // a field naming a DIFFERENT user enum (mutual recursion) is
                        // not matched here, falls through to `resolve_type_inner`, and
                        // hits the seen-set re-entry guard → opaque → fail closed.
                        if is_self_reference(ty, &self.name, &self.generic_params) {
                            return Some((
                                name.clone(),
                                TrustVcType::RecursiveRef(datatype_name.to_string()),
                            ));
                        }
                        let field_ty = registry
                            .resolve_type_inner(ty, substitutions, &mut BTreeSet::new(), seen_enums)
                            .unwrap_or_else(|| {
                                TrustVcType::parse_or_opaque(&extract_type_name(ty))
                            });
                        if field_ty.contains_opaque() {
                            return None;
                        }
                        Some((name.clone(), field_ty))
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(DatatypeVariant::new(variant.name.clone(), fields))
            })
            .collect::<Option<Vec<_>>>();
        seen_enums.remove(&self.name);
        let variants = variants?;
        Some(TrustVcType::Datatype {
            name: datatype_name.to_string(),
            variants,
        })
    }
}

#[derive(Default)]
struct SourceConstRegistry {
    consts: BTreeMap<String, SourceConstTemplate>,
}

struct SourceConstTemplate {
    name: String,
    source_ty: String,
    ty: TrustVcType,
    init: Expr,
    array_len_value: Option<usize>,
    /// Whether the initializer is supported by the scalar-const path
    /// (`apply_referenced_scalar_consts`). A `usize` const may be registered
    /// purely so its folded `array_len_value` can resolve an array length even
    /// when its initializer is not scalar-supported (e.g. `const B: usize =
    /// N + 1`, whose `Path` reference is not a scalar init); in that case the
    /// scalar path must NOT emit an initializer assumption for it, so its
    /// behavior stays byte-identical to before this folder existed.
    scalar_supported: bool,
}

impl SourceConstRegistry {
    fn from_file(file: &File) -> Self {
        let mut registry = Self::default();
        for item in &file.items {
            let syn::Item::Const(item_const) = item else {
                continue;
            };
            let source_ty = extract_type_name(&item_const.ty);
            let ty = TrustVcType::try_from_str(&source_ty);
            let Ok(ty) = ty else {
                continue;
            };
            if !is_supported_source_const_type(&ty) {
                continue;
            }
            let scalar_supported = is_supported_source_const_init(&item_const.expr);
            // Fold the `usize` array-length value in DECLARATION ORDER: at this
            // point `registry.consts` holds exactly the consts declared earlier
            // in the file, so a reference such as `const B: usize = N + 1`
            // resolves against `N`'s already-folded value. The folder is
            // checked and fails closed (returns `None`) on anything it cannot
            // prove equal to rustc's value — see `const_eval_usize`.
            let array_len_value = if source_ty == "usize" {
                const_eval_usize(&item_const.expr, &registry.consts)
            } else {
                None
            };
            // Register the const if it is usable by EITHER path: the scalar path
            // (supported initializer) or the array-length path (folds to a
            // concrete `usize`). A const registered only for its array length
            // carries `scalar_supported == false` so the scalar path skips it.
            if !scalar_supported && array_len_value.is_none() {
                continue;
            }
            let template = SourceConstTemplate {
                name: item_const.ident.to_string(),
                source_ty: source_ty.clone(),
                ty,
                init: (*item_const.expr).clone(),
                array_len_value,
                scalar_supported,
            };
            registry
                .consts
                .entry(template.name.clone())
                .or_insert(template);
        }
        registry
    }

    fn apply_referenced_scalar_consts(&self, func: &ItemFn, vc: &mut VerificationContext) {
        let mut referenced = expr_path_idents_in_block(&func.block);
        // A const referenced ONLY in a `requires`/`ensures` clause (not the body)
        // must still be declared, or the clause fails to lower.
        referenced.extend(expr_path_idents_in_contract_attrs(&func.attrs));
        let mut selected = referenced
            .into_iter()
            .filter_map(|name| self.consts.get(&name))
            // Consts registered solely so their folded `array_len_value` can
            // resolve an array length (initializer not scalar-supported) must
            // not contribute a scalar initializer assumption here.
            .filter(|template| template.scalar_supported)
            .collect::<Vec<_>>();
        selected.sort_by(|left, right| left.name.cmp(&right.name));

        for template in selected {
            if vc.get_variable_type(&template.name).is_none() {
                vc.declare_const_typed(
                    &template.name,
                    template.ty.clone(),
                    &source_const_init_value(&template.init, &template.ty),
                );
            }
        }
    }

    fn usize_const_len(&self, name: &str, shadowed: &BTreeSet<String>) -> Option<usize> {
        if shadowed.contains(name) {
            return None;
        }
        let template = self.consts.get(name)?;
        if template.source_ty == "usize" {
            template.array_len_value
        } else {
            None
        }
    }
}

fn is_supported_source_const_type(ty: &TrustVcType) -> bool {
    matches!(
        ty,
        TrustVcType::Bool | TrustVcType::Char | TrustVcType::Int { .. } | TrustVcType::Uint { .. }
    )
}

fn is_supported_source_const_init(expr: &Expr) -> bool {
    match expr {
        Expr::Lit(_) => true,
        Expr::Paren(paren) => is_supported_source_const_init(&paren.expr),
        Expr::Group(group) => is_supported_source_const_init(&group.expr),
        Expr::Unary(unary) => {
            matches!(unary.op, syn::UnOp::Neg(_)) && is_supported_source_const_init(&unary.expr)
        }
        Expr::Binary(binary) => {
            matches!(
                binary.op,
                syn::BinOp::Add(_) | syn::BinOp::Sub(_) | syn::BinOp::Mul(_)
            ) && is_supported_source_const_init(&binary.left)
                && is_supported_source_const_init(&binary.right)
        }
        _ => false,
    }
}

fn source_const_init_value(init: &Expr, ty: &TrustVcType) -> String {
    let init = extract_expr_string(init);
    match ty {
        TrustVcType::Int { .. } | TrustVcType::Uint { .. } => {
            format!("(({init}) as {})", ty.to_type_string())
        }
        TrustVcType::Bool | TrustVcType::Char => format!("({init})"),
        _ => unreachable!("guarded by is_supported_source_const_type"),
    }
}

/// Checked, recursive const-evaluator for `usize` array lengths.
///
/// Returns EXACTLY rustc's compile-time `usize` value for `expr`, or `None`
/// (fail closed). It folds:
///   * integer literals (`Lit::Int`) parsed as `usize`;
///   * parentheses / invisible groups;
///   * checked `+`, `-`, `*` over `usize`;
///   * a single-ident `Path` referencing ANOTHER already-registered `usize`
///     const's previously folded `array_len_value` (so `const B: usize = N + 1`
///     resolves against `N`).
/// Anything else — and any overflow, underflow (negative result), a non-`usize`
/// or unresolved reference — yields `None`.
///
/// SOUNDNESS (the crux). An array length feeds index-bounds obligations:
/// `[T; N]` ⇒ `a@.len() == N` ⇒ `a[i]` requires `i < N`. Over-approximating `N`
/// would falsely accept an out-of-bounds access (a false `Verified`), so the
/// folder must equal rustc's value or fail. Arithmetic is performed with
/// `usize` `checked_*`, mirroring rustc's checked const `usize` evaluation
/// exactly: for any program that compiles, no step overflows `usize`, so each
/// fold equals the exact mathematical (and therefore rustc) value; any step
/// that overflows / goes negative is a rustc compile error AND returns `None`
/// here, so the two agree (fail closed) rather than producing a wrong-but-
/// accepted length. References resolve only to an earlier const's *exact*
/// folded value (or `None`), so chained refs stay exact. The folder therefore
/// can never over-size `N` and can never introduce a false `Verified`.
///
/// (Width note: like the pre-existing literal path, parsing uses the host
/// `usize` (64-bit). For a narrower *target* width declared via `global size_of
/// usize`, a const that overflows the target but not the host is itself a
/// target compile error — i.e. not a valid program — so accepting it is outside
/// the "input compiles" contract and shared identically with the literal path.)
fn const_eval_usize(expr: &Expr, consts: &BTreeMap<String, SourceConstTemplate>) -> Option<usize> {
    match expr {
        Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(value),
            ..
        }) => value.base10_parse::<usize>().ok(),
        Expr::Paren(paren) => const_eval_usize(&paren.expr, consts),
        Expr::Group(group) => const_eval_usize(&group.expr, consts),
        Expr::Binary(binary) => {
            let left = const_eval_usize(&binary.left, consts)?;
            let right = const_eval_usize(&binary.right, consts)?;
            match binary.op {
                syn::BinOp::Add(_) => left.checked_add(right),
                syn::BinOp::Sub(_) => left.checked_sub(right),
                syn::BinOp::Mul(_) => left.checked_mul(right),
                _ => None,
            }
        }
        Expr::Path(path) => {
            if path.qself.is_some() || path.path.segments.len() != 1 {
                return None;
            }
            let name = path.path.segments[0].ident.to_string();
            let template = consts.get(&name)?;
            if template.source_ty != "usize" {
                return None;
            }
            // Only an earlier const's already-folded EXACT value (or `None`).
            template.array_len_value
        }
        _ => None,
    }
}

fn function_const_generic_names(func: &ItemFn) -> BTreeSet<String> {
    func.sig
        .generics
        .params
        .iter()
        .filter_map(|param| match param {
            syn::GenericParam::Const(param) => Some(param.ident.to_string()),
            _ => None,
        })
        .collect()
}

fn expr_path_idents_in_block(block: &Block) -> BTreeSet<String> {
    let mut collector = ExprPathIdentCollector::default();
    collector.visit_block(block);
    collector.idents
}

/// Single-segment path identifiers referenced inside a function's contract
/// attributes (`requires`/`ensures`/`recommends`/`invariant`/`decreases`). The
/// predicate is carried in the attribute's `Meta::List` token stream, which the
/// body walk does not reach — so a const used ONLY in a `requires` clause
/// (`#[requires(x < N)]`) would otherwise never be declared, and the clause
/// fails to lower. Re-parse each contract predicate and collect its idents.
fn expr_path_idents_in_contract_attrs(attrs: &[syn::Attribute]) -> BTreeSet<String> {
    let mut collector = ExprPathIdentCollector::default();
    for attr in attrs {
        let syn::Meta::List(meta_list) = &attr.meta else {
            continue;
        };
        let is_contract = meta_list.path.segments.last().is_some_and(|seg| {
            matches!(
                seg.ident.to_string().as_str(),
                "requires" | "ensures" | "recommends" | "invariant" | "decreases"
            )
        });
        if !is_contract {
            continue;
        }
        if let Ok(expr) = syn::parse2::<syn::Expr>(meta_list.tokens.clone()) {
            collector.visit_expr(&expr);
        }
    }
    collector.idents
}

#[derive(Default)]
struct ExprPathIdentCollector {
    idents: BTreeSet<String>,
}

impl<'ast> Visit<'ast> for ExprPathIdentCollector {
    fn visit_expr_path(&mut self, path: &'ast syn::ExprPath) {
        if path.qself.is_none() && path.path.segments.len() == 1 {
            self.idents.insert(path.path.segments[0].ident.to_string());
        }
    }
}

/// Collect the self-type name of every hand-written `impl PartialEq for T` (and
/// `impl<..> PartialEq for T`) in `items`, recursing into inline modules. A
/// `#[derive(PartialEq)]` expands to no `Item::Impl` in the source syn AST, so
/// only genuinely custom (possibly non-structural) impls are collected — exactly
/// the types whose `==`/`!=` operator must fail closed rather than structural-lower.
fn collect_manual_partial_eq_impls(items: &[syn::Item], out: &mut BTreeSet<String>) {
    for item in items {
        match item {
            syn::Item::Impl(item_impl) => {
                // A trait impl `impl [<..>] PartialEq [<..>] for T`, not a negative
                // `impl !PartialEq`. `item_impl.trait_` is `Some((polarity, path, _))`.
                if let Some((polarity, trait_path, _)) = &item_impl.trait_ {
                    let is_partial_eq = polarity.is_none()
                        && trait_path
                            .segments
                            .last()
                            .is_some_and(|seg| seg.ident == "PartialEq");
                    if is_partial_eq {
                        if let syn::Type::Path(type_path) = item_impl.self_ty.as_ref() {
                            if let Some(seg) = type_path.path.segments.last() {
                                out.insert(seg.ident.to_string());
                            }
                        }
                    }
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    collect_manual_partial_eq_impls(inner_items, out);
                }
            }
            _ => {}
        }
    }
}

fn collect_source_types_from_items(
    items: &[syn::Item],
    structs: &mut BTreeMap<String, SourceStructTemplate>,
    enums: &mut BTreeMap<String, SourceEnumTemplate>,
    type_aliases: &mut BTreeMap<String, SourceTypeAliasTemplate>,
) {
    for item in items {
        match item {
            syn::Item::Struct(item_struct) => {
                if let Some(template) = SourceStructTemplate::from_item_struct(item_struct) {
                    structs.entry(template.name.clone()).or_insert(template);
                }
            }
            syn::Item::Enum(item_enum) => {
                if let Some(template) = SourceEnumTemplate::from_item_enum(item_enum) {
                    enums.entry(template.name.clone()).or_insert(template);
                }
            }
            syn::Item::Type(item_type) => {
                if let Some(template) = SourceTypeAliasTemplate::from_item_type(item_type) {
                    type_aliases
                        .entry(template.name.clone())
                        .or_insert(template);
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    collect_source_types_from_items(inner_items, structs, enums, type_aliases);
                }
            }
            _ => {}
        }
    }
}

impl SourceStructTemplate {
    fn from_item_struct(item: &syn::ItemStruct) -> Option<Self> {
        let fields = match &item.fields {
            syn::Fields::Named(named) => named
                .named
                .iter()
                .filter_map(|field| {
                    field
                        .ident
                        .as_ref()
                        .map(|ident| (ident.to_string(), field.ty.clone()))
                })
                .collect(),
            syn::Fields::Unnamed(unnamed) => unnamed
                .unnamed
                .iter()
                .enumerate()
                .map(|(index, field)| (index.to_string(), field.ty.clone()))
                .collect(),
            syn::Fields::Unit => Vec::new(),
        };
        let generic_params = item
            .generics
            .params
            .iter()
            .filter_map(|param| {
                if let syn::GenericParam::Type(type_param) = param {
                    Some(type_param.ident.to_string())
                } else {
                    None
                }
            })
            .collect();
        Some(Self {
            name: item.ident.to_string(),
            generic_params,
            fields,
            derived_partial_eq: attrs_derive_trait(&item.attrs, "PartialEq"),
            derived_clone: attrs_derive_trait(&item.attrs, "Clone"),
        })
    }
}

impl SourceEnumTemplate {
    fn from_item_enum(item: &syn::ItemEnum) -> Option<Self> {
        if item.generics.where_clause.is_some() {
            return None;
        }
        let generic_params = item
            .generics
            .params
            .iter()
            .map(|param| match param {
                syn::GenericParam::Type(type_param) => Some(type_param.ident.to_string()),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        let enum_name = item.ident.to_string();
        let has_explicit_discriminants = item
            .variants
            .iter()
            .any(|variant| variant.discriminant.is_some());
        if has_explicit_discriminants
            && item
                .variants
                .iter()
                .any(|variant| !matches!(variant.fields, syn::Fields::Unit))
        {
            return None;
        }
        let mut variants = Vec::with_capacity(item.variants.len());
        for variant in &item.variants {
            let fields = source_enum_variant_fields(&variant.fields)?;
            // Self-referential variant fields (mentioning the enum's own name or
            // `Self`, e.g. `Succ(Box<Nat>)`) are RETAINED. The recursion edge is
            // materialised as a `RecursiveRef` to the owning datatype during type
            // resolution (`to_datatype_type_inner`); the encoder's native datatype
            // theory plus the `dt_size` acyclicity invariant already model
            // well-founded self-recursion. We no longer fail closed on the mere
            // presence of a self-reference. Mutual recursion and negative-position
            // self-references remain fail-closed downstream (they never produce a
            // self-pointing `RecursiveRef`, so they resolve to opaque / `None`).
            variants.push(SourceEnumVariantTemplate {
                name: variant.ident.to_string(),
                fields,
            });
        }
        if variants.is_empty() {
            return None;
        }
        Some(Self {
            name: enum_name,
            generic_params,
            variants,
            derived_partial_eq: attrs_derive_trait(&item.attrs, "PartialEq"),
            derived_clone: attrs_derive_trait(&item.attrs, "Clone"),
        })
    }
}

fn source_enum_variant_fields(fields: &syn::Fields) -> Option<Vec<(String, Type)>> {
    match fields {
        syn::Fields::Named(named) => Some(
            named
                .named
                .iter()
                .map(|field| {
                    field
                        .ident
                        .as_ref()
                        .map(|ident| (ident.to_string(), field.ty.clone()))
                })
                .collect::<Option<Vec<_>>>()?,
        ),
        syn::Fields::Unnamed(unnamed) => Some(
            unnamed
                .unnamed
                .iter()
                .enumerate()
                .map(|(index, field)| (index.to_string(), field.ty.clone()))
                .collect(),
        ),
        syn::Fields::Unit => Some(Vec::new()),
    }
}

/// Strips transparent ownership/heap indirections (`&T`, `&mut T`, `Box<T>`,
/// `Rc<T>`, `Arc<T>`) down to the underlying type, applied repeatedly.
///
/// These wrappers carry no ghost-level meaning: the IR models datatype recursion
/// DIRECTLY via [`TrustVcType::RecursiveRef`], so a recursive field written
/// `Box<Nat>` denotes the carrier `Nat`. We unwrap them only to recognise the
/// recursion edge; non-recursive boxed fields are left to ordinary resolution.
fn strip_transparent_indirection(ty: &Type) -> &Type {
    let mut current = ty;
    loop {
        match current {
            Type::Reference(reference) => current = &reference.elem,
            Type::Path(type_path) if type_path.qself.is_none() => {
                let Some(segment) = type_path.path.segments.last() else {
                    return current;
                };
                if !matches!(segment.ident.to_string().as_str(), "Box" | "Rc" | "Arc") {
                    return current;
                }
                let syn::PathArguments::AngleBracketed(args) = &segment.arguments else {
                    return current;
                };
                let mut type_args = args.args.iter().filter_map(|arg| match arg {
                    syn::GenericArgument::Type(inner) => Some(inner),
                    _ => None,
                });
                match (type_args.next(), type_args.next()) {
                    (Some(inner), None) => current = inner,
                    _ => return current,
                }
            }
            _ => return current,
        }
    }
}

/// Returns true when `ty`, after stripping transparent indirections, is a DIRECT
/// self-reference to the datatype `enum_name` carrying `generic_params` — i.e.
/// regular recursion where the type arguments are exactly the datatype's own
/// parameters, in order (e.g. `enum List<T> { Cons(T, Box<List<T>>) }`), or the
/// bare `Self` alias, or a non-generic self-mention (`enum Nat { Succ(Box<Nat>) }`).
///
/// It deliberately does NOT match a field naming a different type (mutual
/// recursion stays fail-closed) nor an irregular/polymorphic recursive
/// instantiation such as `List<Box<T>>` (left to ordinary resolution, which fails
/// closed). This is the only place the source→IR bridge introduces a recursion
/// edge, so it is intentionally conservative.
fn is_self_reference(ty: &Type, enum_name: &str, generic_params: &[String]) -> bool {
    let inner = strip_transparent_indirection(ty);
    let Type::Path(type_path) = inner else {
        return false;
    };
    if type_path.qself.is_some() {
        return false;
    }
    let Some(segment) = type_path.path.segments.last() else {
        return false;
    };
    let ident = segment.ident.to_string();
    if ident == "Self" {
        // `Self` denotes the enclosing datatype with its own parameters.
        return matches!(segment.arguments, syn::PathArguments::None);
    }
    if ident != enum_name {
        return false;
    }
    match &segment.arguments {
        syn::PathArguments::None => generic_params.is_empty(),
        syn::PathArguments::AngleBracketed(args) => {
            let arg_idents: Vec<String> = args
                .args
                .iter()
                .filter_map(|arg| match arg {
                    syn::GenericArgument::Type(Type::Path(path)) => {
                        path.path.get_ident().map(ToString::to_string)
                    }
                    _ => None,
                })
                .collect();
            arg_idents.len() == args.args.len()
                && arg_idents.len() == generic_params.len()
                && arg_idents
                    .iter()
                    .zip(generic_params)
                    .all(|(arg, param)| arg == param)
        }
        syn::PathArguments::Parenthesized(_) => false,
    }
}

impl SourceTypeAliasTemplate {
    fn from_item_type(item: &syn::ItemType) -> Option<Self> {
        let generic_params = item
            .generics
            .params
            .iter()
            .filter_map(|param| {
                if let syn::GenericParam::Type(type_param) = param {
                    Some(type_param.ident.to_string())
                } else {
                    None
                }
            })
            .collect();
        Some(Self {
            name: item.ident.to_string(),
            generic_params,
            target: (*item.ty).clone(),
        })
    }
}

fn generic_type_args(arguments: &syn::PathArguments) -> Option<Vec<Type>> {
    match arguments {
        syn::PathArguments::None => Some(Vec::new()),
        syn::PathArguments::AngleBracketed(args) => args
            .args
            .iter()
            .map(|arg| match arg {
                syn::GenericArgument::Type(ty) => Some(ty.clone()),
                _ => None,
            })
            .collect(),
        syn::PathArguments::Parenthesized(_) => None,
    }
}

#[derive(Clone)]
struct SourceTraitTemplate {
    name: String,
    generic_params: Vec<String>,
    methods: BTreeMap<String, SourceTraitMethod>,
}

#[derive(Clone)]
struct SourceTraitMethod {
    params: Vec<(String, Type)>,
    return_ty: Type,
}

#[derive(Clone, Default)]
struct SourceTraitRegistry {
    traits: BTreeMap<String, SourceTraitTemplate>,
}

impl SourceTraitRegistry {
    fn from_file(file: &File) -> Self {
        let mut registry = Self::default();
        collect_source_traits_from_items(&file.items, &mut registry.traits, &mut Vec::new());
        registry
    }

    fn apply_referenced_associated_fns(
        &self,
        func: &ItemFn,
        source_structs: Option<&SourceStructRegistry>,
        vc: &mut VerificationContext,
    ) {
        let mut collector = AssociatedTraitFnCallCollector::default();
        for attr in &func.attrs {
            if let Some(name) = path_last_segment(attr.path()) {
                if name == "contract" {
                    if let Ok(clauses) = attr
                        .parse_args_with(
                            syn::punctuated::Punctuated::<
                                AssociatedTraitContractClause,
                                syn::Token![,],
                            >::parse_terminated,
                        )
                        .map(|clauses| clauses.into_iter().collect::<Vec<_>>())
                    {
                        for clause in clauses {
                            for expr in clause.args {
                                collector.visit_expr(&expr);
                            }
                        }
                    }
                } else if matches!(name.as_str(), "requires" | "ensures" | "recommends") {
                    if let Ok(expr) = attr.parse_args::<Expr>() {
                        collector.visit_expr(&expr);
                    }
                }
            }
        }
        collector.visit_block(&func.block);

        for call in collector.calls {
            let Some((return_ty, params)) = self.resolve_call(&call, source_structs) else {
                continue;
            };
            vc.declare_helper_function_typed(&call.fn_name, return_ty, params);
        }
    }

    fn associated_fn_helpers_in_expr_fail_closed(
        &self,
        expr: &Expr,
        source_structs: Option<&SourceStructRegistry>,
        context: &'static str,
    ) -> TrustVcResult<AssociatedHelperSignatures> {
        let mut collector = AssociatedTraitFnCallCollector::default();
        collector.visit_expr(expr);

        let mut helpers = BTreeMap::new();
        for call in collector.calls {
            let signature = self.resolve_call_fail_closed(&call, source_structs, context)?;
            merge_associated_helper_signature(
                &mut helpers,
                call.fn_name.clone(),
                signature,
                context,
            )?;
        }

        Ok(helpers)
    }

    fn resolve_call_fail_closed(
        &self,
        call: &AssociatedTraitFnCall,
        source_structs: Option<&SourceStructRegistry>,
        context: &'static str,
    ) -> TrustVcResult<(TrustVcType, Vec<(String, TrustVcType)>)> {
        let Some((return_ty, params)) = self.resolve_call(call, source_structs) else {
            return Err(TrustVcError::Encoding {
                context,
                detail: format!(
                    "Could not resolve associated trait function `{}` for trait `{}` from source trait \
                     declarations; TrustVc fails closed instead of assuming an untyped helper",
                    call.fn_name, call.trait_path
                ),
            });
        };

        if return_ty.contains_opaque() {
            return Err(TrustVcError::Encoding {
                context,
                detail: format!(
                    "Associated trait function `{}` resolved to unsupported return type `{}`",
                    call.fn_name,
                    return_ty.to_type_string()
                ),
            });
        }
        if let Some((param_name, param_ty)) = params
            .iter()
            .find(|(_, param_ty)| param_ty.contains_opaque())
        {
            return Err(TrustVcError::Encoding {
                context,
                detail: format!(
                    "Associated trait function `{}` resolved unsupported parameter type `{}` \
                     for `{}`",
                    call.fn_name,
                    param_ty.to_type_string(),
                    param_name
                ),
            });
        }

        Ok((return_ty, params))
    }

    fn resolve_call(
        &self,
        call: &AssociatedTraitFnCall,
        source_structs: Option<&SourceStructRegistry>,
    ) -> Option<(TrustVcType, Vec<(String, TrustVcType)>)> {
        let trait_template = self.traits.get(&call.trait_path)?;
        let method = trait_template.methods.get(&call.method_name)?;
        if call.trait_args.len() != trait_template.generic_params.len() {
            return None;
        }

        let substitutions = trait_template
            .generic_params
            .iter()
            .cloned()
            .zip(
                call.trait_args
                    .iter()
                    .map(|ty| resolve_type_with_substitutions(ty, &HashMap::new(), source_structs)),
            )
            .collect::<HashMap<_, _>>();
        let return_ty =
            resolve_type_with_substitutions(&method.return_ty, &substitutions, source_structs);
        let params = method
            .params
            .iter()
            .map(|(name, ty)| {
                (
                    name.clone(),
                    resolve_type_with_substitutions(ty, &substitutions, source_structs),
                )
            })
            .collect();
        Some((return_ty, params))
    }
}

#[derive(Clone)]
struct AssociatedTraitFnCall {
    fn_name: String,
    trait_path: String,
    trait_args: Vec<Type>,
    method_name: String,
}

struct AssociatedTraitContractClause {
    args: Vec<Expr>,
}

impl syn::parse::Parse for AssociatedTraitContractClause {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        let _name: syn::Ident = input.parse()?;
        let content;
        syn::parenthesized!(content in input);
        let args = syn::punctuated::Punctuated::<Expr, syn::Token![,]>::parse_terminated(&content)?;
        Ok(Self {
            args: args.into_iter().collect(),
        })
    }
}

#[derive(Default)]
struct AssociatedTraitFnCallCollector {
    calls: Vec<AssociatedTraitFnCall>,
}

impl<'ast> Visit<'ast> for AssociatedTraitFnCallCollector {
    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        if let syn::Expr::Path(path) = &*call.func {
            if let Some(associated_call) = associated_trait_fn_call_from_path(path) {
                self.calls.push(associated_call);
            }
        }
        syn::visit::visit_expr_call(self, call);
    }
}

fn associated_trait_fn_call_from_path(path: &syn::ExprPath) -> Option<AssociatedTraitFnCall> {
    path.qself.as_ref()?;
    let method_segment = path.path.segments.last()?;
    let trait_segments = path
        .path
        .segments
        .iter()
        .take(path.path.segments.len().checked_sub(1)?)
        .collect::<Vec<_>>();
    let trait_segment = trait_segments.last()?;
    let trait_args = generic_type_args(&trait_segment.arguments).unwrap_or_default();
    let trait_path = trait_segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>()
        .join("::");
    Some(AssociatedTraitFnCall {
        fn_name: expr_path_to_string(path),
        trait_path,
        trait_args,
        method_name: method_segment.ident.to_string(),
    })
}

fn collect_source_traits_from_items(
    items: &[syn::Item],
    traits: &mut BTreeMap<String, SourceTraitTemplate>,
    module_path: &mut Vec<String>,
) {
    for item in items {
        match item {
            syn::Item::Trait(item_trait) => {
                if let Some(template) = SourceTraitTemplate::from_item_trait(item_trait) {
                    let key = if module_path.is_empty() {
                        template.name.clone()
                    } else {
                        format!("{}::{}", module_path.join("::"), template.name)
                    };
                    traits.entry(key).or_insert(template);
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    module_path.push(module.ident.to_string());
                    collect_source_traits_from_items(inner_items, traits, module_path);
                    module_path.pop();
                }
            }
            _ => {}
        }
    }
}

impl SourceTraitTemplate {
    fn from_item_trait(item: &syn::ItemTrait) -> Option<Self> {
        let generic_params = item
            .generics
            .params
            .iter()
            .filter_map(|param| {
                if let syn::GenericParam::Type(type_param) = param {
                    Some(type_param.ident.to_string())
                } else {
                    None
                }
            })
            .collect();
        let methods = item
            .items
            .iter()
            .filter_map(|item| match item {
                syn::TraitItem::Fn(method) => SourceTraitMethod::from_trait_item_fn(method)
                    .map(|method_def| (method.sig.ident.to_string(), method_def)),
                _ => None,
            })
            .collect();
        Some(Self {
            name: item.ident.to_string(),
            generic_params,
            methods,
        })
    }
}

impl SourceTraitMethod {
    fn from_trait_item_fn(method: &syn::TraitItemFn) -> Option<Self> {
        let return_ty = match &method.sig.output {
            syn::ReturnType::Type(_, ty) => (**ty).clone(),
            syn::ReturnType::Default => syn::parse_str::<Type>("()").ok()?,
        };
        let params = method
            .sig
            .inputs
            .iter()
            .enumerate()
            .filter_map(|(index, input)| match input {
                FnArg::Receiver(_) => None,
                FnArg::Typed(pat_type) => {
                    let name = match pat_type.pat.as_ref() {
                        syn::Pat::Ident(pat_ident) => pat_ident.ident.to_string(),
                        _ => format!("arg{index}"),
                    };
                    Some((name, (*pat_type.ty).clone()))
                }
            })
            .collect();
        Some(Self { params, return_ty })
    }
}

fn resolve_type_with_substitutions(
    ty: &Type,
    substitutions: &HashMap<String, TrustVcType>,
    source_structs: Option<&SourceStructRegistry>,
) -> TrustVcType {
    let ty_str = type_string_with_substitutions(ty, substitutions);
    source_structs
        .and_then(|registry| registry.resolve_type_string(&ty_str))
        .unwrap_or_else(|| TrustVcType::parse_or_opaque(&ty_str))
}

fn type_string_with_substitutions(
    ty: &Type,
    substitutions: &HashMap<String, TrustVcType>,
) -> String {
    match ty {
        Type::Reference(reference) => {
            type_string_with_substitutions(&reference.elem, substitutions)
        }
        Type::Path(type_path) if type_path.qself.is_none() => {
            if type_path.path.segments.len() == 1 {
                let segment = &type_path.path.segments[0];
                if matches!(segment.arguments, syn::PathArguments::None) {
                    if let Some(substitution) = substitutions.get(&segment.ident.to_string()) {
                        return substitution.to_type_string();
                    }
                }
            }
            type_path
                .path
                .segments
                .iter()
                .map(|segment| {
                    let ident = segment.ident.to_string();
                    match &segment.arguments {
                        syn::PathArguments::AngleBracketed(args) => {
                            let rendered_args = args
                                .args
                                .iter()
                                .map(|arg| match arg {
                                    syn::GenericArgument::Type(ty) => {
                                        type_string_with_substitutions(ty, substitutions)
                                    }
                                    _ => quote!(#arg).to_string().replace(' ', ""),
                                })
                                .collect::<Vec<_>>()
                                .join(", ");
                            format!("{ident}<{rendered_args}>")
                        }
                        _ => ident,
                    }
                })
                .collect::<Vec<_>>()
                .join("::")
        }
        _ => quote!(#ty).to_string().replace(' ', ""),
    }
}

fn collect_referenced_sibling_helper_contracts(
    file: &File,
    target_func: &ItemFn,
    ctx: &VerificationContext,
) -> TrustVcResult<BTreeMap<String, body_extract::HelperCallContract>> {
    let aliases = block_use_function_aliases(&target_func.block);
    let source_functions = SourceFunctionRegistry::from_file(file);
    // SOUNDNESS (round-8 mutual-recursion lemma class): a proof/broadcast lemma
    // in an ill-founded recursion cycle proves its own `ensures` only circularly
    // from a mutual partner's assumed (equally unproven) postcondition. Trusting
    // that `ensures` at a call site lets a false fact propagate. Drop the
    // postcondition for such helpers (the call is treated as an opaque no-op);
    // requires are KEPT (the caller must still discharge them — fail closed).
    let ill_founded = ill_founded_recursive_function_names(file, ctx);
    // Resolve the target's aliases exactly once, at the root body edge. A
    // dependency found in a sibling helper belongs to that HELPER's lexical
    // scope and must never be resolved through the target's alias table.
    let mut pending = referenced_helper_calls(target_func)
        .into_iter()
        .map(|reference| source_reference_with_aliases(reference, &aliases))
        .collect::<BTreeSet<_>>();
    let no_aliases = BTreeMap::new();
    let mut visited = BTreeSet::new();
    let mut contracts = BTreeMap::new();

    while let Some(reference) = pending.iter().next().cloned() {
        pending.remove(&reference);
        if !visited.insert(reference.clone()) {
            continue;
        }
        let Some(helper) = resolve_non_spec_source_function(
            &source_functions,
            &no_aliases,
            &reference.source_path,
            target_func,
        ) else {
            continue;
        };
        if let Some(mut contract) = helper_call_contract_from_item_fn(helper)? {
            if ill_founded.contains(&helper.sig.ident.to_string()) {
                contract.ensures.clear();
            }
            if !(contract.requires.is_empty() && contract.ensures.is_empty()) {
                contracts.insert(reference.call_symbol.clone(), contract);
            }
        }
        let helper_aliases = block_use_function_aliases(&helper.block);
        for dependency in referenced_helper_calls(helper) {
            let dependency = source_reference_with_aliases(dependency, &helper_aliases);
            if resolve_non_spec_source_function(
                &source_functions,
                &no_aliases,
                &dependency.source_path,
                target_func,
            )
            .is_some()
                && !visited.contains(&dependency)
            {
                pending.insert(dependency);
            }
        }
    }

    Ok(contracts)
}

/// For every free function CALLED in `target_func`'s body and resolvable to a
/// same-file source function, record which of its positional parameters are
/// `&mut` references — keyed by the call symbol exactly as
/// [`call_function_symbol`] renders it.
///
/// SOUNDNESS-CRITICAL (free-call `&mut`-argument framing): a contract-less
/// `fn push_helper(v: &mut Vec<u64>) { v.push(1) }` mutates its referent through
/// the `&mut` argument, but the caller's body model dropped that effect — a
/// post-call read of the argument saw the stale pre-call entry snapshot, a real
/// false `Verified`. The body extractor uses this map to HAVOC the referent of
/// each `&mut`-passed argument at an opaque free call (and to add it to the
/// loop-frame / branch-join modified set). The callee SIGNATURE is required to
/// distinguish a mutating `&mut` argument from a `&`-shared read
/// (`read_helper(v: &Vec<u64>)`), which is syntactically identical at the call
/// site (`f(v)`) but must NOT havoc — so this is what keeps the fix free of
/// over-rejection. A receiver (`self`) param is never a positional argument and
/// is recorded `false`. Only entries with at least one `&mut` position are kept.
fn collect_referenced_sibling_mut_ref_call_args(
    file: &File,
    target_func: &ItemFn,
) -> BTreeMap<String, Vec<bool>> {
    let aliases = block_use_function_aliases(&target_func.block);
    let source_functions = SourceFunctionRegistry::from_file(file);
    let mut out = BTreeMap::new();
    for reference in referenced_helper_calls(target_func) {
        let Some(helper) = resolve_non_spec_source_function(
            &source_functions,
            &aliases,
            &reference.source_path,
            target_func,
        ) else {
            continue;
        };
        let mut_flags: Vec<bool> = helper
            .sig
            .inputs
            .iter()
            .map(|input| match input {
                FnArg::Typed(pat_type) => {
                    matches!(&*pat_type.ty, Type::Reference(r) if r.mutability.is_some())
                }
                FnArg::Receiver(receiver) => {
                    receiver.mutability.is_some() && receiver.reference.is_some()
                }
            })
            .collect();
        if mut_flags.iter().any(|is_mut| *is_mut) {
            out.insert(reference.call_symbol.clone(), mut_flags);
        }
    }
    out
}

fn resolve_non_spec_source_function<'a>(
    source_functions: &'a SourceFunctionRegistry,
    aliases: &BTreeMap<String, String>,
    source_path: &str,
    target_func: &ItemFn,
) -> Option<&'a ItemFn> {
    let resolved_path = aliases
        .get(source_path)
        .map(String::as_str)
        .unwrap_or(source_path);
    let helper = source_functions.get(resolved_path)?;
    if helper.sig.ident == target_func.sig.ident || has_spec_attr(&helper.attrs) {
        return None;
    }
    Some(helper)
}

fn reject_helper_contract_calls_in_target_contracts(
    target_func: &ItemFn,
    helper_contracts: &BTreeMap<String, body_extract::HelperCallContract>,
) -> TrustVcResult<()> {
    if helper_contracts.is_empty() {
        return Ok(());
    }

    for reference in referenced_target_contract_calls(target_func)? {
        if helper_contracts
            .get(&reference.call_symbol)
            .is_some_and(|contract| contract.allow_in_spec)
        {
            continue;
        }
        if helper_contracts.contains_key(&reference.call_symbol) {
            return Err(TrustVcError::Encoding {
                context: "extract sibling helper call contracts",
                detail: format!(
                    "Unsupported call to sibling helper `{}` inside target requires/ensures; \
                     helper call contracts are only propagated from function bodies, so TrustVc \
                     fails closed here instead of verifying with incomplete call-site obligations",
                    reference.call_symbol
                ),
            });
        }
    }

    Ok(())
}

fn apply_when_used_as_spec_contract_functions(
    file: &File,
    target_func: &ItemFn,
    source_structs: Option<&SourceStructRegistry>,
    vc: &mut VerificationContext,
) -> TrustVcResult<()> {
    let source_functions = SourceFunctionRegistry::from_file(file);
    let spec_catalog = crate::spec_function_catalog::SpecFunctionCatalog::from_file(file);
    // Contract attributes and a helper's `when_used_as_spec` attribute both
    // live outside the target BODY. Neither may resolve through its block-local
    // imports.
    let no_aliases = BTreeMap::new();

    for reference in referenced_target_contract_calls(target_func)? {
        let Some(exec_helper) = resolve_non_spec_source_function(
            &source_functions,
            &no_aliases,
            &reference.source_path,
            target_func,
        ) else {
            continue;
        };
        let Some(spec_path) = when_used_as_spec_target_path(&exec_helper.attrs)? else {
            continue;
        };
        let Some(spec_helper) = source_functions.get(&spec_path) else {
            return Err(TrustVcError::Encoding {
                context: "extract when_used_as_spec helper",
                detail: format!(
                    "cannot find function `{spec_path}` referred to in when_used_as_spec"
                ),
            });
        };
        if !has_spec_attr(&spec_helper.attrs) {
            return Err(TrustVcError::Encoding {
                context: "extract when_used_as_spec helper",
                detail: "when_used_as_spec must point from an exec function to a spec function"
                    .to_string(),
            });
        }
        // Keep the exact source path as the solver identity. Collapsing
        // `nested::model` to the bare ident `model` can select a different
        // top-level spec with the same leaf and prove the wrong contract.
        let spec_name = spec_path.clone();
        if !spec_catalog.apply_explicit_spec(&spec_name, vc)? {
            return Err(TrustVcError::Encoding {
                context: "extract when_used_as_spec helper",
                detail: format!("cannot register spec function `{spec_name}`"),
            });
        }
        let def = SiblingHelperDef::from_when_used_as_spec_with_name(
            &reference.call_symbol,
            exec_helper,
            spec_helper,
            &spec_name,
            source_structs,
            vc,
        )?;
        def.apply_to_context(vc);
    }

    Ok(())
}

fn referenced_target_contract_calls(
    target_func: &ItemFn,
) -> TrustVcResult<BTreeSet<SourceCallReference>> {
    let mut collector = HelperCallCollector::default();

    for attr in &target_func.attrs {
        match path_last_segment(attr.path()).as_deref() {
            Some("requires" | "ensures" | "recommends" | "decreases") => {
                let expr =
                    contract_attribute_expr(attr).map_err(|source| TrustVcError::Encoding {
                        context: "extract sibling helper call contracts",
                        detail: format!(
                            "Failed to parse target contract attribute while checking sibling helper calls: {source}"
                        ),
                    })?;
                collector.visit_expr(&expr);
            }
            Some("contract") => {
                for clause in parse_target_contract_clauses(attr)? {
                    for expr in clause.args {
                        collector.visit_expr(&expr);
                    }
                }
            }
            _ => {}
        }
    }

    Ok(collector.calls)
}

/// Parse the parenthesized expression of a `#[requires(..)]` / `#[ensures(..)]`
/// attribute, normalizing Verus surface syntax (chained comparisons and
/// bar-delimited quantifier closures such as `exists |n: T| body`) into forms
/// `syn` accepts. This mirrors how `forall`/`exists` call-forms are parsed
/// elsewhere; the bar-delimited closure is Verus's canonical surface, so it
/// must lower identically to the call form `exists(|n: T| body)`.
fn contract_attribute_expr(attr: &syn::Attribute) -> syn::Result<Expr> {
    let syn::Meta::List(meta_list) = &attr.meta else {
        return Err(syn::Error::new_spanned(
            attr,
            "contract attribute must use parenthesized form, e.g. `#[ensures(expr)]`",
        ));
    };
    crate::chained_comparisons::parse_expr_tokens_with_chains(clause_tokens_without_proof_note(
        meta_list.tokens.clone(),
    ))
}

/// Drops leading `#![verifier::proof_note("…")]` / `custom_err` inner attrs
/// from a contract-clause token stream so the SECONDARY clause consumers
/// (sibling helper-call collection, spec-recommends collection, name-form
/// collection) parse a labeled clause exactly like its unlabeled twin. Label
/// SEMANTICS (pooling, at-most-one, obligation attachment) live solely in
/// `attr_extract` — this helper only keeps the collectors in sync. A
/// malformed recognized label keeps the original tokens, so those consumers
/// fail closed with their original messages.
fn clause_tokens_without_proof_note(tokens: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    match crate::proof_note::peel_leading_inner_proof_note_attrs(tokens.clone()) {
        Ok((_labels, rest)) => rest,
        Err(_) => tokens,
    }
}

/// Lenient clause-expression parse for best-effort collectors: peels a
/// leading proof-note inner attr, then parses a plain `Expr`. Returns `None`
/// on any failure (the collectors treat an unparseable clause as
/// contributing nothing, exactly as before).
fn contract_attr_expr_lenient(attr: &syn::Attribute) -> Option<Expr> {
    let syn::Meta::List(meta_list) = &attr.meta else {
        return None;
    };
    syn::parse2::<Expr>(clause_tokens_without_proof_note(meta_list.tokens.clone())).ok()
}

struct TargetContractClause {
    name: syn::Ident,
    args: Vec<Expr>,
}

impl syn::parse::Parse for TargetContractClause {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        let name: syn::Ident = input.parse()?;
        let content;
        syn::parenthesized!(content in input);
        let args = syn::punctuated::Punctuated::<Expr, syn::Token![,]>::parse_terminated(&content)?;
        Ok(Self {
            name,
            args: args.into_iter().collect(),
        })
    }
}

fn parse_target_contract_clauses(
    attr: &syn::Attribute,
) -> TrustVcResult<Vec<TargetContractClause>> {
    attr.parse_args_with(
        syn::punctuated::Punctuated::<TargetContractClause, syn::Token![,]>::parse_terminated,
    )
    .map(|clauses| clauses.into_iter().collect())
    .map_err(|source| TrustVcError::Encoding {
        context: "extract sibling helper call contracts",
        detail: format!(
            "Failed to parse target #[contract] attribute while checking sibling helper calls: {source}"
        ),
    })
}

/// True iff `attrs` carries a `#[trust_vc::broadcast]` / `#[broadcast]` attribute
/// (NOT `#[broadcast_group]`, whose last segment differs). Part of the file-path
/// broadcast_use! wiring.
fn has_broadcast_attr(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|s| s.ident == "broadcast")
    })
}

/// The group name from a `#[trust_vc::broadcast_group(G)]` attribute, if present.
/// An ungrouped `#[broadcast]` lemma returns `None` (globally active).
fn broadcast_group_name(attrs: &[syn::Attribute]) -> Option<String> {
    attrs.iter().find_map(|attr| {
        (attr
            .path()
            .segments
            .last()
            .is_some_and(|s| s.ident == "broadcast_group"))
        .then(|| attr.parse_args::<syn::Ident>().ok().map(|i| i.to_string()))
        .flatten()
    })
}

/// The trigger pattern EXPR from a `#[trust_vc::trigger(P)]` attribute. A
/// broadcast lemma with NO explicit trigger is skipped by the collector (an
/// un-triggered axiom cannot be instantiated — inert, which is fail-safe).
fn broadcast_trigger_expr(attrs: &[syn::Attribute]) -> Option<syn::Expr> {
    attrs.iter().find_map(|attr| {
        (attr
            .path()
            .segments
            .last()
            .is_some_and(|s| s.ident == "trigger"))
        .then(|| attr.parse_args::<syn::Expr>().ok())
        .flatten()
    })
}

/// Extract the body-statement spec-clause EXPRs `trust_vc::<clause>!( EXPR )` (or
/// `trust_vc_<clause>!`) from a broadcast lemma body. Returns `(present, exprs)`:
/// `present` is true if ANY such clause statement exists (even if it fails to
/// parse — the load-bearing signal for the #NEW guard), `exprs` is `Some(all)`
/// when every occurrence parsed, else `None`. Part of the file-path broadcast_use!
/// wiring.
fn body_broadcast_clause_exprs(block: &syn::Block, clause: &str) -> (bool, Option<Vec<syn::Expr>>) {
    let trust_vc_clause = format!("trust_vc_{clause}");
    let mut present = false;
    let mut any_failed = false;
    let mut exprs = Vec::new();
    for stmt in &block.stmts {
        let mac = match stmt {
            syn::Stmt::Macro(stmt_macro) => &stmt_macro.mac,
            syn::Stmt::Expr(syn::Expr::Macro(expr_macro), _) => &expr_macro.mac,
            _ => continue,
        };
        let is_clause = mac
            .path
            .segments
            .last()
            .is_some_and(|s| s.ident == clause || s.ident == trust_vc_clause.as_str());
        if !is_clause {
            continue;
        }
        present = true;
        match crate::chained_comparisons::parse_expr_tokens_with_chains(mac.tokens.clone()) {
            Ok(expr) => exprs.push(expr),
            Err(_) => any_failed = true,
        }
    }
    if !present {
        return (false, None);
    }
    if any_failed {
        return (true, None);
    }
    (true, Some(exprs))
}

/// Renames a broadcast lemma's PARAM idents to fresh, uniquely-named bound-var
/// idents inside a clause/trigger expression, so a lemma's quantifier binders
/// never collide with another lemma's binders or with the caller's locals (the
/// "Variable already declared" hazard). Mirrors the spec-catalog fresh-binder
/// discipline. Part of the file-path broadcast_use! wiring.
struct BroadcastBoundVarRenamer {
    map: BTreeMap<String, syn::Ident>,
}

impl syn::visit_mut::VisitMut for BroadcastBoundVarRenamer {
    fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
        if let syn::Expr::Path(path_expr) = expr {
            if path_expr.qself.is_none() && path_expr.path.segments.len() == 1 {
                if let Some(fresh) = self.map.get(&path_expr.path.segments[0].ident.to_string()) {
                    path_expr.path.segments[0].ident = fresh.clone();
                }
            }
        }
        syn::visit_mut::visit_expr_mut(self, expr);
    }
}

/// Render a clause/trigger expr to a string with the lemma's params renamed to
/// their fresh bound-var idents.
fn render_broadcast_clause(mut expr: syn::Expr, renamer: &mut BroadcastBoundVarRenamer) -> String {
    use syn::visit_mut::VisitMut;
    renamer.visit_expr_mut(&mut expr);
    expr.to_token_stream().to_string()
}

/// Conjoin rendered clause strings into one condition (`(a) && (b) && …`).
fn conjoin_broadcast_clauses(parts: Vec<String>) -> String {
    if parts.len() == 1 {
        parts.into_iter().next().unwrap_or_default()
    } else {
        parts
            .into_iter()
            .map(|p| format!("({p})"))
            .collect::<Vec<_>>()
            .join(" && ")
    }
}

/// Collect file-local `#[trust_vc::broadcast]` lemmas into grouped (or global)
/// `BroadcastAssume` axioms so `broadcast_use!{ group }` can ACTIVATE them on the
/// FILE-EXTRACTION path. The runtime proc-macro path publishes these by EXECUTING
/// the lemma body; the file path never does, so without this collector the
/// lemma's `ensures` is never an auto-instantiated axiom (the W4 inertness).
///
/// Each lemma publishes, in effect, `forall <params>. (requires ==> ensures)` —
/// the `requires -> guard` fold (attached via `with_broadcast_guard_conditions`,
/// folded downstream in `encoder/verification/broadcast.rs`) is
/// SOUNDNESS-CRITICAL: a bare `ensures` would let a caller lacking the `requires`
/// prove the conclusion unconditionally.
///
/// SOUNDNESS (forward-only activation): each grouped axiom carries its group via
/// `with_broadcast_group`; the position-aware gate (`active_broadcast_groups_before`
/// in `setup_broadcasts.rs` / `invariants/mod.rs`) admits it ONLY for proof
/// obligations at or after a body-ordered `broadcast_use!(group)` marker — never
/// retroactively. An ungrouped lemma is global (always active).
///
/// Fails closed (does NOT publish the lemma's ensures) on:
/// - a lemma in an ILL-FOUNDED recursion cycle (ensures suppressed, exactly like
///   the call-site helper-contract path),
/// - a param that is not a simple typed ident,
/// - a missing explicit trigger (un-triggered axiom is inert = fail-safe),
/// - no `ensures` (nothing to publish), and
/// - **the #NEW GUARD**: a lemma that HAS a `requires` clause but whose guard
///   could not be rendered — never published as a bare ensures. (This closes the
///   false-verify the existing `DroppedBroadcastGuard` gate is blind to, because
///   that gate keys off an already-populated guard Vec.)
fn collect_source_broadcast_lemmas(
    file: &File,
    spec_catalog: &crate::spec_function_catalog::SpecFunctionCatalog,
    vc: &mut VerificationContext,
) -> TrustVcResult<()> {
    let ill_founded = ill_founded_recursive_function_names(file, vc);
    for item in &file.items {
        let syn::Item::Fn(item_fn) = item else {
            continue;
        };
        if !has_broadcast_attr(&item_fn.attrs) {
            continue;
        }
        let name = item_fn.sig.ident.to_string();

        // Register the spec functions this lemma's ensures/requires reference so
        // the published axiom can LOWER even when the TARGET function does not
        // itself reference them (e.g. an inactive group). This registers the
        // spec-fn return types via the same catalog path the target uses.
        spec_catalog.apply_referenced_specs(item_fn, vc)?;

        // Typed params → FRESH, uniquely-named bound vars (so a lemma's
        // quantifier binders never collide with another lemma's binders or the
        // caller's locals — the "Variable already declared" hazard). Fail closed
        // on a param that is not a simple typed ident or has no modelable sort.
        let mut typed_fresh: Vec<(syn::Ident, TrustVcType)> = Vec::new();
        let mut rename_map: BTreeMap<String, syn::Ident> = BTreeMap::new();
        let mut params_ok = true;
        for (idx, input) in item_fn.sig.inputs.iter().enumerate() {
            let syn::FnArg::Typed(pat_type) = input else {
                params_ok = false;
                break;
            };
            let syn::Pat::Ident(pat_ident) = &*pat_type.pat else {
                params_ok = false;
                break;
            };
            let rendered: String = pat_type
                .ty
                .to_token_stream()
                .to_string()
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect();
            let ty = TrustVcType::parse_or_opaque(&rendered);
            if ty.contains_opaque() {
                params_ok = false;
                break;
            }
            let fresh = syn::Ident::new(&format!("__bcq_{name}_{idx}"), pat_ident.ident.span());
            rename_map.insert(pat_ident.ident.to_string(), fresh.clone());
            typed_fresh.push((fresh, ty));
        }
        if !params_ok {
            continue;
        }
        let mut renamer = BroadcastBoundVarRenamer { map: rename_map };
        let bound_vars: Vec<String> = typed_fresh.iter().map(|(f, _)| f.to_string()).collect();

        // Trigger (required; renamed to the fresh binders).
        let Some(trigger_expr) = broadcast_trigger_expr(&item_fn.attrs) else {
            continue;
        };
        let trigger = render_broadcast_clause(trigger_expr, &mut renamer);

        // Ensures (body statements; renamed). Nothing to publish without one.
        let (_, ensures_exprs) = body_broadcast_clause_exprs(&item_fn.block, "ensures");
        let Some(ensures_exprs) = ensures_exprs.filter(|e| !e.is_empty()) else {
            continue;
        };
        let ensures_str = conjoin_broadcast_clauses(
            ensures_exprs
                .into_iter()
                .map(|e| render_broadcast_clause(e, &mut renamer))
                .collect(),
        );

        // Requires (body statements; renamed) → the guard. #NEW SOUNDNESS GUARD:
        // a lemma that HAS a requires but whose guard we could not render must
        // NOT publish a bare ensures.
        let (requires_present, requires_exprs) =
            body_broadcast_clause_exprs(&item_fn.block, "requires");
        if requires_present && requires_exprs.is_none() {
            continue;
        }
        let requires_conditions: Vec<String> = requires_exprs
            .map(|exprs| {
                exprs
                    .into_iter()
                    .map(|e| render_broadcast_clause(e, &mut renamer))
                    .collect()
            })
            .unwrap_or_default();

        // Ill-founded recursion cycle: suppress the ensures axiom entirely
        // (the requires-only fact carries no useful axiom), matching the
        // call-site path's `contract.ensures.clear()` posture.
        if ill_founded.contains(&name) {
            continue;
        }

        let axiom_name = format!("__source_broadcast_{name}");
        let mut obligation = ProofObligation::broadcast_assume(axiom_name, ensures_str)
            .with_bound_vars(bound_vars)
            .with_trigger_patterns(vec![vec![trigger]]);
        if let Some(group) = broadcast_group_name(&item_fn.attrs) {
            obligation = obligation.with_broadcast_group(group);
        }
        obligation = obligation.with_broadcast_guard_conditions(requires_conditions);

        // Belt-and-suspenders #NEW GUARD (independent of the flow above): never
        // publish a lemma that HAD a requires without a guard attached.
        if requires_present && obligation.broadcast_guard.is_none() {
            continue;
        }

        // Declare the FRESH bound-var types so the quantified axiom body
        // (`ensures` / `guard`) lowers — the lowerer resolves each bound var's
        // sort from the declared type, as the spec-fn body-axiom publisher does.
        for (fresh, ty) in &typed_fresh {
            vc.declare_var_typed(&fresh.to_string(), ty.clone());
        }
        vc.push_obligation(obligation);
    }
    Ok(())
}

fn helper_call_contract_from_item_fn(
    item_fn: &ItemFn,
) -> TrustVcResult<Option<body_extract::HelperCallContract>> {
    let Some((params, erased_shared_ref_params, mut_ref_scalar_params)) =
        helper_contract_params(&item_fn.sig)
    else {
        return Ok(None);
    };
    let (requires, ensures) =
        helper_contract_clauses_from_attrs(&item_fn.attrs, Some(&item_fn.sig))?;
    if requires.is_empty() && ensures.is_empty() {
        return Ok(None);
    }
    let return_binding = attr_extract::extract_return_binding(&item_fn.attrs, Some(&item_fn.sig))?
        .unwrap_or_else(|| "result".to_string());
    Ok(Some(body_extract::HelperCallContract {
        params,
        erased_shared_ref_params,
        mut_ref_scalar_params,
        return_binding,
        requires,
        ensures,
        allow_in_spec: has_allow_in_spec_attr(&item_fn.attrs),
    }))
}

fn helper_contract_params(sig: &syn::Signature) -> Option<(Vec<String>, Vec<bool>, Vec<bool>)> {
    let mut names = Vec::with_capacity(sig.inputs.len());
    let mut erased_shared_refs = Vec::with_capacity(sig.inputs.len());
    let mut mut_ref_scalars = Vec::with_capacity(sig.inputs.len());
    for input in &sig.inputs {
        let FnArg::Typed(pat_type) = input else {
            return None;
        };
        let syn::Pat::Ident(pat_ident) = &*pat_type.pat else {
            return None;
        };
        names.push(pat_ident.ident.to_string());
        erased_shared_refs.push(param_extract::is_erased_shared_ref_type(&pat_type.ty));
        // A `&mut <bool/integer>` parameter position: the caller-side contract
        // substitution binds its VALUE (referent) renderings — pre-call for
        // `requires`/`old(P)`, the fresh post-call symbol for bare `P` in
        // `ensures` (slice D of the mut-ref two-state keystone).
        mut_ref_scalars.push(param_extract::is_supported_mut_ref_scalar_type(
            &pat_type.ty,
        ));
    }
    Some((names, erased_shared_refs, mut_ref_scalars))
}

fn helper_has_requires_clause(attrs: &[syn::Attribute]) -> TrustVcResult<bool> {
    let (requires, _) = helper_contract_clauses_from_attrs(attrs, None)?;
    Ok(!requires.is_empty())
}

/// The conjoined `requires` guard of a method, with `self`/params renamed to their
/// axiom bound names (`rename_map`) — so a requires-bearing inherent method's body
/// axiom can be published GUARDED (`guard ==> method == body`) instead of
/// unconditionally. Returns `None` if there is no requires clause or any clause
/// fails to extract, in which case the caller declines the body axiom (fail-closed
/// — never publish an UNGUARDED body for a requires-bearing method).
fn renamed_requires_guard(
    attrs: &[syn::Attribute],
    sig: &syn::Signature,
    rename_map: &HashMap<String, String>,
) -> Option<String> {
    let (requires, _) = helper_contract_clauses_from_attrs(attrs, Some(sig)).ok()?;
    if requires.is_empty() {
        return None;
    }
    let mut parts = Vec::with_capacity(requires.len());
    for clause in &requires {
        let mut condition = clause.condition.clone();
        IdentRenamer {
            rename_map: rename_map.clone(),
        }
        .visit_expr_mut(&mut condition);
        parts.push(format!("({})", quote!(#condition)));
    }
    Some(parts.join(" && "))
}

/// True if the trait method that `item_impl`'s `method_name` implements declares
/// a `requires` clause on the TRAIT DECLARATION (as opposed to the impl). Used to
/// keep a requires-bearing no-`self` associated method out of the unconditional
/// body-axiom registration (dropping the requires there would be a false-verify).
/// An out-of-file / unresolved trait declaration returns `false` — the caller
/// pairs this with an impl-side requires check and a no-arg gate, and a genuinely
/// requires-bearing method that can't be seen also can't be body-axiom-lowered
/// into an obligation, so it stays fail-closed regardless.
fn trait_method_declares_requires(
    file: &syn::File,
    item_impl: &syn::ItemImpl,
    method_name: &str,
) -> TrustVcResult<bool> {
    let Some((_, trait_path, _)) = &item_impl.trait_ else {
        return Ok(false);
    };
    let Some(trait_ident) = trait_path.segments.last().map(|seg| seg.ident.to_string()) else {
        return Ok(false);
    };
    for item in &file.items {
        let syn::Item::Trait(item_trait) = item else {
            continue;
        };
        if item_trait.ident != trait_ident {
            continue;
        }
        for trait_item in &item_trait.items {
            let syn::TraitItem::Fn(trait_fn) = trait_item else {
                continue;
            };
            if trait_fn.sig.ident == method_name {
                return helper_has_requires_clause(&trait_fn.attrs);
            }
        }
    }
    Ok(false)
}

/// True if the IMPL method returns a NON-primitive type — a struct/enum datatype
/// or `Self` — as opposed to a primitive scalar (`u*`/`i*`/`usize`/`isize`/`bool`/
/// `char`/`f32`/`f64`) or unit. Such a return makes the shared per-trait UF
/// incompatible (its abstract slot can't carry the concrete datatype sort — the
/// UF path skips the method), so the concrete impl method — which WRITES the
/// concrete return — is registered through its definitional body axiom instead,
/// exactly as the inherent path already handles a struct-returning method.
fn type_is_primitive_scalar(ty: &syn::Type) -> bool {
    let syn::Type::Path(type_path) = ty else {
        return false;
    };
    if type_path.qself.is_some() {
        return false;
    }
    type_path.path.get_ident().is_some_and(|ident| {
        matches!(
            ident.to_string().as_str(),
            "u8" | "u16"
                | "u32"
                | "u64"
                | "u128"
                | "usize"
                | "i8"
                | "i16"
                | "i32"
                | "i64"
                | "i128"
                | "isize"
                | "bool"
                | "char"
                | "f32"
                | "f64"
        )
    })
}

/// True for a return/parameter type the shared per-trait UF cannot handle
/// correctly but the definitional-body-axiom path CAN — a struct/enum name or
/// `Self` (bare non-primitive path), a tuple, or a generic datatype whose type
/// arguments are all primitive scalars (`Option<u64>`). A struct-typed generic
/// argument (`Option<W>`) is EXCLUDED (a deeper monomorphization axis).
fn type_routes_to_body_axiom(ty: &syn::Type) -> bool {
    match ty {
        // A shared reference (`&Other`) routes on its referent — a `&`-struct
        // parameter behaves like a by-value struct parameter in a spec context
        // (the reference is erased), and the inherent path already verifies such
        // a method.
        syn::Type::Reference(reference) => type_routes_to_body_axiom(&reference.elem),
        syn::Type::Tuple(_) => true,
        syn::Type::Path(type_path) if type_path.qself.is_none() => {
            match type_path.path.segments.last() {
                Some(seg) => match &seg.arguments {
                    syn::PathArguments::None => !type_is_primitive_scalar(ty),
                    syn::PathArguments::AngleBracketed(args) => args.args.iter().all(|arg| {
                        matches!(arg, syn::GenericArgument::Type(t) if type_is_primitive_scalar(t))
                    }),
                    syn::PathArguments::Parenthesized(_) => false,
                },
                None => false,
            }
        }
        _ => false,
    }
}

/// True if any parameter of the impl method (past the receiver) is a type routed
/// through the body axiom — a struct/enum/`Self`/tuple/primitive-arg generic. The
/// bare UF postcondition does not apply for such a parameter (NotProved), so the
/// method is registered through its definitional body axiom instead. The trait
/// method's param SORT is separately resolved (`resolve_trait_decl_param_types`)
/// so registration + encoding no longer fail-closed the whole file.
fn impl_method_has_non_primitive_param(method: &syn::ImplItemFn) -> bool {
    method.sig.inputs.iter().any(|input| match input {
        syn::FnArg::Typed(pat_ty) => type_routes_to_body_axiom(&pat_ty.ty),
        syn::FnArg::Receiver(_) => false,
    })
}

fn impl_method_returns_non_primitive(method: &syn::ImplItemFn) -> bool {
    let syn::ReturnType::Type(_, ty) = &method.sig.output else {
        return false; // `-> ()` — nothing to resolve
    };
    match &**ty {
        // A TUPLE return (`-> (u64, u64)`): the shared per-trait UF registers it
        // but does not apply the compound-return postcondition (spurious CE), so
        // route it through the body axiom like a plain struct return.
        syn::Type::Tuple(_) => true,
        syn::Type::Path(type_path) if type_path.qself.is_none() => {
            match type_path.path.segments.last() {
                Some(seg) => match &seg.arguments {
                    // A bare single-ident path — non-primitive iff not a scalar
                    // (a struct/enum name or `Self`).
                    syn::PathArguments::None => !type_is_primitive_scalar(ty),
                    // A GENERIC datatype (`-> Option<u64>`, `-> Result<u64, _>`):
                    // route it through the body axiom (same spurious-CE fix as a
                    // tuple) ONLY when every type argument is a PRIMITIVE scalar. A
                    // struct-typed argument (`Option<W>`) triggers a generic-
                    // datatype registration conflict ("conflicting variant
                    // metadata") — a deeper monomorphization axis — so leave it on
                    // the UF path (per-function fail-closed, not a whole-file error).
                    syn::PathArguments::AngleBracketed(args) => args.args.iter().all(|arg| {
                        matches!(arg, syn::GenericArgument::Type(t) if type_is_primitive_scalar(t))
                    }),
                    syn::PathArguments::Parenthesized(_) => false, // `Fn(..)`-style
                },
                None => false,
            }
        }
        _ => false, // references, `<S as T>::X` (handled elsewhere), etc.
    }
}

/// True if the TRAIT declares `method_name`'s return type as an associated-type
/// PROJECTION rooted at `Self` (`-> Self::Out` or `-> <Self as Trait>::Out`). The
/// shared per-trait UF cannot carry the per-impl-resolved sort of such a return,
/// so the concrete-receiver UF path bails; the impl's own (concrete-return) method
/// is instead registered through the definitional-body-axiom path. An out-of-file
/// / unresolved trait declaration returns `false` (the method simply stays on the
/// UF path, fail-closed).
fn trait_method_returns_assoc_type(
    file: &syn::File,
    item_impl: &syn::ItemImpl,
    method_name: &str,
) -> bool {
    let Some((_, trait_path, _)) = &item_impl.trait_ else {
        return false;
    };
    let Some(trait_ident) = trait_path.segments.last().map(|seg| seg.ident.to_string()) else {
        return false;
    };
    let is_self_projection = |ty: &syn::Type| -> bool {
        let syn::Type::Path(type_path) = ty else {
            return false;
        };
        // `<Self as Trait>::Out` — qself is `Self`.
        if let Some(qself) = &type_path.qself {
            if let syn::Type::Path(inner) = &*qself.ty {
                return inner.path.is_ident("Self");
            }
            return false;
        }
        // `Self::Out` — a bare path whose first segment is `Self` and which
        // projects at least one associated name past it.
        type_path.path.segments.len() >= 2 && type_path.path.segments[0].ident == "Self"
    };
    for item in &file.items {
        let syn::Item::Trait(item_trait) = item else {
            continue;
        };
        if item_trait.ident != trait_ident {
            continue;
        }
        for trait_item in &item_trait.items {
            let syn::TraitItem::Fn(trait_fn) = trait_item else {
                continue;
            };
            if trait_fn.sig.ident != method_name {
                continue;
            }
            let syn::ReturnType::Type(_, ty) = &trait_fn.sig.output else {
                return false;
            };
            return is_self_projection(ty);
        }
    }
    false
}

fn helper_contract_clauses_from_attrs(
    attrs: &[syn::Attribute],
    sig: Option<&syn::Signature>,
) -> TrustVcResult<(
    Vec<body_extract::HelperContractClause>,
    Vec<body_extract::HelperContractClause>,
)> {
    let solver_mode = crate::mode_attrs::extract_function_solver_mode(attrs)?;
    let mut temp = VerificationContext::new();
    attr_extract::extract_contract_attributes(attrs, &mut temp, solver_mode, sig)?;
    let mut requires = Vec::new();
    let mut ensures = Vec::new();
    for obligation in temp.obligations {
        match obligation.kind {
            ObligationKind::Assume if obligation.name == "precondition" => {
                requires.push(helper_contract_clause_from_obligation(obligation)?);
            }
            ObligationKind::Assert if obligation.name == "postcondition" => {
                ensures.push(helper_contract_clause_from_obligation(obligation)?);
            }
            ObligationKind::Recommends => {}
            _ => {}
        }
    }
    Ok((requires, ensures))
}

fn helper_contract_clause_from_obligation(
    obligation: ProofObligation,
) -> TrustVcResult<body_extract::HelperContractClause> {
    let condition = crate::chained_comparisons::parse_expr_str_with_chains(&obligation.condition)
        .map_err(|source| TrustVcError::Encoding {
        context: "extract sibling helper call contracts",
        detail: format!(
            "Failed to parse sibling helper contract clause `{}`: {}",
            obligation.condition, source
        ),
    })?;
    Ok(body_extract::HelperContractClause {
        condition,
        solver_mode: obligation.solver_mode,
        proof_note: obligation.proof_note,
    })
}

fn apply_source_spec_recommends_in_target_contracts(
    file: &File,
    target_func: &ItemFn,
    source_structs: Option<&SourceStructRegistry>,
    source_traits: Option<&SourceTraitRegistry>,
    vc: &mut VerificationContext,
) -> TrustVcResult<()> {
    let source_functions = SourceFunctionRegistry::from_file(file);
    let source_specs = source_functions
        .functions
        .iter()
        .filter_map(|(source_path, item_fn)| {
            if item_fn.sig.ident == target_func.sig.ident || !has_spec_attr(&item_fn.attrs) {
                return None;
            }
            let recommends = source_spec_recommends_from_attrs(&item_fn.attrs);
            (!recommends.is_empty()).then(|| {
                (
                    source_path.clone(),
                    SourceSpecRecommends {
                        item_fn,
                        recommends,
                    },
                )
            })
        })
        .collect::<HashMap<_, _>>();

    if source_specs.is_empty() {
        return Ok(());
    }

    let mut collector =
        SourceSpecRecommendsCallCollector::new(&source_specs, source_traits, source_structs);

    for attr in &target_func.attrs {
        match path_last_segment(attr.path()).as_deref() {
            Some("requires" | "ensures") => {
                // Peel a leading proof-note inner attr so a labeled clause
                // parses like its unlabeled twin (labels are handled in
                // attr_extract; this collector only needs the expression).
                let expr = contract_attribute_expr(attr).map_err(|source| TrustVcError::Encoding {
                    context: "extract source spec recommends call contracts",
                    detail: format!(
                        "Failed to parse target contract attribute while checking source spec recommends: {source}"
                    ),
                })?;
                collector.visit_expr(&expr);
            }
            Some("contract") => {
                for clause in parse_target_contract_clauses(attr)? {
                    if matches!(clause.name.to_string().as_str(), "requires" | "ensures") {
                        for expr in clause.args {
                            collector.visit_expr(&expr);
                        }
                    }
                }
            }
            _ => {}
        }
        if collector.error.is_some() {
            break;
        }
    }

    if collector.error.is_none() {
        collector.source_aliases = block_use_function_aliases(&target_func.block);
        collector.visit_block(&target_func.block);
    }

    if let Some(err) = collector.error {
        return Err(err);
    }

    for called_spec in collector.called_specs {
        if let Some(source_spec) = source_specs.get(&called_spec.source_path) {
            register_source_function_signature(
                &called_spec.call_symbol,
                source_spec.item_fn,
                source_structs,
                vc,
            )?;
        }
    }

    for (name, (return_ty, params)) in collector.associated_helpers {
        declare_source_spec_associated_helper_fail_closed(&name, return_ty, params, vc)?;
    }

    for obligation in collector.obligations {
        vc.push_obligation(obligation);
    }

    Ok(())
}

fn register_source_function_signature(
    name: &str,
    item_fn: &ItemFn,
    source_structs: Option<&SourceStructRegistry>,
    vc: &mut VerificationContext,
) -> TrustVcResult<()> {
    if vc.helper_functions_typed.contains_key(name) {
        return Ok(());
    }
    let return_ty =
        helper_return_type(&item_fn.sig, source_structs).ok_or_else(|| TrustVcError::Encoding {
            context: "extract source spec recommends call contracts",
            detail: format!("source spec function `{name}` has unsupported return type"),
        })?;
    let params = helper_params(&item_fn.sig, source_structs, vc)?
        .ok_or_else(|| TrustVcError::Encoding {
            context: "extract source spec recommends call contracts",
            detail: format!("source spec function `{name}` uses unsupported parameters"),
        })?
        .into_iter()
        .map(|param| (param.name, param.ty))
        .collect();
    vc.declare_helper_function_typed(name, return_ty, params);
    Ok(())
}

struct SourceSpecRecommends<'a> {
    item_fn: &'a ItemFn,
    recommends: Vec<String>,
}

struct SourceSpecRecommendsCallCollector<'a> {
    source_specs: &'a HashMap<String, SourceSpecRecommends<'a>>,
    source_traits: Option<&'a SourceTraitRegistry>,
    source_structs: Option<&'a SourceStructRegistry>,
    obligations: Vec<ProofObligation>,
    called_specs: BTreeSet<SourceCallReference>,
    associated_helpers: AssociatedHelperSignatures,
    error: Option<TrustVcError>,
    scopes: Vec<BTreeMap<String, Option<String>>>,
    quantifier_scopes: Vec<SourceSpecRecommendsQuantifierScope>,
    path_guards: Vec<String>,
    /// Active only while visiting the verified function BODY. Contract
    /// attributes were visited first with this map empty because block imports
    /// are not in their Rust scope.
    source_aliases: BTreeMap<String, String>,
}

struct SourceSpecRecommendsQuantifierScope {
    params: Vec<String>,
}

impl<'a> SourceSpecRecommendsCallCollector<'a> {
    fn new(
        source_specs: &'a HashMap<String, SourceSpecRecommends<'a>>,
        source_traits: Option<&'a SourceTraitRegistry>,
        source_structs: Option<&'a SourceStructRegistry>,
    ) -> Self {
        Self {
            source_specs,
            source_traits,
            source_structs,
            obligations: Vec::new(),
            called_specs: BTreeSet::new(),
            associated_helpers: BTreeMap::new(),
            error: None,
            scopes: vec![BTreeMap::new()],
            quantifier_scopes: Vec::new(),
            path_guards: Vec::new(),
            source_aliases: BTreeMap::new(),
        }
    }

    fn push_scope(&mut self) {
        self.scopes.push(BTreeMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn current_scope_mut(&mut self) -> &mut BTreeMap<String, Option<String>> {
        if self.scopes.is_empty() {
            self.scopes.push(BTreeMap::new());
        }
        let current = self.scopes.len() - 1;
        &mut self.scopes[current]
    }

    fn bind_local(&mut self, local: &syn::Local) {
        let value = local
            .init
            .as_ref()
            .and_then(|init| self.expr_to_scoped_string(&init.expr));
        if let Some(name) = local_ident_for_recommends(&local.pat) {
            self.current_scope_mut().insert(name, value);
        } else {
            for name in bound_idents_from_pat_for_recommends(&local.pat) {
                self.current_scope_mut().insert(name, None);
            }
        }
    }

    fn assign_local(&mut self, name: &str, value: Option<String>) {
        for scope in self.scopes.iter_mut().rev() {
            if scope.contains_key(name) {
                scope.insert(name.to_string(), value);
                return;
            }
        }
        self.current_scope_mut().insert(name.to_string(), value);
    }

    fn invalidate_local(&mut self, name: &str) {
        self.assign_local(name, None);
    }

    fn lookup_scoped(&self, name: &str) -> Option<String> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name))
            .map(|value| value.as_ref().map(|value| format!("({value})")))
            .unwrap_or_else(|| Some(name.to_string()))
    }

    fn expr_to_scoped_string(&self, expr: &Expr) -> Option<String> {
        match expr {
            Expr::Path(path) if path.qself.is_none() && path.path.segments.len() == 1 => {
                self.lookup_scoped(&path.path.segments[0].ident.to_string())
            }
            Expr::Path(path) => Some(path.path.to_token_stream().to_string()),
            Expr::Lit(_) => Some(extract_expr_string(expr)),
            Expr::Paren(paren) => Some(format!("({})", self.expr_to_scoped_string(&paren.expr)?)),
            Expr::Group(group) => self.expr_to_scoped_string(&group.expr),
            Expr::Unary(unary) => Some(format!(
                "{}{}",
                unary.op.to_token_stream(),
                self.expr_to_scoped_string(&unary.expr)?
            )),
            Expr::Binary(binary) => Some(format!(
                "{} {} {}",
                self.expr_to_scoped_string(&binary.left)?,
                binary.op.to_token_stream(),
                self.expr_to_scoped_string(&binary.right)?
            )),
            Expr::Cast(cast) => Some(format!(
                "{} as {}",
                self.expr_to_scoped_string(&cast.expr)?,
                cast.ty.to_token_stream()
            )),
            Expr::Reference(reference) if reference.mutability.is_none() => Some(format!(
                "& {}",
                self.expr_to_scoped_string(&reference.expr)?
            )),
            Expr::Field(field) => Some(format!(
                "({}).{}",
                self.expr_to_scoped_string(&field.base)?,
                field.member.to_token_stream()
            )),
            Expr::Index(index) => Some(format!(
                "{}[{}]",
                self.expr_to_scoped_string(&index.expr)?,
                self.expr_to_scoped_string(&index.index)?
            )),
            Expr::Call(call) => {
                let Expr::Path(func_path) = &*call.func else {
                    return None;
                };
                let args = self.scoped_call_args(&call.args).ok()?;
                Some(format!(
                    "{}({})",
                    func_path.path.to_token_stream(),
                    args.iter()
                        .map(ToTokens::to_token_stream)
                        .map(|tokens| tokens.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ))
            }
            _ => None,
        }
    }

    fn scoped_call_args(&self, args: &Punctuated<Expr, Token![,]>) -> TrustVcResult<Vec<Expr>> {
        args.iter()
            .map(|arg| {
                let rendered =
                    self.expr_to_scoped_string(arg)
                        .ok_or_else(|| TrustVcError::Encoding {
                            context: "extract source spec recommends call contracts",
                            detail: format!(
                                "Unsupported source-spec recommends call argument `{}`; \
                                 body-call recommends arguments must be scope-resolvable",
                                arg.to_token_stream()
                            ),
                        })?;
                syn::parse_str::<Expr>(&rendered).map_err(|source| TrustVcError::Encoding {
                    context: "extract source spec recommends call contracts",
                    detail: format!(
                        "Failed to parse scoped source-spec recommends call argument `{rendered}`: {source}"
                    ),
                })
            })
            .collect()
    }

    fn wrap_recommends_condition_in_context(&self, condition: String) -> String {
        let mut wrapped = if self.path_guards.is_empty() {
            condition
        } else {
            let guard = self
                .path_guards
                .iter()
                .map(|guard| format!("({guard})"))
                .collect::<Vec<_>>()
                .join(" && ");
            format!("!({guard}) || ({condition})")
        };

        for scope in self.quantifier_scopes.iter().rev() {
            if !scope.params.is_empty() {
                wrapped = format!("forall(|{}| {wrapped})", scope.params.join(", "));
            }
        }

        wrapped
    }

    fn negated_expr_to_scoped_string(&self, expr: &Expr) -> Option<String> {
        if let Expr::Unary(unary) = expr {
            if matches!(unary.op, syn::UnOp::Not(_)) {
                return self.expr_to_scoped_string(&unary.expr);
            }
        }
        Some(format!("!({})", self.expr_to_scoped_string(expr)?))
    }
}

impl<'ast> Visit<'ast> for SourceSpecRecommendsCallCollector<'_> {
    fn visit_block(&mut self, block: &'ast syn::Block) {
        if self.error.is_some() {
            return;
        }
        self.push_scope();
        for stmt in &block.stmts {
            self.visit_stmt(stmt);
            if self.error.is_some() {
                break;
            }
        }
        self.pop_scope();
    }

    fn visit_stmt(&mut self, stmt: &'ast syn::Stmt) {
        if self.error.is_some() {
            return;
        }
        match stmt {
            syn::Stmt::Local(local) => {
                if let Some(init) = &local.init {
                    self.visit_expr(&init.expr);
                    if let Some((_, diverge)) = &init.diverge {
                        self.visit_expr(diverge);
                    }
                }
                self.bind_local(local);
            }
            syn::Stmt::Expr(expr, _) => self.visit_expr(expr),
            syn::Stmt::Macro(stmt_macro) => self.visit_macro(&stmt_macro.mac),
            syn::Stmt::Item(_) => {}
        }
    }

    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        if self.error.is_some() {
            return;
        }

        if let Some(closure) = quantifier_closure_for_recommends(call) {
            let params = closure
                .inputs
                .iter()
                .filter_map(closure_param_for_recommends)
                .collect::<Vec<_>>();
            self.quantifier_scopes
                .push(SourceSpecRecommendsQuantifierScope { params });
            self.visit_expr(&closure.body);
            self.quantifier_scopes.pop();
            return;
        }

        if let Some(reference) = source_call_reference(call) {
            let reference = source_reference_with_aliases(reference, &self.source_aliases);
            if let Some(source_spec) = self.source_specs.get(&reference.source_path) {
                self.called_specs.insert(reference.clone());
                // Recommends is ADVISORY: it yields no proof obligation (see
                // `source_spec_recommends_obligations`). When a call argument is
                // not scope-resolvable there is therefore nothing to guard, so
                // we SKIP this call rather than failing closed — matching Verus,
                // which never lets a callee's recommends affect a caller's
                // verdict. (This is what lets an unresolvable body-call
                // recommends argument verify instead of erroring.)
                if let Ok(call_args) = self.scoped_call_args(&call.args) {
                    match source_spec_recommends_obligations(
                        &reference.call_symbol,
                        source_spec,
                        &call_args,
                        self.source_traits,
                        self.source_structs,
                    ) {
                        Ok(mut resolved) => {
                            if let Err(err) = merge_associated_helper_signatures(
                                &mut self.associated_helpers,
                                resolved.associated_helpers,
                                "extract source spec recommends call contracts",
                            ) {
                                self.error = Some(err);
                                return;
                            }
                            for obligation in &mut resolved.obligations {
                                obligation.condition = self.wrap_recommends_condition_in_context(
                                    obligation.condition.clone(),
                                );
                            }
                            self.obligations.append(&mut resolved.obligations)
                        }
                        Err(err) => {
                            self.error = Some(err);
                            return;
                        }
                    }
                }
            }
        }

        syn::visit::visit_expr_call(self, call);
    }

    fn visit_expr_assign(&mut self, assign: &'ast syn::ExprAssign) {
        if self.error.is_some() {
            return;
        }
        self.visit_expr(&assign.right);
        self.visit_expr(&assign.left);
        if let Some(name) = expr_path_ident_for_recommends(&assign.left) {
            self.assign_local(&name, self.expr_to_scoped_string(&assign.right));
        }
    }

    fn visit_expr_binary(&mut self, binary: &'ast syn::ExprBinary) {
        if self.error.is_some() {
            return;
        }
        if is_assignment_binop_for_recommends(&binary.op) {
            self.visit_expr(&binary.right);
            self.visit_expr(&binary.left);
            if let Some(name) = expr_path_ident_for_recommends(&binary.left) {
                self.invalidate_local(&name);
            }
            return;
        }

        match &binary.op {
            syn::BinOp::And(_) => {
                self.visit_expr(&binary.left);
                if let Some(guard) = self.expr_to_scoped_string(&binary.left) {
                    self.path_guards.push(guard);
                    self.visit_expr(&binary.right);
                    self.path_guards.pop();
                } else {
                    self.visit_expr(&binary.right);
                }
            }
            syn::BinOp::Or(_) => {
                self.visit_expr(&binary.left);
                if let Some(guard) = self.negated_expr_to_scoped_string(&binary.left) {
                    self.path_guards.push(guard);
                    self.visit_expr(&binary.right);
                    self.path_guards.pop();
                } else {
                    self.visit_expr(&binary.right);
                }
            }
            _ => syn::visit::visit_expr_binary(self, binary),
        }
    }

    fn visit_expr_reference(&mut self, reference: &'ast syn::ExprReference) {
        if self.error.is_some() {
            return;
        }
        self.visit_expr(&reference.expr);
        if reference.mutability.is_some() {
            if let Some(name) = expr_path_ident_for_recommends(&reference.expr) {
                self.invalidate_local(&name);
            }
        }
    }

    fn visit_expr_method_call(&mut self, method_call: &'ast syn::ExprMethodCall) {
        if self.error.is_some() {
            return;
        }
        self.visit_expr(&method_call.receiver);
        for arg in &method_call.args {
            self.visit_expr(arg);
        }
        if let Some(name) = expr_path_ident_for_recommends(&method_call.receiver) {
            self.invalidate_local(&name);
        }
    }

    fn visit_expr_macro(&mut self, expr_macro: &'ast syn::ExprMacro) {
        self.visit_macro(&expr_macro.mac);
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        if self.error.is_some() {
            return;
        }

        let trailing_name = path_last_segment(&mac.path);
        // `assert_by!(condition, { proof_block })` (#34): the tokens are NOT a
        // single expression, so the generic `parse2::<Expr>` fallback below
        // silently skips them — and every source spec fn called from the
        // condition or the proof block would go unregistered (its return type
        // never reaches the TypeEnv, and its `recommends` never get checked).
        // Visit both positions explicitly.
        if trailing_name
            .as_deref()
            .is_some_and(|name| matches!(name, "assert_by" | "trust_vc_assert_by"))
        {
            if let crate::AssertByParsed::WithProofBlock {
                condition,
                proof_block,
            } = crate::parse_assert_by(mac.tokens.clone())
            {
                if let Ok(expr) =
                    crate::chained_comparisons::parse_expr_tokens_with_chains(condition)
                {
                    self.visit_expr(&expr);
                }
                if let Ok(block) = syn::parse2::<syn::Block>(proof_block) {
                    self.visit_block(&block);
                }
                return;
            }
        }
        if trailing_name.as_deref().is_some_and(|name| {
            matches!(
                name,
                "assert_by_compute" | "assert_by_bit_vector" | "assert_by_nonlinear"
            )
        }) {
            match crate::parse_solver_mode_assert(mac.tokens.clone()) {
                Ok(parsed) => {
                    self.visit_expr(&parsed.condition);
                    for requires in &parsed.requires {
                        self.visit_expr(requires);
                    }
                }
                Err(source) => {
                    self.error = Some(TrustVcError::Encoding {
                        context: "extract source spec recommends call contracts",
                        detail: format!(
                            "Failed to parse {}!() while checking source spec recommends: {source}",
                            trailing_name.unwrap_or_else(|| mac.path.to_token_stream().to_string())
                        ),
                    });
                }
            }
            return;
        }

        if let Ok(expr) = syn::parse2::<Expr>(mac.tokens.clone()) {
            self.visit_expr(&expr);
        }
    }
}

fn source_spec_recommends_obligations(
    spec_name: &str,
    source_spec: &SourceSpecRecommends<'_>,
    call_args: &[Expr],
    source_traits: Option<&SourceTraitRegistry>,
    source_structs: Option<&SourceStructRegistry>,
) -> TrustVcResult<SourceSpecRecommendsObligations> {
    let Some((params, _, _)) = helper_contract_params(&source_spec.item_fn.sig) else {
        return Err(TrustVcError::Encoding {
            context: "extract source spec recommends call contracts",
            detail: format!("source spec function `{spec_name}` uses unsupported parameters"),
        });
    };

    if call_args.len() != params.len() {
        return Err(TrustVcError::Encoding {
            context: "extract source spec recommends call contracts",
            detail: format!(
                "Call to source spec `{spec_name}` has {} argument(s), but its recommends contract has {} parameter(s)",
                call_args.len(),
                params.len()
            ),
        });
    }

    let substitutions = params
        .iter()
        .cloned()
        .zip(call_args.iter().cloned())
        .collect::<HashMap<_, _>>();

    // Verus treats `recommends` as ADVISORY: a callee's recommends clause is
    // checked only in the callee's OWN recommends pass and is NEVER propagated
    // into a caller's verdict. We therefore resolve the associated-helper
    // signatures referenced by the substituted recommends (so a callee spec
    // surface stays declared for the extractor) but emit NO proof obligation —
    // the substituted recommends is verdict-neutral.
    //
    // The obligation is DROPPED, not downgraded: a `Recommends`-kind obligation
    // is ASSUMED at BodyLevel (prepared_context/validation.rs), so downgrading
    // would let a caller ASSUME a callee's `recommends(false)` and prove
    // anything — unsound. Dropping it is the faithful, verdict-neutral model.
    let mut resolved = SourceSpecRecommendsObligations::default();
    for recommends in source_spec.recommends.iter() {
        let condition_expr =
            substitute_source_spec_recommends_expr(spec_name, recommends, &substitutions)?;
        let associated_helpers = source_spec_recommends_associated_helpers(
            &condition_expr,
            source_traits,
            source_structs,
        )?;
        merge_associated_helper_signatures(
            &mut resolved.associated_helpers,
            associated_helpers,
            "extract source spec recommends call contracts",
        )?;
    }

    Ok(resolved)
}

#[derive(Default)]
struct SourceSpecRecommendsObligations {
    obligations: Vec<ProofObligation>,
    associated_helpers: AssociatedHelperSignatures,
}

fn merge_associated_helper_signatures(
    target: &mut AssociatedHelperSignatures,
    source: AssociatedHelperSignatures,
    context: &'static str,
) -> TrustVcResult<()> {
    for (name, signature) in source {
        merge_associated_helper_signature(target, name, signature, context)?;
    }
    Ok(())
}

fn merge_associated_helper_signature(
    helpers: &mut AssociatedHelperSignatures,
    name: String,
    signature: AssociatedHelperSignature,
    context: &'static str,
) -> TrustVcResult<()> {
    if let Some(existing) = helpers.get(&name) {
        if existing != &signature {
            return Err(TrustVcError::Encoding {
                context,
                detail: format!(
                    "Conflicting associated trait function signatures for `{name}`; \
                     TrustVc fails closed instead of choosing one"
                ),
            });
        }
        return Ok(());
    }
    helpers.insert(name, signature);
    Ok(())
}

fn declare_source_spec_associated_helper_fail_closed(
    name: &str,
    return_ty: TrustVcType,
    params: Vec<(String, TrustVcType)>,
    vc: &mut VerificationContext,
) -> TrustVcResult<()> {
    if let Some((existing_return_ty, existing_params, _)) = vc.helper_functions_typed.get(name) {
        if existing_return_ty != &return_ty || existing_params != &params {
            return Err(TrustVcError::Encoding {
                context: "extract source spec recommends call contracts",
                detail: format!(
                    "Associated trait function `{name}` conflicts with an existing helper \
                     signature; TrustVc fails closed instead of overwriting it"
                ),
            });
        }
        return Ok(());
    }
    vc.declare_helper_function_typed(name, return_ty, params);
    Ok(())
}

fn source_spec_recommends_associated_helpers(
    condition: &Expr,
    source_traits: Option<&SourceTraitRegistry>,
    source_structs: Option<&SourceStructRegistry>,
) -> TrustVcResult<AssociatedHelperSignatures> {
    let mut collector = AssociatedTraitFnCallCollector::default();
    collector.visit_expr(condition);
    if collector.calls.is_empty() {
        return Ok(BTreeMap::new());
    }

    let Some(source_traits) = source_traits else {
        return Err(TrustVcError::Encoding {
            context: "extract source spec recommends call contracts",
            detail:
                "Associated trait function in source-spec recommends could not be resolved without source trait declarations"
                    .to_string(),
        });
    };

    source_traits.associated_fn_helpers_in_expr_fail_closed(
        condition,
        source_structs,
        "extract source spec recommends call contracts",
    )
}

fn substitute_source_spec_recommends_expr(
    spec_name: &str,
    recommends: &str,
    substitutions: &HashMap<String, Expr>,
) -> TrustVcResult<Expr> {
    let mut condition = crate::chained_comparisons::parse_expr_str_with_chains(recommends)
        .map_err(|source| TrustVcError::Encoding {
            context: "extract source spec recommends call contracts",
            detail: format!(
                "Failed to parse source spec `{spec_name}` recommends clause `{recommends}`: {source}"
            ),
        })?;
    SourceSpecRecommendsSubstituter { substitutions }.visit_expr_mut(&mut condition);
    Ok(condition)
}

struct SourceSpecRecommendsSubstituter<'a> {
    substitutions: &'a HashMap<String, Expr>,
}

impl VisitMut for SourceSpecRecommendsSubstituter<'_> {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        let Expr::Path(path) = expr else {
            syn::visit_mut::visit_expr_mut(self, expr);
            return;
        };
        if path.qself.is_none() && path.path.segments.len() == 1 {
            if let Some(segment) = path.path.segments.first() {
                if let Some(replacement) = self.substitutions.get(&segment.ident.to_string()) {
                    *expr = replacement.clone();
                    return;
                }
            }
        }
        syn::visit_mut::visit_expr_mut(self, expr);
    }
}

fn expr_path_ident_for_recommends(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Path(path) if path.qself.is_none() && path.path.segments.len() == 1 => {
            Some(path.path.segments[0].ident.to_string())
        }
        _ => None,
    }
}

fn local_ident_for_recommends(pat: &syn::Pat) -> Option<String> {
    match pat {
        syn::Pat::Ident(pat_ident) if pat_ident.subpat.is_none() => {
            Some(pat_ident.ident.to_string())
        }
        syn::Pat::Paren(paren) => local_ident_for_recommends(&paren.pat),
        syn::Pat::Reference(reference) => local_ident_for_recommends(&reference.pat),
        syn::Pat::Type(typed) => local_ident_for_recommends(&typed.pat),
        _ => None,
    }
}

fn quantifier_closure_for_recommends(call: &syn::ExprCall) -> Option<&syn::ExprClosure> {
    let Expr::Path(path) = &*call.func else {
        return None;
    };
    if path.qself.is_some() || path.path.segments.len() != 1 {
        return None;
    }
    let name = path.path.segments[0].ident.to_string();
    if name != "forall" || call.args.len() != 1 {
        return None;
    }
    match call.args.first()? {
        Expr::Closure(closure) => Some(closure),
        _ => None,
    }
}

fn closure_param_for_recommends(pat: &syn::Pat) -> Option<String> {
    match pat {
        syn::Pat::Type(typed) => {
            let syn::Pat::Ident(ident) = &*typed.pat else {
                return None;
            };
            if ident.subpat.is_some() {
                return None;
            }
            Some(format!("{}: {}", ident.ident, typed.ty.to_token_stream()))
        }
        _ => None,
    }
}

fn bound_idents_from_pat_for_recommends(pat: &syn::Pat) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_bound_idents_for_recommends(pat, &mut names);
    names
}

fn collect_bound_idents_for_recommends(pat: &syn::Pat, names: &mut BTreeSet<String>) {
    match pat {
        syn::Pat::Ident(pat_ident) => {
            names.insert(pat_ident.ident.to_string());
            if let Some((_, subpat)) = &pat_ident.subpat {
                collect_bound_idents_for_recommends(subpat, names);
            }
        }
        syn::Pat::Tuple(tuple) => {
            for elem in &tuple.elems {
                collect_bound_idents_for_recommends(elem, names);
            }
        }
        syn::Pat::Struct(strukt) => {
            for field in &strukt.fields {
                collect_bound_idents_for_recommends(&field.pat, names);
            }
        }
        syn::Pat::TupleStruct(tuple_struct) => {
            for elem in &tuple_struct.elems {
                collect_bound_idents_for_recommends(elem, names);
            }
        }
        syn::Pat::Slice(slice) => {
            for elem in &slice.elems {
                collect_bound_idents_for_recommends(elem, names);
            }
        }
        syn::Pat::Reference(reference) => {
            collect_bound_idents_for_recommends(&reference.pat, names);
        }
        syn::Pat::Type(typed) => {
            collect_bound_idents_for_recommends(&typed.pat, names);
        }
        syn::Pat::Or(or_pat) => {
            for case in &or_pat.cases {
                collect_bound_idents_for_recommends(case, names);
            }
        }
        syn::Pat::Paren(paren) => {
            collect_bound_idents_for_recommends(&paren.pat, names);
        }
        syn::Pat::Rest(_)
        | syn::Pat::Lit(_)
        | syn::Pat::Macro(_)
        | syn::Pat::Path(_)
        | syn::Pat::Range(_)
        | syn::Pat::Verbatim(_)
        | syn::Pat::Wild(_) => {}
        _ => {}
    }
}

fn is_assignment_binop_for_recommends(op: &syn::BinOp) -> bool {
    matches!(
        op,
        syn::BinOp::AddAssign(_)
            | syn::BinOp::SubAssign(_)
            | syn::BinOp::MulAssign(_)
            | syn::BinOp::DivAssign(_)
            | syn::BinOp::RemAssign(_)
            | syn::BinOp::BitXorAssign(_)
            | syn::BinOp::BitAndAssign(_)
            | syn::BinOp::BitOrAssign(_)
            | syn::BinOp::ShlAssign(_)
            | syn::BinOp::ShrAssign(_)
    )
}

fn source_spec_recommends_from_attrs(attrs: &[syn::Attribute]) -> Vec<String> {
    attrs
        .iter()
        .filter(|attr| {
            attr.path()
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "recommends")
        })
        .filter_map(|attr| match &attr.meta {
            syn::Meta::List(meta_list) => {
                let condition = meta_list.tokens.to_string();
                (!condition.trim().is_empty()).then_some(condition)
            }
            _ => None,
        })
        .collect()
}

///
/// True when the trait method that `method_name` implements is safe to route
/// through the concrete-receiver body axiom despite the trait being
/// PARAMETERIZED: every trait-declared param/return position is either a BARE
/// trait type parameter (`-> A`, which the impl instantiates to a concrete type
/// cleanly) or fully concrete (mentions no trait type param). A NESTED
/// type-param position (`Seq<A>`, `Vec<A>`, `Option<A>`, a tuple/reference
/// carrying `A`, …) returns false — routing its instantiated encoding through the
/// body axiom was a confirmed false-verify (da02cb7, `nested_param_stays_closed`),
/// so it stays fail-closed on the generic path. CONSERVATIVE: any shape not
/// provably bare-or-concrete → false.
fn parameterized_trait_method_only_bare_type_params(
    file: &File,
    item_impl: &syn::ItemImpl,
    method_name: &str,
) -> bool {
    let Some((_, trait_path, _)) = &item_impl.trait_ else {
        return false;
    };
    let Some(trait_ident) = trait_path.segments.last().map(|seg| seg.ident.to_string()) else {
        return false;
    };
    for item in &file.items {
        let syn::Item::Trait(item_trait) = item else {
            continue;
        };
        if item_trait.ident != trait_ident {
            continue;
        }
        let trait_type_params: BTreeSet<String> = item_trait
            .generics
            .type_params()
            .map(|param| param.ident.to_string())
            .collect();
        if trait_type_params.is_empty() {
            return true; // not actually parameterized
        }
        for trait_item in &item_trait.items {
            let syn::TraitItem::Fn(trait_fn) = trait_item else {
                continue;
            };
            if trait_fn.sig.ident != method_name {
                continue;
            }
            let mut positions: Vec<&syn::Type> = Vec::new();
            for input in &trait_fn.sig.inputs {
                if let syn::FnArg::Typed(pat_type) = input {
                    positions.push(&pat_type.ty);
                }
            }
            if let syn::ReturnType::Type(_, ty) = &trait_fn.sig.output {
                positions.push(ty);
            }
            return positions
                .iter()
                .all(|ty| syn_type_is_bare_type_param_or_concrete(ty, &trait_type_params));
        }
        return false; // method not found on the trait
    }
    false // trait declaration not in this file
}

/// A `syn` type is bare-or-concrete wrt `type_params` iff it is a BARE type-param
/// path (a single ident in `type_params`, no arguments) OR mentions none of
/// `type_params` anywhere (fully concrete). Membership is token-level (split on
/// non-identifier chars), so a concrete `Other`/`Array` never matches a param
/// named `A`; a `Seq<A>` does (its `A` token is not the bare path).
fn syn_type_is_bare_type_param_or_concrete(ty: &syn::Type, type_params: &BTreeSet<String>) -> bool {
    if let syn::Type::Path(type_path) = ty {
        if type_path.qself.is_none() {
            if let Some(ident) = type_path.path.get_ident() {
                if type_params.contains(&ident.to_string()) {
                    return true; // bare type parameter
                }
            }
        }
    }
    let rendered = quote!(#ty).to_string();
    !rendered
        .split(|c: char| !c.is_alphanumeric() && c != '_')
        .any(|token| type_params.contains(token))
}

/// True iff the TRAIT declares `method_name`'s return as a BARE type-param of the
/// trait's generics (`trait Container<A> { fn get(&self) -> A; }`). This is the
/// EXACT case the impl-postcondition linking axiom drops
/// (`trait_encoding_axioms.rs` skips a `return_type.contains_type_param()`), so
/// the shared per-trait UF stays unconstrained and the call is otherwise UNKNOWN.
/// The impl writes the CONCRETE return, so its definitional body axiom
/// (`S::get(self) == <body>`) carries the right sort — the same mechanism the
/// assoc-type-return and inherent paths use. A concrete trait return (`-> u64`,
/// even on a parameterized trait) is NOT this case: the UF postcondition axiom
/// handles it, so it stays on the UF path (this returns false).
fn trait_method_returns_bare_type_param(
    file: &File,
    item_impl: &syn::ItemImpl,
    method_name: &str,
) -> bool {
    let Some((_, trait_path, _)) = &item_impl.trait_ else {
        return false;
    };
    let Some(trait_ident) = trait_path.segments.last().map(|seg| seg.ident.to_string()) else {
        return false;
    };
    for item in &file.items {
        let syn::Item::Trait(item_trait) = item else {
            continue;
        };
        if item_trait.ident != trait_ident {
            continue;
        }
        let trait_type_params: BTreeSet<String> = item_trait
            .generics
            .type_params()
            .map(|param| param.ident.to_string())
            .collect();
        for trait_item in &item_trait.items {
            let syn::TraitItem::Fn(trait_fn) = trait_item else {
                continue;
            };
            if trait_fn.sig.ident != method_name {
                continue;
            }
            let syn::ReturnType::Type(_, ty) = &trait_fn.sig.output else {
                return false;
            };
            if let syn::Type::Path(type_path) = &**ty {
                if type_path.qself.is_none() {
                    if let Some(ident) = type_path.path.get_ident() {
                        return trait_type_params.contains(&ident.to_string());
                    }
                }
            }
            return false;
        }
        return false;
    }
    false
}

/// Count the trait impls in `file` whose self-type base name is `self_type` and
/// which declare a method named `method_name`. Used as the collision gate for the
/// parameterized-trait body-axiom route: two trait impls on the SAME self-type
/// declaring the SAME method (`impl Container<u64> for S` + `impl Container<u32>
/// for S`, both `get`) would register conflicting `S::get` body axioms, and the
/// `applied` dedup keeps only the FIRST — so a caller resolving to the second
/// would read a mismatched body (a false-verify). A count `!= 1` fails closed,
/// exactly like the inherent leaf-count gate.
fn trait_impl_method_self_leaf_count(file: &File, self_type: &str, method_name: &str) -> usize {
    let mut count = 0usize;
    for item in &file.items {
        let syn::Item::Impl(item_impl) = item else {
            continue;
        };
        if item_impl.trait_.is_none() {
            continue;
        }
        let Some(base) = impl_self_type_base_name(&item_impl.self_ty) else {
            continue;
        };
        if base != self_type {
            continue;
        }
        for impl_item in &item_impl.items {
            if let syn::ImplItem::Fn(method) = impl_item {
                if method.sig.ident == method_name {
                    count += 1;
                }
            }
        }
    }
    count
}

/// A3: register inherent-impl associated functions, `Self::` calls, and
/// receiver methods referenced by the target so their call value gets a type
/// (calls.rs:154 / methods.rs unsupported-method paths fall through otherwise).
///
/// For each referenced **non-generic** inherent method we register:
/// * the associated-call symbol (`Type::method` and, for the enclosing impl,
///   `Self::method`) as a typed helper function (return type + param types),
/// * receiver-method metadata keyed by `(self_type, method)` for `recv.method()`,
/// * a UF helper `Type__method` so the definitional body axiom's call lowers, and
/// * the definitional body axiom `Type__method(self, args) == body` — but ONLY
///   when the method has no `requires` clause and a single pure return
///   expression, mirroring the sibling-helper soundness gate. When the body is
///   not a single pure return, we register the type metadata WITHOUT a body
///   axiom: the call then lowers to an opaque UF, so any assertion about its
///   result fails closed (sound) rather than being assumed.
///
/// Generic inherent impls (impl generics or self-type type args) and methods
/// with their own generic params are SKIPPED entirely, leaving the existing
/// fail-closed "unknown return type"/"unsupported method" diagnostics in place.
fn apply_inherent_impl_methods(
    file: &File,
    target_func: &ItemFn,
    source_structs: Option<&SourceStructRegistry>,
    vc: &mut VerificationContext,
) -> TrustVcResult<()> {
    let registry = InherentImplRegistry::from_file(file);
    // A file with only `#[trait_impl]` impls has an empty INHERENT registry, but
    // its no-self associated methods (`<S as Trait>::assoc()`) are still processed
    // by the trait-impl loop below — so do not early-return on those files.
    let has_trait_impl = file
        .items
        .iter()
        .any(|item| matches!(item, syn::Item::Impl(item_impl) if item_impl.trait_.is_some()));
    // A concrete-instantiation inherent impl (`impl W<u64> { .. }`, no impl
    // generics, type-args self-type) populates NEITHER registry map, so the
    // registry reads empty — but the concrete-instantiation loop below still needs
    // to run for it. Detect it here so the early-return does not skip such a file.
    let has_concrete_instantiation_impl = file.items.iter().any(|item| {
        matches!(item, syn::Item::Impl(item_impl)
            if item_impl.trait_.is_none()
                && item_impl.generics.params.is_empty()
                && concrete_instantiation_self_type_key(&item_impl.self_ty, source_structs).is_some())
    });
    if registry.is_empty() && !has_trait_impl && !has_concrete_instantiation_impl {
        return Ok(());
    }
    let ill_founded_recursive = ill_founded_recursive_function_names(file, vc);
    let enclosing_self = registry.enclosing_self_type(target_func);
    let referenced = referenced_inherent_method_calls(target_func);
    if referenced.is_empty() {
        return Ok(());
    }
    let referenced_names: BTreeSet<String> = referenced.keys().cloned().collect();

    let mut applied: BTreeSet<(String, String)> = BTreeSet::new();
    for (self_type, method) in registry.matching_methods(&referenced_names) {
        let method_name = method.sig.ident.to_string();
        if !applied.insert((self_type.clone(), method_name.clone())) {
            continue;
        }
        // A user inherent method that re-declares a datatype accessor
        // (`is_<Variant>` / `get_<Variant>_<field>`) is redundant: the canonical
        // encoder-backed accessor already resolves `recv.method(..)` with the
        // true tester/selector semantics. Skip it so we neither conflict with the
        // accessor's metadata nor emit a non-lowerable body axiom over its
        // match/panic body. Fail-closed if the source datatype registry is
        // unavailable (we cannot prove redundancy, so register as usual).
        if source_structs.is_some_and(|registry| {
            registry.is_synthesized_datatype_accessor(&self_type, &method_name)
        }) {
            continue;
        }
        let forms = referenced.get(&method_name).copied().unwrap_or_default();
        if let Some(def) = InherentMethodDef::from_impl_method(
            &self_type,
            method,
            source_structs,
            vc,
            &ill_founded_recursive,
            &[],
        )? {
            def.apply_to_context(enclosing_self.as_deref(), forms, vc);
        }
    }

    // CONCRETE-INSTANTIATION inherent impls: `impl W<u64> { fn m(&self) .. }` — a
    // generic struct instantiated at a FULLY-CONCRETE type, with NO impl generics.
    // The registry drops these (its non-generic path skips a type-args self-type
    // via `inherent_self_type_string`, and the generic path requires impl `<A>`
    // generics), so `w.m()` for a `w: W<u64>` parameter fails closed even though
    // `W<u64>` is a registered datatype (its fields already encode). Register them
    // here keyed by the receiver's canonical `to_type_string`, so the direct
    // method lookup resolves.
    //
    // COLLISION-FREE BY CONSTRUCTION (the false-verify guard): gated on a
    // whole-file leaf-count of exactly 1 for `(base, method)`. That count tallies
    // EVERY inherent declaration of the method — generic (`impl<A> W<A>`) AND
    // concrete (`impl W<C>`) — so a count of 1 proves NO other body, monomorphized
    // or concrete, can ever own this method's `sanitize_symbol`-derived UF symbol.
    // Two-bodies-on-one-symbol (the cross-map false-verify the generic path guards
    // against) is therefore impossible. The published fact is the definitional
    // body axiom (`m(self) == <body>`), the actual computation — sound on its own
    // merits; `from_impl_method` fails closed on any opaque/type-param residual.
    for item in &file.items {
        let syn::Item::Impl(item_impl) = item else {
            continue;
        };
        if item_impl.trait_.is_some() {
            continue; // inherent impls only
        }
        if !item_impl.generics.params.is_empty() {
            continue; // impl generics are the generic-monomorphization path's axis
        }
        let Some(self_type_key) =
            concrete_instantiation_self_type_key(&item_impl.self_ty, source_structs)
        else {
            continue;
        };
        let Some(base) = impl_self_type_base_name(&item_impl.self_ty) else {
            continue;
        };
        for impl_item in &item_impl.items {
            let syn::ImplItem::Fn(method) = impl_item else {
                continue;
            };
            // A method with its OWN generic/const params is a separate axis.
            if method.sig.generics.params.iter().any(|param| {
                matches!(
                    param,
                    syn::GenericParam::Type(_) | syn::GenericParam::Const(_)
                )
            }) {
                continue;
            }
            // Spec-mode methods are handled by the spec-fn path, not as
            // definitional inherent body axioms (mirror the non-generic guard).
            if has_spec_attr(&method.attrs)
                || when_used_as_spec_target_path(&method.attrs)
                    .ok()
                    .flatten()
                    .is_some()
            {
                continue;
            }
            let method_name = method.sig.ident.to_string();
            if !referenced_names.contains(&method_name) {
                continue;
            }
            // The collision-free gate — see the block comment above.
            if registry.inherent_method_leaf_count(&base, &method_name) != 1 {
                continue;
            }
            if !applied.insert((self_type_key.clone(), method_name.clone())) {
                continue;
            }
            let forms = referenced.get(&method_name).copied().unwrap_or_default();
            if let Some(def) = InherentMethodDef::from_impl_method(
                &self_type_key,
                method,
                source_structs,
                vc,
                &ill_founded_recursive,
                &[],
            )? {
                def.apply_to_context(enclosing_self.as_deref(), forms, vc);
            }
        }
    }

    // CONCRETE-INSTANTIATION TRAIT impls of a NON-parameterized trait:
    // `#[trait_impl] impl Fetch for W<u64> { fn fetch(&self) -> u64 { self.v } }`.
    // The concrete-receiver trait path does not model a generic-struct
    // instantiation self type, so `w.fetch()` on a `w: W<u64>` fails closed. As
    // with the inherent slice above, register the method's DEFINITIONAL BODY AXIOM
    // keyed by the receiver's canonical `to_type_string`.
    //
    // SOUND: conformance for the instantiation is enforced SEPARATELY — a
    // non-conformant `impl Fetch for W<u64>` fails its `trait impl conformance
    // Fetch::fetch for W<u64> (generic struct)` obligation — so the caller-visible
    // body axiom is the actual computation, never an unproven contract.
    // `from_impl_method` DECLINES a requires-bearing method, so the caller-side
    // trait-requires machinery is never perturbed. COLLISION GATE: skip if a
    // GENERIC trait impl `impl<A> Fetch for W<A>` of the same (trait, base) exists
    // — its per-instantiation monomorphization could own the same concrete symbol.
    // A PARAMETERIZED trait (`Nest<A>`) is left to the generic-trait path's
    // fail-closed nested-type-param guard (never routed through a body axiom).
    for item in &file.items {
        let syn::Item::Impl(item_impl) = item else {
            continue;
        };
        let Some((_, trait_path, _)) = &item_impl.trait_ else {
            continue; // trait impls only
        };
        if !item_impl.generics.params.is_empty() {
            continue; // concrete impl (no impl generics)
        }
        // Non-parameterized trait only (a `impl Nest<u64> for ..` trait carries
        // type args — owned by the generic-trait path).
        if trait_path
            .segments
            .last()
            .is_some_and(|seg| !matches!(seg.arguments, syn::PathArguments::None))
        {
            continue;
        }
        let Some(self_type_key) =
            concrete_instantiation_self_type_key(&item_impl.self_ty, source_structs)
        else {
            continue;
        };
        let Some(base) = impl_self_type_base_name(&item_impl.self_ty) else {
            continue;
        };
        let Some(trait_name) = trait_path.segments.last().map(|seg| seg.ident.to_string()) else {
            continue;
        };
        // Collision gate: a generic trait impl of the same (trait, base)
        // monomorphizes onto the same concrete symbol — skip to stay collision-free.
        let has_generic_trait_impl = file.items.iter().any(|other| {
            matches!(other, syn::Item::Impl(other_impl)
                if !other_impl.generics.params.is_empty()
                    && other_impl.trait_.as_ref().is_some_and(|(_, tp, _)| {
                        tp.segments.last().is_some_and(|s| s.ident == trait_name)
                    })
                    && impl_self_type_base_name(&other_impl.self_ty).as_deref() == Some(base.as_str()))
        });
        if has_generic_trait_impl {
            continue;
        }
        for impl_item in &item_impl.items {
            let syn::ImplItem::Fn(method) = impl_item else {
                continue;
            };
            if method.sig.generics.params.iter().any(|param| {
                matches!(
                    param,
                    syn::GenericParam::Type(_) | syn::GenericParam::Const(_)
                )
            }) {
                continue;
            }
            let method_name = method.sig.ident.to_string();
            if !referenced_names.contains(&method_name) {
                continue;
            }
            if !applied.insert((self_type_key.clone(), method_name.clone())) {
                continue;
            }
            let forms = referenced.get(&method_name).copied().unwrap_or_default();
            if let Some(def) = InherentMethodDef::from_impl_method(
                &self_type_key,
                method,
                source_structs,
                vc,
                &ill_founded_recursive,
                &[],
            )? {
                def.apply_to_context(enclosing_self.as_deref(), forms, vc);
            }
        }
    }

    // NO-SELF associated methods of a `#[trait_impl] impl Trait for S`, called via
    // UFCS `<S as Trait>::assoc()` (rendered `S::assoc` by format_call_expr). Each
    // is registered as an inherent-style associated symbol `S::assoc` with its impl
    // BODY axiom — the SAME mechanism the working inherent `S::assoc()` uses, so no
    // trait-UF phantom self is needed. RESTRICTED to methods with NO `self`
    // receiver: a receiver-bearing trait method is handled by the concrete-receiver
    // path, and keeping this no-self-only means it can never shadow a `recv.m()`
    // call or perturb the receiver-side requires-discharge machinery. Soundness is
    // the definitional body axiom (`S::assoc() == <body>`), the actual computation;
    // the impl's conformance to the trait contract is a separate obligation.
    for item in &file.items {
        let syn::Item::Impl(item_impl) = item else {
            continue;
        };
        if item_impl.trait_.is_none() {
            continue; // trait impls only (inherent impls handled above)
        }
        // A PARAMETERIZED trait impl (`impl Nest<u64> for S4`, trait `Nest<A>`):
        // routing a NESTED type-param method (`fn f(&self, xs: Seq<A>)`) through
        // the concrete-receiver body axiom was a confirmed FALSE-VERIFY (da02cb7,
        // `nested_param_stays_closed`) — its instantiated encoding is unsound. But
        // a method with only BARE type-param / concrete positions (`fn get(&self)
        // -> A`) instantiates cleanly (the impl provides the concrete body, keyed
        // per-self-type, leaf-count-gated), so it is admitted per-method below.
        let trait_is_parameterized = item_impl.trait_.as_ref().is_some_and(|(_, trait_path, _)| {
            trait_path
                .segments
                .last()
                .is_some_and(|seg| !matches!(seg.arguments, syn::PathArguments::None))
        });
        let Some(self_type) = inherent_self_type_string(&item_impl.self_ty) else {
            continue;
        };
        for impl_item in &item_impl.items {
            let syn::ImplItem::Fn(method) = impl_item else {
                continue;
            };
            // A method with its OWN generic/const params is a separate axis.
            if method.sig.generics.params.iter().any(|param| {
                matches!(
                    param,
                    syn::GenericParam::Type(_) | syn::GenericParam::Const(_)
                )
            }) {
                continue;
            }
            let method_name = method.sig.ident.to_string();
            if !referenced_names.contains(&method_name) {
                continue;
            }
            // Parameterized-trait per-method gate. Admit ONLY the method whose
            // TRAIT return is a bare type-param (`fn get(&self) -> A`) AND all of
            // whose positions are bare-type-param-or-concrete: this is the exact
            // case the UF postcondition axiom DROPS (return contains a type param),
            // so the call is otherwise UNKNOWN, and its instantiation is clean (the
            // impl writes the concrete body, keyed per-self-type, collision-gated).
            //   · A NESTED-type-param method (`fn f(&self, xs: Seq<A>)`) stays
            //     fail-closed — routing it was a confirmed false-verify (da02cb7,
            //     `nested_param_stays_closed`).
            //   · A CONCRETE-return method (`fn f(&self, o: Other) -> W`, even on a
            //     parameterized trait) stays on the UF path (its postcondition
            //     axiom is NOT dropped), so admitting it here would double-register.
            if trait_is_parameterized
                && !(trait_method_returns_bare_type_param(file, item_impl, &method_name)
                    && parameterized_trait_method_only_bare_type_params(
                        file,
                        item_impl,
                        &method_name,
                    ))
            {
                continue;
            }
            // Receiver policy. A NO-`self` associated fn is always admitted (the
            // `<S as T>::assoc()` UFCS capability). A WITH-`self` receiver method
            // is admitted here ONLY when the TRAIT declares its return as an
            // associated-type projection (`-> Self::Out`) that this impl binds to a
            // concrete type: the shared per-trait UF `Trait__m(self:Poly)->?` cannot
            // carry that per-impl-resolved return sort, so
            // `register_trait_impl_methods_for_concrete_types` deliberately bails
            // (trait_instantiation.rs guard) and the call is otherwise unresolved.
            // The impl method itself writes the CONCRETE return, so its definitional
            // body axiom (`S::m(self) == <body>`) carries the right sort — the same
            // mechanism the inherent path uses. A concrete-RETURN with-`self` trait
            // method is left to the UF path (so it is never double-registered).
            let has_receiver = method
                .sig
                .inputs
                .iter()
                .any(|input| matches!(input, syn::FnArg::Receiver(_)));
            // A parameterized-trait method whose TRAIT return is a bare type-param
            // (`fn get(&self) -> A`, impl binds `A→u64`) is ALSO admitted here: the
            // UF path's postcondition axiom drops it (return contains a type param),
            // so without the body axiom the call stays UNKNOWN. The impl writes the
            // concrete return; its body axiom carries the right sort. Gated below by
            // the trait-impl leaf-count collision check.
            if has_receiver
                && !trait_method_returns_assoc_type(file, item_impl, &method_name)
                && !trait_method_returns_bare_type_param(file, item_impl, &method_name)
                && !impl_method_returns_non_primitive(method)
                && !impl_method_has_non_primitive_param(method)
            {
                continue;
            }
            // Collision gate for the parameterized-trait body-axiom route: require
            // the (self-type, method) pair be UNIQUE across trait impls so the
            // `applied` keeps-first dedup can never publish a mismatched body for a
            // second same-self-type impl. Fails closed on any collision.
            if trait_is_parameterized
                && trait_impl_method_self_leaf_count(file, &self_type, &method_name) != 1
            {
                continue;
            }
            // NO-`self` associated fns stay ZERO-parameter: a `<S as T>::make(x)`
            // UFCS call renders trait-qualified (`T::make`, not the concrete
            // `S::make` the body axiom keys on — format_call_expr only rewrites the
            // empty-arg form), so a parameter-bearing associated fn would not
            // resolve anyway. A WITH-`self` receiver method (admitted here only for
            // an assoc-type return) MAY take parameters: `s.combine(x)` is an
            // ordinary method call (no render ambiguity), its body axiom
            // `S::combine(self, x) == <body>` is the actual computation, and a
            // `requires` (the only thing a parameter could unsoundly gate) is
            // already excluded below — so no precondition is dropped.
            if !has_receiver
                && method
                    .sig
                    .inputs
                    .iter()
                    .any(|input| matches!(input, syn::FnArg::Typed(_)))
            {
                continue;
            }
            // NO-REQUIRES only. The definitional body axiom `S::assoc() == <body>`
            // is UNCONDITIONAL. The requires obligation for a no-`self` associated
            // trait call is NOT enforced anywhere else (it deliberately stays
            // fail-closed — cf. fndef_types `trait_associated_function_bad_requires`),
            // so publishing the body axiom for a method that declares a `requires`
            // (on the impl OR its trait declaration) would let a precondition-
            // violating call verify — a false-verify. Skip any requires-bearing
            // method; it stays soundly fail-closed.
            if helper_has_requires_clause(&method.attrs)?
                || trait_method_declares_requires(file, item_impl, &method_name)?
            {
                continue;
            }
            // Dedup against the inherent registrations above (and each other): the
            // `(self_type, method)` key guarantees no symbol is defined twice.
            if !applied.insert((self_type.clone(), method_name.clone())) {
                continue;
            }
            let forms = referenced.get(&method_name).copied().unwrap_or_default();
            if let Some(def) = InherentMethodDef::from_impl_method(
                &self_type,
                method,
                source_structs,
                vc,
                &ill_founded_recursive,
                &[],
            )? {
                def.apply_to_context(enclosing_self.as_deref(), forms, vc);
            }
        }
    }

    // Generic inherent methods: monomorphize each per the UNIQUE concrete
    // instantiation the target uses (A2-generic). Every step fails closed —
    // an AMBIGUOUS (same-leaf collision) key, an undiscovered instantiation, a
    // `Conflict`, an unbound impl param, or a residual type param post-
    // substitution leaves the call as `UnsupportedMethod`. Soundness: the
    // abstract method is separately conformance-checked (it is its own
    // verification target on abstract `A`), and the registry collision guard
    // guarantees no concrete UF symbol is ever defined by more than one impl
    // body, so trusting the `A→concrete` monomorphization here cannot launder an
    // unchecked contract nor read a mismatched impl's axiom.
    if !registry.generic_methods.is_empty() {
        let carriers = collect_concrete_receiver_carriers(target_func, source_structs);
        for ((base, method_name), (method, impl_type_params)) in &registry.generic_methods {
            // Defensive skip: a collision-marked key must never monomorphize.
            // (Ambiguous keys are already removed from `generic_methods` at
            // registry build; this makes the fail-closed invariant explicit.)
            if registry
                .generic_ambiguous
                .contains(&(base.clone(), method_name.clone()))
            {
                continue;
            }
            if !referenced_names.contains(method_name) {
                continue;
            }
            let Some(CarrierResolution::Unique(concrete_ty)) = carriers.get(base) else {
                continue;
            };
            let Some(template) =
                source_structs.and_then(|registry| registry.resolve_type_string(base))
            else {
                continue;
            };
            let mut bindings: Vec<(String, TrustVcType)> = Vec::new();
            template.collect_type_param_bindings(concrete_ty, &mut bindings);
            // `collect_type_param_bindings` binds the CARRIER's declared param
            // names (`struct W<P>` → `P→u64`). A generic impl may RENAME them
            // (`impl<A> W<A>` — its body mentions `A`, not `P`). Remap the carrier
            // params onto the impl's own, POSITIONALLY: `admit_generic_inherent_impl`
            // guarantees the impl's self-type args are exactly its type params in
            // order, so impl-param[i] applies at carrier-param[i]. When the names
            // already match this is the identity; when they differ it is what lets
            // the impl's `A→u64` binding reach `from_impl_method`. Sound — it only
            // renames a binding key to the name the method body actually uses.
            if let Some(carrier_params) =
                source_structs.and_then(|registry| registry.datatype_generic_params(base))
            {
                if carrier_params.len() == impl_type_params.len() {
                    let remapped: Vec<(String, TrustVcType)> = impl_type_params
                        .iter()
                        .enumerate()
                        .filter_map(|(i, impl_param)| {
                            let carrier_param = carrier_params.get(i)?;
                            let value = bindings
                                .iter()
                                .find(|(name, _)| name == carrier_param)?
                                .1
                                .clone();
                            Some((impl_param.clone(), value))
                        })
                        .collect();
                    if remapped.len() == impl_type_params.len() {
                        bindings = remapped;
                    }
                }
            }
            if !impl_type_params
                .iter()
                .all(|param| bindings.iter().any(|(name, _)| name == param))
            {
                continue;
            }
            let concrete_self_str = concrete_ty.to_type_string();
            if !applied.insert((concrete_self_str.clone(), method_name.clone())) {
                continue;
            }
            if source_structs.is_some_and(|registry| {
                registry.is_synthesized_datatype_accessor(&concrete_self_str, method_name)
            }) {
                continue;
            }
            let forms = referenced.get(method_name).copied().unwrap_or_default();
            if let Some(def) = InherentMethodDef::from_impl_method(
                &concrete_self_str,
                method,
                source_structs,
                vc,
                &ill_founded_recursive,
                &bindings,
            )? {
                def.apply_to_context(enclosing_self.as_deref(), forms, vc);
            }
        }
    }
    Ok(())
}

/// Which syntactic call forms a method name appears in within the target.
#[derive(Clone, Copy, Default)]
struct CallForms {
    /// `recv.method(...)`
    method: bool,
    /// `Type::method(...)` / `Self::method(...)`
    associated: bool,
}

/// Collects method names that appear as a receiver method call
/// (`recv.method(...)`) and/or an associated/`Self` call (`Type::method(...)`) in
/// the target function's body and contracts, recording which form(s) each name
/// is used in. Used to limit inherent-method registration to referenced methods
/// and to emit only the body axiom(s) for the form(s) actually called.
fn referenced_inherent_method_calls(func: &ItemFn) -> BTreeMap<String, CallForms> {
    #[derive(Default)]
    struct NameCollector {
        forms: BTreeMap<String, CallForms>,
    }
    impl<'ast> Visit<'ast> for NameCollector {
        fn visit_expr_method_call(&mut self, call: &'ast syn::ExprMethodCall) {
            self.forms
                .entry(call.method.to_string())
                .or_default()
                .method = true;
            syn::visit::visit_expr_method_call(self, call);
        }
        fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
            if let Expr::Path(path) = &*call.func {
                if path.path.segments.len() >= 2 {
                    if let Some(last) = path.path.segments.last() {
                        self.forms
                            .entry(last.ident.to_string())
                            .or_default()
                            .associated = true;
                    }
                }
            }
            syn::visit::visit_expr_call(self, call);
        }
        fn visit_macro(&mut self, mac: &'ast syn::Macro) {
            if let Ok(expr) = syn::parse2::<Expr>(mac.tokens.clone()) {
                self.visit_expr(&expr);
            }
            syn::visit::visit_macro(self, mac);
        }
    }
    let mut collector = NameCollector::default();
    for attr in &func.attrs {
        if let Some("requires" | "ensures" | "recommends") =
            path_last_segment(attr.path()).as_deref()
        {
            if let Some(expr) = contract_attr_expr_lenient(attr) {
                collector.visit_expr(&expr);
            }
        }
    }
    collector.visit_block(&func.block);
    collector.forms
}

/// The unique concrete instantiation of a generic-impl base type discovered in
/// the target, or `Conflict` when two distinct instantiations appear for the same
/// base (→ registered for none; fail closed — one UF/axiom cannot serve two
/// backend sorts).
enum CarrierResolution {
    Unique(TrustVcType),
    Conflict,
}

/// Records a discovered concrete carrier, collapsing to `Conflict` on a second
/// distinct instantiation of the same base. A carrier with any residual type
/// param or opaque field is never recorded (it could never key a sound
/// monomorphized registration).
fn record_carrier(out: &mut BTreeMap<String, CarrierResolution>, base: String, ty: TrustVcType) {
    if ty.contains_type_param() || ty.contains_opaque() {
        return;
    }
    match out.get(&base) {
        None => {
            out.insert(base, CarrierResolution::Unique(ty));
        }
        Some(CarrierResolution::Unique(existing)) => {
            if existing.to_type_string() != ty.to_type_string() {
                out.insert(base, CarrierResolution::Conflict);
            }
        }
        Some(CarrierResolution::Conflict) => {}
    }
}

/// Discovers, per generic-impl BASE name, the UNIQUE concrete instantiation the
/// target function uses, so a generic inherent method can be monomorphized to it.
/// Two sources, both safe at registration time (before locals are typed):
///   (a) turbofished struct literals in the body/contracts (`Base::<u64>{..}`),
///   (b) parameter types (`w: Base<u64>`).
/// Two DISTINCT instantiations of one base collapse to `Conflict`. Non-turbofished
/// locals and turbofished associated-call carriers are deferred.
fn collect_concrete_receiver_carriers(
    target_func: &ItemFn,
    source_structs: Option<&SourceStructRegistry>,
) -> BTreeMap<String, CarrierResolution> {
    #[derive(Default)]
    struct CarrierCollector {
        /// `(base_name, carrier_string)` candidates, resolved after the walk.
        raw: Vec<(String, String)>,
    }
    impl<'ast> Visit<'ast> for CarrierCollector {
        fn visit_expr_struct(&mut self, node: &'ast syn::ExprStruct) {
            if let Some(segment) = node.path.segments.last() {
                if matches!(segment.arguments, syn::PathArguments::AngleBracketed(_)) {
                    let base = segment.ident.to_string();
                    // Render the struct path as a type, dropping the `::`
                    // turbofish so the carrier string matches `to_type_string()`
                    // (`ImplWrapper<u64>`, not `ImplWrapper::<u64>`).
                    let mut type_path = syn::TypePath {
                        qself: None,
                        path: node.path.clone(),
                    };
                    if let Some(last) = type_path.path.segments.last_mut() {
                        if let syn::PathArguments::AngleBracketed(ab) = &mut last.arguments {
                            ab.colon2_token = None;
                        }
                    }
                    self.raw
                        .push((base, extract_type_name(&syn::Type::Path(type_path))));
                }
            }
            syn::visit::visit_expr_struct(self, node);
        }
        // Enum construction / associated calls carry the concrete instantiation
        // on a QUALIFIER segment, not a struct literal: `GOpt::<u64>::Some(x)`
        // (a `Call` whose func is this path), `GOpt::<u64>::None` (a bare unit-
        // variant path), `GOpt::<u64>::assoc()`. The `GOpt::<u64>` segment
        // (second-to-last) carries `<u64>`; the last segment is the variant /
        // associated item. Discovering the carrier here lets a generic ENUM
        // inherent method monomorphize exactly as a struct does — the same
        // `record_carrier` guards (type-param / opaque skip, `Conflict` on a
        // second distinct instantiation) and the same registry collision guards
        // then apply, so this widens DISCOVERY only, never the trust surface.
        fn visit_expr_path(&mut self, node: &'ast syn::ExprPath) {
            let segments = &node.path.segments;
            if segments.len() >= 2 {
                let qualifier = &segments[segments.len() - 2];
                if matches!(qualifier.arguments, syn::PathArguments::AngleBracketed(_)) {
                    let base = qualifier.ident.to_string();
                    // Render the qualifier alone as a type (`GOpt<u64>`), dropping
                    // the `::` turbofish so it matches `to_type_string()`.
                    let mut type_seg = qualifier.clone();
                    if let syn::PathArguments::AngleBracketed(ab) = &mut type_seg.arguments {
                        ab.colon2_token = None;
                    }
                    let mut type_segments = syn::punctuated::Punctuated::new();
                    type_segments.push(type_seg);
                    let type_path = syn::TypePath {
                        qself: None,
                        path: syn::Path {
                            leading_colon: None,
                            segments: type_segments,
                        },
                    };
                    self.raw
                        .push((base, extract_type_name(&syn::Type::Path(type_path))));
                }
            }
            syn::visit::visit_expr_path(self, node);
        }
        fn visit_macro(&mut self, mac: &'ast syn::Macro) {
            if let Ok(expr) = syn::parse2::<Expr>(mac.tokens.clone()) {
                self.visit_expr(&expr);
            }
            syn::visit::visit_macro(self, mac);
        }
    }
    let mut collector = CarrierCollector::default();
    for attr in &target_func.attrs {
        if let Some("requires" | "ensures" | "recommends") =
            path_last_segment(attr.path()).as_deref()
        {
            if let Some(expr) = contract_attr_expr_lenient(attr) {
                collector.visit_expr(&expr);
            }
        }
    }
    collector.visit_block(&target_func.block);

    // (b) parameter-typed receivers — only concrete generic instantiations
    // (carrier contains `<`), read straight from the signature.
    for input in &target_func.sig.inputs {
        if let syn::FnArg::Typed(pat_type) = input {
            let carrier = extract_type_name(&pat_type.ty);
            if carrier.contains('<') {
                if let Some(base) = impl_self_type_base_name(&pat_type.ty) {
                    collector.raw.push((base, carrier));
                }
            }
        }
    }

    let mut out: BTreeMap<String, CarrierResolution> = BTreeMap::new();
    for (base, carrier) in collector.raw {
        let Some(ty) = source_structs.and_then(|registry| registry.resolve_type_string(&carrier))
        else {
            continue;
        };
        record_carrier(&mut out, base, ty);
    }
    out
}

/// Registry of non-generic inherent-impl methods in a file, keyed by
/// `(self_type_string, method_name)`. Leaks methods to `'static` to mirror
/// `find_function`'s approach and keep call signatures unchanged.
struct InherentImplRegistry {
    methods: BTreeMap<(String, String), &'static syn::ImplItemFn>,
    /// Nominal keys that collided because source module paths are erased.
    ambiguous_methods: BTreeSet<(String, String)>,
    /// Complete source declarations retained for exact provenance matching.
    by_name: BTreeMap<String, Vec<(String, &'static syn::ImplItemFn)>>,
    /// Fully-generic inherent-impl methods (`impl<A,..> Base<A,..>`) admitted for
    /// PER-INSTANTIATION monomorphization at a concrete receiver. Keyed by
    /// `(base_name, method_name)` → (leaked method, impl type-param idents in
    /// declared order). Kept SEPARATE from `methods`/`by_name` so the non-generic
    /// path is byte-for-byte unchanged and no generic method ever leaks into a
    /// non-generic (template-sorted) registration.
    generic_methods: BTreeMap<(String, String), (&'static syn::ImplItemFn, Vec<String>)>,
    /// Generic `(base, method)` keys that must NEVER monomorphize because more
    /// than one inherent impl of the same leaf declares them. Mirrors the
    /// non-generic `ambiguous_methods` fail-closed discipline: on any collision,
    /// BOTH sides are dropped, so a caller can never read the wrong impl's body
    /// axiom. Covers same-map (two generic impls) AND cross-map (a generic impl
    /// plus a same-leaf concrete `impl Base<C>`, which would land on the same
    /// concrete UF symbol) collisions.
    generic_ambiguous: BTreeSet<(String, String)>,
    /// Number of inherent-impl method declarations per `(base-leaf, method)`
    /// across the ENTIRE file — generic, concrete-generic, or plain. Any generic
    /// method whose leaf-pair count exceeds one is dropped (cross-map guard):
    /// the map `(nominal-base, method, instantiation) → impl-body` stays
    /// INJECTIVE — no concrete UF symbol is ever defined by more than one body.
    inherent_method_leaf_counts: BTreeMap<(String, String), usize>,
}

impl InherentImplRegistry {
    fn from_file(file: &File) -> Self {
        let mut registry = Self {
            methods: BTreeMap::new(),
            ambiguous_methods: BTreeSet::new(),
            by_name: BTreeMap::new(),
            generic_methods: BTreeMap::new(),
            generic_ambiguous: BTreeSet::new(),
            inherent_method_leaf_counts: BTreeMap::new(),
        };
        registry.collect_items(&file.items);
        // CROSS-MAP COLLISION GUARD (registry-build, solver-independent): a
        // generic `impl<A> Base<A>::m` monomorphizes to the concrete key/symbol
        // `Base<C>` / `Base_C__m`. If ANY OTHER inherent impl of the same leaf
        // also declares `m` — a second generic impl OR a concrete `impl Base<C>`
        // (which itself fails closed but still owns that concrete symbol to a
        // caller of it) — the leaf-pair count exceeds one. Drop the generic key
        // and mark it ambiguous so no caller can ever read a mismatched impl's
        // body axiom. This keeps the monomorphized registration INJECTIVE.
        let ambiguous_generic: Vec<(String, String)> = registry
            .generic_methods
            .keys()
            .filter(|key| {
                registry
                    .inherent_method_leaf_counts
                    .get(*key)
                    .copied()
                    .unwrap_or(0)
                    > 1
            })
            .cloned()
            .collect();
        for key in ambiguous_generic {
            registry.generic_methods.remove(&key);
            registry.generic_ambiguous.insert(key);
        }
        registry
    }

    fn is_empty(&self) -> bool {
        self.methods.is_empty() && self.generic_methods.is_empty()
    }

    fn collect_items(&mut self, items: &[syn::Item]) {
        for item in items {
            match item {
                syn::Item::Impl(item_impl) if item_impl.trait_.is_none() => {
                    // Count EVERY inherent-impl method by (base-leaf, method) — for
                    // the cross-map collision guard finalized in `from_file`. This
                    // MUST run before any admission branch so a concrete
                    // `impl Base<C>` (which fails closed and is otherwise skipped
                    // below) still bumps the count that fail-closes a same-leaf
                    // generic `impl<A> Base<A>` monomorphizing onto that symbol.
                    if let Some(base_leaf) = impl_self_type_base_name(&item_impl.self_ty) {
                        for impl_item in &item_impl.items {
                            if let syn::ImplItem::Fn(method) = impl_item {
                                *self
                                    .inherent_method_leaf_counts
                                    .entry((base_leaf.clone(), method.sig.ident.to_string()))
                                    .or_insert(0) += 1;
                            }
                        }
                    }

                    // Generic inherent impls: admit ONLY a fully-generic
                    // `impl<A,..> Base<A,..>` (plain unbounded type params, no
                    // where-clause) into the SEPARATE `generic_methods` map for
                    // per-instantiation monomorphization. Everything else stays
                    // fail-closed (const generics, bounds, where-clauses,
                    // lifetimes, partially-concrete/nested self types).
                    if !item_impl.generics.params.is_empty() {
                        if let Some((base_name, impl_type_params)) =
                            admit_generic_inherent_impl(item_impl)
                        {
                            for impl_item in &item_impl.items {
                                let syn::ImplItem::Fn(method) = impl_item else {
                                    continue;
                                };
                                // A method with its OWN generic/const params is a
                                // separate axis — keep it fail-closed.
                                if method.sig.generics.params.iter().any(|param| {
                                    matches!(
                                        param,
                                        syn::GenericParam::Type(_) | syn::GenericParam::Const(_)
                                    )
                                }) {
                                    continue;
                                }
                                if has_spec_attr(&method.attrs)
                                    || when_used_as_spec_target_path(&method.attrs)
                                        .ok()
                                        .flatten()
                                        .is_some()
                                {
                                    continue;
                                }
                                let method_name = method.sig.ident.to_string();
                                let leaked: &'static syn::ImplItemFn =
                                    Box::leak(Box::new(method.clone()));
                                // SAME-MAP COLLISION GUARD — a like-for-like lift of
                                // the trusted non-generic `ambiguous_methods`
                                // discipline (see below). Two generic impls that
                                // collapse to one nominal `(base, method)` key must
                                // never let source order pick a winner: drop BOTH
                                // and mark the key ambiguous so it fails closed.
                                // (The `from_file` cross-map pass re-catches this
                                // via the leaf count; kept here to mirror the
                                // non-generic path exactly.)
                                let key = (base_name.clone(), method_name);
                                if self.generic_ambiguous.contains(&key) {
                                    continue;
                                }
                                if self
                                    .generic_methods
                                    .insert(key.clone(), (leaked, impl_type_params.clone()))
                                    .is_some()
                                {
                                    self.generic_methods.remove(&key);
                                    self.generic_ambiguous.insert(key);
                                }
                            }
                        }
                        continue;
                    }
                    let Some(self_type) = inherent_self_type_string(&item_impl.self_ty) else {
                        continue;
                    };
                    for impl_item in &item_impl.items {
                        let syn::ImplItem::Fn(method) = impl_item else {
                            continue;
                        };
                        if method.sig.generics.params.iter().any(|param| {
                            matches!(
                                param,
                                syn::GenericParam::Type(_) | syn::GenericParam::Const(_)
                            )
                        }) {
                            continue;
                        }
                        if has_spec_attr(&method.attrs)
                            || when_used_as_spec_target_path(&method.attrs)
                                .ok()
                                .flatten()
                                .is_some()
                        {
                            continue;
                        }
                        let method_name = method.sig.ident.to_string();
                        let leaked: &'static syn::ImplItemFn = Box::leak(Box::new(method.clone()));
                        self.by_name
                            .entry(method_name.clone())
                            .or_default()
                            .push((self_type.clone(), leaked));

                        let key = (self_type.clone(), method_name);
                        if self.ambiguous_methods.contains(&key) {
                            continue;
                        }
                        if self.methods.insert(key.clone(), leaked).is_some() {
                            // Never let source order choose between declarations
                            // that collapse to one nominal registry key.
                            self.methods.remove(&key);
                            self.ambiguous_methods.insert(key);
                        }
                    }
                }
                syn::Item::Mod(module) => {
                    if let Some((_, inner_items)) = &module.content {
                        self.collect_items(inner_items);
                    }
                }
                _ => {}
            }
        }
    }

    /// Returns `(self_type, method)` pairs for inherent methods whose name is in
    /// `referenced`.
    fn matching_methods(
        &self,
        referenced: &BTreeSet<String>,
    ) -> Vec<(String, &'static syn::ImplItemFn)> {
        let mut out = Vec::new();
        for ((self_type, method_name), method) in &self.methods {
            if referenced.contains(method_name) {
                out.push((self_type.clone(), *method));
            }
        }
        out
    }

    /// How many inherent-impl declarations of `(base-leaf, method)` the whole file
    /// contains — generic (`impl<A> Base<A>`) AND concrete (`impl Base<C>`) alike
    /// (see `inherent_method_leaf_counts`). A count of exactly 1 is the
    /// collision-free gate the concrete-instantiation registration relies on.
    fn inherent_method_leaf_count(&self, base: &str, method: &str) -> usize {
        self.inherent_method_leaf_counts
            .get(&(base.to_string(), method.to_string()))
            .copied()
            .unwrap_or(0)
    }

    /// Exact resolution of the impl `self` type that contains the target.
    /// Multiple exact matches deliberately remain unresolved.
    fn enclosing_self_type(&self, target_func: &ItemFn) -> Option<String> {
        let target_name = target_func.sig.ident.to_string();
        let candidates = self.by_name.get(&target_name)?;
        let mut exact = candidates.iter().filter_map(|(self_type, method)| {
            function_discovery::impl_method_matches_item_fn(method, target_func)
                .then(|| self_type.clone())
        });
        let first = exact.next()?;
        if exact.next().is_some() {
            None
        } else {
            Some(first)
        }
    }
}

/// Records how every `impl` method (inherent AND trait impls) in the file takes
/// its `self` receiver, keyed by `(base_self_type_name, method_name)`. This is
/// the user-struct analog of the collection-mutator detection that closed the
/// #62/#63 loop collection-mutation gap: the body extractor uses it to decide
/// whether `recv.method(..)` can mutate the caller's `recv` binding.
///
/// Deliberately INDEPENDENT of `apply_inherent_impl_methods`' modelability gates
/// (return type, generics, opaque, body shape): we only need the receiver's
/// `self` kind, which is well-defined for every method regardless of whether its
/// body/return can be lowered. We DO include trait impls (`impl T for S`) because
/// a `&mut self` trait method mutates `recv` just as an inherent one does;
/// recording its `&self` methods as pure also avoids over-rejecting pure trait
/// reads. A method absent from this map is an UNKNOWN signature (the body
/// extractor fails closed). Walks nested modules.
fn register_impl_method_self_receiver_kinds(items: &[syn::Item], vc: &mut VerificationContext) {
    use crate::vc::SelfReceiverKind;
    for item in items {
        match item {
            syn::Item::Impl(item_impl) => {
                let Some(self_type) = impl_self_type_base_name(&item_impl.self_ty) else {
                    continue;
                };
                for impl_item in &item_impl.items {
                    let syn::ImplItem::Fn(method) = impl_item else {
                        continue;
                    };
                    let Some(syn::FnArg::Receiver(recv)) = method.sig.inputs.first() else {
                        continue;
                    };
                    let kind = if recv.reference.is_some() {
                        if recv.mutability.is_some() {
                            SelfReceiverKind::RefMut
                        } else {
                            SelfReceiverKind::Ref
                        }
                    } else {
                        // `self` / `mut self`: the receiver is moved into the
                        // callee, so it cannot mutate the caller's binding.
                        SelfReceiverKind::Value
                    };
                    vc.register_struct_self_receiver_kind(
                        self_type.clone(),
                        method.sig.ident.to_string(),
                        kind,
                    );
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner)) = &module.content {
                    register_impl_method_self_receiver_kinds(inner, vc);
                }
            }
            _ => {}
        }
    }
}

/// The base type-name of an `impl` self type (e.g. `Foo` for `Foo`, `Foo<T>`,
/// `&mut Foo`, `Box<Foo>`-free path forms). Unlike `inherent_self_type_string`
/// this is lenient about generic arguments because we only need the nominal type
/// name to key receiver-kind metadata. Returns `None` for non-path self types.
fn impl_self_type_base_name(ty: &syn::Type) -> Option<String> {
    match ty {
        syn::Type::Path(type_path) => type_path.path.segments.last().map(|s| s.ident.to_string()),
        syn::Type::Reference(reference) => impl_self_type_base_name(&reference.elem),
        syn::Type::Group(group) => impl_self_type_base_name(&group.elem),
        syn::Type::Paren(paren) => impl_self_type_base_name(&paren.elem),
        _ => None,
    }
}

/// Admits a FULLY-generic inherent impl `impl<A,B,..> Base<A,B,..>` for
/// per-instantiation monomorphization, returning `(base_name, type_param_idents)`.
///
/// Returns `None` (→ fail closed, keeping the existing "unsupported method"
/// diagnostic) unless EVERY guard holds:
/// * every generic param is a plain **unbounded** `Type` param — no const
///   generics, no bounded type params, no lifetimes;
/// * there is no `where`-clause;
/// * the self-type is a plain path whose angle-bracket args are exactly those
///   type params as bare identifiers, in declared order (`ImplWrapper<A>`, not
///   `ImplWrapper<u64>`, `ImplWrapper<Box<A>>`, or a reordered `Foo<B, A>` —
///   reordering is rejected here and deferred; `collect_type_param_bindings`
///   handles it structurally but the minimal slice does not rely on it).
///
/// Bounded params / where-clauses are rejected because monomorphizing `A = u64`
/// would trust `u64: Bound` without checking it (a trait-conformance obligation
/// owned by #2785, not resolvable here).
fn admit_generic_inherent_impl(item_impl: &syn::ItemImpl) -> Option<(String, Vec<String>)> {
    if item_impl.generics.where_clause.is_some() {
        return None;
    }
    let mut param_idents = Vec::new();
    for param in &item_impl.generics.params {
        match param {
            syn::GenericParam::Type(type_param) if type_param.bounds.is_empty() => {
                param_idents.push(type_param.ident.to_string());
            }
            // const / bounded type / lifetime → fail closed.
            _ => return None,
        }
    }
    if param_idents.is_empty() {
        return None;
    }
    let syn::Type::Path(type_path) = &*item_impl.self_ty else {
        return None;
    };
    if type_path.qself.is_some() {
        return None;
    }
    let segment = type_path.path.segments.last()?;
    let base_name = segment.ident.to_string();
    let syn::PathArguments::AngleBracketed(args) = &segment.arguments else {
        return None;
    };
    // Every self-type arg must be a bare-ident type; a non-ident arg (concrete
    // type, nested generic, lifetime, const) collapses the filter_map length and
    // is rejected below.
    let self_arg_idents: Vec<String> = args
        .args
        .iter()
        .filter_map(|arg| match arg {
            syn::GenericArgument::Type(syn::Type::Path(path)) => {
                path.path.get_ident().map(|ident| ident.to_string())
            }
            _ => None,
        })
        .collect();
    if self_arg_idents.len() != args.args.len() || self_arg_idents != param_idents {
        return None;
    }
    Some((base_name, param_idents))
}

/// Renders an inherent impl's `self_ty` to its `to_type_string()` key when it is
/// a plain, non-generic path type (e.g. `Foo`). Returns `None` for generic or
/// otherwise unsupported self types, which are left fail-closed.
/// Canonical `to_type_string` key for a CONCRETE-INSTANTIATION inherent-impl
/// self-type (`W<u64>` → `"W<u64>"`). Returns the SAME canonical string a
/// `w: W<u64>` receiver resolves to (both go through `TrustVcType::to_type_string`),
/// so a method registered under this key resolves at `w.m()`.
///
/// Returns `None` for a plain no-args self-type (`impl W` — owned by the existing
/// non-generic path), a non-path/qualified type, or anything that does not resolve
/// to a fully-concrete registered datatype (a residual type param or opaque =
/// fail closed).
fn concrete_instantiation_self_type_key(
    ty: &syn::Type,
    source_structs: Option<&SourceStructRegistry>,
) -> Option<String> {
    let syn::Type::Path(type_path) = ty else {
        return None;
    };
    if type_path.qself.is_some() {
        return None;
    }
    let segment = type_path.path.segments.last()?;
    // A plain (no-args) self-type is the existing non-generic case; only a
    // type-args instantiation (`W<u64>`) is handled here.
    if matches!(segment.arguments, syn::PathArguments::None) {
        return None;
    }
    let rendered = quote::quote!(#ty).to_string().replace(' ', "");
    let resolved = source_structs?.resolve_type_string(&rendered)?;
    if resolved.contains_opaque() || resolved.contains_type_param() {
        return None;
    }
    Some(resolved.to_type_string())
}

fn inherent_self_type_string(ty: &syn::Type) -> Option<String> {
    let syn::Type::Path(type_path) = ty else {
        return None;
    };
    if type_path.qself.is_some() {
        return None;
    }
    let segment = type_path.path.segments.last()?;
    if !matches!(segment.arguments, syn::PathArguments::None) {
        return None;
    }
    Some(segment.ident.to_string())
}

/// A registered inherent method: its self type, return type, non-receiver
/// params, and (when soundly derivable) a definitional body condition.
struct InherentMethodDef {
    self_type: String,
    method_name: String,
    uf_name: String,
    return_ty: TrustVcType,
    /// `(rust_param_name, bound_name, ty)` for non-receiver params, in order.
    params: Vec<(String, String, TrustVcType)>,
    receiver: Option<InherentReceiver>,
    /// Fresh bound name + type for the `self` receiver, when present.
    self_binding: Option<(String, TrustVcType)>,
    /// Renamed single-return body expression (params/`self` -> bound names), if
    /// a sound definitional axiom is derivable; `None` otherwise (type-only).
    renamed_body: Option<String>,
    /// Renamed conjoined `requires` guard for a requires-bearing method, so the
    /// body axiom is published GUARDED (`guard ==> method == body`) rather than
    /// unconditionally — dropping it would be a false-verify (see the
    /// `trait_method_declares_requires` doc). `None` for a requires-free method;
    /// a requires-bearing method whose guard cannot be extracted/renamed instead
    /// forces `renamed_body = None` (fail-closed, no body axiom).
    guarded_requires: Option<String>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum InherentReceiver {
    Value,
    Ref,
}

impl InherentMethodDef {
    fn from_impl_method(
        self_type: &str,
        method: &syn::ImplItemFn,
        source_structs: Option<&SourceStructRegistry>,
        ctx: &VerificationContext,
        ill_founded_recursive: &BTreeSet<String>,
        type_param_bindings: &[(String, TrustVcType)],
    ) -> TrustVcResult<Option<Self>> {
        // Substitute `Self` → the concrete impl type before reading the return
        // type / params / body. Mirrors the target-lifting substitution in
        // `function_discovery`: a `-> Self` return, a bare `self` receiver, or a
        // `Self::` path in the body must resolve to the concrete type so that a
        // `Self::method(..)` associated call finds this method's concrete return
        // type at registration. Sound — `Self` IS the impl's self type. If
        // `self_type` does not parse as a type (unusual), fall back to the raw
        // method (behaves exactly as before this substitution existed).
        let method_owned;
        let method: &syn::ImplItemFn = match syn::parse_str::<syn::Type>(self_type) {
            Ok(concrete_ty) => {
                let mut owned = method.clone();
                let mut sub = function_discovery::SelfTypeSubstituter::new(&concrete_ty);
                syn::visit_mut::visit_signature_mut(&mut sub, &mut owned.sig);
                syn::visit_mut::visit_block_mut(&mut sub, &mut owned.block);
                method_owned = owned;
                &method_owned
            }
            Err(_) => method,
        };
        let method_name = method.sig.ident.to_string();
        let Some(return_ty) = helper_return_type(&method.sig, source_structs) else {
            return Ok(None);
        };
        // Monomorphize the impl's type params (e.g. `A -> u64` for a call on a
        // concrete `ImplWrapper<u64>` receiver). `type_param_bindings` is empty
        // for the non-generic path, so this is a no-op there. The
        // `contains_type_param` guard below is the fail-closed backstop: a
        // `-> A` return is `TypeParam("A")`, which is NOT `Opaque`, so without a
        // complete binding it would otherwise register a `Poly`-sorted UF (the
        // false-verify vector). Any residual type param → fail closed.
        let return_ty = crate::ir_lowering::substitute_type_params(&return_ty, type_param_bindings);
        if return_ty.contains_opaque() {
            return Ok(None);
        }
        if return_ty.contains_type_param() {
            return Ok(None);
        }

        let self_ty = source_structs
            .and_then(|registry| registry.resolve_type_string(self_type))
            .unwrap_or_else(|| TrustVcType::parse_or_opaque(self_type));
        if self_ty.contains_opaque() {
            return Ok(None);
        }

        let mut used_names: BTreeSet<String> = ctx
            .variables()
            .iter()
            .map(|variable| variable.name.clone())
            .collect();

        let mut receiver = None;
        let mut self_binding = None;
        let mut params = Vec::new();
        for input in &method.sig.inputs {
            match input {
                syn::FnArg::Receiver(recv) => {
                    receiver = Some(if recv.reference.is_some() {
                        InherentReceiver::Ref
                    } else {
                        InherentReceiver::Value
                    });
                    let bound = fresh_sibling_bound_name(&mut used_names, &method_name, "self");
                    self_binding = Some((bound, self_ty.clone()));
                }
                syn::FnArg::Typed(pat_type) => {
                    let syn::Pat::Ident(pat_ident) = &*pat_type.pat else {
                        return Ok(None);
                    };
                    let name = pat_ident.ident.to_string();
                    let ty_str = extract_type_name(&pat_type.ty);
                    let ty = source_structs
                        .and_then(|registry| registry.resolve_type_string(&ty_str))
                        .unwrap_or_else(|| TrustVcType::parse_or_opaque(&ty_str));
                    let ty = crate::ir_lowering::substitute_type_params(&ty, type_param_bindings);
                    if ty.contains_opaque() {
                        return Ok(None);
                    }
                    if ty.contains_type_param() {
                        return Ok(None);
                    }
                    let bound = fresh_sibling_bound_name(&mut used_names, &method_name, &name);
                    params.push((name, bound, ty));
                }
            }
        }

        // Sanitize the self-type into the UF SYMBOL so a concrete generic
        // instantiation (`ImplWrapper<u64>`) does not emit `<`/`>` into the body
        // axiom (the obligation expression parser reads them as comparisons).
        // The registration KEY / `MethodMeta` self-type stays the exact
        // `to_type_string()` form for call-site lookup; only the emitted symbol
        // is sanitized. A no-op for plain non-generic names.
        let uf_name = format!(
            "{}__{method_name}",
            crate::encoder::sanitize_symbol(self_type)
        );

        // Definitional body axiom: only when there is no `requires` clause and
        // the body is a single pure return expression (sibling-helper gate). The
        // body references `self`/params, renamed to their fresh bound names.
        // The self/param -> bound-name rename map, shared by the body and (for a
        // requires-bearing method) the requires guard.
        let mut rename_map = HashMap::new();
        if let Some((self_bound, _)) = &self_binding {
            rename_map.insert("self".to_string(), self_bound.clone());
        }
        for (name, bound, _) in &params {
            rename_map.insert(name.clone(), bound.clone());
        }

        // A `requires` clause no longer blocks the body axiom — it is instead
        // GUARDED below. The other gates still decline (shadowed params, ill-
        // founded self-recursion): no sound definitional axiom is derivable there.
        let body_gated = method_params_shadowed(method)
            || self_recursive_body_axiom_unsound(&method_name, &method.block, &method.attrs)
            || ill_founded_recursive.contains(&method_name);
        let mut renamed_body = if body_gated {
            None
        } else {
            match classify_return_expression(
                &method.block,
                return_ty == TrustVcType::Unit,
                &BTreeSet::new(),
            ) {
                return_extract::ReturnExtraction::Single(return_value) => {
                    let scoped_return = scoped_return_value_expression(
                        &method.block,
                        return_value,
                        &ctx.struct_types,
                    );
                    match syn::parse_str::<Expr>(&scoped_return) {
                        Ok(mut renamed_return) => {
                            IdentRenamer {
                                rename_map: rename_map.clone(),
                            }
                            .visit_expr_mut(&mut renamed_return);
                            Some(quote!(#renamed_return).to_string())
                        }
                        Err(_) => None,
                    }
                }
                return_extract::ReturnExtraction::Missing
                | return_extract::ReturnExtraction::Multiple(_)
                | return_extract::ReturnExtraction::Ambiguous(_) => None,
            }
        };

        // For a requires-bearing method, the body axiom MUST be guarded by the
        // requires — an unconditional `method == body` is a false-verify (see
        // `trait_method_declares_requires`). Build the renamed conjoined guard; if
        // it cannot be built, DROP the body axiom (fail-closed, the prior behavior).
        let guarded_requires =
            if renamed_body.is_some() && helper_has_requires_clause(&method.attrs)? {
                match renamed_requires_guard(&method.attrs, &method.sig, &rename_map) {
                    Some(guard) => Some(guard),
                    None => {
                        renamed_body = None;
                        None
                    }
                }
            } else {
                None
            };

        Ok(Some(Self {
            self_type: self_type.to_string(),
            method_name,
            uf_name,
            return_ty,
            params,
            receiver,
            self_binding,
            renamed_body,
            guarded_requires,
        }))
    }

    fn apply_to_context(
        &self,
        enclosing_self: Option<&str>,
        forms: CallForms,
        ctx: &mut VerificationContext,
    ) {
        // Helper params, receiver (if any) first — matching the order in which
        // `Type::method(self, args)` / `recv.method(args)` pass arguments.
        let mut helper_params: Vec<(String, TrustVcType)> = Vec::new();
        if let Some((self_bound, self_ty)) = &self.self_binding {
            helper_params.push((self_bound.clone(), self_ty.clone()));
        }
        for (_, bound, ty) in &self.params {
            helper_params.push((bound.clone(), ty.clone()));
        }
        let param_types: Vec<TrustVcType> =
            self.params.iter().map(|(_, _, ty)| ty.clone()).collect();

        // Each call symbol the target actually uses gets the same typed signature
        // and a definitional body axiom. The associated-call forms
        // (`Type::method`, `Self::method`) take the receiver as their first
        // explicit argument; the receiver-method UF (`Type__method`, registered
        // as `MethodMeta`) takes the lowered receiver as its first argument. We
        // register ONLY the forms the target references so unused triggers do not
        // pollute the quantifier instantiation space.
        let mut call_symbols: Vec<String> = Vec::new();
        if forms.associated {
            // For a generic-struct INSTANTIATION self type (`W<u64>`), the caller
            // `W::<u64>::new(..)` lowers (via `expr_path_to_string`) to the BASE
            // name `W::new` — the `<u64>` type args are dropped. Register the
            // associated symbol (and thus the body-axiom trigger) under that base
            // form so (a) the trigger string parses — `W<u64>::new(..)` would
            // reparse as the chained comparison `W < u64 > :: new` — and (b) it
            // matches the caller's lowered name. The leaf-count==1 gate on the
            // concrete-instantiation registration keeps `W::new` unambiguous (a
            // single monomorphized `new` per target). A non-generic self (`S`) is
            // unchanged.
            let assoc_type = match self.self_type.find('<') {
                Some(idx) => &self.self_type[..idx],
                None => self.self_type.as_str(),
            };
            call_symbols.push(format!("{}::{}", assoc_type, self.method_name));
            if enclosing_self == Some(self.self_type.as_str()) {
                call_symbols.push(format!("Self::{}", self.method_name));
            }
        }
        if forms.method && self.receiver.is_some() {
            call_symbols.push(self.uf_name.clone());
        }
        if call_symbols.is_empty() {
            return;
        }

        for symbol in &call_symbols {
            ctx.declare_helper_function_typed(
                symbol,
                self.return_ty.clone(),
                helper_params.clone(),
            );
        }

        // Receiver-method metadata: `recv.method(args)` -> uf_name(recv, args).
        if forms.method && self.receiver.is_some() {
            ctx.register_inherent_method(
                self.self_type.clone(),
                self.method_name.clone(),
                self.uf_name.clone(),
                self.return_ty.clone(),
                param_types,
            );
        }

        let Some(renamed_body) = &self.renamed_body else {
            return;
        };

        for (bound, ty) in &helper_params {
            if ctx.get_variable_type(bound).is_none() {
                ctx.declare_var_typed(bound, ty.clone());
            }
        }
        if matches!(self.receiver, Some(InherentReceiver::Ref)) {
            if let Some((self_bound, _)) = &self.self_binding {
                ctx.mark_erased_shared_ref_var(self_bound);
            }
        }

        let call_args = helper_params
            .iter()
            .map(|(bound, _)| bound.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        for symbol in &call_symbols {
            let trigger = format!("{symbol}({call_args})");
            let axiom_name = format!(
                "__body_axiom_{}_inherent_method",
                sanitize_axiom_symbol(symbol)
            );
            if ctx
                .obligations()
                .iter()
                .any(|obligation| obligation.name() == axiom_name)
            {
                continue;
            }
            // A requires-bearing method's body axiom is GUARDED by the (renamed)
            // precondition — `guard ==> (method == body)`. Publishing `method ==
            // body` unconditionally would be a false-verify when the body only
            // holds under the precondition. A requires-free method keeps the bare
            // definitional equality.
            let condition = match &self.guarded_requires {
                Some(guard) => format!("({guard}) ==> ({trigger} == ({renamed_body}))"),
                // Parenthesize the body: a boolean/comparison body (e.g. `a == b`)
                // would otherwise splice into `{trigger} == a == b`, a chained
                // comparison that fails to parse. Parens are an identity otherwise.
                None => format!("{trigger} == ({renamed_body})"),
            };
            ctx.push_obligation(
                ProofObligation::broadcast_assume(axiom_name, condition)
                    .with_bound_vars(
                        helper_params
                            .iter()
                            .map(|(bound, _)| bound.clone())
                            .collect(),
                    )
                    .with_trigger_patterns(vec![vec![trigger.clone()]]),
            );
        }
    }
}

/// Sanitizes a call symbol (which may contain `::`) into an obligation-name-safe
/// token.
fn sanitize_axiom_symbol(symbol: &str) -> String {
    symbol.replace("::", "__")
}

/// Whether any of the method's parameters (or `self`) are shadowed by a body
/// `let` binding — in which case the single-return body axiom would be unsound,
/// so we suppress it (register the type only).
fn method_params_shadowed(method: &syn::ImplItemFn) -> bool {
    let mut param_names: BTreeSet<String> = BTreeSet::new();
    for input in &method.sig.inputs {
        match input {
            syn::FnArg::Receiver(_) => {
                param_names.insert("self".to_string());
            }
            syn::FnArg::Typed(pat_type) => {
                if let syn::Pat::Ident(pat_ident) = &*pat_type.pat {
                    param_names.insert(pat_ident.ident.to_string());
                }
            }
        }
    }
    let mut collector = ParamShadowCollector {
        param_names: &param_names,
        shadowed: false,
    };
    collector.visit_block(&method.block);
    collector.shadowed
}

/// SOUNDNESS GATE (round-4, proof/exec self-recursion class): a single-return
/// body axiom `f(x) == body(x)` whose `body(x)` references `f` itself is a
/// faithful equation only when the recursion it encodes terminates. With no
/// `#[decreases]` measure the equation can be contradictory — e.g. the reported
/// `fn m(&self, n) -> u32 { self.m(n) + 1 }`, whose axiom `m(s,n) == m(s,n) + 1`
/// is arithmetically `0 == 1` — which entails `false` and lets ANY goal mentioning
/// `f` verify vacuously (a catastrophic false `Verified`).
///
/// Verus admits a recursive definition's defining axiom only after DISCHARGING a
/// termination proof. This is the proof/exec body-axiom analogue of the spec
/// catalog's [`SpecFunctionCatalog::recursion_suppresses_axiom`] Stage-1
/// structural gate and of the proc-macro path's check in
/// [`crate::proof_expand::expand_proof_with_tracked`]: a function whose body calls
/// itself (`self.f(..)` / `Self::f(..)` / `Type::f(..)` / bare `f(..)`, matched by
/// name) and carries NO `#[decreases]` clause must NOT publish a usable body
/// axiom — it is registered uninterpreted (UF only) instead. A well-founded
/// recursive function annotated with `#[decreases]`, and any non-recursive
/// function, are unaffected.
///
/// Honest partial: this is the STRUCTURAL stage only. A self-recursive function
/// that carries a `#[decreases]` clause whose measure does not actually shrink is
/// still trusted here (mirroring the proc-macro path); the semantic measure proof
/// runs only for spec functions in the catalog. The detection is name-approximate
/// (a call to a same-named method on an unrelated type counts), which can only
/// OVER-suppress (register UF) and is therefore sound.
fn self_recursive_body_axiom_unsound(
    fn_name: &str,
    block: &syn::Block,
    attrs: &[syn::Attribute],
) -> bool {
    crate::block_contains_self_call(fn_name, block)
        && !crate::proof_expand::has_decreases_metadata(attrs)
}

/// SOUNDNESS GATE (round-8, mutual-recursion broadcast/proof lemma class):
/// the set of file-local function names whose contract `ensures` AND
/// single-return body axiom must NOT be trusted because the function sits in a
/// recursion CYCLE that is not termination-guarded.
///
/// [`self_recursive_body_axiom_unsound`] only catches DIRECT self-recursion
/// (`f` calls `f`). A MUTUAL cycle (`la` calls `lb`, `lb` calls `la`) bypasses
/// it: each lemma's `ensures op(i)` is discharged circularly from the other's
/// assumed postcondition with no termination measure, so an external caller of
/// `la` trusts the (false) `op(i)`, and a false goal verifies — a catastrophic
/// false `Verified` (round-8 findings 15-16). This generalizes the gate to a
/// full recursion-cycle check, mirroring the spec catalog's Stage-1 structural
/// gate ([`crate::spec_function_catalog::SpecFunctionCatalog`]
/// `recursion_suppresses_axiom`).
///
/// A name is reported iff it participates in a recursion cycle (a self-edge, or
/// a strongly-connected component with >1 member) AND some member of that cycle
/// lacks a `#[decreases]` clause. A well-founded cycle whose EVERY member
/// carries `#[decreases]` (and any non-recursive function) is unaffected — no
/// over-rejection — matching the directive that "a well-founded
/// mutually-recursive pair WITH `#[decreases]` still works" and that
/// "self-recursive-with-decreases [is] unaffected".
///
/// Honest partial: this is the STRUCTURAL stage only. Exactly like the
/// pre-existing [`self_recursive_body_axiom_unsound`] gate (and the proc-macro
/// path), a cycle whose every member carries a `#[decreases]` clause is trusted
/// WITHOUT proving the measure actually shrinks. So a mutually-recursive pair
/// carrying a non-shrinking `#[decreases]` on both members is NOT caught here
/// (round-8 finding 15's decreases-bearing variant) — it is the mutual analog
/// of the deliberately-unaffected self-recursive-with-decreases case, and
/// closing it needs the semantic measure-decrease proof the spec catalog runs in
/// `recursion_suppresses_axiom` Stage 2. The detection is name-approximate
/// (calls match by final-segment identifier; method calls match by method name),
/// which can only OVER-suppress (register a function uninterpreted), so it is
/// sound.
/// The source signature/attrs/body of a file-graph recursion node, retained so the
/// semantic Stage-2 termination proof can be reconstructed for a proof/exec-fn
/// cycle. Stored as `Option` per name: a name collision sets it to `None`
/// (ambiguous), which makes Stage 2 suppress that cycle because termination was
/// not positively established.
#[derive(Clone)]
struct SourceFnRecursionInfo {
    sig: syn::Signature,
    attrs: Vec<syn::Attribute>,
    block: Block,
}

fn ill_founded_recursive_function_names(
    file: &File,
    ctx: &VerificationContext,
) -> BTreeSet<String> {
    // `guarded[name]` is true only if EVERY function carrying that name has a
    // `#[decreases]` clause (conservative on name collisions: any unguarded
    // occurrence makes the name unguarded, which can only over-suppress).
    let mut guarded: BTreeMap<String, bool> = BTreeMap::new();
    let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut nodes: BTreeMap<String, Option<SourceFnRecursionInfo>> = BTreeMap::new();
    collect_file_fn_recursion_nodes(&file.items, &mut guarded, &mut edges, &mut nodes);

    // Restrict the call graph to edges that target a function defined in the
    // file (external / library calls are not recursion edges here).
    for callees in edges.values_mut() {
        callees.retain(|callee| guarded.contains_key(callee));
    }

    let mut ill_founded = BTreeSet::new();
    // Memoize the Stage-2 semantic verdict per cycle (keyed by sorted members) so a
    // cycle's solver query runs once even though every member iterates the outer loop.
    let mut stage2_cache: BTreeMap<String, Option<bool>> = BTreeMap::new();
    for name in guarded.keys() {
        // The strongly-connected component of `name` = nodes reachable FROM it
        // that can also reach BACK to it.
        let forward = reachable_forward(&edges, name);
        let backward = reachable_backward(&edges, name);
        let cycle: BTreeSet<&String> = forward.intersection(&backward).collect();
        let has_self_edge = edges
            .get(name)
            .is_some_and(|callees| callees.contains(name));
        let is_recursive = has_self_edge || cycle.iter().any(|member| *member != name);
        if !is_recursive {
            continue;
        }
        let fully_guarded = cycle
            .iter()
            .all(|member| guarded.get(*member).copied().unwrap_or(false));
        if !fully_guarded {
            // Stage 1 — structural: some cycle member lacks `#[decreases]`.
            ill_founded.insert(name.clone());
            continue;
        }
        // Stage 2 — semantic: every member carries `#[decreases]`, but the measure
        // must be PROVEN to strictly decrease on every recursive edge. A
        // structurally-guarded cycle whose declared measure does not actually shrink
        // (e.g. a mutual pair passing the SAME argument back) is otherwise TRUSTED —
        // the round-8 findings 15-16 catastrophic false `Verified`. Suppress unless
        // the semantic check positively proves termination. An unmodelable member
        // or ambiguous source-name collision yields `None` and must fail closed.
        let mut members: Vec<&String> = cycle.iter().copied().collect();
        if members.is_empty() {
            members.push(name);
        }
        members.sort();
        let cache_key = members
            .iter()
            .map(|member| member.as_str())
            .collect::<Vec<_>>()
            .join(",");
        let verdict = *stage2_cache.entry(cache_key).or_insert_with(|| {
            let mut source_members = Vec::with_capacity(members.len());
            for member in &members {
                match nodes.get(*member) {
                    Some(Some(info)) => source_members.push((
                        (*member).clone(),
                        info.sig.clone(),
                        info.attrs.clone(),
                        info.block.clone(),
                    )),
                    // Ambiguous (name collision) or missing source → cannot analyze.
                    _ => return None,
                }
            }
            crate::spec_function_catalog::source_cycle_terminates(&source_members, ctx)
        });
        if verdict != Some(true) {
            ill_founded.insert(name.clone());
        }
    }
    ill_founded
}

/// Registers every function defined under `items` (free functions including
/// those nested in inline modules, inherent + trait-impl methods, and trait
/// default-method bodies) as a node in the file-local recursion call graph used
/// by [`ill_founded_recursive_function_names`].
fn collect_file_fn_recursion_nodes(
    items: &[syn::Item],
    guarded: &mut BTreeMap<String, bool>,
    edges: &mut BTreeMap<String, BTreeSet<String>>,
    nodes: &mut BTreeMap<String, Option<SourceFnRecursionInfo>>,
) {
    for item in items {
        match item {
            syn::Item::Fn(item_fn) => {
                add_fn_recursion_node(
                    &item_fn.sig,
                    &item_fn.attrs,
                    &item_fn.block,
                    guarded,
                    edges,
                    nodes,
                );
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    collect_file_fn_recursion_nodes(inner_items, guarded, edges, nodes);
                }
            }
            syn::Item::Impl(item_impl) => {
                for impl_item in &item_impl.items {
                    if let syn::ImplItem::Fn(method) = impl_item {
                        add_fn_recursion_node(
                            &method.sig,
                            &method.attrs,
                            &method.block,
                            guarded,
                            edges,
                            nodes,
                        );
                    }
                }
            }
            syn::Item::Trait(item_trait) => {
                for trait_item in &item_trait.items {
                    if let syn::TraitItem::Fn(trait_fn) = trait_item {
                        if let Some(default_block) = &trait_fn.default {
                            add_fn_recursion_node(
                                &trait_fn.sig,
                                &trait_fn.attrs,
                                default_block,
                                guarded,
                                edges,
                                nodes,
                            );
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

fn add_fn_recursion_node(
    sig: &syn::Signature,
    attrs: &[syn::Attribute],
    block: &Block,
    guarded: &mut BTreeMap<String, bool>,
    edges: &mut BTreeMap<String, BTreeSet<String>>,
    nodes: &mut BTreeMap<String, Option<SourceFnRecursionInfo>>,
) {
    let name = sig.ident.to_string();
    let has_decreases = crate::proof_expand::has_decreases_metadata(attrs);
    guarded
        .entry(name.clone())
        .and_modify(|g| *g = *g && has_decreases)
        .or_insert(has_decreases);
    let mut called = block_called_function_names(block);
    // Also count calls routed through a function-item value (`let f = g; f()`), so a
    // recursion cycle hidden behind fn-item values is caught by the same gate.
    let fn_value_calls = fn_value_call_edges(block);
    called.extend(fn_value_calls.edges);
    if !fn_value_calls.complete {
        // An incomplete static call graph cannot justify publishing a contract:
        // the unresolved target may be this function or another cycle member.
        called.insert(name.clone());
    }
    edges.entry(name.clone()).or_default().extend(called);
    // Retain the source fn for the semantic Stage-2 termination proof; a name
    // collision marks the node ambiguous (`None`) so Stage 2 fails closed.
    match nodes.entry(name) {
        std::collections::btree_map::Entry::Vacant(slot) => {
            slot.insert(Some(SourceFnRecursionInfo {
                sig: sig.clone(),
                attrs: attrs.to_vec(),
                block: block.clone(),
            }));
        }
        std::collections::btree_map::Entry::Occupied(mut slot) => {
            slot.insert(None);
        }
    }
}

/// Final-segment identifiers of every function-or-method call syntactically in
/// `block` (path calls by last segment, method calls by method name). Skips
/// leading-`::` absolute/external paths. Name-approximate by design.
fn block_called_function_names(block: &Block) -> BTreeSet<String> {
    let mut collector = crate::mode_paths::PathCallCollector::default();
    collector.visit_block(block);
    collector
        .calls
        .iter()
        .filter(|call| !call.leading_colon)
        .map(|call| call.fn_name().to_string())
        .filter(|name| !name.is_empty())
        .collect()
}

/// Extra recursion-graph edges for calls made THROUGH a function-item value bound to
/// a local: `let f = some_fn; ...; f(args)` really calls `some_fn`, but the direct
/// collector sees `f(args)` as calling the local `f` (which is not a file function),
/// so a recursion cycle routed through fn-item values is invisible to it and bypasses
/// the ill-founded-recursion suppression (`la` and `lb` calling each other through
/// `let x = lb; x()` would publish circular `ensures` unchecked).
///
/// Resolvable aliases are followed transitively and lexical block shadows are
/// restored. If a called local cannot be resolved, or a tracked binding is
/// reassigned, `complete` becomes false and the caller is conservatively treated
/// as recursive.
fn fn_value_call_edges(block: &Block) -> FnValueCallEdges {
    let mut collector = FnValueCallCollector::default();
    syn::visit::Visit::visit_block(&mut collector, block);
    FnValueCallEdges {
        edges: collector.edges,
        complete: collector.complete,
    }
}

#[derive(Debug, PartialEq, Eq)]
struct FnValueCallEdges {
    edges: BTreeSet<String>,
    complete: bool,
}

#[derive(Clone)]
enum FnValueBinding {
    Known(String),
    Unknown,
}

struct FnValueCallCollector {
    bindings: std::collections::HashMap<String, FnValueBinding>,
    edges: BTreeSet<String>,
    complete: bool,
}

impl Default for FnValueCallCollector {
    fn default() -> Self {
        Self {
            bindings: std::collections::HashMap::new(),
            edges: BTreeSet::new(),
            complete: true,
        }
    }
}

impl FnValueCallCollector {
    fn path_binding(&self, expr: &syn::Expr) -> Option<FnValueBinding> {
        let syn::Expr::Path(expr_path) = expr else {
            return None;
        };
        if expr_path.qself.is_some() || expr_path.path.leading_colon.is_some() {
            return None;
        }
        let last = expr_path.path.segments.last()?;
        if expr_path.path.segments.len() == 1 {
            if let Some(binding) = self.bindings.get(&last.ident.to_string()) {
                return Some(binding.clone());
            }
        }
        Some(FnValueBinding::Known(last.ident.to_string()))
    }

    fn local_binding(&self, local: &syn::Local) -> FnValueBinding {
        local
            .init
            .as_ref()
            .filter(|init| init.diverge.is_none())
            .and_then(|init| self.path_binding(&init.expr))
            .unwrap_or(FnValueBinding::Unknown)
    }

    fn pat_idents(pat: &syn::Pat) -> Vec<String> {
        #[derive(Default)]
        struct Collector(Vec<String>);

        impl<'ast> syn::visit::Visit<'ast> for Collector {
            fn visit_pat_ident(&mut self, pat: &'ast syn::PatIdent) {
                self.0.push(pat.ident.to_string());
                syn::visit::visit_pat_ident(self, pat);
            }
        }

        let mut collector = Collector::default();
        collector.visit_pat(pat);
        collector.0
    }
}

impl<'ast> syn::visit::Visit<'ast> for FnValueCallCollector {
    fn visit_block(&mut self, block: &'ast syn::Block) {
        let incoming = self.bindings.clone();
        syn::visit::visit_block(self, block);
        self.bindings = incoming;
    }

    fn visit_local(&mut self, local: &'ast syn::Local) {
        // Initializers execute in the pre-binding environment (`let f = f`).
        if let Some(init) = &local.init {
            self.visit_expr(&init.expr);
            if let Some((_, diverge)) = &init.diverge {
                self.visit_expr(diverge);
            }
        }
        for attr in &local.attrs {
            self.visit_attribute(attr);
        }
        self.visit_pat(&local.pat);

        let idents = Self::pat_idents(&local.pat);
        if idents.len() == 1 && matches!(&local.pat, syn::Pat::Ident(_)) {
            let binding = self.local_binding(local);
            self.bindings.insert(idents[0].clone(), binding);
        } else {
            for ident in idents {
                self.bindings.insert(ident, FnValueBinding::Unknown);
            }
        }
    }

    fn visit_expr_assign(&mut self, assign: &'ast syn::ExprAssign) {
        self.visit_expr(&assign.left);
        self.visit_expr(&assign.right);
        if let syn::Expr::Path(path) = &*assign.left {
            if path.qself.is_none()
                && path.path.leading_colon.is_none()
                && path.path.segments.len() == 1
            {
                let ident = path.path.segments[0].ident.to_string();
                let was_known = matches!(self.bindings.get(&ident), Some(FnValueBinding::Known(_)));
                if self.bindings.contains_key(&ident) {
                    // Persist incompleteness across a nested block restore: an
                    // assignment to an outer fn-value binding may reach a later call.
                    if was_known {
                        self.complete = false;
                    }
                    self.bindings.insert(ident, FnValueBinding::Unknown);
                }
            }
        }
    }

    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        if let syn::Expr::Path(expr_path) = &*call.func {
            if expr_path.qself.is_none()
                && expr_path.path.leading_colon.is_none()
                && expr_path.path.segments.len() == 1
            {
                let ident = expr_path.path.segments[0].ident.to_string();
                match self.bindings.get(&ident) {
                    Some(FnValueBinding::Known(target)) => {
                        self.edges.insert(target.clone());
                    }
                    Some(FnValueBinding::Unknown) => {
                        self.complete = false;
                    }
                    None => {}
                }
            }
        }
        syn::visit::visit_expr_call(self, call);
    }
}

/// Forward reachability over `edges` from `start` (inclusive).
fn reachable_forward(edges: &BTreeMap<String, BTreeSet<String>>, start: &str) -> BTreeSet<String> {
    let mut seen = BTreeSet::new();
    let mut stack = vec![start.to_string()];
    while let Some(current) = stack.pop() {
        if !seen.insert(current.clone()) {
            continue;
        }
        if let Some(callees) = edges.get(&current) {
            for callee in callees {
                if !seen.contains(callee) {
                    stack.push(callee.clone());
                }
            }
        }
    }
    seen
}

/// Reverse reachability over `edges` into `target` (inclusive).
fn reachable_backward(
    edges: &BTreeMap<String, BTreeSet<String>>,
    target: &str,
) -> BTreeSet<String> {
    let mut seen = BTreeSet::new();
    let mut stack = vec![target.to_string()];
    while let Some(current) = stack.pop() {
        if !seen.insert(current.clone()) {
            continue;
        }
        for (caller, callees) in edges {
            if callees.contains(&current) && !seen.contains(caller) {
                stack.push(caller.clone());
            }
        }
    }
    seen
}

/// Captures a trait-impl method body as a single pure return expression for the
/// auxiliary conformance check (see [`crate::ir::ConformanceMethodBody`]).
///
/// The receiver is canonicalized to `self` and each non-receiver parameter to
/// its positional name `__trust_vc_conf_arg_{i}`; the conformance pass renames
/// these onto its `__trust_vc_impl_*` surface positionally. This reuses the
/// SAME single-pure-return soundness gate as the inherent-method body axiom
/// (`classify_return_expression` + the no-`requires`/no-shadow guard), so the
/// captured text is the method's actual return value — never a contract or an
/// approximation. Returns `None` (leaving conformance on its prior body-axiom
/// path) for any body the gate rejects or that fails to re-parse; never errors,
/// so it cannot alter the verdict of any other extraction step.
fn capture_conformance_method_body(
    method: &syn::ImplItemFn,
) -> Option<crate::ir::ConformanceMethodBody> {
    // No `requires` clause and no parameter/`self` shadowing — exactly the gate
    // that makes a single-return body axiom sound. A requires-check error is
    // treated as "has requires" (skip), so capture never fails the file.
    if helper_has_requires_clause(&method.attrs).unwrap_or(true) || method_params_shadowed(method) {
        return None;
    }

    let mut param_count = 0usize;
    let mut rename_map: HashMap<String, String> = HashMap::new();
    for input in &method.sig.inputs {
        match input {
            FnArg::Receiver(_) => {}
            FnArg::Typed(pat_type) => {
                let Pat::Ident(pat_ident) = pat_type.pat.as_ref() else {
                    // Non-ident parameter pattern: cannot positionally rename
                    // soundly, so decline to capture.
                    return None;
                };
                rename_map.insert(
                    pat_ident.ident.to_string(),
                    format!("__trust_vc_conf_arg_{param_count}"),
                );
                param_count += 1;
            }
        }
    }

    let return_is_unit = matches!(method.sig.output, syn::ReturnType::Default);
    let return_value =
        match classify_return_expression(&method.block, return_is_unit, &BTreeSet::new()) {
            return_extract::ReturnExtraction::Single(value) => value,
            _ => return None,
        };
    // No struct registry is threaded into conformance-method-body capture, so an
    // owned-local field write inside a default method body renders without the
    // functional-update resolution (the pre-existing behavior for this path).
    let body = scoped_return_value_expression(&method.block, return_value, &[]);
    let mut body_expr: Expr = syn::parse_str(&body).ok()?;
    IdentRenamer { rename_map }.visit_expr_mut(&mut body_expr);

    Some(crate::ir::ConformanceMethodBody::new(
        quote!(#body_expr).to_string(),
        param_count,
    ))
}

fn apply_sibling_helper_functions(
    file: &File,
    target_func: &ItemFn,
    source_structs: Option<&SourceStructRegistry>,
    source_file_is_crate_root: Option<bool>,
    vc: &mut VerificationContext,
) -> TrustVcResult<()> {
    let source_functions = SourceFunctionRegistry::from_file(file);
    let aliases = block_use_function_aliases(&target_func.block);
    let ill_founded_recursive = ill_founded_recursive_function_names(file, vc);
    // Spec functions called transitively from a sibling helper's BODY must be
    // registered (signature + any defining axiom) before that helper's body
    // axiom is lowered, or the lowering fails with "unknown return type for
    // function '<spec>'". The target-driven `apply_referenced_specs` only
    // descends from the *target*, so a spec reached solely through an exec
    // sibling (e.g. `verify_all_constraints` → exec `eval_constraint` → opaque
    // spec `eval_terms`) is otherwise never registered. Build a function-local
    // catalog for each applied helper so its block `use` aliases cannot leak into
    // another helper's lexical scope, then register its referenced specs.
    // Canonicalize only the root references with the target's imports. Every
    // transitive edge is canonicalized below with the declaring helper's own
    // block aliases; reusing `aliases` there would leak the target import into a
    // different Rust scope and can bind a body axiom to the wrong function.
    let mut pending = referenced_helper_calls(target_func)
        .into_iter()
        .map(|reference| source_reference_with_aliases(reference, &aliases))
        .collect::<BTreeSet<_>>();
    let no_aliases = BTreeMap::new();
    let mut applied = BTreeSet::new();

    while let Some(reference) = pending.iter().next().cloned() {
        pending.remove(&reference);
        if !applied.insert(reference.clone()) {
            continue;
        }
        let Some(helper) = resolve_non_spec_source_function(
            &source_functions,
            &no_aliases,
            &reference.source_path,
            target_func,
        ) else {
            continue;
        };
        // Register spec functions the helper's body calls (transitively) so the
        // helper body axiom below can lower their applications.
        let helper_module = match function_discovery::enclosing_inline_module_path(file, helper) {
            function_discovery::EnclosingModuleResolution::Unique(path) => Some(path),
            function_discovery::EnclosingModuleResolution::Ambiguous => None,
        };
        validate_block_use_alias_resolution(
            file,
            helper,
            helper,
            helper_module.as_deref(),
            source_file_is_crate_root,
        )?;
        let mut spec_catalog = crate::spec_function_catalog::SpecFunctionCatalog::from_file(file);
        spec_catalog.register_exact_aliases(&block_use_function_aliases(&helper.block))?;
        spec_catalog.apply_referenced_specs(helper, vc)?;
        if let Some(def) = SiblingHelperDef::from_item_fn_with_name(
            &reference.call_symbol,
            helper,
            source_structs,
            vc,
            &ill_founded_recursive,
        )? {
            def.apply_to_context(vc);
        }
        let helper_aliases = block_use_function_aliases(&helper.block);
        for dependency in referenced_helper_calls(helper) {
            let dependency = source_reference_with_aliases(dependency, &helper_aliases);
            if resolve_non_spec_source_function(
                &source_functions,
                &no_aliases,
                &dependency.source_path,
                target_func,
            )
            .is_some()
                && !applied.contains(&dependency)
            {
                pending.insert(dependency);
            }
        }
    }

    Ok(())
}

fn apply_block_use_alias_helper_functions(
    file: &File,
    target_func: &ItemFn,
    source_structs: Option<&SourceStructRegistry>,
    vc: &mut VerificationContext,
) -> TrustVcResult<()> {
    let aliases = block_use_function_aliases(&target_func.block);
    if aliases.is_empty() {
        return Ok(());
    }

    let referenced_names = referenced_helper_call_symbols(target_func);
    let source_functions = SourceFunctionRegistry::from_file(file);
    let ill_founded_recursive = ill_founded_recursive_function_names(file, vc);
    for (alias, source_path) in aliases {
        if !referenced_names.contains(&alias) {
            continue;
        }
        let Some(helper) = source_functions.get(&source_path) else {
            continue;
        };
        // Spec aliases are registered by `SpecFunctionCatalog` above, which
        // preserves their opacity, recursion/decreases, and uninterpreted
        // semantics. Emitting one as a `SiblingHelperDef` would instead grant
        // an executable body axiom and could prove facts that the spec lane is
        // required to keep hidden. The catalog's exact-alias bridge handles
        // the positive `use m::test as test2` case without that authority leak.
        if helper.sig.ident == target_func.sig.ident || has_spec_attr(&helper.attrs) {
            continue;
        }
        if let Some(def) = SiblingHelperDef::from_item_fn_with_name(
            &alias,
            helper,
            source_structs,
            vc,
            &ill_founded_recursive,
        )? {
            def.apply_alias_to_context(vc)?;
        }
    }

    Ok(())
}

fn block_use_function_aliases(block: &Block) -> BTreeMap<String, String> {
    let mut collector = UseAliasCollector::default();
    collector.visit_block(block);
    collector
        .outer_aliases
        .into_iter()
        .filter_map(|(alias, source_paths)| {
            if source_paths.len() == 1 && !collector.bound_names.contains(&alias) {
                source_paths
                    .into_iter()
                    .next()
                    .map(|source_path| (alias, source_path))
            } else {
                None
            }
        })
        .collect()
}

/// Reject aliases whose Rust lexical identity cannot be represented by the
/// source lane's one-symbol-per-spelling model. Outer-block imports are the one
/// admitted shape. A nested import, duplicate import, or local binder with the
/// same spelling is rejected when that spelling is called; body imports are
/// also forbidden from retargeting function contract attributes, which live
/// outside the body scope.
fn validate_block_use_alias_resolution(
    file: &File,
    func: &ItemFn,
    source_identity_func: &ItemFn,
    enclosing_inline_module: Option<&[String]>,
    source_file_is_crate_root: Option<bool>,
) -> TrustVcResult<()> {
    let mut collector = UseAliasCollector::default();
    collector.visit_block(&func.block);
    for input in &func.sig.inputs {
        if let FnArg::Typed(pat_type) = input {
            collector.visit_pat(&pat_type.pat);
        }
    }

    if collector.outer_aliases.is_empty()
        && collector.nested_aliases.is_empty()
        && !collector.outer_has_glob
        && !collector.nested_has_glob
        && !collector.local_macro_contains_use
    {
        return Ok(());
    }

    let mut called = referenced_helper_call_symbols(func);
    // The generic helper collector intentionally ignores some proof-macro token
    // shapes. Alias safety must cover those too: use the spec catalog's
    // chain-/assert-by-aware call collector so `assert!(alias())` cannot hide a
    // nested-scope reference from this fail-closed gate.
    called.extend(crate::spec_function_catalog::called_names_in_block(
        &func.block,
    ));
    called.extend(visibility_target_names_in_block(&func.block));
    called.extend(expression_path_names_in_block(&func.block));
    let mut contract_names = referenced_target_contract_calls(func)?
        .into_iter()
        .map(|reference| reference.call_symbol)
        .collect::<BTreeSet<_>>();
    contract_names.extend(target_contract_expression_path_names(func)?);

    if let Some(alias) = collector
        .outer_absolute_aliases
        .iter()
        .find(|alias| called.contains(*alias))
    {
        return Err(TrustVcError::Encoding {
            context: "block use alias resolution",
            detail: format!(
                "absolute block use alias `{alias}` uses a leading `::`; that path is not \
                 crate-local provenance, so TrustVc fails closed instead of rebinding it to \
                 a same-spelled local module"
            ),
        });
    }

    if collector.outer_has_glob || collector.nested_has_glob {
        return Err(TrustVcError::Encoding {
            context: "block use alias resolution",
            detail: "block `use ...::*` imports are not source-symbol indexed; TrustVc fails \
                     closed instead of resolving a bare call through a same-spelled function \
                     from another Rust scope"
                .to_string(),
        });
    }

    if collector.local_macro_contains_use {
        return Err(TrustVcError::Encoding {
            context: "block use alias resolution",
            detail: "function-local macro_rules expansion contains a `use` item; macro-expanded \
                     imports are not lexical-scope indexed, so TrustVc fails closed instead of \
                     letting an expanded alias fall back to another source symbol"
                .to_string(),
        });
    }

    let used_relative_alias = collector
        .outer_non_crate_aliases
        .iter()
        .find(|alias| called.contains(*alias));
    if let Some(alias) = used_relative_alias {
        match enclosing_inline_module {
            Some(module) if module.is_empty() => {}
            Some(module) => {
                return Err(TrustVcError::Encoding {
                    context: "block use alias resolution",
                    detail: format!(
                        "relative block use alias `{alias}` occurs inside inline module `{}`; \
                         module-relative alias symbols are not yet provenance-indexed, so \
                         TrustVc fails closed (use an explicit `crate::` path)",
                        module.join("::")
                    ),
                });
            }
            None => {
                return Err(TrustVcError::Encoding {
                    context: "block use alias resolution",
                    detail: format!(
                        "cannot recover the exact enclosing module for relative block use \
                         alias `{alias}`; TrustVc fails closed instead of resolving it at \
                         crate root"
                    ),
                });
            }
        }
    }

    let used_crate_alias = collector
        .outer_aliases
        .keys()
        .filter(|alias| !collector.outer_non_crate_aliases.contains(*alias))
        .find(|alias| called.contains(*alias));
    if let Some(alias) = used_crate_alias {
        match source_file_is_crate_root {
            Some(true) => {}
            Some(false) => {
                return Err(TrustVcError::Encoding {
                    context: "block use alias resolution",
                    detail: format!(
                        "crate-root block use alias `{alias}` occurs in a non-root source \
                         file; cross-file block imports are not yet indexed, so TrustVc \
                         fails closed instead of resolving it against a file-local module"
                    ),
                });
            }
            None => {
                return Err(TrustVcError::Encoding {
                    context: "block use alias resolution",
                    detail: format!(
                        "cannot recover crate-root provenance for block use alias `{alias}`; \
                         TrustVc fails closed instead of guessing its source module"
                    ),
                });
            }
        }
    }

    for alias in collector.outer_aliases.keys() {
        if contract_names.contains(alias) {
            return Err(TrustVcError::Encoding {
                context: "block use alias resolution",
                detail: format!(
                    "function-body use alias `{alias}` is also referenced from a target \
                     contract attribute; body imports are not in attribute \
                     scope, so TrustVc fails closed instead of conflating the names"
                ),
            });
        }
    }

    let source_functions = SourceFunctionRegistry::from_file(file);
    for (alias, source_paths) in &collector.outer_aliases {
        if !called.contains(alias) {
            continue;
        }
        if source_paths.len() != 1 {
            return Err(TrustVcError::Encoding {
                context: "block use alias resolution",
                detail: format!(
                    "function-body alias `{alias}` has multiple possible import targets; \
                     scope-indexed resolution is unavailable, so TrustVc fails closed"
                ),
            });
        }
        if collector.bound_names.contains(alias) {
            return Err(TrustVcError::Encoding {
                context: "block use alias resolution",
                detail: format!(
                    "function-body alias `{alias}` is shadowed by a local/closure/match \
                     binding; TrustVc fails closed instead of assigning both values one \
                     solver symbol"
                ),
            });
        }

        let source_path = source_paths
            .iter()
            .next()
            .expect("one source path after ambiguity gate");
        let Some(source_helper) = source_functions.get(source_path) else {
            return Err(TrustVcError::Encoding {
                context: "block use alias resolution",
                detail: format!(
                    "function-body alias `{alias}` does not resolve to a source function \
                     at `{source_path}`; TrustVc fails closed instead of letting the bare \
                     spelling fall back to another helper kind or Rust scope"
                ),
            });
        };
        if source_path.contains("::") && !matches!(source_helper.vis, syn::Visibility::Public(_)) {
            return Err(TrustVcError::Encoding {
                context: "block use alias resolution",
                detail: format!(
                    "function-body alias `{alias}` targets non-public nested function \
                     `{source_path}`; exact module privacy is not yet indexed, so TrustVc \
                     fails closed instead of granting cross-module visibility"
                ),
            });
        }
        if source_path != alias && source_functions.get(alias).is_some() {
            return Err(TrustVcError::Encoding {
                context: "block use alias resolution",
                detail: format!(
                    "function-body alias `{alias}` shadows a different source helper; \
                     the source lane has one solver symbol per spelling, so TrustVc \
                     fails closed instead of conflating `{alias}` with `{source_path}`"
                ),
            });
        }
    }

    let active_aliases = collector
        .outer_aliases
        .keys()
        .filter(|alias| called.contains(*alias))
        .cloned()
        .collect::<BTreeSet<_>>();
    reject_alias_references_outside_function(file, source_identity_func, &active_aliases)?;

    for alias in collector.nested_aliases.keys() {
        if called.contains(alias) {
            return Err(TrustVcError::Encoding {
                context: "block use alias resolution",
                detail: format!(
                    "nested-block use alias `{alias}` is referenced by this function; \
                     nested import scopes are not yet symbol-indexed, so TrustVc fails \
                     closed instead of leaking the alias outside its Rust scope"
                ),
            });
        }
    }

    Ok(())
}

#[derive(Default)]
struct ExpressionPathNameCollector {
    names: BTreeSet<String>,
}

impl<'ast> Visit<'ast> for ExpressionPathNameCollector {
    fn visit_expr_path(&mut self, path: &'ast syn::ExprPath) {
        if path.qself.is_none()
            && path.path.leading_colon.is_none()
            && path.path.segments.len() == 1
        {
            if let Some(segment) = path.path.segments.first() {
                self.names.insert(segment.ident.to_string());
            }
        }
        syn::visit::visit_expr_path(self, path);
    }
}

fn expression_path_names_in_block(block: &Block) -> BTreeSet<String> {
    let mut collector = ExpressionPathNameCollector::default();
    collector.visit_block(block);
    collector.names
}

fn target_contract_expression_path_names(func: &ItemFn) -> TrustVcResult<BTreeSet<String>> {
    let mut collector = ExpressionPathNameCollector::default();
    for attr in &func.attrs {
        match path_last_segment(attr.path()).as_deref() {
            Some("requires" | "ensures" | "recommends" | "decreases") => {
                let expr =
                    contract_attribute_expr(attr).map_err(|source| TrustVcError::Encoding {
                        context: "block use alias resolution",
                        detail: format!(
                            "failed to parse target contract while checking body alias scope: {source}"
                        ),
                    })?;
                collector.visit_expr(&expr);
            }
            Some("contract") => {
                for clause in parse_target_contract_clauses(attr)? {
                    for expr in clause.args {
                        collector.visit_expr(&expr);
                    }
                }
            }
            _ => {}
        }
    }
    Ok(collector.names)
}

/// Every alias bridge is currently a query-global equality between two solver
/// symbols. Until symbols carry lexical-scope identity, that equality is sound
/// only when the alias spelling is absent from every OTHER source function: an
/// unrelated spec/helper body using the same bare name would otherwise inherit
/// the target body's import and could acquire a false defining axiom.
fn reject_alias_references_outside_function(
    file: &File,
    func: &ItemFn,
    active_aliases: &BTreeSet<String>,
) -> TrustVcResult<()> {
    if active_aliases.is_empty() {
        return Ok(());
    }

    let mut functions = Vec::new();
    collect_function_like_items(&file.items, &mut functions);
    let exact_matches = functions
        .iter()
        .enumerate()
        .filter_map(|(index, candidate)| {
            item_fn_source_identity_eq(candidate, func).then_some(index)
        })
        .collect::<Vec<_>>();
    let current_index = (exact_matches.len() == 1).then_some(exact_matches[0]);

    for (index, candidate) in functions.iter().enumerate() {
        if current_index == Some(index) {
            continue;
        }
        let referenced = function_source_reference_names(candidate)?;
        if let Some(alias) = active_aliases
            .iter()
            .find(|alias| referenced.contains(*alias))
        {
            return Err(TrustVcError::Encoding {
                context: "block use alias resolution",
                detail: format!(
                    "function-body alias `{alias}` is also referenced from source function \
                     `{}`; alias equalities are query-global until source symbols carry \
                     lexical-scope identity, so TrustVc fails closed instead of leaking the \
                     import into that function",
                    candidate.sig.ident
                ),
            });
        }
    }
    Ok(())
}

fn function_source_reference_names(func: &ItemFn) -> TrustVcResult<BTreeSet<String>> {
    let mut names = referenced_helper_call_symbols(func);
    names.extend(crate::spec_function_catalog::called_names_in_block(
        &func.block,
    ));
    names.extend(visibility_target_names_in_block(&func.block));
    names.extend(expression_path_names_in_block(&func.block));
    names.extend(
        referenced_target_contract_calls(func)?
            .into_iter()
            .map(|reference| reference.call_symbol),
    );
    names.extend(target_contract_expression_path_names(func)?);
    Ok(names)
}

fn collect_function_like_items(items: &[syn::Item], out: &mut Vec<ItemFn>) {
    for item in items {
        match item {
            syn::Item::Fn(item_fn) => out.push(item_fn.clone()),
            syn::Item::Impl(impl_block) => {
                for impl_item in &impl_block.items {
                    if let syn::ImplItem::Fn(method) = impl_item {
                        out.push(ItemFn {
                            attrs: method.attrs.clone(),
                            vis: method.vis.clone(),
                            sig: method.sig.clone(),
                            block: Box::new(method.block.clone()),
                        });
                    }
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    collect_function_like_items(inner_items, out);
                }
            }
            syn::Item::Trait(trait_block) => {
                for trait_item in &trait_block.items {
                    if let syn::TraitItem::Fn(method) = trait_item {
                        if let Some(block) = &method.default {
                            out.push(ItemFn {
                                attrs: method.attrs.clone(),
                                vis: syn::Visibility::Inherited,
                                sig: method.sig.clone(),
                                block: Box::new(block.clone()),
                            });
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

fn item_fn_source_identity_eq(left: &ItemFn, right: &ItemFn) -> bool {
    quote!(#left).to_string() == quote!(#right).to_string()
}

fn visibility_target_names_in_block(block: &Block) -> BTreeSet<String> {
    #[derive(Default)]
    struct Collector {
        names: BTreeSet<String>,
    }

    impl<'ast> Visit<'ast> for Collector {
        fn visit_macro(&mut self, mac: &'ast syn::Macro) {
            let macro_name = mac
                .path
                .segments
                .last()
                .map(|segment| segment.ident.to_string());
            if matches!(macro_name.as_deref(), Some("reveal" | "hide")) {
                if let Ok(path) = syn::parse2::<syn::Path>(mac.tokens.clone()) {
                    if path.leading_colon.is_none() && path.segments.len() == 1 {
                        if let Some(segment) = path.segments.first() {
                            if !matches!(segment.arguments, syn::PathArguments::Parenthesized(_)) {
                                self.names.insert(segment.ident.to_string());
                            }
                        }
                    }
                }
            }

            // `syn` does not visit macro token streams. Explicitly descend into
            // the proof block shapes the body extractor supports so a nested
            // alias used only by `reveal!`/`hide!` inside `assert_by!` remains
            // visible to the scope-safety gate.
            if let Some(proof_block) = crate::spec_function_catalog::by_block_proof_block(mac) {
                self.visit_block(&proof_block);
            }
            syn::visit::visit_macro(self, mac);
        }
    }

    let mut collector = Collector::default();
    collector.visit_block(block);
    collector.names
}

fn canonicalize_visibility_aliases(
    vc: &mut VerificationContext,
    exact_aliases: &HashMap<String, String>,
) {
    if exact_aliases.is_empty() {
        return;
    }

    let canonicalize = |obligation: &mut ProofObligation| {
        if matches!(
            obligation.kind,
            ObligationKind::Reveal | ObligationKind::Hide
        ) {
            if let Some(canonical) = exact_aliases.get(&obligation.name) {
                obligation.name.clone_from(canonical);
            }
        }
    };
    for obligation in &mut vc.obligations {
        canonicalize(obligation);
    }
    for obligations in vc.assert_by_scopes.values_mut() {
        for obligation in obligations {
            canonicalize(obligation);
        }
    }
    vc.hidden_fns = vc
        .hidden_fns
        .iter()
        .map(|name| {
            exact_aliases
                .get(name)
                .cloned()
                .unwrap_or_else(|| name.clone())
        })
        .collect();
}

#[derive(Default)]
struct UseAliasCollector {
    outer_aliases: BTreeMap<String, BTreeSet<String>>,
    outer_non_crate_aliases: BTreeSet<String>,
    /// Bindings introduced by `use ::path::item`. A leading-colon path is not
    /// crate-local provenance in Rust 2018+, so stripping it and looking up a
    /// same-spelled local module would be an unsound guess.
    outer_absolute_aliases: BTreeSet<String>,
    outer_has_glob: bool,
    nested_aliases: BTreeMap<String, BTreeSet<String>>,
    nested_has_glob: bool,
    local_macro_contains_use: bool,
    bound_names: BTreeSet<String>,
    block_depth: usize,
}

impl UseAliasCollector {
    fn token_stream_contains_use(tokens: proc_macro2::TokenStream) -> bool {
        tokens.into_iter().any(|token| match token {
            proc_macro2::TokenTree::Ident(ident) => ident == "use",
            proc_macro2::TokenTree::Group(group) => Self::token_stream_contains_use(group.stream()),
            proc_macro2::TokenTree::Punct(_) | proc_macro2::TokenTree::Literal(_) => false,
        })
    }

    fn contains_glob(tree: &syn::UseTree) -> bool {
        match tree {
            syn::UseTree::Path(path) => Self::contains_glob(&path.tree),
            syn::UseTree::Group(group) => group.items.iter().any(Self::contains_glob),
            syn::UseTree::Glob(_) => true,
            syn::UseTree::Name(_) | syn::UseTree::Rename(_) => false,
        }
    }

    fn collect_alias_names(tree: &syn::UseTree, aliases: &mut BTreeSet<String>) {
        match tree {
            syn::UseTree::Path(path) => Self::collect_alias_names(&path.tree, aliases),
            syn::UseTree::Name(name) => {
                aliases.insert(name.ident.to_string());
            }
            syn::UseTree::Rename(rename) => {
                aliases.insert(rename.rename.to_string());
            }
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    Self::collect_alias_names(item, aliases);
                }
            }
            syn::UseTree::Glob(_) => {}
        }
    }

    fn collect_tree(
        aliases: &mut BTreeMap<String, BTreeSet<String>>,
        prefix: &mut Vec<String>,
        tree: &syn::UseTree,
    ) {
        match tree {
            syn::UseTree::Path(path) => {
                prefix.push(path.ident.to_string());
                Self::collect_tree(aliases, prefix, &path.tree);
                prefix.pop();
            }
            syn::UseTree::Name(name) => {
                let alias = name.ident.to_string();
                let source_path = normalized_use_source_path(prefix, &alias);
                aliases.entry(alias).or_default().insert(source_path);
            }
            syn::UseTree::Rename(rename) => {
                let alias = rename.rename.to_string();
                let source_path = normalized_use_source_path(prefix, &rename.ident.to_string());
                aliases.entry(alias).or_default().insert(source_path);
            }
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    Self::collect_tree(aliases, prefix, item);
                }
            }
            syn::UseTree::Glob(_) => {}
        }
    }

    fn collect_non_crate_aliases(
        prefix: &mut Vec<String>,
        tree: &syn::UseTree,
        aliases: &mut BTreeSet<String>,
    ) {
        match tree {
            syn::UseTree::Path(path) => {
                prefix.push(path.ident.to_string());
                Self::collect_non_crate_aliases(prefix, &path.tree, aliases);
                prefix.pop();
            }
            syn::UseTree::Name(name) => {
                if prefix.first().map(String::as_str) != Some("crate") {
                    aliases.insert(name.ident.to_string());
                }
            }
            syn::UseTree::Rename(rename) => {
                if prefix.first().map(String::as_str) != Some("crate") {
                    aliases.insert(rename.rename.to_string());
                }
            }
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    Self::collect_non_crate_aliases(prefix, item, aliases);
                }
            }
            syn::UseTree::Glob(_) => {}
        }
    }
}

impl<'ast> Visit<'ast> for UseAliasCollector {
    fn visit_block(&mut self, block: &'ast Block) {
        self.block_depth += 1;
        syn::visit::visit_block(self, block);
        self.block_depth -= 1;
    }

    fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
        let mut prefix = Vec::new();
        let is_outer = self.block_depth == 1;
        if Self::contains_glob(&item.tree) {
            if is_outer {
                self.outer_has_glob = true;
            } else {
                self.nested_has_glob = true;
            }
        }
        let aliases = if is_outer {
            &mut self.outer_aliases
        } else {
            &mut self.nested_aliases
        };
        Self::collect_tree(aliases, &mut prefix, &item.tree);
        if is_outer {
            if item.leading_colon.is_some() {
                Self::collect_alias_names(&item.tree, &mut self.outer_absolute_aliases);
            }
            let mut prefix = Vec::new();
            Self::collect_non_crate_aliases(
                &mut prefix,
                &item.tree,
                &mut self.outer_non_crate_aliases,
            );
        }
    }

    fn visit_pat_ident(&mut self, pat: &'ast syn::PatIdent) {
        self.bound_names.insert(pat.ident.to_string());
        syn::visit::visit_pat_ident(self, pat);
    }

    // Local item bodies/modules establish independent Rust scopes. Their use
    // declarations must be analyzed when that item itself is verified, not as
    // aliases of the enclosing target function.
    fn visit_item_fn(&mut self, _item: &'ast ItemFn) {}

    fn visit_item_mod(&mut self, _item: &'ast syn::ItemMod) {}

    fn visit_item_macro(&mut self, item: &'ast syn::ItemMacro) {
        if item
            .mac
            .path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "macro_rules")
            && Self::token_stream_contains_use(item.mac.tokens.clone())
        {
            self.local_macro_contains_use = true;
        }
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        // `syn` treats macro tokens as opaque. Descend into the proof-block
        // shapes the body extractor understands so an import inside
        // `assert_by!` / `assert_forall_by!` is classified as NESTED rather
        // than silently falling back to a same-spelled outer function.
        if let Some(proof_block) = crate::spec_function_catalog::by_block_proof_block(mac) {
            self.visit_block(&proof_block);
        }
        syn::visit::visit_macro(self, mac);
    }
}

fn normalized_use_source_path(prefix: &[String], leaf: &str) -> String {
    let mut path = prefix
        .iter()
        .filter(|segment| segment.as_str() != "crate" && segment.as_str() != "self")
        .cloned()
        .collect::<Vec<_>>();
    path.push(leaf.to_string());
    path.join("::")
}

#[derive(Debug, Clone)]
struct SiblingHelperParam {
    name: String,
    bound_name: String,
    ty: TrustVcType,
    erased_shared_ref: bool,
}

#[derive(Debug, Clone)]
struct SiblingHelperDef {
    name: String,
    params: Vec<SiblingHelperParam>,
    return_ty: TrustVcType,
    body_condition: Option<String>,
    trigger: Option<String>,
}

impl SiblingHelperDef {
    /// The first declaration of a body-local exec alias must own a fresh solver
    /// symbol. Ordinary sibling registration historically overwrites identical
    /// helper entries, but doing that for an alias could silently rebind a const,
    /// trait helper, or another source function that lives outside the import's
    /// Rust scope.
    fn apply_alias_to_context(&self, ctx: &mut VerificationContext) -> TrustVcResult<()> {
        if ctx.helper_functions_typed.contains_key(&self.name) {
            return Err(TrustVcError::Encoding {
                context: "block use alias resolution",
                detail: format!(
                    "function-body alias `{}` conflicts with an existing helper identity; \
                     TrustVc fails closed instead of rebinding one solver symbol",
                    self.name
                ),
            });
        }
        self.apply_to_context(ctx);
        Ok(())
    }

    fn from_item_fn_with_name(
        name: &str,
        item_fn: &ItemFn,
        source_structs: Option<&SourceStructRegistry>,
        ctx: &VerificationContext,
        ill_founded_recursive: &BTreeSet<String>,
    ) -> TrustVcResult<Option<Self>> {
        if when_used_as_spec_target_path(&item_fn.attrs)?.is_some() {
            return Ok(None);
        }
        let name = name.to_string();
        let Some(return_ty) = helper_return_type(&item_fn.sig, source_structs) else {
            return Ok(None);
        };
        if return_ty.contains_opaque() {
            return Ok(None);
        }
        let Some(params) = helper_params(&item_fn.sig, source_structs, ctx)? else {
            return Ok(None);
        };
        if params.iter().any(|param| param.ty.contains_opaque()) {
            return Ok(None);
        }

        let (body_condition, trigger) = if helper_has_requires_clause(&item_fn.attrs)?
            || params_shadowed_in_body(item_fn)
            || self_recursive_body_axiom_unsound(
                &item_fn.sig.ident.to_string(),
                &item_fn.block,
                &item_fn.attrs,
            )
            || ill_founded_recursive.contains(&item_fn.sig.ident.to_string())
        {
            (None, None)
        } else {
            match classify_return_expression(
                &item_fn.block,
                return_ty == TrustVcType::Unit,
                &BTreeSet::new(),
            ) {
                return_extract::ReturnExtraction::Single(return_value) => {
                    let scoped_return = scoped_return_value_expression(
                        &item_fn.block,
                        return_value,
                        &ctx.struct_types,
                    );
                    let Ok(mut renamed_return) = syn::parse_str::<Expr>(&scoped_return) else {
                        return Ok(None);
                    };
                    let mut rename_map = HashMap::new();
                    for param in &params {
                        rename_map.insert(param.name.clone(), param.bound_name.clone());
                    }
                    IdentRenamer { rename_map }.visit_expr_mut(&mut renamed_return);
                    let call_args = params
                        .iter()
                        .map(|param| param.bound_name.as_str())
                        .collect::<Vec<_>>()
                        .join(", ");
                    let trigger = format!("{name}({call_args})");
                    let body = quote!(#renamed_return).to_string();
                    (Some(format!("{trigger} == {body}")), Some(trigger))
                }
                return_extract::ReturnExtraction::Missing
                | return_extract::ReturnExtraction::Multiple(_)
                | return_extract::ReturnExtraction::Ambiguous(_) => (None, None),
            }
        };

        Ok(Some(Self {
            name,
            params,
            return_ty,
            body_condition,
            trigger,
        }))
    }

    fn from_when_used_as_spec_with_name(
        name: &str,
        exec_fn: &ItemFn,
        spec_fn: &ItemFn,
        spec_name: &str,
        source_structs: Option<&SourceStructRegistry>,
        ctx: &VerificationContext,
    ) -> TrustVcResult<Self> {
        reject_when_used_as_spec_unsupported_signature(exec_fn, spec_fn)?;
        let name = name.to_string();
        let return_ty = helper_return_type(&exec_fn.sig, source_structs).ok_or_else(|| {
            TrustVcError::Encoding {
                context: "extract when_used_as_spec helper",
                detail: format!(
                    "when_used_as_spec exec function `{}` has unsupported return type",
                    exec_fn.sig.ident
                ),
            }
        })?;
        if return_ty.contains_opaque() {
            return Err(TrustVcError::Encoding {
                context: "extract when_used_as_spec helper",
                detail: format!(
                    "when_used_as_spec exec function `{}` has opaque return type",
                    exec_fn.sig.ident
                ),
            });
        }
        let params = helper_params(&exec_fn.sig, source_structs, ctx)?.ok_or_else(|| {
            TrustVcError::Encoding {
                context: "extract when_used_as_spec helper",
                detail: format!(
                    "when_used_as_spec exec function `{}` uses unsupported parameters",
                    exec_fn.sig.ident
                ),
            }
        })?;
        let spec_params = helper_params(&spec_fn.sig, source_structs, ctx)?.ok_or_else(|| {
            TrustVcError::Encoding {
                context: "extract when_used_as_spec helper",
                detail: format!(
                    "when_used_as_spec spec function `{}` uses unsupported parameters",
                    spec_fn.sig.ident
                ),
            }
        })?;
        if params.len() != spec_params.len()
            || params
                .iter()
                .zip(&spec_params)
                .any(|(left, right)| left.ty != right.ty)
        {
            return Err(TrustVcError::Encoding {
                context: "extract when_used_as_spec helper",
                detail: "when_used_as_spec function should have the same parameters".to_string(),
            });
        }
        if params.iter().any(|param| param.ty.contains_opaque()) {
            return Err(TrustVcError::Encoding {
                context: "extract when_used_as_spec helper",
                detail: format!(
                    "when_used_as_spec exec function `{}` has opaque parameter type",
                    exec_fn.sig.ident
                ),
            });
        }
        let spec_return_ty = helper_return_type(&spec_fn.sig, source_structs).ok_or_else(|| {
            TrustVcError::Encoding {
                context: "extract when_used_as_spec helper",
                detail: format!(
                    "when_used_as_spec spec function `{}` has unsupported return type",
                    spec_fn.sig.ident
                ),
            }
        })?;
        if return_ty != spec_return_ty {
            return Err(TrustVcError::Encoding {
                context: "extract when_used_as_spec helper",
                detail: "when_used_as_spec function should have the same return types".to_string(),
            });
        }
        let call_args = params
            .iter()
            .map(|param| param.bound_name.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        let trigger = format!("{name}({call_args})");
        let body = format!("{spec_name}({call_args})");
        Ok(Self {
            name,
            params,
            return_ty,
            body_condition: Some(format!("{trigger} == {body}")),
            trigger: Some(trigger),
        })
    }

    fn apply_to_context(&self, ctx: &mut VerificationContext) {
        let helper_params = self
            .params
            .iter()
            .map(|param| (param.name.clone(), param.ty.clone()))
            .collect();
        ctx.declare_helper_function_typed(&self.name, self.return_ty.clone(), helper_params);

        let Some(body_condition) = &self.body_condition else {
            return;
        };
        let Some(trigger) = &self.trigger else {
            return;
        };

        for param in &self.params {
            if ctx.get_variable_type(&param.bound_name).is_none() {
                ctx.declare_var_typed(&param.bound_name, param.ty.clone());
            }
            if param.erased_shared_ref {
                ctx.mark_erased_shared_ref_var(&param.bound_name);
            }
        }

        let axiom_name = format!("__body_axiom_{}_sibling_helper", self.name);
        if ctx
            .obligations()
            .iter()
            .any(|obligation| obligation.name() == axiom_name)
        {
            return;
        }

        ctx.push_obligation(
            ProofObligation::broadcast_assume(axiom_name, body_condition.clone())
                .with_bound_vars(
                    self.params
                        .iter()
                        .map(|param| param.bound_name.clone())
                        .collect(),
                )
                .with_trigger_patterns(vec![vec![trigger.clone()]]),
        );
    }
}

fn helper_return_type(
    sig: &syn::Signature,
    source_structs: Option<&SourceStructRegistry>,
) -> Option<TrustVcType> {
    match &sig.output {
        syn::ReturnType::Type(_, ty) => {
            let ty_str = extract_type_name(ty);
            Some(
                source_structs
                    .and_then(|registry| registry.resolve_type_string(&ty_str))
                    .unwrap_or_else(|| TrustVcType::parse_or_opaque(&ty_str)),
            )
        }
        syn::ReturnType::Default if sig.asyncness.is_none() => Some(TrustVcType::Unit),
        syn::ReturnType::Default => None,
    }
}

fn helper_params(
    sig: &syn::Signature,
    source_structs: Option<&SourceStructRegistry>,
    ctx: &VerificationContext,
) -> TrustVcResult<Option<Vec<SiblingHelperParam>>> {
    let mut used_names: BTreeSet<String> = ctx
        .variables()
        .iter()
        .map(|variable| variable.name.clone())
        .collect();
    let mut params = Vec::with_capacity(sig.inputs.len());

    for input in &sig.inputs {
        let FnArg::Typed(pat_type) = input else {
            return Ok(None);
        };
        let syn::Pat::Ident(pat_ident) = &*pat_type.pat else {
            return Ok(None);
        };
        let name = pat_ident.ident.to_string();
        let ty_str = extract_type_name(&pat_type.ty);
        let ty = source_structs
            .and_then(|registry| registry.resolve_type_string(&ty_str))
            .unwrap_or_else(|| TrustVcType::parse_or_opaque(&ty_str));
        let erased_shared_ref = param_extract::is_erased_shared_ref_type(&pat_type.ty);
        let bound_name = fresh_sibling_bound_name(&mut used_names, &sig.ident.to_string(), &name);
        params.push(SiblingHelperParam {
            name,
            bound_name,
            ty,
            erased_shared_ref,
        });
    }

    Ok(Some(params))
}

fn fresh_sibling_bound_name(
    used_names: &mut BTreeSet<String>,
    fn_name: &str,
    param_name: &str,
) -> String {
    let base = format!("__trust_vc_sibling_{}_{}", fn_name, param_name);
    if used_names.insert(base.clone()) {
        return base;
    }

    for i in 1.. {
        let candidate = format!("{base}_{i}");
        if used_names.insert(candidate.clone()) {
            return candidate;
        }
    }
    unreachable!("unbounded suffix search must find a fresh name")
}

fn has_spec_attr(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "spec")
    })
}

fn has_allow_in_spec_attr(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        let segments = attr
            .path()
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect::<Vec<_>>();
        matches!(segments.as_slice(), [name] if name == "allow_in_spec")
            || matches!(
                segments.as_slice(),
                [prefix, name] if (prefix == "trust_vc" || prefix == "verifier") && name == "allow_in_spec"
            )
    })
}

fn when_used_as_spec_target_path(attrs: &[syn::Attribute]) -> TrustVcResult<Option<String>> {
    for attr in attrs {
        let segments = attr
            .path()
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect::<Vec<_>>();
        let is_when_used = matches!(segments.as_slice(), [name] if name == "when_used_as_spec")
            || matches!(
                segments.as_slice(),
                [prefix, name] if (prefix == "trust_vc" || prefix == "verifier") && name == "when_used_as_spec"
            );
        if !is_when_used {
            continue;
        }
        let path = attr
            .parse_args::<syn::Path>()
            .map_err(|source| TrustVcError::Encoding {
                context: "extract when_used_as_spec helper",
                detail: format!("failed to parse when_used_as_spec target path: {source}"),
            })?;
        return Ok(source_path_from_path(&path));
    }
    Ok(None)
}

fn source_path_from_path(path: &syn::Path) -> Option<String> {
    if path.leading_colon.is_some() {
        return None;
    }
    let mut segments = path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>();
    while segments
        .first()
        .is_some_and(|segment| segment == "crate" || segment == "self")
    {
        segments.remove(0);
    }
    (!segments.is_empty()).then(|| segments.join("::"))
}

fn reject_when_used_as_spec_unsupported_signature(
    exec_fn: &ItemFn,
    spec_fn: &ItemFn,
) -> TrustVcResult<()> {
    if !exec_fn.sig.generics.params.is_empty() || !spec_fn.sig.generics.params.is_empty() {
        return Err(TrustVcError::Encoding {
            context: "extract when_used_as_spec helper",
            detail: "when_used_as_spec function should have the same type bounds; generic mappings are unsupported".to_string(),
        });
    }
    if exec_fn.sig.inputs.iter().any(fn_arg_is_mut_reference)
        || spec_fn.sig.inputs.iter().any(fn_arg_is_mut_reference)
    {
        return Err(TrustVcError::Encoding {
            context: "extract when_used_as_spec helper",
            detail: "when_used_as_spec not supported for function with &mut param".to_string(),
        });
    }
    Ok(())
}

fn fn_arg_is_mut_reference(input: &FnArg) -> bool {
    match input {
        FnArg::Typed(pat_type) => type_is_mut_reference(&pat_type.ty),
        FnArg::Receiver(receiver) => receiver.mutability.is_some(),
    }
}

fn type_is_mut_reference(ty: &Type) -> bool {
    match ty {
        Type::Reference(reference) => reference.mutability.is_some(),
        Type::Paren(paren) => type_is_mut_reference(&paren.elem),
        Type::Group(group) => type_is_mut_reference(&group.elem),
        _ => false,
    }
}

fn referenced_helper_calls(func: &ItemFn) -> BTreeSet<SourceCallReference> {
    let mut collector = HelperCallCollector::default();
    for attr in &func.attrs {
        match path_last_segment(attr.path()).as_deref() {
            Some("requires" | "ensures") => {
                if let Some(expr) = contract_attr_expr_lenient(attr) {
                    collector.visit_expr(&expr);
                }
            }
            Some("contract") => {
                if let Ok(clauses) = parse_target_contract_clauses(attr) {
                    for clause in clauses {
                        if matches!(clause.name.to_string().as_str(), "requires" | "ensures") {
                            for expr in clause.args {
                                collector.visit_expr(&expr);
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
    collector.visit_block(&func.block);
    collector.calls
}

fn referenced_helper_call_symbols(func: &ItemFn) -> BTreeSet<String> {
    referenced_helper_calls(func)
        .into_iter()
        .map(|reference| reference.call_symbol)
        .collect()
}

#[derive(Default)]
struct HelperCallCollector {
    calls: BTreeSet<SourceCallReference>,
}

impl<'ast> Visit<'ast> for HelperCallCollector {
    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        if !expr_call_has_closure_arg(call) {
            if let Some(reference) = source_call_reference(call) {
                self.calls.insert(reference);
            }
        }
        syn::visit::visit_expr_call(self, call);
    }

    fn visit_expr_method_call(&mut self, call: &'ast syn::ExprMethodCall) {
        if expr_method_call_has_closure_arg(call) {
            for arg in &call.args {
                self.visit_expr(arg);
            }
            self.visit_expr(&call.receiver);
            return;
        }
        syn::visit::visit_expr_method_call(self, call);
    }

    fn visit_expr_macro(&mut self, expr_macro: &'ast syn::ExprMacro) {
        self.visit_macro(&expr_macro.mac);
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        if is_solver_mode_assert_macro(mac) {
            if let Ok(parsed) = crate::parse_solver_mode_assert(mac.tokens.clone()) {
                self.visit_expr(&parsed.condition);
                for requires in &parsed.requires {
                    self.visit_expr(requires);
                }
            }
            return;
        }
        syn::visit::visit_macro(self, mac);
    }
}

fn expr_call_has_closure_arg(call: &syn::ExprCall) -> bool {
    call.args
        .iter()
        .any(|arg| matches!(arg, syn::Expr::Closure(_)))
}

fn expr_method_call_has_closure_arg(call: &syn::ExprMethodCall) -> bool {
    call.args
        .iter()
        .any(|arg| matches!(arg, syn::Expr::Closure(_)))
}

fn is_solver_mode_assert_macro(mac: &syn::Macro) -> bool {
    mac.path.segments.last().is_some_and(|segment| {
        segment.ident == "assert_by_nonlinear"
            || segment.ident == "assert_by_bit_vector"
            || segment.ident == "assert_by_compute"
    })
}

fn params_shadowed_in_body(item_fn: &ItemFn) -> bool {
    let param_names = item_fn
        .sig
        .inputs
        .iter()
        .filter_map(|input| match input {
            FnArg::Typed(pat_type) => match &*pat_type.pat {
                syn::Pat::Ident(pat_ident) => Some(pat_ident.ident.to_string()),
                _ => None,
            },
            FnArg::Receiver(_) => None,
        })
        .collect::<BTreeSet<_>>();
    let mut collector = ParamShadowCollector {
        param_names: &param_names,
        shadowed: false,
    };
    collector.visit_block(&item_fn.block);
    collector.shadowed
}

struct ParamShadowCollector<'a> {
    param_names: &'a BTreeSet<String>,
    shadowed: bool,
}

impl<'ast> Visit<'ast> for ParamShadowCollector<'_> {
    fn visit_pat_ident(&mut self, pat: &'ast syn::PatIdent) {
        if self.param_names.contains(&pat.ident.to_string()) {
            self.shadowed = true;
            return;
        }
        syn::visit::visit_pat_ident(self, pat);
    }
}

struct IdentRenamer {
    rename_map: HashMap<String, String>,
}

impl VisitMut for IdentRenamer {
    fn visit_expr_path_mut(&mut self, path: &mut syn::ExprPath) {
        if path.qself.is_none() && path.path.segments.len() == 1 {
            let segment = &mut path.path.segments[0];
            if let Some(replacement) = self.rename_map.get(&segment.ident.to_string()) {
                segment.ident = syn::Ident::new(replacement, Span::call_site());
            }
        }
        syn::visit_mut::visit_expr_path_mut(self, path);
    }
}
