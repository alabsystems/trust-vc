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
pub(crate) mod function_discovery;
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

/// TEST-ONLY convenience: locate a function by name, discarding the reason for a
/// miss.
///
/// Deliberately `#[cfg(test)]`. This signature is what let the reason go missing
/// in the first place — the caller had to invent one, and the library gate
/// invented "not found" for a name that was present twice. Production code has
/// exactly one path (`resolve_function_in_file(..).require_unique(..)`), which
/// cannot lose it. In-module tests only ever ask "is it there", never "why not",
/// so they keep the terse form without reopening the hole.
#[cfg(test)]
fn find_function<'a>(file: &'a File, name: &str) -> Option<&'a ItemFn> {
    match function_discovery::resolve_function_in_file(file, name) {
        function_discovery::FunctionResolution::Unique(func) => Some(func),
        function_discovery::FunctionResolution::NotFound
        | function_discovery::FunctionResolution::Ambiguous(_) => None,
    }
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
///
/// POINTER WIDTH: the listing runs at ONE width (the pinned directive's, else
/// the host's) and that is not an under-approximation. The walk that produces
/// these names (`encoder::verification::trait_conformance`) enumerates
/// `trait_impl_decls` × `trait_decls` and formats `{Trait}::{method} for
/// {Type}` from the DECLARATIONS; the `List` mode never lowers a body (its
/// `unbuildable` arm returns `None` and keeps walking). Nothing in that walk
/// reads [`crate::ir::pointer_width`], so the name SET is width-invariant even
/// though each name's VERDICT is not. Verification is where the width plan
/// belongs, and that is where it now lives.
pub fn list_trait_conformance_obligations(file_path: &str) -> TrustVcResult<Vec<String>> {
    let (pinned_width, ast) = read_conformance_source(file_path)?;
    let ctx = prepare_file_conformance_context(file_path, pinned_width, &ast)?;
    let _guard = pinned_width.map(crate::ir::PointerWidthGuard::install);
    let prepared = crate::prepared_context::prepare_context(&ctx)?;
    crate::encoder::AYEncoder::list_conformance_obligations(&prepared)
}

/// The pointer width(s) a FILE's conformance obligations must be checked at.
///
/// The conformance analogue of the function lane's plan (`verify_unit_at_width`
/// / [`verify_unit_dual_width`]). It exists because the conformance lane used to
/// have NO plan at all: it installed only the pinned `global size_of usize`
/// directive and otherwise solved once at the HOST width, so an impl whose body
/// violates its trait `ensures` at a 32-bit `usize` came back `Verified` on a
/// 64-bit host. That is a cardinal false verify, and it is not hypothetical —
///
/// ```ignore
/// #[trust_vc::trait_spec]
/// trait Doubler {
///     #[trust_vc::requires(x <= 4294967295)]
///     #[trust_vc::ensures(result >= x)]
///     fn dbl(x: usize) -> usize;
/// }
/// #[trust_vc::trait_impl]
/// impl Doubler for Wide { fn dbl(x: usize) -> usize { x * 2 } }
/// ```
///
/// reported `"trait impl conformance Doubler::dbl for Wide": "verified"` from
/// `cargo trust-vc check`, while adding `global size_of usize == 4` to the SAME
/// file produced a counterexample (`x = 4294967295`, `result = 4294967294`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConformanceWidthPlan {
    /// A `global size_of usize == N` directive pins the target architecture, or
    /// nothing in the file is width-dependent: one pass, unchanged behavior.
    Single,
    /// No directive and the file IS width-dependent. Rust permits both a 32-bit
    /// and a 64-bit `usize`, so the impl conforms only if it conforms at BOTH.
    Dual,
}

/// Decides the [`ConformanceWidthPlan`] for an already-parsed conformance source.
///
/// A pinned directive wins, exactly as in the function lane. Otherwise the
/// decision is delegated to `crate::ir::file_is_pointer_width_polymorphic` — the
/// same body `unit_is_pointer_width_polymorphic` runs for functions, minus the
/// per-function token scan that has no counterpart here (a conformance
/// obligation's "unit" is the impl, which is a file ITEM and is therefore
/// already covered by the file scan).
fn conformance_width_plan(pinned_width: Option<u32>, ast: &File) -> ConformanceWidthPlan {
    if pinned_width.is_some() {
        return ConformanceWidthPlan::Single;
    }
    if crate::ir::file_is_pointer_width_polymorphic(ast) {
        ConformanceWidthPlan::Dual
    } else {
        ConformanceWidthPlan::Single
    }
}

/// Verifies exactly ONE trait-impl conformance obligation of `file_path`,
/// addressed by the name [`list_trait_conformance_obligations`] reports.
///
/// This is the impl's own report channel. An unknown name fails CLOSED
/// (`Error`) and an impl body that cannot be lowered onto the conformance
/// surface fails CLOSED (`Unknown`) — neither may be mistaken for a discharged
/// obligation.
///
/// Runs under the file's [`ConformanceWidthPlan`]. For
/// [`ConformanceWidthPlan::Dual`] both widths must discharge, combined by the
/// SAME [`combine_dual_width_results`] the function lane uses, so the two lanes
/// agree on the verdict AND on the `_32bit`/`_64bit`/`_32bit_64bit` arch tag.
/// This can only ever ADD rejections relative to the previous single-width run.
pub fn verify_trait_conformance_obligation(
    file_path: &str,
    obligation_name: &str,
) -> TrustVcResult<VerifyResult> {
    // Parsing is pointer-width independent, so parse once; only extraction
    // (which bakes usize/isize widths into the IR) and verification re-run per
    // width, each under its own guard.
    let (pinned_width, ast) = read_conformance_source(file_path)?;
    match conformance_width_plan(pinned_width, &ast) {
        ConformanceWidthPlan::Single => {
            verify_conformance_at_width(file_path, pinned_width, &ast, obligation_name)
        }
        ConformanceWidthPlan::Dual => {
            let result_32 = {
                let _guard = crate::ir::PointerWidthGuard::install(32);
                verify_conformance_at_width(file_path, None, &ast, obligation_name)?
            };
            let result_64 = {
                let _guard = crate::ir::PointerWidthGuard::install(64);
                verify_conformance_at_width(file_path, None, &ast, obligation_name)?
            };
            Ok(combine_dual_width_results(result_32, result_64))
        }
    }
}

/// One conformance pass. `pinned_width` installs the directive's width (the
/// `Single`-plan case); under the `Dual` plan the caller has already installed
/// the pass width and passes `None` so nothing overrides it.
///
/// Extraction and verification are both inside the installed width: the
/// obligation set bakes in usize/isize bit-widths and the solver reads them
/// back, so the two must agree.
fn verify_conformance_at_width(
    file_path: &str,
    pinned_width: Option<u32>,
    ast: &File,
    obligation_name: &str,
) -> TrustVcResult<VerifyResult> {
    let ctx = prepare_file_conformance_context(file_path, pinned_width, ast)?;
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

/// Reads, directive-scans, strips, normalizes and parses a conformance source.
///
/// Split out of [`prepare_file_conformance_context`] so the dual-width plan can
/// parse ONCE and re-extract per width (parsing is pointer-width independent),
/// and so the plan decision and the extraction cannot drift onto two different
/// views of the same file.
///
/// The returned `pinned_width` has already been released — `pinned_width_from_guard`
/// drops the scanned guard — so the caller starts from an override-free state and
/// installs the width it actually wants per pass.
fn read_conformance_source(file_path: &str) -> TrustVcResult<(Option<u32>, File)> {
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
    Ok((pinned_width, ast))
}

/// Builds the FILE-level verification context that trait conformance is checked
/// against, independent of any particular function in the file.
///
/// Conformance obligations belong to the file's impls, not to a function, so
/// they must be checkable even when the file contains no function at all (an
/// `impl Tr for bool {}` with a violating inherited default is still an error).
/// A synthetic, contract-free probe function stands in as the "current"
/// function; every trait/impl/struct/helper registration is driven off the FILE,
/// exactly as in [`verify_function_from_file`].
///
/// Extraction runs under `pinned_width` when the file pins one; otherwise it
/// runs under whatever width the CALLER installed (the dual-width plan installs
/// 32 then 64 around this call), so the obligation set is always baked at the
/// width it will be solved at.
fn prepare_file_conformance_context(
    file_path: &str,
    pinned_width: Option<u32>,
    ast: &File,
) -> TrustVcResult<VerificationContext> {
    let probe_ident = syn::Ident::new(CONFORMANCE_PROBE_FN, Span::call_site());
    let probe: ItemFn = syn::parse_quote! {
        fn #probe_ident() {}
    };

    let _guard = pinned_width.map(crate::ir::PointerWidthGuard::install);
    let mut ctx = extract_verification_conditions_from_parts_inner(
        Some(ast),
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
    Ok(ctx)
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

    // Find the target function. Go through the SHARED renderer so this lane and
    // the CLI cannot disagree about why a name failed to resolve: an ambiguous
    // name is reported AS ambiguous, not laundered into "not found" (the name is
    // present — twice — and "not found" points the reader at the wrong thing).
    let func = function_discovery::resolve_function_in_file(&ast, func_name)
        .require_unique(func_name, file_path)
        .map_err(|detail| TrustVcError::Internal {
            context: "find function in verification source",
            detail,
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
        None if crate::ir::unit_is_pointer_width_polymorphic(Some(&ast), func) => {
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

// The width-polymorphism predicate that decides between the single-width and the
// dual-width plan lives in `crate::ir::unit_is_pointer_width_polymorphic`. It
// used to exist as a private copy HERE and a hand-copied second copy in
// `cargo-trust-vc`'s `verify.rs`; the two drifted (the CLI copy lost the numeric
// literal-suffix arm, so `4294967295usize + 1` planned a single host-width
// solve). Both entry points now call the ONE `ir` implementation so they cannot
// disagree again.

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
    // Two same-named traits in different modules is LEGAL Rust that stock
    // `rustc --edition 2021` compiles and runs, and `impl real::Tr for S` is not
    // ambiguous — the qualifier names exactly one declaration. Every trait
    // registry below is nevertheless keyed by a bare ident, so before anything
    // reads the file, delete the same-named declarations no impl header names.
    // What survives is a file with unique trait idents, which is the invariant
    // `reject_duplicate_trait_names` asserts further down and which the
    // last-segment-keyed lanes (trait bounds, supertraits, the receiver-kind
    // map, `trait_method_declares_requires`) silently depend on. Undecidable
    // shapes still fail the file CLOSED in here.
    // (`crate::trait_path_resolution::prune_shadowed_duplicate_traits`.)
    let pruned_file;
    let file = match file {
        Some(file) => {
            pruned_file = crate::trait_path_resolution::prune_shadowed_duplicate_traits(file)?;
            Some(pruned_file.as_ref().unwrap_or(file))
        }
        None => None,
    };

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
                file,
                func,
                enclosing_inline_module.as_deref(),
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

    // Quarantine every macro invocation whose NAME a lane below would give a
    // trust-vc meaning to but that this FILE does not bind to that macro — a
    // `macro_rules! assume` shadowing the prelude, a `use util::noop as assume`,
    // an `m::assume!` whose qualifier the lane discarded. Every one of those was
    // read as trust-vc's macro; `assume!` in particular was consumed as a spec
    // ASSUMPTION, which bought a false verify outright, and a shadowed
    // `matches!` got BOTH directions wrong at once. The offending name is
    // rewritten to a reserved ident no lane recognises, so all of them fail
    // closed without any of them learning about scopes. Runs BEFORE the
    // `matches!` desugar, whose recognition it is one of the consumers of.
    // See macro_scope.rs.
    let macro_quarantined;
    let func = match crate::macro_scope::quarantine_shadowed_spec_macros(
        func,
        file,
        enclosing_inline_module.as_deref(),
    ) {
        Some(owned) => {
            macro_quarantined = owned;
            &macro_quarantined
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

    // Desugar a `const`-NAME pattern into its literal value (`const K: u64 = 5;
    // match n { K => .. }` becomes `match n { 5 => .. }`). A bare ident in
    // pattern position is Rust ITEM resolution, not a binding, whenever a
    // `const` of that name is in scope — the pattern predicates decided this by
    // SPELLING, which vacuously discharged the sibling arms of an uppercase
    // const arm (a CARDINAL false verify: `match n { K => {} _ => assert!(false) }`
    // verified while the identical `5 => {}` refuted). Only a UNIQUE
    // file-top-level const with a literal initializer is folded; every other
    // declared const/static name is renamed to a reserved marker that all
    // pattern lanes fail closed on. Runs AFTER the `matches!` desugar so
    // `matches!(x, K)` has already become a `match`. See
    // const_pattern_desugar.rs.
    let const_pat_desugared;
    let func = match crate::const_pattern_desugar::desugar_const_patterns(func, file) {
        Some(owned) => {
            const_pat_desugared = owned;
            &const_pat_desugared
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
    let func = match crate::enum_int_cast_desugar::desugar_enum_int_cast(
        func,
        file,
        enclosing_inline_module.as_deref(),
    ) {
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
    // test_rlimit_inf). N grants DETERMINISTIC work — `N` upstream rlimit
    // units become `N × RLIMIT_UNIT_CONFLICTS` SAT conflicts — and
    // additionally FLOORS the wall backstop at the milliseconds the old
    // wall-only mapping would have granted, so raising `N` never shrinks the
    // envelope on either axis. Malformed arguments fail closed with the
    // verbatim upstream message. See `mode_attrs::extract_function_rlimit`.
    if let Some(rlimit) = crate::mode_attrs::extract_function_rlimit(&func.attrs)? {
        vc.set_rlimit_conflicts(rlimit.conflicts);
        if rlimit.wall_floor_ms > crate::encoder::verification_wall_backstop_default_ms() {
            vc.set_rlimit(rlimit.wall_floor_ms);
        }
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
    let source_structs =
        file.map(|file| SourceStructRegistry::from_file(file, enclosing_inline_module.as_deref()));
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
                    // Peel `&` / `&mut` / `&'a` before the lookup, mirroring
                    // `parse_or_opaque`, which strips references BEFORE applying
                    // its own ≤2-char type-param heuristic. Without this peel a
                    // reference-typed generic resolved by NAME LENGTH alone:
                    // `&T` landed on TypeParam via the heuristic while
                    // `&Item` / `&__TrustVcAPIT0` fell through to `Opaque` and
                    // sank the whole context to "unrecognized types". The
                    // reference decoration is dropped either way (a `&T`
                    // parameter is already modeled as its referent), so this
                    // only makes the DECLARED-name path agree with the
                    // heuristic path instead of trailing it.
                    let referent =
                        param_extract::strip_leading_references(var_type.trim()).trim_end();
                    declared_type_params
                        .contains(referent)
                        .then(|| TrustVcType::TypeParam(referent.to_string()))
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

    // The bound paths are resolved from the module the FUNCTION is written in —
    // a module-local `T: Tr` names its own module's declaration, exactly as it
    // does for `rustc`. An AMBIGUOUS enclosing module leaves resolution off and
    // the lane on its historical last-segment keying.
    trait_contracts::apply_function_trait_bounds(
        file,
        enclosing_inline_module.as_deref(),
        func,
        source_structs.as_ref(),
        &mut vc,
    )?;
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
    // Companion framing state for the SAME decision, covering the two shapes
    // `mut_ref_call_args` structurally cannot: a method call's arguments
    // (`h.hit(t)`), and a callee this file cannot resolve at all. See
    // `collect_file_method_arg_mut_flags` / `mut_ref_reborrowable_bindings`.
    let mut method_arg_mut_flags = BTreeMap::new();
    let mut mut_ref_reborrowable = BTreeSet::new();
    // Base context for the broadcast-lemma contract check, captured while the
    // spec catalog is in scope: the target's declarations plus EVERY catalogued
    // spec fn's definitional body axiom, forcibly revealed, and no obligations.
    // See `suppress_unestablished_broadcast_lemma_axioms`.
    let mut broadcast_check_base: Option<VerificationContext> = None;
    // Rendered `assert!` proof steps per broadcast-lemma axiom name, sharing the
    // contract's `__bcq_*` binder renaming.
    let mut broadcast_lemma_proof_steps: BTreeMap<String, Vec<String>> = BTreeMap::new();
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
        method_arg_mut_flags = collect_file_method_arg_mut_flags(file);
        mut_ref_reborrowable = mut_ref_reborrowable_bindings(func);
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
        // UNCONDITIONAL, and deliberately not gated on `#[trust_vc::trait_spec]`:
        // `register_trait_decl_self_receiver_kinds` below keys `(trait, method)`
        // by the trait's BARE ident over EVERY `trait` item in the file, so two
        // same-named traits silently overwrite each other's receiver kinds — a
        // `&mut self` method answered as `Ref` is the dropped-mutation false
        // verify that map exists to prevent. The same bare-name keying runs
        // through `TraitBound`, `TraitDecl::supertraits` and the trait contract
        // registry. None of them can represent such a file, so it is rejected
        // rather than resolved by declaration order.
        // Both gates are UNCONDITIONAL and share one index build. The type gate
        // is the counterpart for the receiver side: `apply_inherent_impl_methods`
        // above and `register_trait_impl_methods_for_concrete_types` in
        // `prepared_context::type_env` both key method metadata by the self
        // type's BARE ident, and the trait-impl pass defers to any existing
        // binding on the theory that "an inherent method shadows a trait
        // method". That is only true within ONE type; with the module path
        // erased, an inherent method on `inner::S` outranks the trait method of
        // a different top-level `S` and answers its call sites — a cardinal
        // false verify. No registry here can represent such a file.
        let scope_index = crate::trait_path_resolution::TraitScopeIndex::build(file);
        scope_index.reject_duplicate_trait_names()?;
        // TYPE SIDE: the duplicate-ident check is the cheap DETECTOR, not the
        // verdict. Two same-named types in different inline modules is legal
        // Rust that stock `rustc --edition 2021` compiles and runs, and a use
        // site that writes the bare name is not ambiguous — its module scope
        // names exactly one of them, exactly as it does for `rustc`. Failing the
        // FILE on the mere presence of the pair cost every legal program in it
        // (including functions that never mention the colliding name).
        //
        // So when the detector fires, the collision is RESOLVED against the
        // scopes that hold code, and only what resolution genuinely cannot
        // settle is rejected. See `resolve_duplicate_type_names_or_reject` for
        // why this is a resolution and not the trait side's prune.
        if scope_index.reject_duplicate_type_names().is_err() {
            resolve_duplicate_type_names_or_reject(file, enclosing_inline_module.as_deref())?;
        }
        // A macro that DECLARES a type is invisible to that walk, and the check
        // above only reaches a file where a VISIBLE duplicate already fired the
        // detector. A macro-declared type shadowing an outer one with no visible
        // duplicate was therefore still answered by the bare-name maps — a
        // confident WRONG shape, cardinal in both registries and in either
        // declaration order. Nothing can resolve it (the expansion is not in the
        // AST), so the narrowly-scoped shape is refused outright.
        reject_macro_shadowable_type_resolution(file, enclosing_inline_module.as_deref())?;
        register_trait_decl_self_receiver_kinds(&file.items, &mut vc);
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
        collect_source_broadcast_lemmas(
            file,
            &spec_catalog,
            &mut vc,
            &mut broadcast_lemma_proof_steps,
        )?;
        if vc
            .obligations()
            .iter()
            .any(|o| o.name().starts_with("__source_broadcast_"))
        {
            let mut base = vc.clone();
            base.obligations.clear();
            spec_catalog.apply_all_specs_revealed(&mut base);
            broadcast_check_base = Some(base);
        }
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
    // inherent and trait-supplied): CONJOIN the two `requires` sets.
    //
    // This used to drop the key entirely so NEITHER fired, justified as "a
    // missed obligation is always sound". That is TRUE FOR AN ASSUMPTION AND
    // FALSE FOR A `requires`: dropping it lets a precondition-VIOLATING call
    // through unflagged. It is the third member of the same class as the
    // receiver-shape drop (`body_extract.rs`) and the two-trait ambiguity drop
    // (`trait_contracts.rs`), both fixed.
    //
    // Conjunction is the sound resolution and the concern that motivated the
    // drop — "never emit a wrong `requires`" — is what picks it over the
    // disjunction. The call is one of the candidates and we cannot tell which,
    // so requiring BOTH is stronger than either: it over-rejects, never misses.
    // The disjunction would be weaker than either and would preserve the hole.
    // Both entries bind `self` (`TRAIT_RECEIVER_NAME`), so when the parameter
    // lists agree the clauses share binders and the call-site positional
    // substitution is well-formed for all of them.
    if let Some(file) = file {
        let inherent_method_call_contracts =
            trait_contracts::inherent_impl_method_requires(&file.items)?;
        for (key, contract) in inherent_method_call_contracts {
            match concrete_method_call_contracts.get_mut(&key) {
                Some(existing) if existing.param_names == contract.param_names => {
                    for clause in contract.requires {
                        if !existing.requires.contains(&clause) {
                            existing.requires.push(clause);
                        }
                    }
                }
                // Differing arity or parameter names: the clauses bind different
                // binders, so there is no well-formed conjunction and merging
                // would substitute against the wrong ones. Still drops.
                Some(_) => {
                    concrete_method_call_contracts.remove(&key);
                }
                None => {
                    concrete_method_call_contracts.insert(key, contract);
                }
            }
        }
    }

    // SOUNDNESS-CRITICAL: the ONE seed applied by BOTH the in-body obligation
    // lane (immediately below) and the return-value render lane (further down,
    // via `scoped_return_value_expression`). The two lanes decide the same
    // program, so they must start from the same caller state — seeding one and
    // not the other is what produced two cardinal false verifies in a row.
    // See `body_extract::CollectorLaneSeed`.
    let lane_seed = body_extract::CollectorLaneSeed {
        supported_mut_ref_param_targets: &supported_mut_ref_param_targets,
        mut_ref_call_args: &mut_ref_call_args,
        method_arg_mut_flags: &method_arg_mut_flags,
        mut_ref_reborrowable_bindings: &mut_ref_reborrowable,
        fn_bound_spec_fn_params: &fn_bound_spec_fn_param_names,
    };

    // Extract assertions from function body
    let mut_ref_post_state = if sibling_helper_contracts.is_empty()
        && trait_method_call_contracts.is_empty()
        && concrete_method_call_contracts.is_empty()
    {
        body_extract::extract_body_assertions_with_mut_ref_param_targets(
            &func.block,
            &mut vc,
            function_solver_mode,
            &lane_seed,
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
            &lane_seed,
        )?
    };

    // SOUNDNESS-CRITICAL (cardinal false-verify): drop any `#[trust_vc::broadcast]`
    // lemma axiom whose own contract does not establish its `ensures`.
    //
    // `collect_source_broadcast_lemmas` publishes `forall params. guard ==> ensures`
    // for every lemma WITHOUT checking it. A bogus lemma therefore injects a
    // CONTRADICTORY premise, and a contradictory premise proves everything — the
    // engine documents that against itself in `encoder/verification/assertion.rs`.
    // The `broadcast_vacuity_probe` backstop only fires when the assumption set is
    // INCONSISTENT; a lemma that is consistent but simply unestablished (the
    // ordinary case, an `ensures` over an `#[opaque]` spec fn) sails through it.
    //
    // WHY HERE AND NOT AT THE PUBLISH SITE. The check needs the definitional
    // spec-fn body axioms to be present, and at collector time they are NOT: a
    // spec fn referenced only from inside `ensures!()` / `assert!()` macro tokens
    // is registered during BODY EXTRACTION, which runs after the collector.
    // Measured — the context holds ZERO obligations at collector time, so a check
    // placed there proves `bcf(c) == c` with nothing known about `bcf` and
    // suppresses every legitimate lemma. Running after extraction is what makes
    // the definitional axioms available. This is still extraction-local: it never
    // re-enters `extract_verification_conditions_from_parts_inner`.
    //
    // Removing the obligation here is exactly equivalent to never publishing it.
    suppress_unestablished_broadcast_lemma_axioms(
        &mut vc,
        broadcast_check_base.as_ref(),
        &broadcast_lemma_proof_steps,
    );

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
                // Fail-closed, same reasoning as the `Missing` arm below: a
                // return value the renderer declines to model (today: a
                // `let PAT = … else { return … }` tail whose PAT's refutability
                // cannot be decided) would otherwise leave `result`
                // unconstrained or, worse, bound to a conditional whose
                // condition was guessed.
                let Some((return_str, havoc_deps)) = scoped_return_value_expression(
                    &func.block,
                    return_value,
                    &vc.struct_types,
                    Some(&vc),
                    &lane_seed,
                ) else {
                    return Err(TrustVcError::Internal {
                        context: "extract verification conditions",
                        detail: format!(
                            "Function '{}' has a return expression that cannot be soundly \
                             modeled — postconditions referencing `{}` would be unsound",
                            func.sig.ident, result_var
                        ),
                    });
                };
                // The rendered value may read a fresh symbol standing for the
                // arbitrary state a binding is in after an unmodelled mutation
                // (`fn g(t: &mut impl Ctr) -> int { t.bump(); t.a() }`). Declare
                // it here or `result == …` names a variable that does not exist.
                declare_havoc_dependencies(&mut vc, havoc_deps);
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
                //
                // Every clause must render: the disjunction is only an
                // over-approximation while it lists ALL the possible return
                // values. Silently dropping one that failed to render would
                // narrow `result` to a strict subset of what the body can
                // return, which is the unsound direction — so a single
                // unmodelable value fails the whole extraction closed.
                //
                // SOUNDNESS (per-clause havoc symbols must stay DISTINCT): each
                // clause renders against its own throwaway context, whose fresh
                // unmodelled-mutation-havoc names restart from zero and only
                // avoid collisions with names ALREADY declared in `vc`. Rendering
                // the clauses in a batch would therefore let two branches mint the
                // same name for two unrelated arbitrary states, and identifying
                // them removes models where they differ — which NARROWS `result`,
                // the unsound direction this whole arm exists to avoid. Declaring
                // each clause's symbols before rendering the next makes the next
                // render skip them.
                let mut clauses = Vec::with_capacity(return_exprs.len());
                for return_value in &return_exprs {
                    let Some((return_str, havoc_deps)) = scoped_return_value_expression(
                        &func.block,
                        *return_value,
                        &vc.struct_types,
                        Some(&vc),
                        &lane_seed,
                    ) else {
                        return Err(TrustVcError::Internal {
                            context: "extract verification conditions",
                            detail: format!(
                                "Function '{}' has a multi-path return value that cannot be \
                                 soundly modeled — postconditions referencing `{}` would be \
                                 unsound",
                                func.sig.ident, result_var
                            ),
                        });
                    };
                    declare_havoc_dependencies(&mut vc, havoc_deps);
                    clauses.push(format!("({result_var} == {return_str})"));
                }
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

/// Fail closed when a postcondition reads a `&mut <collection-or-array>` parameter
/// (`Vec`/`[T]`/`HashSet`/`HashMap`/…, modeled as
/// `Seq`/`Set`/`Map`/`Multiset`/`Array`)
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
                        | TrustVcType::Array(_, _)
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

/// Renders the canonical return value of `block` as a scoped-value expression
/// string, or `None` when the value is not modelable and the caller must
/// DECLINE to bind it.
///
/// `ctx` supplies the declared variable types a `let … else` tail needs to type
/// its scrutinee; pass `None` only where no context exists.
///
/// The second tuple element lists fresh unmodelled-mutation-havoc symbols the
/// rendered value reads. A caller that USES the string must declare them
/// (`declare_havoc_dependencies`); a caller that cannot must decline whenever
/// the list is non-empty. See [`body_extract::ScopedReturnRender`].
fn scoped_return_value_expression(
    block: &Block,
    return_value: return_extract::ReturnValue<'_>,
    struct_types: &[StructDef],
    ctx: Option<&VerificationContext>,
    seed: &body_extract::CollectorLaneSeed<'_>,
) -> Option<(String, Vec<(String, TrustVcType)>)> {
    match return_value {
        return_extract::ReturnValue::Expr(return_expr) => {
            let (rendered, havoc_deps, _) =
                scoped_return_expression(block, return_expr, struct_types, ctx, 0, seed)?;
            Some((rendered, havoc_deps))
        }
        return_extract::ReturnValue::Conditional {
            local,
            then_value,
            else_value,
            ..
        } => {
            // SOUNDNESS-CRITICAL. The condition selects between the two values;
            // getting it wrong in EITHER direction erases a reachable return.
            // The one authority on it is the obligation collector's own let-else
            // handler, which is type-aware and fails closed — this lane used to
            // carry a hand-copied predicate that had drifted into answering
            // `"true"` for every pattern it did not recognize, which made the
            // else value unreachable and discharged the postcondition against
            // the then value alone (cardinal false verify). `None` here means
            // the model is declined outright; an unmodelled return is an
            // over-rejection, not a hole.
            let condition = body_extract::extract_tail_let_else_match_condition(block, local, ctx)?;
            // The two branch values become ONE model (`if C { .. } else { .. }`),
            // so their havoc symbols must be DISJOINT: each render starts its
            // fresh-name counter where the previous one stopped. Sharing a name
            // between the branches would identify two unrelated arbitrary states
            // and remove the models in which they differ — narrowing `result`.
            let (then_value, mut havoc_deps, next_havoc_index) =
                scoped_return_expression(block, then_value, struct_types, ctx, 0, seed)?;
            let (else_value, else_deps, _) = scoped_return_expression(
                block,
                else_value,
                struct_types,
                ctx,
                next_havoc_index,
                seed,
            )?;
            havoc_deps.extend(else_deps);
            Some((
                format!("if {condition} {{ {then_value} }} else {{ {else_value} }}"),
                havoc_deps,
            ))
        }
        return_extract::ReturnValue::Unit => Some(("()".to_string(), Vec::new())),
    }
}

/// Declares the fresh unmodelled-mutation-havoc symbols a return render depends
/// on, so the rendered value is a well-formed model in THIS context.
///
/// Each symbol is unconstrained by construction — it denotes the arbitrary state
/// a binding is in after a call whose effect is not modeled — so declaring it is
/// never a strengthening. Nothing else may reference it: the names come from the
/// render's own throwaway context and carry a `__post_mut_` / `__havoc_` infix.
fn declare_havoc_dependencies(vc: &mut VerificationContext, deps: Vec<(String, TrustVcType)>) {
    for (name, ty) in deps {
        if vc.get_variable_type(&name).is_none() {
            vc.declare_var_typed(&name, ty);
        }
    }
}

/// Renders the return expression, together with any fresh
/// unmodelled-mutation-havoc symbols the rendered value READS. The caller must
/// declare those symbols before using the render — see
/// [`body_extract::ScopedReturnRender`].
fn scoped_return_expression(
    block: &Block,
    return_expr: &Expr,
    struct_types: &[StructDef],
    ctx: Option<&VerificationContext>,
    havoc_index_base: usize,
    seed: &body_extract::CollectorLaneSeed<'_>,
) -> Option<(String, Vec<(String, TrustVcType)>, usize)> {
    let render = body_extract::extract_scoped_return_expression(
        block,
        return_expr,
        struct_types,
        ctx,
        havoc_index_base,
        seed,
    );
    // SOUNDNESS-CRITICAL. The raw token fallback below is the caller answering
    // for a render that declined, and for a return expression whose nested
    // blocks carry statement-position mutations that answer is WRONG in the
    // false-verify direction: `if f { bump(t); t.n } else { bump(t); t.n }`
    // re-emitted verbatim reads both branch tails against the ENTRY `t`.
    // `ScopedReturnRender::raw_fallback_unsound` says so; propagate the decline
    // instead of overwriting it. Every caller of this function already treats
    // `None` as "decline the model" (a dropped body axiom, or the
    // `TrustVcError::Internal` fail-closed on the function under extraction).
    if render.rendered.is_none() && render.raw_fallback_unsound {
        return None;
    }
    Some((
        render
            .rendered
            .unwrap_or_else(|| extract_expr_string(return_expr)),
        render.havoc_dependencies,
        render.next_havoc_index,
    ))
}

// NOTE: the let-else match condition and its variant tester used to be
// hand-copied here. They now live once, in
// `body_extract::pattern_match_condition_for_scoped_value` (reached via
// `extract_tail_let_else_match_condition`), because the copy had silently
// drifted away from the original on every axis that decides soundness. Do not
// reintroduce a local predicate for this.

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
    /// Inline-module-qualified path (`app::util::f`) → declaration.
    functions: BTreeMap<String, ItemFn>,
    /// Qualified paths claimed by MORE THAN ONE structurally different
    /// declaration — the `#[cfg]`-arm shape, which this per-file syn walk cannot
    /// evaluate. They are struck from `functions` and fail closed.
    ambiguous_paths: BTreeSet<String>,
    /// Every inline-module path in the file, including the file root. Used to
    /// resolve a call whose use-site scope could not be pinned down: only a
    /// spelling that names the SAME declaration from every module resolves.
    module_scopes: BTreeSet<Vec<String>>,
}

/// How a call path is ROOTED, read from the spelling at the use site.
///
/// `functions` is keyed by inline-module path, so a written spelling can only be
/// matched against it once the module it is relative to is known.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
enum CallPathRoot {
    /// A plain relative spelling (`f`, `util::f`, `super::f`), resolved against
    /// the use site's own inline module.
    #[default]
    Relative,
    /// `crate::`-rooted, or a spelling canonicalized through a block `use`
    /// alias. Matched against the FILE root only: this walk cannot tell whether
    /// the file it was handed IS the crate root, and an alias target is a
    /// crate-relative `use` path, so file-root matching is the only reading
    /// either one ever had.
    FileRoot,
    /// `self::`-rooted: the use site's own module and nothing else.
    SelfModule,
}

/// `module::segments` joined into a `functions` key.
fn qualified_function_key(module: &[String], segments: &[String]) -> String {
    module
        .iter()
        .chain(segments.iter())
        .cloned()
        .collect::<Vec<_>>()
        .join("::")
}

impl SourceFunctionRegistry {
    fn from_file(file: &File) -> Self {
        let mut collected = SourceFunctionCollection::default();
        collect_source_functions_from_items(&file.items, &mut Vec::new(), &mut collected);
        let mut registry = Self {
            functions: collected.functions,
            ambiguous_paths: collected.ambiguous,
            module_scopes: collected.scopes,
        };
        for path in &registry.ambiguous_paths {
            registry.functions.remove(path);
        }
        registry
    }

    fn get(&self, path: &str) -> Option<&ItemFn> {
        self.functions.get(path)
    }

    /// The declaration a call spelled `written` and rooted `root` names when it
    /// is written inside inline module `scope`.
    ///
    /// SOUNDNESS (FV-A, the call-path twin of the FV-1 type-registry hole): the
    /// registry has always been keyed by the DECLARATION's module path while the
    /// lookup used the spelling as WRITTEN, i.e. read as file-root-relative. A
    /// `util::f(x)` written inside `mod app` therefore resolved to a top-level
    /// `mod util`'s `f` — a different body, a different `requires` and a
    /// different `ensures` from the one Rust calls. Resolving against the use
    /// site's own module, innermost first and then outward, is the walk Rust
    /// does, restricted to what a per-file syn AST exposes; everything it cannot
    /// see returns `None`, which every caller turns into an opaque call.
    ///
    /// Order-independence is by construction: scope decides, never source
    /// position.
    fn resolve_key(
        &self,
        written: &str,
        root: CallPathRoot,
        scope: Option<&[String]>,
    ) -> Option<String> {
        let mut segments = written
            .split("::")
            .map(str::to_string)
            .collect::<Vec<String>>();
        if segments.is_empty() || segments.iter().any(String::is_empty) {
            return None;
        }
        let starts_with_super = segments.first().is_some_and(|segment| segment == "super");

        match root {
            CallPathRoot::FileRoot => {
                if starts_with_super {
                    return None;
                }
                let key = segments.join("::");
                return self.functions.contains_key(&key).then_some(key);
            }
            CallPathRoot::SelfModule => {
                if starts_with_super {
                    return None;
                }
                let key = qualified_function_key(scope?, &segments);
                return self.functions.contains_key(&key).then_some(key);
            }
            CallPathRoot::Relative => {}
        }

        if starts_with_super {
            // `super::` names exactly as many levels up as there are `super`s;
            // walking further outward would be a guess, so it fails closed.
            let mut base = scope?.to_vec();
            while segments.first().is_some_and(|segment| segment == "super") {
                segments.remove(0);
                base.pop()?;
            }
            if segments.is_empty() {
                return None;
            }
            let key = qualified_function_key(&base, &segments);
            return self.functions.contains_key(&key).then_some(key);
        }

        let Some(scope) = scope else {
            // The use site's module could not be pinned down (no unique
            // declaration site). Resolve only a spelling that names the SAME
            // declaration from every module in the file — the reading is then
            // scope-independent, so no scope needs to be known.
            let mut candidates = BTreeSet::new();
            for module in &self.module_scopes {
                let key = qualified_function_key(module, &segments);
                if self.functions.contains_key(&key) {
                    candidates.insert(key);
                }
            }
            return (candidates.len() == 1)
                .then(|| candidates.into_iter().next().expect("one candidate"));
        };

        (0..=scope.len()).rev().find_map(|depth| {
            let key = qualified_function_key(&scope[..depth], &segments);
            self.functions.contains_key(&key).then_some(key)
        })
    }

    fn resolve(
        &self,
        written: &str,
        root: CallPathRoot,
        scope: Option<&[String]>,
    ) -> Option<(&ItemFn, String)> {
        let key = self.resolve_key(written, root, scope)?;
        let item_fn = self.functions.get(&key)?;
        Some((item_fn, key))
    }
}

/// One walk over a file's items: the module-qualified function map, the paths it
/// could not settle, and every inline-module scope it saw.
#[derive(Default)]
struct SourceFunctionCollection {
    functions: BTreeMap<String, ItemFn>,
    ambiguous: BTreeSet<String>,
    scopes: BTreeSet<Vec<String>>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct SourceCallReference {
    source_path: String,
    call_symbol: String,
    root: CallPathRoot,
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
        // An alias target is a crate-relative `use` path, never a spelling
        // relative to the calling module — keep it on the file-root reading it
        // has always had rather than re-rooting it at the use site's scope.
        reference.root = CallPathRoot::FileRoot;
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
    let root = match segments.first().map(String::as_str) {
        Some("crate") => CallPathRoot::FileRoot,
        Some("self") => CallPathRoot::SelfModule,
        _ => CallPathRoot::Relative,
    };
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
        root,
    })
}

fn call_function_symbol(call: &syn::ExprCall) -> Option<String> {
    source_call_reference(call).map(|reference| reference.call_symbol)
}

/// `Type::method` for a QUALIFIED-UFCS call `<H as B>::tb(&h, t)`, matching the
/// key `file_associated_fn_signatures` records for `impl B for H { fn tb }`.
///
/// `source_call_reference` declines any path carrying a `qself`, so
/// `call_function_symbol` answers `None` for this spelling and the argument
/// framing had nothing to look up. That is not a reason to treat the arguments
/// as unwritable: only the CONTRACT routing differs between `H::tb(&h, t)` and
/// `<H as B>::tb(&h, t)`.
fn qualified_ufcs_call_symbol(call: &syn::ExprCall) -> Option<String> {
    let syn::Expr::Path(path) = &*call.func else {
        return None;
    };
    let qself = path.qself.as_ref()?;
    let type_name = impl_self_type_last_segment(&qself.ty)?;
    let method = path.path.segments.last()?.ident.to_string();
    Some(format!("{type_name}::{method}"))
}

fn collect_source_functions_from_items(
    items: &[syn::Item],
    prefix: &mut Vec<String>,
    out: &mut SourceFunctionCollection,
) {
    out.scopes.insert(prefix.clone());
    for item in items {
        match item {
            syn::Item::Fn(item_fn) => {
                let mut path = prefix.clone();
                path.push(item_fn.sig.ident.to_string());
                let key = path.join("::");
                match out.functions.entry(key.clone()) {
                    std::collections::btree_map::Entry::Vacant(slot) => {
                        slot.insert(item_fn.clone());
                    }
                    std::collections::btree_map::Entry::Occupied(existing) => {
                        // One module path, two declarations: only a `#[cfg]` pair
                        // can produce this in legal Rust, and which arm is live
                        // is not decidable from the syn AST. First-declaration-
                        // wins would pick a body/contract the compiler may not
                        // have selected, so the path fails closed. A
                        // token-identical re-declaration is not a collision:
                        // either reading gives the same facts.
                        let previous = existing.get();
                        if quote!(#previous).to_string() != quote!(#item_fn).to_string() {
                            out.ambiguous.insert(key);
                        }
                    }
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    prefix.push(module.ident.to_string());
                    collect_source_functions_from_items(inner_items, prefix, out);
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
    /// Bare type names declared MORE THAN ONCE in the file with structurally
    /// different definitions (typically a nested `mod` type shadowing a
    /// top-level one) that scope-relative resolution could NOT settle. These
    /// names are struck from `structs`/`enums`/`type_aliases` and fail closed.
    /// See `record_source_type_declaration`.
    ambiguous_type_names: BTreeSet<String>,
    /// Colliding bare names that scope-relative resolution DID settle, mapped to
    /// the inline-module path of the winning declaration (the one installed in
    /// the bare-keyed maps above). A use site that spells such a name with an
    /// explicit qualifier must name that same module — otherwise it means the
    /// other declaration, whose shape the bare carrier cannot represent, and
    /// resolution declines. See `SourceStructRegistry::written_path_names_module`.
    resolved_collision_modules: BTreeMap<String, Vec<String>>,
    /// The inline-module path of the function under verification, i.e. the scope
    /// a bare type name is written in. `None` when the caller could not pin it
    /// down (no file, or `EnclosingModuleResolution::Ambiguous`), in which case
    /// no collision is resolved at all.
    use_site_scope: Option<Vec<String>>,
}

impl SourceStructRegistry {
    /// Builds the registry for a use site in inline module `use_site_scope`.
    ///
    /// `use_site_scope` is `None` when the enclosing module of the verified
    /// function could not be pinned down; every collision then fails closed,
    /// which is the pre-resolution behaviour.
    fn from_file(file: &File, use_site_scope: Option<&[String]>) -> Self {
        let mut collected = SourceTypeCollection::default();
        collect_source_types_from_items(&file.items, &mut Vec::new(), &mut collected);
        let mut registry = Self {
            structs: collected.structs,
            enums: collected.enums,
            type_aliases: collected.type_aliases,
            ambiguous_type_names: collected.ambiguous,
            use_site_scope: use_site_scope.map(<[String]>::to_vec),
            ..Self::default()
        };

        // Resolution pass: a colliding bare name that EVERY code-bearing scope
        // in the file agrees on is not a guess — scope, not declaration order,
        // decides it, so both orders of the same two declarations answer the
        // same way. The winner replaces whatever first-declaration-wins left in
        // the bare-keyed maps (and clears the other two maps, so a struct/enum
        // collision cannot be settled by map priority either).
        if let Some(scope) = use_site_scope {
            let mut scopes = collected.index.fn_scopes.clone();
            scopes.insert(scope.to_vec());
            for name in registry.ambiguous_type_names.clone() {
                let Some(key) = collected.index.resolve_uniformly(&name, &scopes) else {
                    continue;
                };
                let module = key
                    .rsplit_once("::")
                    .map(|(module, _)| module.split("::").map(str::to_string).collect::<Vec<_>>())
                    .unwrap_or_default();
                let winning_struct = collected.qualified_structs.get(&key);
                let winning_enum = collected.qualified_enums.get(&key);
                let winning_alias = collected.qualified_type_aliases.get(&key);
                if winning_struct.is_none() && winning_enum.is_none() && winning_alias.is_none() {
                    continue;
                }
                registry.structs.remove(&name);
                registry.enums.remove(&name);
                registry.type_aliases.remove(&name);
                if let Some(template) = winning_struct {
                    registry.structs.insert(name.clone(), template.clone());
                }
                if let Some(template) = winning_enum {
                    registry.enums.insert(name.clone(), template.clone());
                }
                if let Some(template) = winning_alias {
                    registry.type_aliases.insert(name.clone(), template.clone());
                }
                registry.ambiguous_type_names.remove(&name);
                registry.resolved_collision_modules.insert(name, module);
            }
        }

        // Fail closed on every bare name resolution could not settle: keeping
        // either candidate would silently answer field/variant queries for a
        // type the use site may not name. Removing it makes the type
        // unrecognized, which the downstream lowering declines rather than
        // guesses at.
        for name in &registry.ambiguous_type_names {
            registry.structs.remove(name);
            registry.enums.remove(name);
            registry.type_aliases.remove(name);
        }
        collect_manual_partial_eq_impls(
            &crate::trait_path_resolution::TraitScopeIndex::build(file),
            &file.items,
            &mut Vec::new(),
            &mut registry.manual_partial_eq_types,
        );
        registry
    }

    /// True when the qualifier a use site actually WROTE names `module`, read
    /// from the use site's own scope.
    ///
    /// Only consulted for a bare name whose collision was resolved by scope: the
    /// bare-keyed maps hold exactly one of the two shapes, so a qualified
    /// spelling that names the OTHER one must decline rather than silently
    /// receive the winner's fields. `crate::`- and `::`-rooted spellings always
    /// decline: this walk cannot tell whether the file it was handed is the
    /// crate root, so it cannot confirm they name an inline module here.
    fn written_path_names_module(&self, path: &syn::Path, module: &[String]) -> bool {
        if path.leading_colon.is_some() {
            return false;
        }
        let mut segments: Vec<String> = path
            .segments
            .iter()
            .take(path.segments.len().saturating_sub(1))
            .map(|segment| segment.ident.to_string())
            .collect();
        let scope = self.use_site_scope.as_deref().unwrap_or(&[]);
        match segments.first().map(String::as_str) {
            Some("crate") => false,
            Some("self") => {
                segments.remove(0);
                let mut base = scope.to_vec();
                base.extend(segments);
                base == module
            }
            Some("super") => {
                let mut base = scope.to_vec();
                while segments.first().is_some_and(|segment| segment == "super") {
                    segments.remove(0);
                    if base.pop().is_none() {
                        return false;
                    }
                }
                base.extend(segments);
                base == module
            }
            _ => (0..=scope.len()).rev().any(|depth| {
                let mut base = scope[..depth].to_vec();
                base.extend(segments.iter().cloned());
                base == module
            }),
        }
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
        // A bare name whose collision was settled by SCOPE holds exactly one of
        // its two shapes here. A use site that wrote an explicit qualifier must
        // therefore name the winning module; if it names the other declaration,
        // the bare carrier cannot represent it and this fails closed.
        if let Some(module) = self.resolved_collision_modules.get(&name) {
            if (type_path.path.segments.len() > 1 || type_path.path.leading_colon.is_some())
                && !self.written_path_names_module(&type_path.path, module)
            {
                return None;
            }
        }
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
///
/// SOUNDNESS (rename), a MEASURED FALSE VERIFY. This is a FAIL-CLOSED gate, so a
/// name test it fails to recognise opens the hole it exists to close.
/// `use core::cmp::PartialEq as Eq2; impl Eq2 for P { fn eq(..) -> bool { false } }`
/// wrote the last segment `"Eq2"`, the impl went uncollected, `x == x` lowered
/// structurally and **VERIFIED** — against an `eq` that always returns `false`.
/// The byte-identical `impl PartialEq for P` correctly errored. Stock
/// `rustc --edition 2021` compiles and runs the renamed program and prints
/// `x == x is false`.
///
/// So the header is matched on its EXPANDED path — the import followed to what
/// it actually names — rather than on the spelling at the impl. Expansion only
/// substitutes what the program itself imported, so this cannot start collecting
/// a type whose `==` is genuinely structural.
fn collect_manual_partial_eq_impls(
    index: &crate::trait_path_resolution::TraitScopeIndex,
    items: &[syn::Item],
    module_path: &mut Vec<String>,
    out: &mut BTreeSet<String>,
) {
    for item in items {
        match item {
            syn::Item::Impl(item_impl) => {
                // A trait impl `impl [<..>] PartialEq [<..>] for T`, not a negative
                // `impl !PartialEq`. `item_impl.trait_` is `Some((polarity, path, _))`.
                if let Some((polarity, trait_path, _)) = &item_impl.trait_ {
                    let is_partial_eq = polarity.is_none()
                        && index
                            .expanded_path_segments(module_path, trait_path)
                            .last()
                            .is_some_and(|last| last == "PartialEq");
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
                    module_path.push(module.ident.to_string());
                    collect_manual_partial_eq_impls(index, inner_items, module_path, out);
                    module_path.pop();
                }
            }
            _ => {}
        }
    }
}

/// The registry key for a declaration of `name` inside inline module `module`
/// (`[] , "S"` → `"S"`; `["helper"], "S"` → `"helper::S"`).
fn qualified_type_key(module: &[String], name: &str) -> String {
    if module.is_empty() {
        name.to_string()
    } else {
        format!("{}::{}", module.join("::"), name)
    }
}

/// One source-level declaration of a bare type name: which inline module it was
/// written in, plus a token fingerprint used to tell "two spellings of the same
/// shape" from "two genuinely different types".
#[derive(Clone, Debug)]
struct SourceTypeDeclSite {
    module: Vec<String>,
    fingerprint: String,
}

/// A single non-glob `use` binding written in one inline module.
#[derive(Clone, Debug)]
struct SourceUseBinding {
    /// The name the binding introduces into its module (`use a::S as T` → `T`).
    in_scope_name: String,
    /// The path segments as written, MINUS the leaf.
    module_segments: Vec<String>,
    /// The last segment of the written path (`use a::S as T` → `S`).
    leaf: String,
    /// `use ::x::S` / `use crate::x::S` — rooted outside anything this
    /// per-file walk can see, so the binding is unresolvable by construction.
    out_of_file: bool,
}

/// A `use path::*` written in one inline module.
#[derive(Clone, Debug)]
struct SourceGlobImport {
    module_segments: Vec<String>,
    out_of_file: bool,
}

/// Scope facts about a file's type declarations: where each bare name was
/// declared, what each module imports, and which modules hold code. This is the
/// entire input to bare-name resolution — there is no `use` graph across files,
/// no macro expansion and no crate graph, so anything not visible here fails
/// closed rather than being guessed at.
#[derive(Default, Clone, Debug)]
struct SourceTypeScopeIndex {
    /// Bare name → every declaration of it in the file, in source order.
    declarations: BTreeMap<String, Vec<SourceTypeDeclSite>>,
    /// Module path → the non-glob `use` bindings written there.
    imports: BTreeMap<Vec<String>, Vec<SourceUseBinding>>,
    /// Module path → the globs written there.
    globs: BTreeMap<Vec<String>, Vec<SourceGlobImport>>,
    /// Module paths holding code-bearing items (`fn` / `impl` / `trait`, plus
    /// unexpanded item macros, whose contents this walk cannot see at all).
    ///
    /// These are exactly the scopes whose bodies, contracts and axioms can end
    /// up in ONE verification context alongside the verified function's — source
    /// functions, inherent impls and trait impls are all collected file-wide,
    /// not scope-locally. The registry carries ONE shape per bare name (the
    /// carrier name, the `StructDef` name and the SMT sort name are all the bare
    /// name), so a name may only be resolved when EVERY such scope resolves it
    /// identically; otherwise one scope's facts would be typed against the other
    /// scope's shape. `const`/`static` are deliberately NOT code-bearing here:
    /// `SourceConstRegistry` walks top-level items only and admits only scalar
    /// and array-length types, so a module const can never carry a user datatype
    /// into the context.
    fn_scopes: BTreeSet<Vec<String>>,
    /// Module path → the path of an unexpanded item-macro INVOCATION written
    /// there (`decl_s!();`), NOT a `macro_rules!` definition, which binds a
    /// macro name and declares no item.
    ///
    /// `fn_scopes` already records these scopes as code-bearing, but that only
    /// makes the scope's USE SITES participate in agreement. What is missing is
    /// the DECLARATION: an invocation that expands to `struct S { .. }` binds
    /// `S` in this module, and no walk over the unexpanded AST can see it. See
    /// [`SourceTypeScopeIndex::macro_shadowable_binding`].
    macro_scopes: BTreeMap<Vec<String>, String>,
}

/// An unexpanded item macro that could bind a bare type name NEARER to a use
/// site than the declaration the scope walk would otherwise choose.
struct MacroShadowRisk<'a> {
    /// The module holding the invocation.
    macro_module: &'a [String],
    /// The invoked macro's path, for the diagnostic.
    macro_name: &'a str,
    /// A bare type name declared strictly OUTSIDE `macro_module` — the one the
    /// walk would answer with, and the one the expansion could shadow.
    shadowable_name: &'a str,
    /// Where that declaration lives.
    shadowable_module: &'a [String],
}

/// Outcome of resolving a bare type name against one use-site scope.
#[derive(Clone, Debug, PartialEq, Eq)]
enum ScopeResolution {
    /// The name resolves to exactly this declaration (a `qualified_type_key`).
    Resolved(String),
    /// No sound answer: nothing in scope, several candidates, a glob that could
    /// supply a competing binding, or an import pointing out of this file.
    Unresolvable,
}

impl SourceTypeScopeIndex {
    /// The declaration of `leaf` in module `module`, when there is exactly one
    /// shape there. Two structurally different declarations under one module
    /// path (the `#[cfg]`-arm shape) resolve to nothing.
    fn unique_declaration(&self, module: &[String], leaf: &str) -> Option<String> {
        let sites = self.declarations.get(leaf)?;
        let mut fingerprints = BTreeSet::new();
        for site in sites {
            if site.module.as_slice() == module {
                fingerprints.insert(site.fingerprint.as_str());
            }
        }
        if fingerprints.len() == 1 {
            Some(qualified_type_key(module, leaf))
        } else {
            None
        }
    }

    /// The absolute (file-relative) module path(s) a `use`/glob path written in
    /// `module` could name. A plain-leading path is crate-root-relative under
    /// the 2015 reading and current-module-relative under the uniform-path
    /// reading; both are returned and the caller requires them to agree.
    fn use_path_targets(
        &self,
        module_segments: &[String],
        module: &[String],
    ) -> Option<Vec<Vec<String>>> {
        let mut segments = module_segments.to_vec();
        match segments.first().map(String::as_str) {
            Some("self") => {
                segments.remove(0);
                let mut base = module.to_vec();
                base.extend(segments);
                Some(vec![base])
            }
            Some("super") => {
                let mut base = module.to_vec();
                while segments.first().is_some_and(|segment| segment == "super") {
                    segments.remove(0);
                    base.pop()?;
                }
                base.extend(segments);
                Some(vec![base])
            }
            // `crate::` was already classified `out_of_file`: this walk cannot
            // tell whether the file it was handed IS the crate root, so a
            // `crate::`-rooted path may name a module in a completely different
            // file that happens to share a name with an inline one here.
            Some(_) => {
                let root_relative = segments.clone();
                let mut module_relative = module.to_vec();
                module_relative.extend(segments);
                if root_relative == module_relative {
                    Some(vec![root_relative])
                } else {
                    Some(vec![root_relative, module_relative])
                }
            }
            None => Some(vec![module.to_vec()]),
        }
    }

    /// The declaration a non-glob `use` binding names, or `None` when this file
    /// cannot settle it (out-of-file root, target module not declared here, or
    /// the two readings of a plain-leading path disagree).
    fn resolve_use_binding(&self, binding: &SourceUseBinding, module: &[String]) -> Option<String> {
        if binding.out_of_file {
            return None;
        }
        let targets = self.use_path_targets(&binding.module_segments, module)?;
        let mut resolved = BTreeSet::new();
        for target in &targets {
            // A target this file does not declare is an import from ANOTHER file
            // or crate. Falling through to an in-file declaration of the same
            // leaf would silently answer with a type the use site does not name.
            resolved.insert(self.unique_declaration(target, &binding.leaf)?);
        }
        if resolved.len() == 1 {
            resolved.into_iter().next()
        } else {
            None
        }
    }

    /// True when a glob only re-imports an ANCESTOR of the importing module —
    /// the `use super::*` shape. The scope walk already visits every ancestor,
    /// so such a glob contributes no candidate the walk would otherwise miss.
    fn glob_is_ancestor_only(&self, glob: &SourceGlobImport, module: &[String]) -> bool {
        if glob.out_of_file {
            return false;
        }
        let Some(targets) = self.use_path_targets(&glob.module_segments, module) else {
            return false;
        };
        targets
            .iter()
            .all(|target| target.len() < module.len() && module.starts_with(target))
    }

    /// Resolves bare `name` as written at a use site in module `scope`, walking
    /// the scope and its ancestors outward exactly as Rust does: an explicit
    /// item or `use` in the innermost module that has one wins, and a glob is
    /// only consulted where no explicit binding exists.
    ///
    /// This is deliberately NOT a Rust name resolver. Everything it cannot see —
    /// out-of-line modules, macro-generated items, other files, other crates —
    /// yields `Unresolvable`, which the caller turns into a decline.
    fn resolve_bare_name(&self, name: &str, scope: &[String]) -> ScopeResolution {
        for depth in (0..=scope.len()).rev() {
            let module = &scope[..depth];
            let mut candidates = BTreeSet::new();
            let mut saw_binding = false;

            if let Some(sites) = self.declarations.get(name) {
                if sites.iter().any(|site| site.module.as_slice() == module) {
                    saw_binding = true;
                    match self.unique_declaration(module, name) {
                        Some(key) => {
                            candidates.insert(key);
                        }
                        None => return ScopeResolution::Unresolvable,
                    }
                }
            }

            for binding in self.imports.get(module).into_iter().flatten() {
                if binding.in_scope_name != name {
                    continue;
                }
                saw_binding = true;
                match self.resolve_use_binding(binding, module) {
                    Some(key) => {
                        candidates.insert(key);
                    }
                    None => return ScopeResolution::Unresolvable,
                }
            }

            if saw_binding {
                return match candidates.len() {
                    1 => ScopeResolution::Resolved(
                        candidates.into_iter().next().expect("one candidate"),
                    ),
                    _ => ScopeResolution::Unresolvable,
                };
            }

            for glob in self.globs.get(module).into_iter().flatten() {
                if !self.glob_is_ancestor_only(glob, module) {
                    return ScopeResolution::Unresolvable;
                }
            }
        }
        ScopeResolution::Unresolvable
    }

    /// An unexpanded item macro whose expansion could bind a bare type name
    /// nearer to `use_site` than the declaration this walk resolves it to.
    ///
    /// The walk answers a bare name by stepping OUTWARD from the use site's
    /// module, exactly as `rustc` does, and it is sound only while it can see
    /// every binding each step holds. A macro invocation is the one item that
    /// defeats that: `mod inner { decl_s!(); }` may expand to
    /// `struct S { x: u64 }`, which binds `S` in `inner` and would win over a
    /// top-level `struct S { x: u8 }` for every use site in `inner` — while
    /// this walk, seeing no `S` in `inner`, steps past it and answers with the
    /// top-level shape. That is a CONFIDENT WRONG ANSWER, not a decline, and it
    /// is the same defect in both directions: the false claim verifies against
    /// the outer shape while the true one is refuted against it.
    ///
    /// Three conditions must hold together, and each one is load-bearing:
    ///
    /// 1. The invocation is in a NON-EMPTY module. A macro at the file root can
    ///    shadow nothing: it would have to bind a name nearer than a
    ///    declaration lying strictly outside the root, and there is no such
    ///    place. (A root expansion that re-declares a visible root type is not
    ///    shadowing but a duplicate-definition error, which `rustc` rejects
    ///    before this engine sees it.)
    /// 2. The invocation's module is an ANCESTOR-OR-SELF of the use site, i.e.
    ///    it sits on the outward walk path. A macro in a module the use site
    ///    does not lie inside cannot bind anything the use site's walk reads.
    ///    When the use site's own scope could not be pinned down (`None`) this
    ///    filter is skipped, which is the conservative reading.
    /// 3. Some type is declared STRICTLY OUTSIDE the invocation's module — the
    ///    declaration the expansion would shadow. Without one there is nothing
    ///    for the walk to have answered wrongly: a name bound only by the
    ///    expansion is carried by no registry at all and already fails closed
    ///    as an unrecognized type.
    ///
    /// This is deliberately NOT "reject every file containing a macro". A macro
    /// at the file root, a macro in a sibling module, and a module whose types
    /// are all declared locally are all untouched.
    fn macro_shadowable_binding(&self, use_site: Option<&[String]>) -> Option<MacroShadowRisk<'_>> {
        for (macro_module, macro_name) in &self.macro_scopes {
            // (1) a root invocation is outside nothing.
            if macro_module.is_empty() {
                continue;
            }
            // (2) only invocations on the use site's outward walk path matter.
            if let Some(scope) = use_site {
                if !is_module_prefix(macro_module, scope) {
                    continue;
                }
            }
            // (3) something must exist outside it for the expansion to shadow.
            for (name, sites) in &self.declarations {
                for site in sites {
                    if is_strict_module_prefix(&site.module, macro_module) {
                        return Some(MacroShadowRisk {
                            macro_module,
                            macro_name,
                            shadowable_name: name,
                            shadowable_module: &site.module,
                        });
                    }
                }
            }
        }
        None
    }

    /// The declaration `name` resolves to when EVERY scope in `scopes` agrees.
    ///
    /// Agreement is what makes one bare carrier sound: the verified function's
    /// scope decides nothing on its own, because a contract or body from another
    /// module in the same file can be lowered into the same verification context
    /// against the same bare sort. Disagreement is a decline.
    fn resolve_uniformly(&self, name: &str, scopes: &BTreeSet<Vec<String>>) -> Option<String> {
        let mut agreed: Option<String> = None;
        for scope in scopes {
            match self.resolve_bare_name(name, scope) {
                ScopeResolution::Resolved(key) => match &agreed {
                    Some(previous) if *previous != key => return None,
                    Some(_) => {}
                    None => agreed = Some(key),
                },
                ScopeResolution::Unresolvable => return None,
            }
        }
        agreed
    }
}

/// Decides a file whose bare type idents are NOT unique, instead of refusing it.
///
/// Runs ONLY when `TraitScopeIndex::reject_duplicate_type_names` has already
/// detected a duplicate, so every file this pass can touch is one the previous
/// cut rejected outright. It can therefore only ever admit more, never less.
///
/// # Why a resolution and not the trait side's prune
///
/// [`crate::trait_path_resolution::prune_shadowed_duplicate_traits`] restores
/// the unique-ident invariant by DELETING the declarations no `impl` header
/// names. That works because a trait is named in exactly one syntactic place —
/// an impl header — so the live set is decidable from a handful of paths.
///
/// A TYPE is named at USE SITES INSIDE FUNCTION BODIES: parameters, returns,
/// locals, casts, struct literals, patterns, `::` paths. There is no small set
/// of headers to read, and deleting the losing declaration would additionally
/// destroy the one signal that keeps a qualified use site honest —
/// `fn f(p: narrow_inner::P)` must FAIL CLOSED, and
/// `SourceStructRegistry::written_path_names_module` can only make it do so
/// while `narrow_inner::P` is still a declaration the registry knows it is not
/// carrying. Prune it away and that parameter silently receives the winner's
/// fields, which is the false-verify direction.
///
/// So the invariant is restored by RESOLUTION. Every declaration stays; what is
/// established here is that a bare ident DENOTES one declaration throughout the
/// file's code, which is precisely what the bare-name-keyed registries need:
///
/// 1. Every scope that holds code (`fn` / `impl` / `trait` / an unexpanded item
///    macro) must resolve the duplicated bare name to the SAME declaration, by
///    the same outward module walk `rustc` does. They can, because a file's
///    source functions, inherent impls and trait impls are collected file-wide
///    into ONE verification context whose carrier name, `StructDef` name and SMT
///    sort name are all the bare ident. Disagreement does NOT fail the file: see
///    [`duplicate_type_name_keeps_a_readable_key`], which refuses only the
///    obligations a disagreement can actually reach.
/// 2. The shape the bare-keyed maps carry must be the winner's. Where the name
///    is `ambiguous` the registry's own resolution pass installs it (or strikes
///    the name and fails closed); where it is not — every TEMPLATED declaration
///    is token-identical — the maps hold whichever declaration a template could
///    be built for, and that one has to BE the winner.
/// 3. An unexpanded item-macro INVOCATION anywhere in the file is rejected
///    outright. Step 1's walk is only sound because it can see every binding a
///    scope holds; a macro that expands to `struct S { .. }` would shadow the
///    declaration the walk chose, and the walk would answer with the outer one —
///    a confident wrong shape rather than a decline. The macro already marks its
///    scope code-bearing, but that is not enough: what is missing is a
///    DECLARATION, not a use site.
/// 4. An `impl` header that names the duplicated type with an explicit module
///    qualifier is rejected. `impl_self_type_base_name` — the key every method
///    registry uses — is the path's LAST SEGMENT, so `impl inner::S` and a bare
///    `impl S` in the same file are literally the same key with two different
///    meanings. A BARE `impl S` needs no check: an impl makes its module
///    code-bearing, so step 1 already forced it to agree.
///
/// After 1–4 a bare type ident denotes one declaration and one method set, and
/// every consumer keyed by it is correct by construction.
fn resolve_duplicate_type_names_or_reject(
    file: &File,
    use_site_scope: Option<&[String]>,
) -> TrustVcResult<()> {
    let mut collected = SourceTypeCollection::default();
    collect_source_types_from_items(&file.items, &mut Vec::new(), &mut collected);

    let mut scopes = collected.index.fn_scopes.clone();
    if let Some(scope) = use_site_scope {
        scopes.insert(scope.to_vec());
    }

    let mut duplicated: BTreeSet<String> = BTreeSet::new();
    for (name, sites) in &collected.index.declarations {
        if sites.len() < 2 {
            continue;
        }
        duplicated.insert(name.clone());
        // Step 1. `resolve_uniformly` walks each code-bearing scope outward
        // exactly as Rust does and answers only when every one of them agrees;
        // globs, `#[cfg]` arms in one module, renamed imports and imports rooted
        // outside this file all yield nothing.
        //
        // Disagreement is NOT a verdict on the file. It says one thing only:
        // nothing keyed by this bare ident may be READ, because the key cannot
        // name which declaration it means. Where the registries' own guards have
        // already made the key unreadable, that is already true and there is
        // nothing left to refuse — which is exactly the shape the A2-generic
        // collision pins are built out of. Only a key that SURVIVES those guards
        // is refused, and with the same wording as before.
        let Some(key) = collected.index.resolve_uniformly(name, &scopes) else {
            if let Some(why) = duplicate_type_name_keeps_a_readable_key(&file.items, name) {
                return Err(duplicate_type_name_rejection(name, sites, &why));
            }
            continue;
        };
        // Step 2.
        if !collected.ambiguous.contains(name)
            && bare_source_type_is_modeled(&collected, name)
            && !qualified_source_type_is_modeled(&collected, &key)
        {
            return Err(duplicate_type_name_rejection(
                name,
                sites,
                "the declaration this file's use sites name has no shape this engine can model, \
                 so the bare carrier would answer with the OTHER declaration's shape",
            ));
        }
    }
    if duplicated.is_empty() {
        return Ok(());
    }
    // Step 3.
    if let Some(macro_name) = first_unexpanded_item_macro(&file.items) {
        let name = duplicated.iter().next().expect("a duplicated name");
        let sites = collected
            .index
            .declarations
            .get(name)
            .map(Vec::as_slice)
            .unwrap_or_default();
        return Err(duplicate_type_name_rejection(
            name,
            sites,
            &format!(
                "this file also invokes the item macro `{macro_name}!`, whose expansion could \
                 declare a same-named type that scope resolution cannot see"
            ),
        ));
    }
    // Step 4.
    reject_qualified_duplicate_impl_self_types(&file.items, &duplicated)
}

/// Why a duplicated bare type name that resolution could NOT settle still has a
/// key some consumer would READ — or `None` when every consumer is already
/// answering nothing for it, in which case there is nothing to refuse.
///
/// # Why this is not a whole-file refusal any more
///
/// `57f17079` closed a cardinal false verify by failing any file that declares
/// two same-named types; `a10aea13` cut that back to the cases scope resolution
/// cannot settle. Both still failed the FILE, and a file is the wrong unit: an
/// unresolvable bare ident is a statement about ONE NAME, and the obligations
/// that never touch that name are decided by registries the collision cannot
/// reach. Measured cost of the file-wide cut: all 14 pins in
/// `a2_generic_soundness` — the suite that guards cross-contamination between
/// two same-leaf receivers, i.e. this very defect class — died before reaching
/// a single assertion, because their fixture declares the colliding pair ON
/// PURPOSE. A gate that makes its own soundness pins untestable is a deferred
/// fix, not a fix.
///
/// # What is already unreadable, and why it needs no refusal
///
/// * The SHAPE maps. `record_source_type_declaration` marks a name `ambiguous`
///   unless every declaration is token-identical, and
///   `SourceStructRegistry::from_file` strikes an unresolved ambiguous name from
///   `structs`/`enums`/`type_aliases`, so its use sites are an unrecognized type
///   that the lowering declines. Token-identical declarations are not a hazard
///   at all: whichever one a use site means, the shape it gets is the same.
/// * The receiver-kind map. `register_struct_self_receiver_kind` promotes a
///   conflicting re-registration to `RefMut`, the most-mutating kind, so a
///   bare-name collision can only ever ADD havoc.
/// * The `&mut`-argument flags. `collect_file_method_arg_mut_flags` is keyed by
///   method name alone and OR-merges the flags, likewise conservative.
/// * The INHERENT method registry. A same-key collision drops BOTH sides —
///   `ambiguous_methods` on the non-generic path, `generic_ambiguous` plus the
///   file-wide `inherent_method_leaf_counts` on the generic one — so no concrete
///   symbol is ever defined by two bodies. This is precisely the guard
///   `a2_generic_soundness`'s `LeafClash`/`Wrapper` pins exist to exercise.
///
/// # What is NOT covered, and is therefore still refused
///
/// Exactly the hole `57f17079` named. A bare method key survives its registry's
/// guard when the guard never sees a collision:
///
/// 1. a TRAIT impl on the name. `register_trait_impl_methods_for_concrete_types`
///    keys by the same bare leaf, runs in a different pass, and "never overrides
///    an existing binding" — so an inherent method on `inner::S` outranks the
///    trait method of a different top-level `S`, and the two per-impl trait
///    ensures axioms land on one concrete symbol. That was the cardinal
///    reproducer, and it is inverted-pair confirmed on this tree: with this
///    refusal removed, `assert!(r == 1)` (FALSE) verifies while `r == 2` (TRUE)
///    is refuted.
/// 2. an inherent method declared exactly ONCE on the leaf. One registration
///    under a key both declarations answer to is not a collision to any guard;
///    it simply answers the other type's call sites too.
/// 3. two or more declarations that do NOT collapse onto one registry key —
///    a generic `impl<A> S<A>` beside a concrete `impl S<u64>`, or two concrete
///    impls at different instantiations. The generic side is dropped by the leaf
///    count, and the concrete side is left owning the symbol alone, which is
///    case 2 again by another route.
///
/// A file the FIRST branch admits is still one every previous cut rejected
/// outright, so this can only ever admit more, never less.
fn duplicate_type_name_keeps_a_readable_key(items: &[syn::Item], name: &str) -> Option<String> {
    let mut trait_impl: Option<String> = None;
    let mut inherent: BTreeMap<String, Vec<Option<String>>> = BTreeMap::new();
    collect_duplicate_type_name_impl_keys(items, name, &mut trait_impl, &mut inherent);

    if let Some(trait_name) = trait_impl {
        return Some(format!(
            "one of them carries `impl {trait_name} for {name}`, whose bridged method metadata is \
             keyed by that same bare name from a pass the inherent-method collision guard never \
             sees"
        ));
    }
    for (method, registry_keys) in inherent {
        // `None` marks a generic impl: it registers under the BARE leaf and is
        // dropped whenever the file-wide leaf count exceeds one. `Some(s)` marks
        // a non-generic impl registering under the self-type string `s`, dropped
        // only against another registration under the SAME string. Declarations
        // that reach NEITHER map are not collected at all, so "two entries" here
        // really does mean two registrations racing for one key — a single
        // survivor beside a skipped twin is the hazard, not a collapse.
        let collapses = registry_keys.len() > 1
            && registry_keys
                .iter()
                .all(|key| *key == *registry_keys.first().expect("non-empty"));
        if collapses {
            continue;
        }
        return Some(format!(
            "the inherent method `{name}::{method}` is registered under a key no collision guard \
             strikes, so that one registration answers the call sites of both declarations"
        ));
    }
    None
}

/// Collects, for base leaf `name`, the first trait impl on it and the registry
/// key every inherent declaration of each method would land on.
///
/// The key mirrors `InherentImplRegistry::collect_items` exactly: a generic impl
/// goes to `generic_methods` under the bare leaf (`None` here), a non-generic one
/// to `methods` under `inherent_self_type_string` (`Some(_)` here), and a method
/// that registry SKIPS is not recorded at all — a declaration that reaches no map
/// cannot collapse anything, and treating it as one half of a collision would
/// leave its unskipped twin answering both types. Recursing into inline `mod`s is
/// required: the registry does the same, so a nested impl competes for the
/// identical key.
fn collect_duplicate_type_name_impl_keys(
    items: &[syn::Item],
    name: &str,
    trait_impl: &mut Option<String>,
    inherent: &mut BTreeMap<String, Vec<Option<String>>>,
) {
    for item in items {
        match item {
            syn::Item::Impl(item_impl) => {
                if impl_self_type_base_name(&item_impl.self_ty).as_deref() != Some(name) {
                    continue;
                }
                if let Some((_, path, _)) = &item_impl.trait_ {
                    if trait_impl.is_none() {
                        *trait_impl = Some(
                            path.segments
                                .last()
                                .map(|segment| segment.ident.to_string())
                                .unwrap_or_else(|| name.to_string()),
                        );
                    }
                    continue;
                }
                let generic = !item_impl.generics.params.is_empty();
                // The generic map admits only a fully-generic `impl<A,..> Base<A,..>`;
                // anything else registers nothing at all from this impl.
                if generic && admit_generic_inherent_impl(item_impl).is_none() {
                    continue;
                }
                let registry_key = if generic {
                    None
                } else {
                    let Some(self_type) = inherent_self_type_string(&item_impl.self_ty) else {
                        continue;
                    };
                    Some(self_type)
                };
                for impl_item in &item_impl.items {
                    let syn::ImplItem::Fn(method) = impl_item else {
                        continue;
                    };
                    if !inherent_impl_method_reaches_registry(method, generic) {
                        continue;
                    }
                    inherent
                        .entry(method.sig.ident.to_string())
                        .or_default()
                        .push(registry_key.clone());
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner)) = &module.content {
                    collect_duplicate_type_name_impl_keys(inner, name, trait_impl, inherent);
                }
            }
            _ => {}
        }
    }
}

/// Whether `InherentImplRegistry::collect_items` would actually record `method`,
/// mirroring its per-method skips on the branch `generic` selects.
///
/// Kept next to [`collect_duplicate_type_name_impl_keys`] because the collapse
/// test above is only sound while the two agree: a method the registry skips on
/// one declaration and records on the other is ONE registration under a shared
/// key, which is exactly the shape that must still be refused.
fn inherent_impl_method_reaches_registry(method: &syn::ImplItemFn, generic: bool) -> bool {
    let own_type_params = method.sig.generics.params.iter().any(|param| {
        matches!(
            param,
            syn::GenericParam::Type(_) | syn::GenericParam::Const(_)
        )
    });
    if own_type_params {
        return false;
    }
    if when_used_as_spec_target_path(&method.attrs)
        .ok()
        .flatten()
        .is_some()
    {
        return false;
    }
    if generic {
        // The generic map leaves every `#[spec]` method to the spec lane.
        !has_spec_attr(&method.attrs)
    } else {
        // The non-generic map admits `#[spec]` methods, except the two markers
        // that have no publishable definition.
        !(has_spec_attr(&method.attrs)
            && (has_opaque_attr(&method.attrs) || has_uninterp_attr(&method.attrs)))
    }
}

/// The path of the first unexpanded item-macro INVOCATION in `file`.
///
/// A `macro_rules! m { .. }` DEFINITION is `syn::Item::Macro` too but declares
/// nothing, so it is identified by its `ident` and skipped.
fn first_unexpanded_item_macro(items: &[syn::Item]) -> Option<String> {
    for item in items {
        match item {
            syn::Item::Macro(item_macro) if item_macro.ident.is_none() => {
                return Some(
                    item_macro
                        .mac
                        .path
                        .segments
                        .iter()
                        .map(|segment| segment.ident.to_string())
                        .collect::<Vec<_>>()
                        .join("::"),
                );
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner)) = &module.content {
                    if let Some(found) = first_unexpanded_item_macro(inner) {
                        return Some(found);
                    }
                }
            }
            _ => {}
        }
    }
    None
}

/// True when the bare-keyed shape maps carry a model for `name`.
fn bare_source_type_is_modeled(collected: &SourceTypeCollection, name: &str) -> bool {
    collected.structs.contains_key(name)
        || collected.enums.contains_key(name)
        || collected.type_aliases.contains_key(name)
}

/// True when the module-keyed shape maps carry a model for the declaration
/// `key` (a `qualified_type_key`).
fn qualified_source_type_is_modeled(collected: &SourceTypeCollection, key: &str) -> bool {
    collected.qualified_structs.contains_key(key)
        || collected.qualified_enums.contains_key(key)
        || collected.qualified_type_aliases.contains_key(key)
}

/// Rejects `impl <module>::<Dup> { .. }` / `impl Tr for <module>::<Dup>`.
///
/// Every method registry keys on `impl_self_type_base_name`, i.e. the self
/// type's LAST SEGMENT, so a qualified header lands on the same key as a bare
/// one while meaning a different declaration. A bare header is already settled
/// by the agreement check — an `impl` makes its module code-bearing.
fn reject_qualified_duplicate_impl_self_types(
    items: &[syn::Item],
    duplicated: &BTreeSet<String>,
) -> TrustVcResult<()> {
    for item in items {
        match item {
            syn::Item::Impl(item_impl) => {
                let Some(name) = impl_self_type_base_name(&item_impl.self_ty) else {
                    continue;
                };
                if duplicated.contains(&name) && impl_self_type_is_qualified(&item_impl.self_ty) {
                    return Err(TrustVcError::Encoding {
                        context: "resolve bare type name",
                        detail: format!(
                            "two types in this file are both named `{name}`, and an `impl` header \
                             here names one of them with an explicit module qualifier; every \
                             method registry is keyed by the receiver type's bare name, so that \
                             header is indistinguishable from an impl on the other declaration \
                             and neither can be verified — rename one",
                        ),
                    });
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner)) = &module.content {
                    reject_qualified_duplicate_impl_self_types(inner, duplicated)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// True when an impl's self type is written with anything other than a single
/// bare identifier — a module qualifier, a leading `::`, or a `<T as Tr>` qself.
fn impl_self_type_is_qualified(ty: &syn::Type) -> bool {
    match ty {
        syn::Type::Path(type_path) => {
            type_path.qself.is_some()
                || type_path.path.leading_colon.is_some()
                || type_path.path.segments.len() > 1
        }
        syn::Type::Reference(reference) => impl_self_type_is_qualified(&reference.elem),
        syn::Type::Group(group) => impl_self_type_is_qualified(&group.elem),
        syn::Type::Paren(paren) => impl_self_type_is_qualified(&paren.elem),
        _ => false,
    }
}

/// The rejection for a duplicated bare type name resolution could not settle.
///
/// Wording is load-bearing: `cross_scope_type_name_collision_soundness` asserts
/// the refusal NAMES the collision (``both named `S` ``) and says why (`bare
/// name`), because a bare `!Verified` guard would also be satisfied by an
/// unrelated failure.
/// True when module `outer` is `inner` or encloses it (`[]` encloses every
/// module; `["a"]` encloses `["a","b"]`).
fn is_module_prefix(outer: &[String], inner: &[String]) -> bool {
    outer.len() <= inner.len() && inner[..outer.len()] == *outer
}

/// True when `outer` STRICTLY encloses `inner` — the relation that makes a
/// binding in `inner` shadow a declaration in `outer` rather than collide with
/// it.
fn is_strict_module_prefix(outer: &[String], inner: &[String]) -> bool {
    outer.len() < inner.len() && is_module_prefix(outer, inner)
}

/// Refuses a function whose bare type names an unexpanded item macro could have
/// re-bound nearer than the declaration the scope walk chose.
///
/// This closes the residual that `a10aea13` recorded and left open: that
/// commit's step 3 rejects an item macro only in a file where a VISIBLE
/// duplicate already fired the detector, so a macro-declared type shadowing a
/// top-level one with no visible duplicate resolved by the bare-name maps
/// exactly as before. Measured on this tree, that was CARDINAL and exploitable
/// in both registries and in either declaration order:
///
/// ```ignore
/// pub struct S { pub x: u8 }                      // the only VISIBLE `S`
/// mod inner {
///     macro_rules! decl_s { () => { pub struct S { pub x: u64 } }; }
///     decl_s!();                                  // the REAL `S` in here
///     fn f(s: S) { trust_vc::assert!(s.x <= 255u64); }  // FALSE -- verified
/// }
/// ```
///
/// `rustc --edition 2021` compiles and runs that file and prints
/// `inner S::x = 18446744073709551615`, so `s.x <= 255` is false; the engine
/// answered `verified` from the top-level `u8` shape. The method registry was
/// exposed identically — with a macro-declared `impl S { fn v() -> 2 }`,
/// `s.v() == 1` verified while the TRUE `s.v() == 2` was refuted with a model
/// showing the 8-bit carrier.
///
/// The remedy is a REFUSAL, not a resolution, because there is nothing to
/// resolve: the expansion is not in the AST, so no walk can learn what it
/// declares. It is scoped by
/// [`SourceTypeScopeIndex::macro_shadowable_binding`] to exactly the shape
/// where the outcome could depend on the expansion, which costs no capability
/// that exists today — a macro-declared type is carried by no registry, so its
/// own use sites already fail closed as unrecognized types.
fn reject_macro_shadowable_type_resolution(
    file: &File,
    use_site_scope: Option<&[String]>,
) -> TrustVcResult<()> {
    let mut collected = SourceTypeCollection::default();
    collect_source_types_from_items(&file.items, &mut Vec::new(), &mut collected);
    let Some(risk) = collected.index.macro_shadowable_binding(use_site_scope) else {
        return Ok(());
    };
    Err(TrustVcError::Encoding {
        context: "resolve bare type name",
        detail: format!(
            "{} invokes the item macro `{}!`, whose expansion this engine cannot see; it could \
             declare a type named `{}` there, which would shadow the declaration in {} that bare \
             type names in this scope currently resolve to — so no bare type name here can be \
             resolved soundly. Expand the macro by hand, or move it out of the modules enclosing \
             this function",
            render_source_module(risk.macro_module),
            risk.macro_name,
            risk.shadowable_name,
            render_source_module(risk.shadowable_module),
        ),
    })
}

fn duplicate_type_name_rejection(
    name: &str,
    sites: &[SourceTypeDeclSite],
    why: &str,
) -> TrustVcError {
    let mut modules: Vec<String> = Vec::new();
    for site in sites {
        let rendered = render_source_module(&site.module);
        if !modules.contains(&rendered) {
            modules.push(rendered);
        }
    }
    while modules.len() < 2 {
        modules.push("the same module".to_string());
    }
    TrustVcError::Encoding {
        context: "resolve bare type name",
        detail: format!(
            "two types in this file are both named `{name}` ({} and {}); method resolution is \
             keyed by the receiver type's bare name, and {why}, so the two declarations are \
             indistinguishable and neither can be verified — rename one",
            modules[0], modules[1],
        ),
    }
}

fn render_source_module(module: &[String]) -> String {
    if module.is_empty() {
        "the file root".to_string()
    } else {
        format!("`{}`", module.join("::"))
    }
}

/// Everything one walk over a file's items collects about its type
/// declarations: the legacy bare-keyed maps (unchanged, first-declaration-wins)
/// plus module-keyed copies and the scope index that lets a colliding bare name
/// be resolved instead of struck.
#[derive(Default)]
struct SourceTypeCollection {
    structs: BTreeMap<String, SourceStructTemplate>,
    enums: BTreeMap<String, SourceEnumTemplate>,
    type_aliases: BTreeMap<String, SourceTypeAliasTemplate>,
    qualified_structs: BTreeMap<String, SourceStructTemplate>,
    qualified_enums: BTreeMap<String, SourceEnumTemplate>,
    qualified_type_aliases: BTreeMap<String, SourceTypeAliasTemplate>,
    declared: BTreeMap<String, String>,
    ambiguous: BTreeSet<String>,
    index: SourceTypeScopeIndex,
}

/// Records one source-type declaration against its BARE identifier, marking the
/// key AMBIGUOUS when a structurally different declaration already claimed it.
///
/// The bare-keyed maps have no module-path resolution — the carrier name, the
/// `StructDef` name and the SMT sort name are all the bare name — so two
/// declarations of one bare name are indistinguishable there. `.or_insert`
/// therefore let the FIRST declaration win, and a nested
/// `mod helper { struct S { x: u8 } }` silently supplied the field types for a
/// top-level `struct S { x: u64 }`, verifying `s.x <= 255` for a `u64` field (a
/// cardinal false-verify whose verdict flipped purely with declaration order).
///
/// Flagging the name here is step one. Step two is
/// [`SourceTypeScopeIndex::resolve_uniformly`], which resolves the flagged name
/// against the use site's module scope; only names it cannot settle are struck
/// from the registry, and every use of a struck name resolves as an unrecognized
/// type, which the downstream lowering already declines.
///
/// Token-identical re-declarations are NOT a collision: whichever one a use site
/// means, the resolved shape is the same, so keeping one loses nothing.
fn record_source_type_declaration(
    name: &str,
    fingerprint: String,
    declared: &mut BTreeMap<String, String>,
    ambiguous: &mut BTreeSet<String>,
) {
    match declared.get(name) {
        None => {
            declared.insert(name.to_string(), fingerprint);
        }
        Some(previous) if *previous == fingerprint => {}
        Some(_) => {
            ambiguous.insert(name.to_string());
        }
    }
}

/// Records the declaration site of `name` (module path + token fingerprint) for
/// scope-relative resolution.
fn record_source_type_decl_site(
    index: &mut SourceTypeScopeIndex,
    module: &[String],
    name: &str,
    fingerprint: String,
) {
    index
        .declarations
        .entry(name.to_string())
        .or_default()
        .push(SourceTypeDeclSite {
            module: module.to_vec(),
            fingerprint,
        });
}

/// Flattens one `use` tree into the bindings and globs it introduces into
/// `module`. `prefix` accumulates the path segments walked so far.
fn collect_use_tree(
    tree: &syn::UseTree,
    prefix: &mut Vec<String>,
    out_of_file: bool,
    module: &[String],
    index: &mut SourceTypeScopeIndex,
) {
    match tree {
        syn::UseTree::Path(path) => {
            prefix.push(path.ident.to_string());
            collect_use_tree(&path.tree, prefix, out_of_file, module, index);
            prefix.pop();
        }
        syn::UseTree::Name(name) => {
            let leaf = name.ident.to_string();
            index
                .imports
                .entry(module.to_vec())
                .or_default()
                .push(SourceUseBinding {
                    in_scope_name: leaf.clone(),
                    module_segments: prefix.clone(),
                    leaf,
                    out_of_file,
                });
        }
        syn::UseTree::Rename(rename) => {
            index
                .imports
                .entry(module.to_vec())
                .or_default()
                .push(SourceUseBinding {
                    in_scope_name: rename.rename.to_string(),
                    module_segments: prefix.clone(),
                    leaf: rename.ident.to_string(),
                    out_of_file,
                });
        }
        syn::UseTree::Glob(_) => {
            index
                .globs
                .entry(module.to_vec())
                .or_default()
                .push(SourceGlobImport {
                    module_segments: prefix.clone(),
                    out_of_file,
                });
        }
        syn::UseTree::Group(group) => {
            for item in &group.items {
                collect_use_tree(item, prefix, out_of_file, module, index);
            }
        }
    }
}

fn collect_source_types_from_items(
    items: &[syn::Item],
    prefix: &mut Vec<String>,
    out: &mut SourceTypeCollection,
) {
    for item in items {
        match item {
            // The declaration SITE is recorded whether or not a template could
            // be built for the item, and the bare-keyed shape maps are filled
            // only when one could. The two are deliberately NOT gated together:
            // an item this walk cannot model still OCCUPIES its bare ident in
            // every downstream registry, so leaving it out of the scope index
            // would let a use site inside `mod a` walk straight past
            // `mod a { struct S { <unmodelable> } }` and resolve `S` to a
            // DIFFERENT top-level `S` — a confident wrong shape, which is the
            // false-verify direction. Recording it can only ever make
            // resolution decline.
            syn::Item::Struct(item_struct) => {
                let fingerprint = item_struct.to_token_stream().to_string();
                record_source_type_decl_site(
                    &mut out.index,
                    prefix,
                    &item_struct.ident.to_string(),
                    fingerprint.clone(),
                );
                if let Some(template) = SourceStructTemplate::from_item_struct(item_struct) {
                    record_source_type_declaration(
                        &template.name,
                        fingerprint,
                        &mut out.declared,
                        &mut out.ambiguous,
                    );
                    out.qualified_structs
                        .entry(qualified_type_key(prefix, &template.name))
                        .or_insert_with(|| template.clone());
                    out.structs.entry(template.name.clone()).or_insert(template);
                }
            }
            syn::Item::Enum(item_enum) => {
                let fingerprint = item_enum.to_token_stream().to_string();
                record_source_type_decl_site(
                    &mut out.index,
                    prefix,
                    &item_enum.ident.to_string(),
                    fingerprint.clone(),
                );
                if let Some(template) = SourceEnumTemplate::from_item_enum(item_enum) {
                    record_source_type_declaration(
                        &template.name,
                        fingerprint,
                        &mut out.declared,
                        &mut out.ambiguous,
                    );
                    out.qualified_enums
                        .entry(qualified_type_key(prefix, &template.name))
                        .or_insert_with(|| template.clone());
                    out.enums.entry(template.name.clone()).or_insert(template);
                }
            }
            syn::Item::Type(item_type) => {
                let fingerprint = item_type.to_token_stream().to_string();
                record_source_type_decl_site(
                    &mut out.index,
                    prefix,
                    &item_type.ident.to_string(),
                    fingerprint.clone(),
                );
                if let Some(template) = SourceTypeAliasTemplate::from_item_type(item_type) {
                    record_source_type_declaration(
                        &template.name,
                        fingerprint,
                        &mut out.declared,
                        &mut out.ambiguous,
                    );
                    out.qualified_type_aliases
                        .entry(qualified_type_key(prefix, &template.name))
                        .or_insert_with(|| template.clone());
                    out.type_aliases
                        .entry(template.name.clone())
                        .or_insert(template);
                }
            }
            // A `union` is never modeled, but it occupies its bare ident in the
            // method registries exactly as a struct does, so it must be visible
            // to collision resolution.
            syn::Item::Union(item_union) => {
                record_source_type_decl_site(
                    &mut out.index,
                    prefix,
                    &item_union.ident.to_string(),
                    item_union.to_token_stream().to_string(),
                );
            }
            syn::Item::Use(item_use) => {
                let out_of_file = item_use.leading_colon.is_some()
                    || matches!(&item_use.tree, syn::UseTree::Path(path) if path.ident == "crate");
                collect_use_tree(
                    &item_use.tree,
                    &mut Vec::new(),
                    out_of_file,
                    prefix,
                    &mut out.index,
                );
            }
            syn::Item::Fn(_) | syn::Item::Impl(_) | syn::Item::Trait(_) => {
                out.index.fn_scopes.insert(prefix.clone());
            }
            syn::Item::Macro(item_macro) => {
                out.index.fn_scopes.insert(prefix.clone());
                // A `macro_rules! m { .. }` DEFINITION is an `Item::Macro` too,
                // but it binds a macro name and declares no item; only an
                // INVOCATION (no ident) can expand to a type declaration.
                if item_macro.ident.is_none() {
                    out.index
                        .macro_scopes
                        .entry(prefix.clone())
                        .or_insert_with(|| {
                            item_macro
                                .mac
                                .path
                                .segments
                                .iter()
                                .map(|segment| segment.ident.to_string())
                                .collect::<Vec<_>>()
                                .join("::")
                        });
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    prefix.push(module.ident.to_string());
                    collect_source_types_from_items(inner_items, prefix, out);
                    prefix.pop();
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
    // Every edge is read in the module its CALLER is written in: a spelling in a
    // sibling helper means what Rust makes it mean THERE, not what the same
    // spelling would mean at the target.
    let target_scope = enclosing_module_scope(file, target_func);
    let mut pending = referenced_helper_calls(target_func)
        .into_iter()
        .map(|reference| {
            (
                source_reference_with_aliases(reference, &aliases),
                target_scope.clone(),
            )
        })
        .collect::<BTreeSet<_>>();
    let no_aliases = BTreeMap::new();
    let mut visited = BTreeSet::new();
    let mut contracts = BTreeMap::new();
    let mut symbol_bindings = BTreeMap::new();

    while let Some(edge) = pending.iter().next().cloned() {
        pending.remove(&edge);
        if !visited.insert(edge.clone()) {
            continue;
        }
        let (reference, scope) = edge;
        let Some((helper, key)) = resolve_non_spec_source_function(
            &source_functions,
            &no_aliases,
            &reference,
            scope.as_deref(),
            target_func,
        ) else {
            continue;
        };
        bind_call_symbol(&mut symbol_bindings, &reference.call_symbol, &key)?;
        if let Some(mut contract) = helper_call_contract_from_item_fn(helper)? {
            if ill_founded.contains(&helper.sig.ident.to_string()) {
                contract.ensures.clear();
            }
            if !(contract.requires.is_empty() && contract.ensures.is_empty()) {
                contracts.insert(reference.call_symbol.clone(), contract);
            }
        }
        let helper_aliases = block_use_function_aliases(&helper.block);
        let helper_scope = enclosing_module_scope(file, helper);
        for dependency in referenced_helper_calls(helper) {
            let dependency = (
                source_reference_with_aliases(dependency, &helper_aliases),
                helper_scope.clone(),
            );
            if resolve_non_spec_source_function(
                &source_functions,
                &no_aliases,
                &dependency.0,
                dependency.1.as_deref(),
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

/// Every lexical SCOPE that can introduce a callee spelling, enumerated ONCE so
/// that "the resolver consulted one scope and silently answered nothing" cannot
/// recur.
///
/// SOUNDNESS-CRITICAL, and the reason this is a type rather than three locals:
/// `collect_referenced_sibling_mut_ref_call_args` used to take its aliases from
/// `block_use_function_aliases(&target_func.block)` alone — the TARGET
/// FUNCTION'S OWN BLOCK. A FILE-LEVEL `use m::bump2;` was therefore invisible,
/// `bump2(t)` resolved to nothing, no entry reached `mut_ref_call_args`, and the
/// mutation was a no-op: `fn a2(t: &mut C) -> u64 { bump2(t); t.n }` proved
/// `result == 0` while every execution returns 1. The in-block form
/// (`use m::bump as loc; loc(t)`) and the qualified form (`m::bump(t)`) were
/// both correctly refuted the whole time, so the hole was purely "which scope
/// did the resolver look in".
///
/// Constructed only by exhaustive struct literal and consumed only by an
/// exhaustive destructure in [`CalleeAliasScopes::merged`], so a future scope is
/// a COMPILE ERROR until someone decides in writing how it merges — the same
/// technique [`body_extract::CollectorLaneSeed`] uses for lane state.
struct CalleeAliasScopes {
    /// `use` items written in the TARGET FUNCTION's own outer block.
    function_block: BTreeMap<String, String>,
    /// `use` items written at FILE top level.
    file_top_level: BTreeMap<String, String>,
    /// `use` items written in the inline modules ENCLOSING the target function.
    enclosing_modules: BTreeMap<String, String>,
}

impl CalleeAliasScopes {
    fn collect(file: &File, target_func: &ItemFn) -> Self {
        let enclosing = enclosing_module_scope(file, target_func);
        Self {
            function_block: block_use_function_aliases(&target_func.block),
            file_top_level: item_use_function_aliases(&file.items),
            enclosing_modules: match enclosing.as_deref() {
                Some(path) if !path.is_empty() => enclosing_module_use_aliases(&file.items, path),
                _ => BTreeMap::new(),
            },
        }
    }

    /// The three scopes as one alias map.
    ///
    /// A spelling introduced by two scopes with two DIFFERENT targets is
    /// DROPPED, not resolved by innermost-wins. This map's only consumer decides
    /// whether a call may write through an argument, and a resolution that names
    /// the wrong declaration can answer "this parameter is `&`-shared" for a
    /// callee that actually takes `&mut` — the false-verify direction. Dropping
    /// leaves the spelling UNRESOLVED, which routes to the argument-type
    /// fallback (see `mut_ref_reborrowable_bindings`) and fails closed.
    fn merged(&self) -> BTreeMap<String, String> {
        let CalleeAliasScopes {
            function_block,
            file_top_level,
            enclosing_modules,
        } = self;
        let mut out: BTreeMap<String, String> = BTreeMap::new();
        let mut conflicted: BTreeSet<String> = BTreeSet::new();
        for scope in [function_block, file_top_level, enclosing_modules] {
            for (alias, source_path) in scope {
                match out.get(alias) {
                    Some(previous) if previous != source_path => {
                        conflicted.insert(alias.clone());
                    }
                    Some(_) => {}
                    None => {
                        out.insert(alias.clone(), source_path.clone());
                    }
                }
            }
        }
        for alias in conflicted {
            out.remove(&alias);
        }
        out
    }
}

/// Function-name aliases introduced by the `use` items DIRECTLY in `items`
/// (no descent into modules — each module scope is collected separately).
fn item_use_function_aliases(items: &[syn::Item]) -> BTreeMap<String, String> {
    let mut aliases: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for item in items {
        if let syn::Item::Use(item_use) = item {
            UseAliasCollector::collect_tree(&mut aliases, &mut Vec::new(), &item_use.tree);
        }
    }
    aliases
        .into_iter()
        .filter_map(|(alias, source_paths)| {
            // Two `use` items binding one spelling to two paths is not
            // resolvable here; leave it unresolved so the caller fails closed.
            (source_paths.len() == 1)
                .then(|| source_paths.into_iter().next().map(|path| (alias, path)))
                .flatten()
        })
        .collect()
}

/// `item_use_function_aliases` for every inline module along `path`, merged
/// outermost-first (an inner module's `use` shadows an outer one's).
fn enclosing_module_use_aliases(items: &[syn::Item], path: &[String]) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    let mut current = items;
    for segment in path {
        let Some(inner) = current.iter().find_map(|item| match item {
            syn::Item::Mod(module) if module.ident == segment.as_str() => {
                module.content.as_ref().map(|(_, inner)| inner.as_slice())
            }
            _ => None,
        }) else {
            // An out-of-line `mod m;` has no items HERE. Returning what we have
            // is not a silent default: the spellings we could not see simply do
            // not resolve, and an unresolved callee fails closed at the use site.
            break;
        };
        out.extend(item_use_function_aliases(inner));
        current = inner;
    }
    out
}

/// The `&mut` positions of `inputs`, one flag per entry. A `&mut self` receiver
/// counts as a `&mut` position (it occupies argument slot 0 in the UFCS
/// spelling `H::hit(&mut h, x)`); `&self` / by-value `self` do not.
fn signature_mut_ref_flags<'a>(inputs: impl Iterator<Item = &'a FnArg>) -> Vec<bool> {
    inputs
        .map(|input| match input {
            FnArg::Typed(pat_type) => {
                matches!(&*pat_type.ty, Type::Reference(r) if r.mutability.is_some())
            }
            FnArg::Receiver(receiver) => {
                receiver.mutability.is_some() && receiver.reference.is_some()
            }
        })
        .collect()
}

/// The callee-signature `&mut` argument positions for every call spelling
/// `target_func`'s body can resolve, keyed by the call symbol exactly as
/// [`call_function_symbol`] renders it.
///
/// SOUNDNESS-CRITICAL (free-call `&mut`-argument framing): a contract-less
/// `fn push_helper(v: &mut Vec<u64>) { v.push(1) }` mutates its referent through
/// the `&mut` argument, but the caller's body model dropped that effect — a
/// post-call read of the argument saw the stale pre-call entry snapshot, a real
/// false `Verified`. The body extractor uses this map to HAVOC the referent of
/// each `&mut`-passed argument at an opaque call (and to add it to the
/// loop-frame / branch-join modified set). The callee SIGNATURE is required to
/// distinguish a mutating `&mut` argument from a `&`-shared read
/// (`read_helper(v: &Vec<u64>)`), which is syntactically identical at the call
/// site (`f(v)`) but must NOT havoc — so this is what keeps the fix free of
/// over-rejection.
///
/// PRESENCE IN THIS MAP MEANS "RESOLVED", and that is load-bearing. The earlier
/// version kept only entries with at least one `&mut` position, which made a
/// resolved pure reader indistinguishable from a callee this file cannot see at
/// all — and the consumer's fallback for an unresolvable callee is to havoc a
/// reborrowed `&mut` argument. An all-`false` vector is therefore recorded, and
/// it is what tells the consumer "the answer is genuinely NO".
///
/// Covers free `fn`s (through all three scopes of [`CalleeAliasScopes`]) AND
/// inherent/trait-impl ASSOCIATED functions spelled `Type::name` — the latter
/// were invisible to `SourceFunctionRegistry`, so `H::zap(t)` with
/// `impl H { fn zap(c: &mut C) }` was a second live false verify.
fn collect_referenced_sibling_mut_ref_call_args(
    file: &File,
    target_func: &ItemFn,
) -> BTreeMap<String, Vec<bool>> {
    let aliases = CalleeAliasScopes::collect(file, target_func).merged();
    let source_functions = SourceFunctionRegistry::from_file(file);
    let target_scope = enclosing_module_scope(file, target_func);
    let associated = file_associated_fn_signatures(file);
    let mut out = BTreeMap::new();
    for reference in referenced_helper_calls(target_func) {
        if let Some((helper, _)) = resolve_non_spec_source_function(
            &source_functions,
            &aliases,
            &reference,
            target_scope.as_deref(),
            target_func,
        ) {
            out.insert(
                reference.call_symbol.clone(),
                signature_mut_ref_flags(helper.sig.inputs.iter()),
            );
            continue;
        }
        // `Type::name` associated functions and inherent methods called through
        // their UFCS spelling. Keyed on the call symbol as written; an ambiguous
        // name (two same-named declarations under one type) is absent from
        // `associated` and therefore stays UNRESOLVED, which fails closed.
        if let Some(flags) = associated.get(&reference.call_symbol) {
            out.insert(reference.call_symbol.clone(), flags.clone());
        }
    }
    // The QUALIFIED-UFCS spelling `<H as B>::tb(&h, t)` never appears in
    // `referenced_helper_calls` (`source_call_reference` declines a `qself`
    // path), so its `Type::method` key would be missing from the loop above.
    // Merge the whole associated table: these keys can only be matched by a
    // `Type::method` call spelling, and the consumer looks up by key.
    for (key, flags) in associated {
        out.entry(key).or_insert(flags);
    }
    out
}

/// `Type::name -> signature &mut flags` for every inherent-impl and trait-impl
/// associated function / method declared in `file`, descending into inline
/// modules. The receiver occupies slot 0, matching the UFCS call spelling.
///
/// A name declared twice under one type with DIFFERENT flags is REMOVED rather
/// than resolved by first-wins: an entry here is read as the authoritative "this
/// parameter is not `&mut`" answer, so a wrong pick is the false-verify
/// direction. Removal leaves the spelling unresolved, which fails closed.
fn file_associated_fn_signatures(file: &File) -> BTreeMap<String, Vec<bool>> {
    fn walk(
        items: &[syn::Item],
        out: &mut BTreeMap<String, Vec<bool>>,
        dropped: &mut BTreeSet<String>,
    ) {
        for item in items {
            match item {
                syn::Item::Impl(item_impl) => {
                    let Some(type_name) = impl_self_type_last_segment(&item_impl.self_ty) else {
                        continue;
                    };
                    for impl_item in &item_impl.items {
                        if let syn::ImplItem::Fn(method) = impl_item {
                            let key = format!("{type_name}::{}", method.sig.ident);
                            let flags = signature_mut_ref_flags(method.sig.inputs.iter());
                            match out.get(&key) {
                                Some(previous) if *previous != flags => {
                                    dropped.insert(key);
                                }
                                Some(_) => {}
                                None => {
                                    out.insert(key, flags);
                                }
                            }
                        }
                    }
                }
                syn::Item::Mod(module) => {
                    if let Some((_, inner)) = &module.content {
                        walk(inner, out, dropped);
                    }
                }
                _ => {}
            }
        }
    }
    let mut out = BTreeMap::new();
    let mut dropped = BTreeSet::new();
    walk(&file.items, &mut out, &mut dropped);
    for key in dropped {
        out.remove(&key);
    }
    out
}

fn impl_self_type_last_segment(ty: &Type) -> Option<String> {
    match ty {
        Type::Path(type_path) => type_path
            .path
            .segments
            .last()
            .map(|segment| segment.ident.to_string()),
        Type::Reference(reference) => impl_self_type_last_segment(&reference.elem),
        _ => None,
    }
}

/// `method name -> per-ARGUMENT `&mut` flags` (receiver EXCLUDED, so the
/// positions line up with `ExprMethodCall::args`), unioned over every method of
/// that name declared anywhere in `file` — inherent impls, trait declarations
/// and trait impls alike.
///
/// SOUNDNESS-CRITICAL (method-call `&mut`-argument framing): the free-call havoc
/// keys on `ExprCall`, so `impl H { fn hit(&self, c: &mut C) }` called as
/// `h.hit(t)` never reached it at all and the mutation of `t` was dropped — a
/// live cardinal false verify in both the return lane and the in-body `assert!`
/// lane, and the trait form `impl B for H { fn bump(&self, c: &mut C) }` with it.
///
/// The union is the conservative direction: this map's `true` HAVOCS (a
/// possible mutation must be modeled) and its `false` DECLINES, so a position
/// may only be reported `false` when EVERY same-named declaration in the file
/// agrees. Absence means the file declares no such method at all, which routes
/// the call to the argument-type fallback rather than to a silent "no mutable
/// args" — the distinction this whole fix is about.
fn collect_file_method_arg_mut_flags(file: &File) -> BTreeMap<String, Vec<bool>> {
    fn record(out: &mut BTreeMap<String, Vec<bool>>, sig: &syn::Signature) {
        let flags = signature_mut_ref_flags(
            sig.inputs
                .iter()
                .filter(|input| !matches!(input, FnArg::Receiver(_))),
        );
        let entry = out.entry(sig.ident.to_string()).or_default();
        if entry.len() < flags.len() {
            entry.resize(flags.len(), false);
        }
        for (slot, is_mut) in entry.iter_mut().zip(flags.iter()) {
            *slot = *slot || *is_mut;
        }
    }
    fn walk(items: &[syn::Item], out: &mut BTreeMap<String, Vec<bool>>) {
        for item in items {
            match item {
                syn::Item::Impl(item_impl) => {
                    for impl_item in &item_impl.items {
                        if let syn::ImplItem::Fn(method) = impl_item {
                            record(out, &method.sig);
                        }
                    }
                }
                syn::Item::Trait(item_trait) => {
                    for trait_item in &item_trait.items {
                        if let syn::TraitItem::Fn(method) = trait_item {
                            record(out, &method.sig);
                        }
                    }
                }
                syn::Item::Mod(module) => {
                    if let Some((_, inner)) = &module.content {
                        walk(inner, out);
                    }
                }
                _ => {}
            }
        }
    }
    let mut out = BTreeMap::new();
    walk(&file.items, &mut out);
    out
}

/// The bindings of `func` whose OWN declared type is `&mut T` — the `&mut`
/// parameters, plus a `&mut self` receiver.
///
/// SOUNDNESS-CRITICAL, and the piece that makes an UNRESOLVABLE callee fail
/// closed. Passing one of these bare (`bump2(t)`, `h.hit(t)`, `H::zap(t)`,
/// `other_crate::f(t)`) REBORROWS the mutable reference into the call, so the
/// callee — whoever it turns out to be — may write through it. This answer needs
/// no callee resolution at all, which is exactly why it is the right fallback:
/// the previous model answered "no mutable arguments" whenever it could not
/// resolve the callee, and a caller that cannot compute an answer must be told
/// so rather than handed a default that reads as "nothing to do here".
///
/// It is a FALLBACK, not a replacement: when the callee DOES resolve, its
/// signature is authoritative and can say NO (`read(c: &C)` called as `read(t)`
/// with `t: &mut C` is an implicit reborrow-coercion to `&C` and must not
/// havoc). Only an unresolved callee reaches this set.
fn mut_ref_reborrowable_bindings(func: &ItemFn) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for input in &func.sig.inputs {
        match input {
            FnArg::Receiver(receiver) => {
                if receiver.reference.is_some() && receiver.mutability.is_some() {
                    out.insert("self".to_string());
                }
            }
            FnArg::Typed(pat_type) => {
                if matches!(&*pat_type.ty, Type::Reference(r) if r.mutability.is_some()) {
                    if let syn::Pat::Ident(pat_ident) = &*pat_type.pat {
                        out.insert(pat_ident.ident.to_string());
                    }
                }
            }
        }
    }
    out
}

/// The inline-module path `func` is declared in, or `None` when this file does
/// not pin it down uniquely (two token-identical declarations in two modules).
/// `None` makes every scope-relative call resolution fall back to the
/// scope-independent reading, which fails closed on anything a scope would have
/// been needed to settle.
fn enclosing_module_scope(file: &File, func: &ItemFn) -> Option<Vec<String>> {
    match function_discovery::enclosing_inline_module_path(file, func) {
        function_discovery::EnclosingModuleResolution::Unique(path) => Some(path),
        function_discovery::EnclosingModuleResolution::Ambiguous => None,
    }
}

/// Resolve one call edge to a non-spec source function, reading its spelling
/// from the module `scope` the edge is WRITTEN in (see
/// [`SourceFunctionRegistry::resolve_key`]). Returns the declaration together
/// with its module-qualified key, which callers use to detect two different
/// callees claiming one call symbol.
fn resolve_non_spec_source_function<'a>(
    source_functions: &'a SourceFunctionRegistry,
    aliases: &BTreeMap<String, String>,
    reference: &SourceCallReference,
    scope: Option<&[String]>,
    target_func: &ItemFn,
) -> Option<(&'a ItemFn, String)> {
    let reference = source_reference_with_aliases(reference.clone(), aliases);
    let (helper, key) = source_functions.resolve(&reference.source_path, reference.root, scope)?;
    if helper.sig.ident == target_func.sig.ident || has_spec_attr(&helper.attrs) {
        return None;
    }
    Some((helper, key))
}

/// Record that call symbol `symbol` resolved to declaration `key`, failing
/// closed when a symbol already bound to a DIFFERENT declaration.
///
/// The call symbol is the spelling, and the spelling is the solver identity of
/// the body axiom and the call-site contract. Once calls resolve against their
/// own module, two scopes in one file can spell the same path (`util::f`) and
/// mean two different functions; registering both under one symbol would put
/// one function's body axiom on the other's calls. Neither answer is safe, so
/// the extraction fails rather than picking one.
fn bind_call_symbol(
    bindings: &mut BTreeMap<String, String>,
    symbol: &str,
    key: &str,
) -> TrustVcResult<()> {
    match bindings.get(symbol) {
        Some(previous) if previous != key => Err(TrustVcError::Encoding {
            context: "resolve sibling helper call",
            detail: format!(
                "call symbol `{symbol}` names `{previous}` in one module and `{key}` in \
                 another; the source lane has one solver symbol per spelling, so TrustVc \
                 fails closed instead of conflating the two functions"
            ),
        }),
        Some(_) => Ok(()),
        None => {
            bindings.insert(symbol.to_string(), key.to_string());
            Ok(())
        }
    }
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
    let target_scope = enclosing_module_scope(file, target_func);

    for reference in referenced_target_contract_calls(target_func)? {
        let Some((exec_helper, _)) = resolve_non_spec_source_function(
            &source_functions,
            &no_aliases,
            &reference,
            target_scope.as_deref(),
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
    lemma_proof_steps: &mut BTreeMap<String, Vec<String>>,
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

        // PROOF STEPS. A lemma body may carry `assert!(..)` steps that do the
        // actual work of establishing the `ensures`. Render them with the SAME
        // renamer so they bind the same `__bcq_*` binders as the contract —
        // that shared renaming is why this must happen HERE and not in the
        // later suppression pass, which sees only obligations.
        //
        // They are carried out as ASSERTS, not assumes: each is discharged in
        // turn and only then available as a fact for the next one and for the
        // `ensures`. Assuming them would let a lemma bootstrap itself from an
        // unproven step, which is the very hole this check exists to close.
        let (_, assert_exprs) = body_broadcast_clause_exprs(&item_fn.block, "assert");
        let proof_steps: Vec<String> = assert_exprs
            .unwrap_or_default()
            .into_iter()
            .map(|e| render_broadcast_clause(e, &mut renamer))
            .collect();

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
        if !proof_steps.is_empty() {
            lemma_proof_steps.insert(axiom_name.clone(), proof_steps);
        }
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

/// Drops every `#[trust_vc::broadcast]` lemma axiom whose own contract does not
/// establish the `ensures` it publishes.
///
/// For each `__source_broadcast_*` obligation this discharges
/// `guard |- ensures` over the lemma's already-renamed fresh binders, in a
/// DISCARDED child that carries the ambient definitional spec-fn axioms but NO
/// lemma axiom of its own. Proving `P(c)` for free UNCONSTRAINED constants is
/// proving `forall x. P(x)`, so this is the right query, and it reuses the
/// strings the collector already rendered — no re-parse, no `syn` work.
///
/// NO LEMMA CAN JUSTIFY ITSELF OR A SIBLING: `broadcast_lemma_check_child` drops
/// every `__source_broadcast_*`. The call-edge SCC in
/// `ill_founded_recursive_function_names` does NOT cover this — two lemmas that
/// never call each other can still prove each other through published axioms.
/// The cost is that a lemma legitimately depending on a prior lemma is dropped;
/// that is over-rejection, and the fix for it is in-order publish-as-you-go, NOT
/// relaxing to "keep all", which reintroduces the hole in circular form.
///
/// SCOPE, stated honestly. `body_broadcast_clause_exprs` reads only top-level
/// `requires!` / `ensures!` statements, so the collector's model of a lemma is
/// already contract-only and this check is faithful to that model and no wider.
/// A lemma carrying real PROOF STEPS (`assert!`, `calc!`, a helper call) is
/// judged on its contract alone and is dropped if the `ensures` does not follow.
/// No file-path lemma in the tree has such a step today. The failure direction is
/// over-rejection, never a hole.
///
/// VACUITY IS A PASS, for the reason the closure def-side check gives: an
/// unsatisfiable guard makes the published `guard ==> ensures` INERT, since the
/// guard can never hold. Every other non-`Verified` verdict — counterexample,
/// not-proved, timeout, encoding error — DROPS the axiom.
fn suppress_unestablished_broadcast_lemma_axioms(
    vc: &mut VerificationContext,
    check_base: Option<&VerificationContext>,
    lemma_proof_steps: &BTreeMap<String, Vec<String>>,
) {
    let Some(check_base) = check_base else {
        return;
    };
    const SOURCE_BROADCAST_PREFIX: &str = "__source_broadcast_";

    let candidates: Vec<(String, String, Vec<String>)> = vc
        .obligations()
        .iter()
        .filter(|obligation| obligation.name().starts_with(SOURCE_BROADCAST_PREFIX))
        .map(|obligation| {
            (
                obligation.name().to_string(),
                obligation.condition().to_string(),
                obligation
                    .broadcast_guard
                    .as_ref()
                    .map(|guards| guards.iter().map(|g| g.condition.clone()).collect())
                    .unwrap_or_default(),
            )
        })
        .collect();
    if candidates.is_empty() {
        return;
    }

    let mut unestablished: BTreeSet<String> = BTreeSet::new();
    for (name, ensures, guards) in candidates {
        // The base already carries the TRUE definitions, revealed. Without them
        // an opaque spec fn contributes nothing and EVERY lemma over one is
        // dropped, legitimate or not.
        let mut child = check_base.broadcast_lemma_check_child();
        for (index, guard) in guards.iter().enumerate() {
            child.push_obligation(ProofObligation::assume(
                format!("__broadcast_lemma_guard_{name}_{index}"),
                guard.clone(),
            ));
        }
        // Discharge the body's proof steps IN ORDER first: each is asserted, and
        // once proven becomes a usable fact for the next step and for the
        // `ensures`. A lemma that does its work in the body is therefore judged
        // on that work, not on its contract alone.
        for (index, step) in lemma_proof_steps
            .get(&name)
            .map(Vec::as_slice)
            .unwrap_or_default()
            .iter()
            .enumerate()
        {
            child.push_obligation(ProofObligation::assert(
                format!("__broadcast_lemma_step_{name}_{index}"),
                step.clone(),
            ));
        }
        child.push_obligation(ProofObligation::assert(
            format!("__broadcast_lemma_check_{name}"),
            ensures.clone(),
        ));

        let verdict = child.verify();
        let established = match &verdict {
            VerifyResult::Verified => true,
            VerifyResult::Unknown { category, .. } => {
                matches!(category, crate::encoder::UnknownCategory::VacuousTruth)
            }
            _ => false,
        };
        if std::env::var("TVC_DEBUG_BCAST_CHECK").is_ok() {
            eprintln!("[bcast-check] {name} established={established} verdict={verdict:?}");
        }
        if !established {
            unestablished.insert(name);
        }
    }

    if !unestablished.is_empty() {
        vc.obligations
            .retain(|obligation| !unestablished.contains(obligation.name()));
    }
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
///
/// SOUNDNESS: the search must recurse into `mod` blocks. The safety argument
/// above — "a declaration this can't see also can't be lowered, so it's
/// fail-closed regardless" — holds only for traits genuinely outside the file. A
/// module-NESTED trait is in the file and IS registered:
/// `trait_contracts::collect_source_trait_declarations` recurses into
/// `syn::Item::Mod`. Scanning only `file.items` therefore missed exactly the
/// declarations the collector had already accepted, so a requires-bearing
/// method's body axiom published unconditionally and a precondition-violating
/// call could verify. The two views must not diverge.
///
/// SOUNDNESS (rename): the header's LAST SEGMENT is not the trait. `use
/// origin::Orig as Alias; impl Alias for S` writes `"Alias"`, which names no
/// in-file declaration, so the scan found nothing, reported "no requires" and
/// the body axiom published UNCONDITIONALLY — a call-site PRECONDITION DROP that
/// let `#[requires(false)]` verify. Measured through the production CLI against
/// the byte-identical `impl origin::Orig for S`, which correctly errored. NO
/// duplicate ident is involved, so `reject_duplicate_trait_names` and
/// `prune_shadowed_duplicate_traits` — which only engage when two declarations
/// share a bare ident — never see it. The same spelling defeats a `pub use`
/// chain, a grouped `use {A as a}` and a `self::`-rooted rename.
///
/// A rename can also name the WRONG declaration: `use origin::Orig as Decoy`
/// next to `mod other { trait Decoy { /* no requires */ } }` resolved `"Decoy"`
/// to `other::Decoy` and dropped `origin::Orig`'s `requires` — again with every
/// declaration ident distinct. So the query is answered by the DECLARATION the
/// header actually resolves to, at its exact MODULE PATH, via the same
/// `TraitScopeIndex` walk the impl-header and trait-bound lanes use. Matching the
/// module path (not just the resolved ident) means this does not have to assume
/// the duplicate-ident gate has already run — it has not: this lane executes
/// before `reject_duplicate_trait_names`.
fn trait_method_declares_requires(
    file: &syn::File,
    item_impl: &syn::ItemImpl,
    method_name: &str,
) -> TrustVcResult<bool> {
    let Some((_, trait_path, _)) = &item_impl.trait_ else {
        return Ok(false);
    };
    // The impl headers this lane visits are all written at the file root
    // (`apply_inherent_impl_methods` iterates `file.items` only), so the
    // resolution scope is the crate root.
    let index = crate::trait_path_resolution::TraitScopeIndex::build(file);
    let Some((module, trait_ident)) = index.resolve_trait_path_decl(&[], trait_path) else {
        return match index.resolve_impl_trait_path(&[], trait_path) {
            // A trait this file genuinely does not declare, whose last segment
            // also cannot be mistaken for one that it does. Unchanged, and the
            // pre-existing modular-trust boundary: an invisible declaration's
            // `requires` is invisible to every lane, exactly as for a foreign
            // inherent method.
            crate::trait_path_resolution::TraitPathResolution::Foreign(_) => Ok(false),
            // Competing or undecidable. `true` WITHHOLDS the body axiom, which
            // is the fail-closed direction for this caller — it must never be
            // resolved by declaration order.
            _ => Ok(true),
        };
    };
    let Some(items) = items_at_module_path(&file.items, &module) else {
        return Ok(true); // the index named a module this walk cannot reach
    };
    trait_method_declares_requires_in_items(items, &trait_ident, method_name)
}

/// The item list of the inline module at `module` (empty = the file root), or
/// `None` when the path names no reachable inline module.
fn items_at_module_path<'a>(items: &'a [syn::Item], module: &[String]) -> Option<&'a [syn::Item]> {
    let Some((head, rest)) = module.split_first() else {
        return Some(items);
    };
    for item in items {
        let syn::Item::Mod(item_mod) = item else {
            continue;
        };
        if item_mod.ident != head {
            continue;
        }
        let (_, inner) = item_mod.content.as_ref()?;
        return items_at_module_path(inner, rest);
    }
    None
}

/// Requires-lookup half of [`trait_method_declares_requires`], over the item list
/// of the ONE module the header resolved into. Deliberately NOT recursive into
/// nested `mod`s any more: the module path is now exact, and re-descending would
/// re-admit a same-named declaration the header does not name.
fn trait_method_declares_requires_in_items(
    items: &[syn::Item],
    trait_ident: &str,
    method_name: &str,
) -> TrustVcResult<bool> {
    for item in items {
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
///
/// The gate is NOT specific to parameterized traits — it was originally wired
/// only to that branch, and the unparameterized case it left open is a CARDINAL
/// false verify: `trait TA { fn v()->u64 }` + `trait TB { fn v()->u64 }` both
/// implemented for `bool` bind ONE symbol `bool::v` (the concrete name carries
/// the self type, not the trait), the `<bool as TB>::v()` call site renders
/// `bool::v` with the trait qualifier DISCARDED, and the keeps-first `applied`
/// dedup answered BOTH calls with the first-declared body — so
/// `assert!(x == 1)` after `let x = <bool as TB>::v()` VERIFIED (truth: 2)
/// while the true `x == 2` was refuted, and flipping the two impls' source
/// order inverted every verdict.
///
/// Counting recurses into inline `mod` bodies: a nested `impl TB for bool` is
/// just as ambiguous a `bool::v` as a sibling one, and counting it makes the
/// key fail closed rather than silently resolve to whichever impl the
/// registration walk happens to see.
fn trait_impl_method_self_leaf_count(file: &File, self_type: &str, method_name: &str) -> usize {
    fn count_in_items(items: &[syn::Item], self_type: &str, method_name: &str) -> usize {
        let mut count = 0usize;
        for item in items {
            match item {
                syn::Item::Impl(item_impl) => {
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
                syn::Item::Mod(module) => {
                    if let Some((_, inner)) = &module.content {
                        count += count_in_items(inner, self_type, method_name);
                    }
                }
                _ => {}
            }
        }
        count
    }
    count_in_items(&file.items, self_type, method_name)
}

/// Count the INHERENT impls in `file` whose self-type base name is `self_type`
/// and which declare a method named `method_name`. The mirror of
/// [`trait_impl_method_self_leaf_count`] for the other declaration KIND, and
/// deliberately a pure function of the `syn::File` (not of
/// `InherentImplRegistry`, whose maps are filtered by admission gates and by
/// what the target function happens to reference) so that
/// [`MethodSymbolCensus::of`] sees every source declaration that competes for
/// the symbol, not just the ones some earlier pass admitted.
fn inherent_impl_method_self_leaf_count(file: &File, self_type: &str, method_name: &str) -> usize {
    fn count_in_items(items: &[syn::Item], self_type: &str, method_name: &str) -> usize {
        let mut count = 0usize;
        for item in items {
            match item {
                syn::Item::Impl(item_impl) => {
                    if item_impl.trait_.is_some() {
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
                syn::Item::Mod(module) => {
                    if let Some((_, inner)) = &module.content {
                        count += count_in_items(inner, self_type, method_name);
                    }
                }
                _ => {}
            }
        }
        count
    }
    count_in_items(&file.items, self_type, method_name)
}

/// The SURFACE a `(self_type, method)` pair is called through. The two surfaces
/// have DIFFERENT resolution rules, and collapsing them is precisely the defect
/// [`MethodSymbolCensus`] exists to make unrepresentable.
///
/// This distinction is not a nicety. `20e12591` fixed the trait-vs-trait
/// collision by gating on the bare pair with no surface, which ALSO deleted the
/// inherent registration for a `&self` method — and deleting the inherent
/// registration is what handed `t.w()` to the trait, because the inherent-wins
/// precedence in `prepared_context::type_env` is implemented as REGISTRATION
/// ORDER over a shared `(type, method)` map (`register_trait_impl_methods_for_
/// concrete_types` is documented "never overrides an existing binding … matching
/// Rust, where an inherent method shadows a trait method of the same name").
/// Removing the shadowing entry does not fail closed; it PROMOTES the shadowed
/// one.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum MethodCallSurface {
    /// `recv.m(..)`. RUST'S OWN RULE APPLIES: an inherent method takes
    /// precedence over a trait method of the same name. The UFCS spellings that
    /// mean the TRAIT (`B1::w(&t)`, `<T as B1>::w(&t)`) render trait-qualified
    /// and resolve through the per-trait UF `B1__w(Box_T(t))`, so they never
    /// land on this surface and an inherent declaration cannot capture them.
    Receiver,
    /// `S::m()` — the no-`self` associated-function rendering.
    /// `body_extract::format_call_expr` DISCARDS the trait qualifier
    /// (`<S as Tr>::m()` renders `S::m`), so the rendered symbol cannot
    /// distinguish an inherent `S::m` from ANY `<S as Tr>::m`. Every collision
    /// on this surface is genuinely unresolvable, which is why `20e12591`'s
    /// blanket drop was right HERE and wrong on `Receiver`.
    AssociatedPath,
}

/// Which DECLARATION KIND a `(self_type, method)` pair names, when it names
/// exactly one.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ResolvedMethodDecl {
    Inherent,
    Trait,
}

/// The complete census of source declarations competing for one
/// `(self_type, method_name)` symbol.
///
/// SOLE AUTHORITY for "which declaration does this method symbol name?". It is
/// an ENUM, not a pair of counts, so [`MethodSymbolCensus::resolve`] is an
/// exhaustive match and a newly-recognised declaration shape is a COMPILE
/// ERROR rather than a silent fall-through to first-wins — the failure mode
/// that produced this defect class eleven times. There is no `Default` and no
/// `..rest` constructor: the only way to obtain one is [`Self::of`], which
/// walks the whole file including inline `mod` bodies.
///
/// The resolution rule, applied uniformly: a symbol that does not resolve to
/// EXACTLY ONE declaration is DROPPED so the caller fails closed. Never
/// first-wins, never innermost-wins — naming the WRONG declaration is the
/// false-verify direction.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum MethodSymbolCensus {
    /// No declaration of this pair anywhere in the file.
    Undeclared,
    /// Exactly one inherent declaration, no trait-impl declaration.
    InherentUnique,
    /// Exactly one trait-impl declaration, no inherent declaration.
    TraitUnique,
    /// Exactly one inherent declaration AND one or more trait-impl
    /// declarations. Rust resolves `recv.m()` to the INHERENT one; the
    /// associated-path rendering cannot express the distinction.
    InherentShadowsTraits,
    /// Two or more inherent declarations (with or without trait impls).
    InherentAmbiguous,
    /// No inherent declaration and two or more trait-impl declarations.
    TraitAmbiguous,
}

impl MethodSymbolCensus {
    /// Censuses every declaration of `(self_type, method_name)` in `file`.
    fn of(file: &File, self_type: &str, method_name: &str) -> Self {
        let inherent = inherent_impl_method_self_leaf_count(file, self_type, method_name);
        let trait_impls = trait_impl_method_self_leaf_count(file, self_type, method_name);
        match (inherent, trait_impls) {
            (0, 0) => Self::Undeclared,
            (0, 1) => Self::TraitUnique,
            (0, _) => Self::TraitAmbiguous,
            (1, 0) => Self::InherentUnique,
            (1, _) => Self::InherentShadowsTraits,
            (_, _) => Self::InherentAmbiguous,
        }
    }

    /// The declaration this symbol names on `surface`, or `None` when no single
    /// declaration can be named — in which case every consumer must publish
    /// NOTHING about the symbol, so the caller fails closed.
    fn resolve(self, surface: MethodCallSurface) -> Option<ResolvedMethodDecl> {
        match (self, surface) {
            (Self::Undeclared, _) => None,
            (Self::InherentUnique, _) => Some(ResolvedMethodDecl::Inherent),
            (Self::TraitUnique, _) => Some(ResolvedMethodDecl::Trait),
            // Rust's shadowing rule, and the whole point of the surface split.
            (Self::InherentShadowsTraits, MethodCallSurface::Receiver) => {
                Some(ResolvedMethodDecl::Inherent)
            }
            // `<S as Tr>::m()` and `S::m()` render to the SAME string, so the
            // shadowing rule cannot be applied to the rendered symbol.
            (Self::InherentShadowsTraits, MethodCallSurface::AssociatedPath) => None,
            (Self::InherentAmbiguous, _) => None,
            (Self::TraitAmbiguous, _) => None,
        }
    }

    /// Whether a TRAIT impl's contract may be published about the shared
    /// concrete symbol `Type__method` — i.e. whether that symbol denotes this
    /// trait's method rather than an inherent one (or nothing determinate).
    ///
    /// SOUNDNESS-CRITICAL, and the half `20e12591` left open. The per-impl
    /// linking axiom `Tr__m(Box_S(s)) == S__m(s)` equates the trait UF with the
    /// concrete symbol. When an inherent `S::m` owns that symbol and carries its
    /// own definitional body axiom `S__m(s) == 4` while the trait's
    /// postcondition axiom says `Tr__m(_) == 9`, the linking axiom makes the
    /// context state `4 == 9` — a CONTRADICTION, which proves everything. So
    /// restoring the inherent body axiom (the `Receiver` half above) is only
    /// sound if the trait simultaneously stops claiming the symbol.
    fn trait_may_claim_concrete_symbol(self) -> bool {
        // The associated-path surface is the strictest of the two and is the one
        // that governs a bare `Type__method` string, which is exactly what the
        // linking axiom targets.
        matches!(
            self.resolve(MethodCallSurface::AssociatedPath),
            Some(ResolvedMethodDecl::Trait)
        )
    }
}

/// The trait-method names declared by `item_impl` whose shared concrete symbol
/// `Type__method` this impl may NOT claim, because `root_file` resolves that
/// symbol to a different declaration.
///
/// Feeds [`crate::ir::TraitImplDecl::inherent_shadowed_methods`], which the
/// per-impl linking axiom and the concrete-sorted trait-ensures axiom consult
/// before publishing anything about that symbol. `AssociatedPath` is the
/// surface used deliberately: the thing being guarded IS a bare
/// `Type__method` string, which is what the associated-path rendering produces
/// and what makes both spellings indistinguishable.
pub(crate) fn shadowed_trait_impl_methods(
    root_file: &File,
    item_impl: &syn::ItemImpl,
) -> std::collections::BTreeSet<String> {
    let mut shadowed = std::collections::BTreeSet::new();
    let Some(self_type) = impl_self_type_base_name(&item_impl.self_ty) else {
        return shadowed;
    };
    for impl_item in &item_impl.items {
        let syn::ImplItem::Fn(method) = impl_item else {
            continue;
        };
        let method_name = method.sig.ident.to_string();
        if !MethodSymbolCensus::of(root_file, &self_type, &method_name)
            .trait_may_claim_concrete_symbol()
        {
            shadowed.insert(method_name);
        }
    }
    shadowed
}

/// The surface an impl method is CALLED through, decided by its receiver.
/// A `self`-taking method is reached as `recv.m(..)`; a no-`self` associated
/// function is reached as `Type::m()`.
fn method_call_surface(method: &syn::ImplItemFn) -> MethodCallSurface {
    if method
        .sig
        .inputs
        .iter()
        .any(|input| matches!(input, syn::FnArg::Receiver(_)))
    {
        MethodCallSurface::Receiver
    } else {
        MethodCallSurface::AssociatedPath
    }
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
        // CROSS-KIND RESOLUTION. The registry already refuses to let source
        // order choose between two INHERENT declarations of one nominal key
        // (`ambiguous_methods`); this resolves the pair against the TRAIT
        // declarations that compete for the same symbol.
        //
        // This gate used to be the surface-blind
        // `trait_impl_method_self_leaf_count(..) != 0 => continue`, i.e. "an
        // inherent method is dropped whenever ANY trait impl for the type
        // declares that name". For the associated-path surface that is right:
        // `<S as Mk>::make()` renders `S::make` with the trait qualifier
        // DISCARDED, so inherent and trait land on ONE symbol that nothing can
        // tell apart. For the RECEIVER surface it was a CARDINAL FALSE VERIFY in
        // the opposite direction. Dropping the inherent registration does not
        // fail closed there: inherent-wins is implemented as REGISTRATION ORDER
        // in `prepared_context::type_env` (the trait lane is registered last and
        // "never overrides an existing binding"), so deleting the inherent entry
        // PROMOTES the trait's contract onto `t.w()`. Measured through the
        // production CLI, cache off, with an inherent `w -> 4` beside
        // `impl B1 for T { fn w -> 9 }`:
        //
        //     ensures(result == 4) { t.w() }  ->  counterexample   (TRUE, refuted)
        //     ensures(result == 9) { t.w() }  ->  VERIFIED         (FALSE, proved)
        //
        // Ground truth under stock `rustc --edition 2021`: `t.w()` is 4 and
        // `B1::w(&t)` is 9. Both directions wrong at once.
        //
        // `MethodSymbolCensus` is the sole authority; it is an exhaustive enum
        // so a new declaration shape cannot silently fall through to first-wins.
        // `Some(Inherent)` is the ONLY admitting answer here.
        if MethodSymbolCensus::of(file, &self_type, &method_name)
            .resolve(method_call_surface(method))
            != Some(ResolvedMethodDecl::Inherent)
        {
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
            file,
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
                file,
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
                file,
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
            // Collision gate for the trait body-axiom route, through the SAME
            // sole authority the inherent loop above consults, so the two lanes
            // cannot drift: this body axiom is published only when the shared
            // `Type::method` symbol resolves to a TRAIT declaration.
            //
            // It subsumes both of the counts this used to spell out by hand — a
            // second trait impl of the same `(self-type, method)` makes the pair
            // `TraitAmbiguous` (no first-wins body for a caller to misread), and
            // an inherent declaration of that name makes it
            // `InherentShadowsTraits`, which resolves AWAY from the trait on both
            // surfaces (to the inherent one on `Receiver`, per Rust; to nothing
            // on `AssociatedPath`, where the rendering is genuinely ambiguous).
            // `trait_is_parameterized` is still consulted by the per-method
            // admission gates above; only the collision gate is centralised here.
            if MethodSymbolCensus::of(file, &self_type, &method_name)
                .resolve(method_call_surface(method))
                != Some(ResolvedMethodDecl::Trait)
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
                file,
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
                file,
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
                        // A `#[spec]` method on an INHERENT impl (`impl S { spec fn
                        // inv(&self) -> bool { .. } }` — the ubiquitous Verus
                        // invariant-predicate shape) used to be skipped here on the
                        // assumption that the spec lane owns it. It does not: the
                        // spec-function catalog collects `syn::Item::Fn` ONLY, never
                        // `syn::ImplItem::Fn`, so such a method was registered NOWHERE
                        // and every `self.inv()` / `s.inv()` in a spec position died as
                        // "inv() on type `S` — not available in specification context".
                        // Admitting it here routes it through the SAME inherent-method
                        // pipeline as a plain method: a typed UF plus a definitional
                        // body axiom that is already requires-GUARDED, shadow-gated and
                        // ill-founded-recursion-gated by `InherentMethodDef`.
                        //
                        // Two spec-lane markers still decline, so the change only ever
                        // ADDS a definition where the semantics are the plain one:
                        //   * `#[opaque]` — the definition is deliberately hidden until
                        //     revealed; publishing it unconditionally would defeat
                        //     opacity (and the reveal machinery has no hook here).
                        //   * `#[uninterp]` — declared with NO body; there is no
                        //     definitional axiom to publish.
                        // `#[when_used_as_spec]` keeps declining as before: its exec
                        // body is NOT the spec meaning, so the exec body axiom would be
                        // the wrong definition.
                        let spec_lane_declines = has_spec_attr(&method.attrs)
                            && (has_opaque_attr(&method.attrs) || has_uninterp_attr(&method.attrs));
                        if spec_lane_declines
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

/// SOUNDNESS-CRITICAL (generic-receiver mutation framing). Records how each
/// TRAIT-DECLARED method takes its `self` receiver, keyed by the DECLARING
/// trait's name, for every `trait` item in the file (nested modules included).
///
/// This is the sibling of `register_impl_method_self_receiver_kinds` for the one
/// receiver shape that registry structurally cannot reach: a receiver whose
/// declared type is a `TypeParam` — `fn g<T: Tr>(t: &mut T)` and its
/// `fn g(t: &mut impl Tr)` sugar. Such a receiver has no `Datatype`, so
/// `receiver_struct_type_name` returns `None`, the struct branch of the
/// method-call mutation framing never fires, and an `&mut self` trait call was
/// left as a NO-OP on the caller's binding: two `t.a()` reads bracketing
/// `t.bump()` both lowered to the SAME `Tr__a(t)` term, so `y - x == 0` — a
/// FALSE claim — verified.
///
/// Deliberately INDEPENDENT of `#[trust_vc::trait_spec]` and of any modelability
/// gate: only the `self` kind is needed and it is well-defined for every
/// declared method. A `(trait, method)` absent from this map is UNKNOWN and the
/// consumer leaves the receiver alone — a trait that is not declared in the file
/// contributes no method resolution either, so its calls already fail closed at
/// lowering.
fn register_trait_decl_self_receiver_kinds(items: &[syn::Item], vc: &mut VerificationContext) {
    use crate::vc::SelfReceiverKind;
    for item in items {
        match item {
            syn::Item::Trait(item_trait) => {
                let trait_name = item_trait.ident.to_string();
                for trait_item in &item_trait.items {
                    let syn::TraitItem::Fn(method) = trait_item else {
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
                        // `self` / `mut self`: moved into the callee, so it
                        // cannot mutate the CALLER's binding.
                        SelfReceiverKind::Value
                    };
                    vc.register_trait_method_self_receiver_kind(
                        trait_name.clone(),
                        method.sig.ident.to_string(),
                        kind,
                    );
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner)) = &module.content {
                    register_trait_decl_self_receiver_kinds(inner, vc);
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
    /// `file` is the declaring file and is SOUNDNESS-CRITICAL, not incidental:
    /// the definitional body axiom published here is `Ty__m(self, args) == BODY`,
    /// and deciding whether BODY is modelable needs the file's mutation vectors
    /// (see `body_has_unframeable_mutation`).
    fn from_impl_method(
        self_type: &str,
        file: &File,
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
        // SOUNDNESS-CRITICAL (cardinal false verify), the inherent-method twin of
        // the sibling-helper gate: `impl C { fn via(mut self) -> u64 {
        // bump(&mut self); self.n } }` published `C__via(self) == self.n` against
        // the ENTRY `self`, so `C { n: 0 }.via()` proved `result == 0` while every
        // execution returns 1. Same for the receiver form (`self.tick()`). See
        // `body_has_unframeable_mutation`.
        let body_gated = method_params_shadowed(method)
            || body_has_unframeable_mutation(&method.block, file, &method.sig)
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
                    // A body axiom is `method(args) == BODY`; an unmodelable
                    // BODY must DROP the axiom, never be approximated. (The
                    // let-else lane's old guessed condition made this axiom
                    // outright FALSE for the else path, which proves anything.)
                    scoped_return_value_expression(
                        &method.block,
                        return_value,
                        &ctx.struct_types,
                        Some(ctx),
                        // This renders a METHOD's body, not the function under
                        // extraction, so none of the caller's seed applies. Read
                        // `CollectorLaneSeed::EMPTY` before assuming that is
                        // safe: "an empty seed can only produce fewer havocs" is
                        // NOT a soundness argument here — fewer havocs means the
                        // `havoc_deps` drop below does not fire.
                        &body_extract::CollectorLaneSeed::EMPTY,
                    )
                    .and_then(|(scoped_return, havoc_deps)| {
                        // A definitional axiom's binders are fixed by the method
                        // signature, so a body whose value reads an
                        // unmodelled-mutation havoc symbol has nowhere to declare
                        // it — and `method(args) == BODY` over a free symbol would
                        // be an outright FALSE premise. Drop the axiom (documented
                        // fail-closed behaviour of this lane).
                        if !havoc_deps.is_empty() {
                            return None;
                        }
                        let mut renamed_return = syn::parse_str::<Expr>(&scoped_return).ok()?;
                        IdentRenamer {
                            rename_map: rename_map.clone(),
                        }
                        .visit_expr_mut(&mut renamed_return);
                        Some(quote!(#renamed_return).to_string())
                    })
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
/// `recursion_suppresses_axiom` Stage 2.
///
/// "NOT caught HERE" IS NOT A SYSTEM-LEVEL GAP — read at face value the
/// paragraph above describes a live false `Verified`, and it is not one. Stage 2
/// does catch it. Probed cache-off: a contradictory `bad(n) == bad(n) + 1` under
/// a non-shrinking `#[decreases]`, and its mutual analog `p/q`, are both REFUTED
/// (axiom suppressed), while a well-founded `#[decreases]` and a non-recursive
/// spec fn both stay usable — so the discrimination is on whether the measure
/// shrinks, not on recursion per se. That Stage-2 coverage is what stands
/// between this structural partial and a cardinal false `Verified`, and nothing
/// pinned it, so a Stage-2 regression would have opened the hole silently with
/// every local comment still reading as intended. All four rows are now pinned
/// by `tests/nonshrinking_decreases_axiom_suppression.rs`.
///
/// The detection is name-approximate
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
    // The conformance lane has no verification context to type a scrutinee
    // against, so a refutable `let … else` tail declines here and the capture is
    // dropped — the sound direction for a captured body that becomes a
    // conformance-checked equation.
    let (body, havoc_deps) = scoped_return_value_expression(
        &method.block,
        return_value,
        &[],
        None,
        &body_extract::CollectorLaneSeed::EMPTY,
    )?;
    // Same rule as the trait-default body axiom below: this capture becomes a
    // conformance-checked EQUATION whose binders are fixed, so a body reading an
    // unmodelled-mutation havoc symbol must drop the capture, not free-float it.
    if !havoc_deps.is_empty() {
        return None;
    }
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
    // As above: each edge carries the module its CALLER is written in, so a
    // spelling is read in its own Rust scope rather than at the target's.
    let target_scope = enclosing_module_scope(file, target_func);
    let mut pending = referenced_helper_calls(target_func)
        .into_iter()
        .map(|reference| {
            (
                source_reference_with_aliases(reference, &aliases),
                target_scope.clone(),
            )
        })
        .collect::<BTreeSet<_>>();
    let no_aliases = BTreeMap::new();
    let mut applied = BTreeSet::new();
    let mut symbol_bindings = BTreeMap::new();

    while let Some(edge) = pending.iter().next().cloned() {
        pending.remove(&edge);
        if !applied.insert(edge.clone()) {
            continue;
        }
        let (reference, scope) = edge;
        let Some((helper, key)) = resolve_non_spec_source_function(
            &source_functions,
            &no_aliases,
            &reference,
            scope.as_deref(),
            target_func,
        ) else {
            continue;
        };
        bind_call_symbol(&mut symbol_bindings, &reference.call_symbol, &key)?;
        // Register spec functions the helper's body calls (transitively) so the
        // helper body axiom below can lower their applications.
        let helper_module = enclosing_module_scope(file, helper);
        let alias_validation = validate_block_use_alias_resolution(
            file,
            helper,
            helper,
            helper_module.as_deref(),
            source_file_is_crate_root,
        );
        if let Err(error) = alias_validation {
            // A unit-returning sibling with no `&mut` parameters has no logical
            // result or caller-visible mutation to axiomize. If its body uses
            // an import shape whose lexical identity we cannot represent, keep
            // that call opaque instead of failing an otherwise independent
            // caller. This is a loss of completeness, never authority: the
            // helper body and all of its transitive body facts are omitted.
            // Requires/ensures were collected separately above and remain
            // enforced at the call site.
            //
            // Non-unit results and `&mut` parameters must still fail closed:
            // omitting either could hide exactly the value or mutation that the
            // caller's postcondition observes.
            let body_is_logically_opaque = matches!(helper.sig.output, syn::ReturnType::Default)
                && !helper.sig.inputs.iter().any(fn_arg_is_mut_reference);
            if matches!(
                &error,
                TrustVcError::Encoding {
                    context: "block use alias resolution",
                    ..
                }
            ) && body_is_logically_opaque
            {
                continue;
            }
            return Err(error);
        }
        let mut spec_catalog = crate::spec_function_catalog::SpecFunctionCatalog::from_file(file);
        spec_catalog.register_exact_aliases(&block_use_function_aliases(&helper.block))?;
        spec_catalog.apply_referenced_specs(helper, vc)?;
        if let Some(def) = SiblingHelperDef::from_item_fn_with_name(
            &reference.call_symbol,
            file,
            helper,
            source_structs,
            vc,
            &ill_founded_recursive,
        )? {
            def.apply_to_context(vc);
        }
        let helper_aliases = block_use_function_aliases(&helper.block);
        for dependency in referenced_helper_calls(helper) {
            let dependency = (
                source_reference_with_aliases(dependency, &helper_aliases),
                helper_module.clone(),
            );
            if resolve_non_spec_source_function(
                &source_functions,
                &no_aliases,
                &dependency.0,
                dependency.1.as_deref(),
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
            file,
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

    if collector.nested_has_glob {
        return Err(TrustVcError::Encoding {
            context: "block use alias resolution",
            detail: "nested-block `use ...::*` import is not source-symbol indexed; its symbols \
                     enter an inner lexical scope that TrustVc does not model, so TrustVc fails \
                     closed instead of resolving a bare call through a same-spelled function \
                     from another Rust scope"
                .to_string(),
        });
    }

    // An outer-block glob is rejected only for the ambiguity this gate actually
    // names: a bare call the glob could bind whose spelling ALSO exists in some
    // other Rust scope. rustc already resolved this body — it compiled — so when
    // no competing binding of that spelling exists, the glob is the only
    // candidate and resolving through it reproduces rustc's own choice.
    //
    // This is deliberately conservative in both directions. A file-local
    // function of the same spelling actually *shadows* the glob in rustc, so
    // resolving to it would be correct; we still fail closed there rather than
    // encode a shadowing rule this lane does not otherwise model.
    if collector.outer_has_glob {
        // Only CALL spellings matter here. `called` above is deliberately a
        // superset — it mixes in expression paths and visibility targets — so
        // intersecting it directly would fire on every ordinary parameter or
        // `let` binder. A local binder or an explicit `use` alias also shadows a
        // glob deterministically in rustc and is already modelled by this lane,
        // so neither is an ambiguity. What is left is the real hazard: a bare
        // call whose spelling is ALSO defined as a function in this file.
        let mut call_symbols = referenced_helper_call_symbols(func);
        call_symbols.extend(crate::spec_function_catalog::called_names_in_block(
            &func.block,
        ));
        let file_function_spellings = SourceFunctionRegistry::from_file(file)
            .functions
            .keys()
            .filter_map(|path| path.rsplit("::").next().map(str::to_string))
            .collect::<BTreeSet<_>>();
        let shadowed = call_symbols
            .iter()
            .find(|name| file_function_spellings.contains(*name));
        if let Some(alias) = shadowed {
            return Err(TrustVcError::Encoding {
                context: "block use alias resolution",
                detail: format!(
                    "block `use ...::*` import can bind `{alias}`, which another Rust scope \
                     spells identically; glob imports are not source-symbol indexed, so TrustVc \
                     fails closed instead of resolving that bare call through the wrong \
                     definition"
                ),
            });
        }
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
            // quality-audit: allow-expect — the len() != 1 ambiguity gate above returned Err
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

/// True when `block` may mutate one of ITS OWN bindings in a way a definitional
/// BODY AXIOM cannot model — the gate shared by both body-axiom publishers
/// (`SiblingHelperDef::from_item_fn_with_name` and
/// `InherentMethodDef::from_impl_method`).
///
/// SOUNDNESS-CRITICAL — five measured cardinal false verifies across four
/// clauses:
///
///     pub fn bump(c: &mut C) { c.n = c.n + 1; }
///     pub fn via(mut c: C) -> u64 { bump(&mut c); c.n }      // via(c) == c.n
///     impl C { pub fn via(mut self) -> u64 { self.tick(); self.n } }
///     impl C { pub fn via(mut self) -> u64 { bump(&mut self); self.n } }
///     pub fn via(mut c: C) -> u64 { c.n = c.n + 1; c.n }     // clause 4
///     impl C { pub fn via(mut self) -> u64 { self.n = self.n + 1; self.n } }
///
/// Each published its body against the ENTRY value, so `via(C { n: 0 })` proved
/// `result == 0` while every execution returns 1. A published axiom is a PREMISE
/// — a false one proves arbitrary goals — so this is not an ordinary
/// over-approximation site.
///
/// WHY A GATE AND NOT FRAMING. These renders run over the TARGET's context, in
/// which the helper's/method's own PARAMETERS are not declared, and both the
/// free-call havoc (`havoc_mut_ref_call_arg_referents`) and the receiver havoc
/// resolve their subject through a tracked binding or a declared type. Neither
/// has anything to bind here, so seeding the render cannot help — measured, and
/// the false verify survived a seeded first draft. A definitional axiom's
/// binders are fixed by the signature, so unlike the caller lane there is also
/// no fresh symbol to fall back on: the axiom is DROPPED and the function stays
/// an opaque uninterpreted function, this lane's documented fail-closed
/// behaviour.
///
/// Clause 4 (a direct projected write to a PARAMETER) was added after the first
/// three shipped, and its existence is the lesson: clauses 1-3 are all
/// CALL-SITE shaped, so a bare `c.n = c.n + 1` — the same false axiom with the
/// call removed — walked straight past every one of them. When a gate
/// enumerates the ways an effect can be SPELLED, the next spelling is a hole.
///
/// The four clauses are deliberately NAME- and SHAPE-based rather than resolved
/// through types: the receiver's type is exactly what is unavailable here. They
/// over-approximate in the fail-closed direction only, and each is gated on the
/// body's own CALL SITES — a file that merely declares a mutator costs a
/// non-calling body nothing — except clause 4, which is gated on the write's
/// place ROOT being one of this signature's own binders. A body that only reads
/// keeps its axiom (`a_pure_sibling_helper_keeps_its_body_axiom`), and a field
/// write to a body-local keeps it too
/// (`a_field_write_to_a_body_local_keeps_its_body_axiom`).
fn body_has_unframeable_mutation(block: &syn::Block, file: &File, sig: &syn::Signature) -> bool {
    let (mut_self_methods, mut_ref_param_fns) = file_mutation_vectors(file);

    struct Finder<'a> {
        mut_self_methods: &'a BTreeSet<String>,
        mut_ref_param_fns: &'a BTreeSet<String>,
        /// The published function's OWN parameter binders — see clause 4.
        param_names: &'a BTreeSet<String>,
        found: bool,
    }
    impl<'ast> Visit<'ast> for Finder<'_> {
        // Clause 1: a `&mut` BORROW of anything. Whatever it is handed to may
        // write through it, and this render tracks no place through which the
        // write could be observed. Covers `bump(&mut c)` / `bump(&mut self)`
        // regardless of whether the callee resolves.
        fn visit_expr_reference(&mut self, reference: &'ast syn::ExprReference) {
            if reference.mutability.is_some() {
                self.found = true;
            }
            syn::visit::visit_expr_reference(self, reference);
        }
        // Clause 2: a call to a method some `impl`/`trait` in the file declares
        // with a `&mut self` receiver. Covers `self.tick()` / `c.tick()`.
        fn visit_expr_method_call(&mut self, call: &'ast syn::ExprMethodCall) {
            if self.mut_self_methods.contains(&call.method.to_string()) {
                self.found = true;
            }
            syn::visit::visit_expr_method_call(self, call);
        }
        // Clause 3: a call to a file-declared free function that takes a `&mut`
        // parameter, with no `&mut` at the call site — the argument is already a
        // reference (`fn via(c: &mut C) -> u64 { bump(c); c.n }`). This is the
        // same callee-signature signal the caller lane's havoc uses; here it is
        // matched on the path's last segment because the axiom lane has no scope
        // resolution of its own.
        fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
            if let syn::Expr::Path(path) = &*call.func {
                if let Some(last) = path.path.segments.last() {
                    if self.mut_ref_param_fns.contains(&last.ident.to_string()) {
                        self.found = true;
                    }
                }
            }
            syn::visit::visit_expr_call(self, call);
        }
        // Clause 4: a DIRECT WRITE to a projected place (`c.n = c.n + 1`,
        // `v[0] = 1`, `*p = 1`) rooted at one of the published function's OWN
        // PARAMETERS — including `self`.
        //
        // SOUNDNESS-CRITICAL, and NOT reachable by clauses 1-3: every one of
        // those is CALL-SITE shaped, and a bare field assignment calls nothing.
        // `fn via(mut c: C) -> u64 { c.n = c.n + 1; c.n }` therefore still
        // published `via(c) == c.n` over the ENTRY `c` — the same false premise
        // the call-shaped clauses were added for, with the call removed. Its
        // `impl C { fn via(mut self) -> u64 { self.n = self.n + 1; self.n } }`
        // twin likewise. Measured: `ensures(result == 0u64)` for
        // `via(C { n: 0 })` proved, while `ensures(result == 1u64)` — the TRUE
        // claim — was refuted, which is the signature of an axiom pinned to the
        // entry state.
        //
        // NARROWNESS, and what a blunter "any field write" clause would fail:
        // the write must be rooted at a PARAMETER. A field write to a LOCAL the
        // body itself created is modeled correctly by the render
        // (`fn via(x: u64) -> u64 { let mut c = C { n: x }; c.n = 5; c.n }`
        // proves `via(1) == 5` and refutes `via(1) == 1`), so gating on the
        // syntactic shape alone would retire a working capability. A BARE
        // scalar assignment to a parameter (`fn via(mut v: u64) { v = v + 1; v }`)
        // is also modeled correctly and is excluded by the projection test.
        fn visit_expr_assign(&mut self, assign: &'ast syn::ExprAssign) {
            if self.projected_param_write(&assign.left) {
                self.found = true;
            }
            syn::visit::visit_expr_assign(self, assign);
        }
        fn visit_expr_binary(&mut self, binary: &'ast syn::ExprBinary) {
            if binop_is_assignment(&binary.op) && self.projected_param_write(&binary.left) {
                self.found = true;
            }
            syn::visit::visit_expr_binary(self, binary);
        }
    }

    impl Finder<'_> {
        fn projected_param_write(&self, target: &syn::Expr) -> bool {
            // A BARE `ident = ..` is a whole-binding rebind the render models;
            // only a projection (`c.n`, `v[0]`, `*p`, and their nestings) is
            // unmodelable over a parameter binder.
            if matches!(target, syn::Expr::Path(_)) {
                return false;
            }
            place_root_ident(target).is_some_and(|root| self.param_names.contains(&root))
        }
    }

    let param_names = signature_binding_names(sig);
    let mut finder = Finder {
        mut_self_methods: &mut_self_methods,
        mut_ref_param_fns: &mut_ref_param_fns,
        param_names: &param_names,
        found: false,
    };
    finder.visit_block(block);
    finder.found
}

/// The root binding of a place expression, peeling field / index / deref /
/// paren wrappers (`(*o).inner.v[i]` -> `o`).
fn place_root_ident(expr: &syn::Expr) -> Option<String> {
    match expr {
        syn::Expr::Path(path) => (path.qself.is_none() && path.path.segments.len() == 1)
            .then(|| path.path.segments[0].ident.to_string()),
        syn::Expr::Field(field) => place_root_ident(&field.base),
        syn::Expr::Index(index) => place_root_ident(&index.expr),
        syn::Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Deref(_)) => {
            place_root_ident(&unary.expr)
        }
        syn::Expr::Paren(paren) => place_root_ident(&paren.expr),
        syn::Expr::Group(group) => place_root_ident(&group.expr),
        _ => None,
    }
}

/// Every binding name introduced by `sig`'s parameter list, including `self`.
fn signature_binding_names(sig: &syn::Signature) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for input in &sig.inputs {
        match input {
            FnArg::Receiver(_) => {
                out.insert("self".to_string());
            }
            FnArg::Typed(pat_type) => {
                out.extend(pat_binding_names(&pat_type.pat));
            }
        }
    }
    out
}

fn pat_binding_names(pat: &syn::Pat) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    fn walk(pat: &syn::Pat, out: &mut BTreeSet<String>) {
        match pat {
            syn::Pat::Ident(pat_ident) => {
                out.insert(pat_ident.ident.to_string());
                if let Some((_, sub)) = &pat_ident.subpat {
                    walk(sub, out);
                }
            }
            syn::Pat::Reference(inner) => walk(&inner.pat, out),
            syn::Pat::Type(inner) => walk(&inner.pat, out),
            syn::Pat::Paren(inner) => walk(&inner.pat, out),
            syn::Pat::Tuple(tuple) => {
                for element in &tuple.elems {
                    walk(element, out);
                }
            }
            syn::Pat::TupleStruct(tuple) => {
                for element in &tuple.elems {
                    walk(element, out);
                }
            }
            syn::Pat::Struct(strukt) => {
                for field in &strukt.fields {
                    walk(&field.pat, out);
                }
            }
            syn::Pat::Slice(slice) => {
                for element in &slice.elems {
                    walk(element, out);
                }
            }
            syn::Pat::Or(or) => {
                for case in &or.cases {
                    walk(case, out);
                }
            }
            _ => {}
        }
    }
    walk(pat, &mut out);
    out
}

/// `(methods declared `&mut self`, free functions with a `&mut` parameter)` for
/// every `impl` / `trait` / `fn` in `items`, descending into inline modules
/// exactly as the receiver-kind registries do.
///
/// Read from the FILE, not from the context's receiver-kind registries:
/// `apply_inherent_impl_methods` and `apply_sibling_helper_functions` both run
/// BEFORE `register_impl_method_self_receiver_kinds` /
/// `register_trait_decl_self_receiver_kinds`, so those maps are still empty at
/// gate time and a context-based gate silently never fires. (Measured: it did
/// not, and the false verify survived it.)
///
/// `&self` and by-value `self` are excluded — they cannot mutate the caller's
/// binding — and so is a `&`-shared parameter, which is spelled identically at
/// the call site. That exclusion is what keeps the gate from being a blanket
/// rejection.
fn file_mutation_vectors(file: &File) -> (BTreeSet<String>, BTreeSet<String>) {
    fn walk(
        items: &[syn::Item],
        mut_self: &mut BTreeSet<String>,
        mut_param: &mut BTreeSet<String>,
    ) {
        fn is_mut_self(sig: &syn::Signature) -> bool {
            matches!(
                sig.inputs.first(),
                Some(syn::FnArg::Receiver(recv))
                    if recv.reference.is_some() && recv.mutability.is_some()
            )
        }
        fn has_mut_ref_param(sig: &syn::Signature) -> bool {
            sig.inputs.iter().any(|input| match input {
                syn::FnArg::Typed(pat_type) => {
                    matches!(&*pat_type.ty, Type::Reference(r) if r.mutability.is_some())
                }
                syn::FnArg::Receiver(_) => false,
            })
        }
        for item in items {
            match item {
                syn::Item::Fn(item_fn) => {
                    if has_mut_ref_param(&item_fn.sig) {
                        mut_param.insert(item_fn.sig.ident.to_string());
                    }
                }
                syn::Item::Impl(item_impl) => {
                    for impl_item in &item_impl.items {
                        if let syn::ImplItem::Fn(method) = impl_item {
                            if is_mut_self(&method.sig) {
                                mut_self.insert(method.sig.ident.to_string());
                            }
                            if has_mut_ref_param(&method.sig) {
                                mut_param.insert(method.sig.ident.to_string());
                            }
                        }
                    }
                }
                syn::Item::Trait(item_trait) => {
                    for trait_item in &item_trait.items {
                        if let syn::TraitItem::Fn(method) = trait_item {
                            if is_mut_self(&method.sig) {
                                mut_self.insert(method.sig.ident.to_string());
                            }
                            if has_mut_ref_param(&method.sig) {
                                mut_param.insert(method.sig.ident.to_string());
                            }
                        }
                    }
                }
                syn::Item::Mod(module) => {
                    if let Some((_, inner)) = &module.content {
                        walk(inner, mut_self, mut_param);
                    }
                }
                _ => {}
            }
        }
    }
    let mut mut_self = BTreeSet::new();
    let mut mut_param = BTreeSet::new();
    walk(&file.items, &mut mut_self, &mut mut_param);
    (mut_self, mut_param)
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

    /// `file` is the declaring file, and it is SOUNDNESS-CRITICAL rather than
    /// incidental: the body axiom published here is `name(args) == BODY`, and
    /// deciding whether BODY is modelable at all requires THIS helper's own
    /// callee signatures — the target's tell you nothing about it.
    ///
    /// Without it, `fn via(mut c: C) -> u64 { bump(&mut c); c.n }` published
    /// `via(c) == c.n` against the ENTRY `c` — an outright FALSE premise, and a
    /// cardinal false verify at any call site (`via(C { n: 0 })` proved
    /// `result == 0` when every execution returns 1).
    fn from_item_fn_with_name(
        name: &str,
        file: &File,
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

        // SOUNDNESS-CRITICAL (cardinal false verify). A body that may mutate one
        // of its own bindings publishes an axiom over the ENTRY value —
        // `fn via(mut c: C) -> u64 { bump(&mut c); c.n }` published
        // `via(c) == c.n`, an outright FALSE premise, and `via(C { n: 0 })`
        // proved `result == 0` while every execution returns 1. See
        // `body_has_unframeable_mutation` for why this is a publisher gate and
        // not something the render could be seeded to handle.
        let (body_condition, trigger) = if helper_has_requires_clause(&item_fn.attrs)?
            || params_shadowed_in_body(item_fn)
            || body_has_unframeable_mutation(&item_fn.block, file, &item_fn.sig)
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
                    // Same rule as the trait-default body axiom: an unmodelable
                    // body must DROP the definitional axiom rather than be
                    // approximated, or `name(args) == BODY` becomes an outright
                    // false premise.
                    let Some((scoped_return, _havoc_deps)) = scoped_return_value_expression(
                        &item_fn.block,
                        return_value,
                        &ctx.struct_types,
                        Some(ctx),
                        // The caller's seed describes the function under
                        // extraction, not this helper. The helper's own
                        // `&mut`-call framing is handled by the gate ABOVE (which
                        // drops the axiom outright) rather than by seeding this
                        // render, because the render cannot frame the helper's
                        // PARAMETERS: `havoc_mut_ref_call_arg_referents` only
                        // rebinds a root it can see as a tracked binding, and a
                        // helper's params are declared in neither this throwaway
                        // scope stack nor the target's context.
                        &body_extract::CollectorLaneSeed::EMPTY,
                    )
                    .filter(|(_, havoc_deps)| havoc_deps.is_empty()) else {
                        return Ok(None);
                    };
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

/// `#[opaque]` / `#[trust_vc::opaque]` — the spec function's DEFINITION is
/// deliberately hidden from the solver until an explicit `reveal`. Mirrors
/// `spec_function_catalog::has_opaque_attr` (private there); kept as a local
/// last-segment match so the inherent-method registry can decline to publish a
/// body axiom for an opaque spec method.
fn has_opaque_attr(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "opaque")
    })
}

/// `#[uninterp]` — a spec function DECLARED with no body (its `Block` is a
/// synthesized empty one). There is no definition to publish.
fn has_uninterp_attr(attrs: &[syn::Attribute]) -> bool {
    crate::spec_function_catalog::has_uninterp_attr(attrs)
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
