// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::TrustVcType;
use std::collections::BTreeSet;
use syn::{FnArg, Pat, Type};

/// Extracts declared verification variables from a function input.
///
/// This includes explicit bindings for `self` receivers so method-style
/// signatures cannot silently skip the receiver in the verification context.
pub(super) fn extract_vars_from_input(input: &FnArg) -> TrustVcResult<Vec<(String, String)>> {
    extract_vars_from_input_resolving_array_lengths(input, &|_| None, &BTreeSet::new())
}

/// Extracts declared verification variables, resolving array lengths.
///
/// `array_len_resolver` maps a length ident to a concrete literal `usize` (for
/// top-level `const N: usize = <lit>` parameters). `const_generic_len_names`
/// holds the function's own const-generic parameters (`fn f<const N: usize>`);
/// when a non-literal array length names one of these, the parameter is modeled
/// with a *symbolic* length (`Seq<elem>`) whose `view().len()` is tied to the
/// `N` parameter by the caller, instead of failing closed. This is sound: a
/// length-`N` sequence is a strictly more general model than a fixed-length
/// array, so it can never prove a property that the concrete array would refute.
pub(super) fn extract_vars_from_input_resolving_array_lengths(
    input: &FnArg,
    array_len_resolver: &impl Fn(&str) -> Option<usize>,
    const_generic_len_names: &BTreeSet<String>,
) -> TrustVcResult<Vec<(String, String)>> {
    match input {
        FnArg::Typed(pat_type) => extract_vars_from_pattern_resolving_array_lengths(
            &pat_type.pat,
            &pat_type.ty,
            array_len_resolver,
            const_generic_len_names,
        ),
        FnArg::Receiver(receiver) => {
            Ok(vec![("self".to_string(), extract_type_name(&receiver.ty))])
        }
    }
}

/// Returns `(param_name, const_generic_ident)` when `input` is a by-value or
/// by-reference fixed-size array parameter `[elem; N]` whose length names one
/// of the function's const-generic parameters in `const_generic_len_names`.
///
/// The caller uses this to (a) declare `N` as a `usize` verification variable
/// and (b) bind `param@.len() == N`. Returns `None` for literal lengths,
/// top-level-const lengths, non-array parameters, and tuple/struct patterns
/// (those keep their existing handling).
pub(super) fn const_generic_array_length_binding(
    input: &FnArg,
    array_len_resolver: &impl Fn(&str) -> Option<usize>,
    const_generic_len_names: &BTreeSet<String>,
) -> Option<(String, String)> {
    let FnArg::Typed(pat_type) = input else {
        return None;
    };
    let Pat::Ident(ident) = &*pat_type.pat else {
        return None;
    };
    let len_ident = const_generic_array_len_ident(&pat_type.ty)?;
    // A length that resolves to a concrete literal is handled by the existing
    // literal path; only genuinely symbolic const-generic lengths bind here.
    if array_len_resolver(&len_ident).is_some() {
        return None;
    }
    if !const_generic_len_names.contains(&len_ident) {
        return None;
    }
    Some((ident.ident.to_string(), len_ident))
}

pub(super) fn extract_erased_shared_ref_vars_from_input(
    input: &FnArg,
    const_generic_len_names: &BTreeSet<String>,
) -> TrustVcResult<Vec<String>> {
    match input {
        FnArg::Typed(pat_type) if is_erased_shared_ref_type(&pat_type.ty) => {
            // Thread the function's const-generic length params so a symbolic
            // `&[u8; N]` parameter is not rejected here while the main typed
            // path accepts it (the reject is a type-modeling concern, but this
            // name-only walk shares the same pattern matcher).
            Ok(extract_vars_from_pattern_resolving_array_lengths(
                &pat_type.pat,
                &pat_type.ty,
                &|_| None,
                const_generic_len_names,
            )?
            .into_iter()
            .map(|(name, _)| name)
            .collect())
        }
        FnArg::Receiver(receiver) if is_erased_shared_ref_type(&receiver.ty) => {
            Ok(vec!["self".to_string()])
        }
        _ => Ok(Vec::new()),
    }
}

pub(super) fn extract_erased_ghost_vars_from_input(input: &FnArg) -> TrustVcResult<Vec<String>> {
    match input {
        FnArg::Typed(pat_type) if is_erased_ghost_type(&pat_type.ty) => {
            Ok(extract_vars_from_pattern(&pat_type.pat, &pat_type.ty)?
                .into_iter()
                .map(|(name, _)| name)
                .collect())
        }
        _ => Ok(Vec::new()),
    }
}

pub(super) fn extract_supported_mut_ref_scalar_vars_from_input(
    input: &FnArg,
) -> TrustVcResult<Vec<String>> {
    match input {
        FnArg::Typed(pat_type) if is_supported_mut_ref_scalar_type(&pat_type.ty) => {
            Ok(extract_vars_from_pattern(&pat_type.pat, &pat_type.ty)?
                .into_iter()
                .map(|(name, _)| name)
                .collect())
        }
        _ => Ok(Vec::new()),
    }
}

/// The binding name of a parameter declared as a mutable reference `&mut T`
/// (any referent type), when the pattern is a simple identifier. Used to
/// identify `&mut <collection>` params, whose post-body FINAL value a method
/// mutation does not thread into the string body model — a postcondition over
/// them must fail closed (the straight-line sibling of the catastrophic loop
/// collection-mutation gap).
///
/// This deliberately reads ONLY the binding ident and does NOT run the
/// type-rejecting pattern extractor: a `&mut [T; N]` const-generic-length param
/// is modeled symbolically elsewhere and must not be rejected here. Non-ident
/// patterns (rare for `&mut` params) yield no name; the worst case is a missed
/// fail-closed, never a spurious extraction error on a previously-OK function.
pub(super) fn extract_mut_ref_var_from_input(input: &FnArg) -> Option<String> {
    let FnArg::Typed(pat_type) = input else {
        return None;
    };
    if !is_mut_ref_type(&pat_type.ty) {
        return None;
    }
    pattern_binding_ident(&pat_type.pat)
}

/// The bound identifier of a simple binding pattern (`x`, `mut x`, `&x`,
/// `&mut x`), peeling reference/paren wrappers. Returns `None` for compound
/// patterns (tuples, structs, …).
fn pattern_binding_ident(pat: &Pat) -> Option<String> {
    match pat {
        Pat::Ident(ident) => Some(ident.ident.to_string()),
        Pat::Reference(reference) => pattern_binding_ident(&reference.pat),
        Pat::Paren(paren) => pattern_binding_ident(&paren.pat),
        Pat::Type(pat_type) => pattern_binding_ident(&pat_type.pat),
        _ => None,
    }
}

fn is_mut_ref_type(ty: &Type) -> bool {
    matches!(ty, Type::Reference(reference) if reference.mutability.is_some())
}

pub(super) fn is_erased_shared_ref_type(ty: &Type) -> bool {
    matches!(ty, Type::Reference(reference) if reference.mutability.is_none())
}

pub(super) fn is_supported_mut_ref_scalar_type(ty: &Type) -> bool {
    let Type::Reference(reference) = ty else {
        return false;
    };
    if reference.mutability.is_none() {
        return false;
    }

    let referent_ty = TrustVcType::parse_or_opaque(&extract_type_name(&reference.elem));
    matches!(referent_ty, TrustVcType::Bool) || referent_ty.is_integer()
}

fn is_erased_ghost_type(ty: &Type) -> bool {
    let Type::Path(type_path) = ty else {
        return false;
    };
    type_path
        .path
        .segments
        .last()
        .is_some_and(|segment| segment.ident == "Ghost")
}

/// Extracts variable names from a pattern, handling complex patterns like
/// references, mutability, and tuple destructuring. Returns (name, type) pairs.
///
/// Returns an error for unsupported patterns (struct destructuring, enum
/// matching, etc.) because silently dropping variables would produce false
/// verification results — preconditions referencing them would fail to bind.
pub(super) fn extract_vars_from_pattern(
    pat: &Pat,
    ty: &Type,
) -> TrustVcResult<Vec<(String, String)>> {
    extract_vars_from_pattern_resolving_array_lengths(pat, ty, &|_| None, &BTreeSet::new())
}

fn extract_vars_from_pattern_resolving_array_lengths(
    pat: &Pat,
    ty: &Type,
    array_len_resolver: &impl Fn(&str) -> Option<usize>,
    const_generic_len_names: &BTreeSet<String>,
) -> TrustVcResult<Vec<(String, String)>> {
    match pat {
        Pat::Ident(ident) => {
            let name = ident.ident.to_string();
            reject_unsupported_const_generic_array_type(
                &name,
                ty,
                array_len_resolver,
                const_generic_len_names,
            )?;
            Ok(vec![(
                name,
                extract_type_name_resolving_array_lengths(
                    ty,
                    array_len_resolver,
                    const_generic_len_names,
                ),
            )])
        }
        Pat::Reference(ref_pat) => {
            // &x: &T or &mut x: &mut T — unwrap reference to get inner pattern
            // The type is the referenced type, not the reference itself
            let inner_ty = if let Type::Reference(ref_ty) = ty {
                &*ref_ty.elem
            } else {
                ty
            };
            extract_vars_from_pattern_resolving_array_lengths(
                &ref_pat.pat,
                inner_ty,
                array_len_resolver,
                const_generic_len_names,
            )
        }
        Pat::Tuple(tuple) => {
            // (a, b): (T1, T2) — extract from each element with matching type
            if let Type::Tuple(type_tuple) = ty {
                let mut vars = Vec::new();
                for (elem_pat, elem_ty) in tuple.elems.iter().zip(type_tuple.elems.iter()) {
                    vars.extend(extract_vars_from_pattern_resolving_array_lengths(
                        elem_pat,
                        elem_ty,
                        array_len_resolver,
                        const_generic_len_names,
                    )?);
                }
                Ok(vars)
            } else {
                Err(TrustVcError::Encoding {
                    context: "extract parameter variables",
                    detail: format!(
                        "Tuple pattern with non-tuple type '{}' — variables would be silently dropped",
                        extract_type_name(ty)
                    ),
                })
            }
        }
        Pat::Type(type_pat) => {
            // Redundant type annotation wrapping — unwrap and recurse
            extract_vars_from_pattern_resolving_array_lengths(
                &type_pat.pat,
                ty,
                array_len_resolver,
                const_generic_len_names,
            )
        }
        Pat::Wild(_) => {
            // Wildcard `_` pattern — intentionally discarded, no variables to bind
            Ok(Vec::new())
        }
        _ => Err(TrustVcError::Encoding {
            context: "extract parameter variables",
            detail: "Unsupported parameter pattern in function signature — \
                     variables from this pattern will be missing from verification context, \
                     which could cause false verification results"
                .to_string(),
        }),
    }
}

fn reject_unsupported_const_generic_array_type(
    name: &str,
    ty: &Type,
    array_len_resolver: &impl Fn(&str) -> Option<usize>,
    const_generic_len_names: &BTreeSet<String>,
) -> TrustVcResult<()> {
    let Some((shape, len)) = const_generic_array_shape(ty) else {
        return Ok(());
    };
    let len_ident = const_generic_array_len_ident(ty);
    // A length that resolves to a concrete literal (top-level `const N: usize`)
    // keeps its fixed-length array model.
    if len_ident.as_deref().and_then(array_len_resolver).is_some() {
        return Ok(());
    }
    // A length naming one of the function's own const-generic parameters is
    // modeled symbolically (`Seq<elem>` with `len() == N`) by the caller, so it
    // is accepted here rather than rejected.
    if len_ident
        .as_deref()
        .is_some_and(|ident| const_generic_len_names.contains(ident))
    {
        return Ok(());
    }
    Err(TrustVcError::Encoding {
        context: "extract parameter variables",
        detail: format!(
            "unsupported const-generic array length in parameter `{name}`: `{shape}` uses \
             non-literal length `{len}`. TrustVc only supports fixed literal array lengths today."
        ),
    })
}

fn extract_type_name_resolving_array_lengths(
    ty: &Type,
    array_len_resolver: &impl Fn(&str) -> Option<usize>,
    const_generic_len_names: &BTreeSet<String>,
) -> String {
    match ty {
        Type::Reference(reference) => {
            let inner = extract_type_name_resolving_array_lengths(
                &reference.elem,
                array_len_resolver,
                const_generic_len_names,
            );
            if reference.mutability.is_some() {
                format!("&mut {inner}")
            } else {
                format!("&{inner}")
            }
        }
        Type::Array(array) => {
            let Some(name) = expr_single_path_ident(&array.len) else {
                return extract_type_name(ty);
            };
            let elem = extract_type_name_resolving_array_lengths(
                &array.elem,
                array_len_resolver,
                const_generic_len_names,
            );
            if let Some(len) = array_len_resolver(&name) {
                return format!("[{elem};{len}]");
            }
            // Symbolic const-generic length `[elem; N]`: model as a
            // variable-length `Seq<elem>`. The caller binds the view length to
            // the `N` parameter (`param@.len() == N`). A sequence of arbitrary
            // length is strictly weaker than a fixed-length array, so this can
            // only prove fewer obligations — never a false Verified.
            if const_generic_len_names.contains(&name) {
                return format!("Seq<{elem}>");
            }
            extract_type_name(ty)
        }
        _ => extract_type_name(ty),
    }
}

fn const_generic_array_shape(ty: &Type) -> Option<(String, String)> {
    match ty {
        Type::Reference(reference) => const_generic_array_shape(&reference.elem),
        Type::Array(array)
            if !matches!(
                array.len,
                syn::Expr::Lit(syn::ExprLit {
                    lit: syn::Lit::Int(_),
                    ..
                })
            ) =>
        {
            let elem = extract_type_name(&array.elem);
            let len = expr_compact_string(&array.len);
            Some((format!("[{elem}; {len}]"), len))
        }
        _ => None,
    }
}

fn const_generic_array_len_ident(ty: &Type) -> Option<String> {
    match ty {
        Type::Reference(reference) => const_generic_array_len_ident(&reference.elem),
        Type::Array(array) => expr_single_path_ident(&array.len),
        _ => None,
    }
}

fn expr_single_path_ident(expr: &syn::Expr) -> Option<String> {
    let syn::Expr::Path(path) = expr else {
        return None;
    };
    if path.qself.is_none() && path.path.segments.len() == 1 {
        Some(path.path.segments[0].ident.to_string())
    } else {
        None
    }
}

fn expr_compact_string(expr: &syn::Expr) -> String {
    use quote::quote;
    quote!(#expr).to_string().replace(' ', "")
}

/// Classifies whether an origin syn *type string* (as produced by
/// [`extract_type_name`] / [`extract_type_name_resolving_array_lengths`]) is a
/// `usize`-length-bounded EXEC collection: a `Vec<T>`, a slice `[T]`, or an
/// array `[T; N]`, peeling any leading references. Returns `true` only for those
/// shapes.
///
/// SOUNDNESS BOUNDARY (the crux of the Vec/Seq length-boundedness lane): this
/// MUST return `false` for a spec `Seq<T>` (and everything else). An exec `Vec`
/// and a spec `Seq` both collapse to `TrustVcType::Seq` in `parse_or_opaque`, so
/// this string — the origin syn spelling, captured BEFORE that collapse — is the
/// sole place the two are distinguished. A `Vec`/`[..]` genuinely cannot hold
/// more than `usize::MAX` elements (so `len <= 2^pointer_width-1` is a true fact
/// the encoder may assert); a `Seq`'s length is an unbounded `Int` and must
/// never receive that bound (doing so poisons the huge-length soundness guards).
///
/// The classifier is deliberately POSITIVE-only: it recognizes `Vec`/slice/array
/// and returns `false` for anything it does not positively recognize, so a
/// `Seq<T>`, `Set`, `Map`, scalar, datatype, etc. can never be misclassified as
/// bounded. Note the symbolic const-generic array path
/// ([`extract_type_name_resolving_array_lengths`]) intentionally renders as
/// `Seq<elem>`, so it classifies as UNBOUNDED here — a sound (strictly weaker)
/// under-approximation, never a leak.
pub(super) fn syn_type_string_is_bounded_len_collection(type_str: &str) -> bool {
    let peeled = strip_leading_references(type_str.trim());
    // A slice `[T]` or an array `[T; N]` — both length-bounded. (A tuple renders
    // as `(..)`, never `[..]`, so this does not over-match.)
    if peeled.starts_with('[') {
        return true;
    }
    // A `Vec<..>` path: the final `::`-separated segment before any `<` must be
    // exactly `Vec` (`Vec<T>`, `std::vec::Vec<T>`, `alloc::vec::Vec<T>`). `Seq`,
    // `Set`, `Map`, `Multiset`, … all fail this and stay unbounded.
    let head = peeled.split('<').next().unwrap_or(peeled).trim();
    let last_segment = head.rsplit("::").next().unwrap_or(head).trim();
    last_segment == "Vec"
}

/// Peels leading reference decorations (`&`, `&mut`, `&'a`, `&'a mut`, `&&`, …)
/// from an origin syn type string, mirroring how `parse_or_opaque` strips
/// references before classifying the referent.
fn strip_leading_references(input: &str) -> &str {
    let mut rest = input.trim_start();
    while let Some(after_amp) = rest.strip_prefix('&') {
        rest = after_amp.trim_start();
        // Optional lifetime token `'a`.
        if let Some(after_tick) = rest.strip_prefix('\'') {
            let end = after_tick
                .find(|c: char| !(c == '_' || c.is_ascii_alphanumeric()))
                .unwrap_or(after_tick.len());
            rest = after_tick[end..].trim_start();
        }
        // Optional `mut` KEYWORD (not a type whose name merely starts with `mut`).
        if let Some(after_mut) = rest.strip_prefix("mut") {
            if after_mut
                .chars()
                .next()
                .is_none_or(|c| !(c == '_' || c.is_ascii_alphanumeric()))
            {
                rest = after_mut.trim_start();
            }
        }
    }
    rest
}

/// Extracts a type name as a string.
///
/// Preserves exact Rust type names so the encoder can map them to the correct
/// bitvector widths. For example, `u8` stays `"u8"` (8-bit BV), not collapsed
/// to `"u32"` (32-bit BV), which would change overflow semantics.
pub(super) fn extract_type_name(ty: &Type) -> String {
    use quote::quote;
    let type_str = quote!(#ty).to_string();

    // Normalize whitespace from quote! output but preserve the exact type name.
    // TrustVcType::from_str plus the encoder's internal sort translation keeps
    // backend sorts aligned with the original Rust bit widths.
    type_str.replace(' ', "")
}

#[cfg(test)]
mod bounded_len_classifier_tests {
    use super::syn_type_string_is_bounded_len_collection as is_bounded;
    use super::{extract_type_name, extract_vars_from_input};

    /// The SOUNDNESS BOUNDARY, exhaustively pinned: exec `Vec`/slice/array origin
    /// syn spellings classify as length-bounded; a spec `Seq<T>` (and everything
    /// else) does NOT. Leaking `true` to a `Seq` is the reverted false-verify.
    #[test]
    fn vec_slice_array_are_bounded_seq_is_not() {
        // Bounded — genuine exec collections (usize-bounded length).
        for s in [
            "Vec<i32>",
            "Vec<i128>",
            "Vec<Vec<u8>>",
            "std::vec::Vec<i32>",
            "alloc::vec::Vec<u8>",
            "&Vec<i32>",
            "&mut Vec<i32>",
            "& Vec < i32 >",
            "&'a Vec<i32>",
            "&'a mut Vec<i32>",
            "[i32]",
            "[u8]",
            "&[u8]",
            "&mut [u8]",
            "[i32;4]",
            "[i32; 4]",
            "&[i32;4]",
        ] {
            assert!(is_bounded(s), "expected `{s}` to be length-bounded");
        }

        // UNBOUNDED — the crux. A spec `Seq<T>` must NEVER be bounded, nor may any
        // non-Vec/slice/array type be misclassified as bounded.
        for s in [
            "Seq<i32>",
            "Seq<Seq<i32>>",
            "&Seq<i32>",
            "&mut Seq<i32>",
            "&'a Seq<i32>",
            "i32",
            "u128",
            "usize",
            "bool",
            "Set<i32>",
            "Map<i32, i32>",
            "Multiset<i32>",
            "String",
            "(Vec<i32>, i32)", // a tuple as a whole is not a bounded collection
            "MyVecAlias",      // an alias named like Vec-ish but not `Vec`
            "Vector<i32>",     // last segment is `Vector`, not `Vec`
        ] {
            assert!(
                !is_bounded(s),
                "expected `{s}` to be UNBOUNDED, but it classified as bounded"
            );
        }
    }

    /// End-to-end at the string level: a real `Vec` param syn type renders to a
    /// string the classifier accepts; a real `Seq` param renders to one it
    /// rejects. This is the exact provenance the extraction seam reads.
    #[test]
    fn classifier_agrees_with_extracted_param_type_strings() {
        let vec_input: syn::FnArg = syn::parse_str("v: Vec<i32>").unwrap();
        let (name, ty_str) = extract_vars_from_input(&vec_input).unwrap().pop().unwrap();
        assert_eq!(name, "v");
        assert!(
            is_bounded(&ty_str),
            "extracted `{ty_str}` should be bounded"
        );

        let seq_input: syn::FnArg = syn::parse_str("s: Seq<i32>").unwrap();
        let (name, ty_str) = extract_vars_from_input(&seq_input).unwrap().pop().unwrap();
        assert_eq!(name, "s");
        assert!(
            !is_bounded(&ty_str),
            "extracted `{ty_str}` should be UNBOUNDED"
        );

        // A `&[i32]` slice reference param.
        let slice_input: syn::FnArg = syn::parse_str("sl: &[i32]").unwrap();
        let (_n, ty_str) = extract_vars_from_input(&slice_input)
            .unwrap()
            .pop()
            .unwrap();
        assert!(
            is_bounded(&ty_str),
            "extracted `{ty_str}` (slice) should be bounded"
        );

        // Tuple param: `Vec` element bounded, `Seq` element not — per-binding.
        let tuple_input: syn::FnArg = syn::parse_str("(v, s): (Vec<i32>, Seq<i32>)").unwrap();
        let pairs = extract_vars_from_input(&tuple_input).unwrap();
        let by_name: std::collections::HashMap<_, _> = pairs.into_iter().collect();
        assert!(
            is_bounded(&by_name["v"]),
            "tuple element `v: Vec` should be bounded, got `{}`",
            by_name["v"]
        );
        assert!(
            !is_bounded(&by_name["s"]),
            "tuple element `s: Seq` should be UNBOUNDED, got `{}`",
            by_name["s"]
        );

        // Sanity: extract_type_name of a bare Vec renders the `Vec` head.
        let vec_ty: syn::Type = syn::parse_str("Vec<i32>").unwrap();
        assert!(is_bounded(&extract_type_name(&vec_ty)));
    }
}
