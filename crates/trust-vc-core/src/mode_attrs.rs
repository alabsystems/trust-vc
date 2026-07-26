//! Shared function/method mode classification from attributes.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Classifies `syn::ItemFn` and `syn::ImplItemFn` as Exec, Proof, or Spec
//! based on their `#[trust_vc::*]` attributes. Previously duplicated across
//! `mode_index`, `mode_scan`, and `recursion_graph`.
//!
//! Part of #2561.

use crate::error::{TrustVcError, TrustVcResult};
use crate::mode::FunctionMode;
use crate::vc::SolverMode;
use syn::punctuated::Punctuated;
use syn::Token;

/// Classifies a free function's mode from its attributes.
///
/// Recognizes both fully-qualified (`#[trust_vc::proof]`) and imported
/// short-form (`#[proof]`) attributes.
pub(crate) fn classify_item_fn(item: &syn::ItemFn) -> FunctionMode {
    classify_attrs(&item.attrs)
}

/// Classifies an impl method's mode from its attributes.
pub(crate) fn classify_impl_method(method: &syn::ImplItemFn) -> FunctionMode {
    classify_attrs(&method.attrs)
}

/// Extracts the type name from an impl block's self type.
/// Returns `None` for complex types (e.g., `<T as Trait>::Assoc`).
pub(crate) fn extract_impl_type_name(ty: &syn::Type) -> Option<String> {
    match ty {
        syn::Type::Path(tp) if tp.qself.is_none() => {
            tp.path.segments.last().map(|s| s.ident.to_string())
        }
        _ => None,
    }
}

/// Shared attribute classification logic.
fn classify_attrs(attrs: &[syn::Attribute]) -> FunctionMode {
    for attr in attrs {
        let path = attr.path();
        let segments: Vec<_> = path.segments.iter().map(|s| s.ident.to_string()).collect();
        match segments.as_slice() {
            [prefix, name] if prefix == "trust_vc" => match name.as_str() {
                "proof" | "broadcast" | "broadcast_group" => return FunctionMode::Proof,
                "spec" | "spec_mode" => return FunctionMode::Spec,
                _ => {}
            },
            [name] => match name.as_str() {
                "proof" | "broadcast" | "broadcast_group" => return FunctionMode::Proof,
                "spec" | "spec_mode" => return FunctionMode::Spec,
                _ => {}
            },
            _ => {}
        }
    }
    FunctionMode::Exec
}

/// Extracts an ambient solver mode from Verus-style function attributes.
///
/// Recognizes `#[verifier(nonlinear)]`, `#[verifier(nonlinear_arith)]`,
/// `#[verifier(bit_vector)]`, and the same spellings under `trust_vc::`.
/// Non-solver verifier options such as `spinoff_prover` are ignored here.
pub(crate) fn extract_function_solver_mode(
    attrs: &[syn::Attribute],
) -> TrustVcResult<Option<SolverMode>> {
    let mut mode = None;

    for attr in attrs {
        let segments: Vec<_> = attr
            .path()
            .segments
            .iter()
            .map(|s| s.ident.to_string())
            .collect();

        if is_verifier_list_attr(&segments) {
            let args = attr
                .parse_args_with(Punctuated::<syn::Meta, Token![,]>::parse_terminated)
                .map_err(|source| TrustVcError::Encoding {
                    context: "extract function solver mode",
                    detail: format!("failed to parse verifier attribute: {source}"),
                })?;

            for meta in args {
                match &meta {
                    syn::Meta::Path(path) => {
                        if let Some(candidate) = solver_mode_from_path(path) {
                            merge_solver_mode(&mut mode, candidate)?;
                        }
                    }
                    // `#[verifier(rlimit(N))]` — a per-function solver budget,
                    // not a solver mode. Validate the argument here (fail
                    // closed on malformed input, matching the upstream
                    // attribute error) so EVERY caller of this extractor
                    // rejects a bad rlimit; the value itself is consumed by
                    // `extract_function_rlimit_ms` on the verified function.
                    syn::Meta::List(list) if is_rlimit_path(&list.path) => {
                        parse_rlimit_ms(list.tokens.clone())?;
                    }
                    // Prover-shape directives that trust-vc already honors by
                    // default — accepted as NO-OPS so they stop over-rejecting.
                    // `loop_isolation(false)` asks Verus to leak outer context
                    // into loop bodies; trust-vc keeps its DEFAULT isolated loop
                    // encoding, which is strictly stronger (a proof relying on
                    // the leaked context fails closed rather than false-verifying).
                    // `spinoff_prover` (per-obligation isolation) is already the
                    // default, and `allow_complex_invariants` lifts a Verus-only
                    // restriction trust-vc never imposed. This arm changes ONLY
                    // attribute parsing — the verification encoding is untouched.
                    syn::Meta::List(list) if is_ignored_verifier_option(&list.path) => {}
                    other => {
                        return Err(TrustVcError::Encoding {
                            context: "extract function solver mode",
                            detail: format!(
                                "failed to parse verifier attribute: unsupported verifier option `{}`",
                                quote::quote!(#other)
                            ),
                        });
                    }
                }
            }
        } else if let Some(option) = verifier_path_option(&segments) {
            if let Some(candidate) = solver_mode_from_name(option) {
                merge_solver_mode(&mut mode, candidate)?;
            }
        }
    }

    Ok(mode)
}

fn is_verifier_list_attr(segments: &[String]) -> bool {
    matches!(segments, [name] if name == "verifier")
        || matches!(segments, [prefix, name] if prefix == "trust_vc" && name == "verifier")
}

fn is_rlimit_path(path: &syn::Path) -> bool {
    path.segments.len() == 1
        && path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "rlimit")
}

/// Prover-shape verifier options that trust-vc accepts and ignores (no-op),
/// because its default encoding already subsumes them. Recognized in the
/// argument-carrying (`loop_isolation(false)`) list form so they no longer fail
/// the closed `other =>` arm. Crucially, ignoring these NEVER weakens an
/// obligation: `loop_isolation(false)` is dropped in favor of the stronger
/// isolated encoding, `spinoff_prover` isolation is already the default, and
/// `allow_complex_invariants` only lifts a restriction trust-vc never imposed.
fn is_ignored_verifier_option(path: &syn::Path) -> bool {
    path.segments.last().is_some_and(|segment| {
        matches!(
            segment.ident.to_string().as_str(),
            "loop_isolation" | "spinoff_prover" | "allow_complex_invariants"
        )
    })
}

/// Sentinel for `#[verifier::rlimit(infinity)]`: effectively unlimited (one
/// year of nominal solver budget) while staying safe for `Instant + Duration`
/// arithmetic in the watchdog derivations (`u64::MAX` milliseconds would
/// overflow the monotonic clock's nanosecond representation).
pub(crate) const RLIMIT_INFINITY_MS: u64 = 31_536_000_000;

/// Extracts the per-function solver budget from Verus-style
/// `#[verifier::rlimit(N)]` / `#[verifier::rlimit(infinity)]` attributes
/// (path form) and `#[verifier(rlimit(N))]` (list form), plus the same
/// spellings under `trust_vc::`.
///
/// Upstream semantics (rust_verify `verifier.rs::set_rlimit`, `attributes.rs::
/// get_rlimit_arg`): `rlimit(N)` grants `N × RLIMIT_PER_SECOND` Z3 resource
/// units — i.e. roughly N SECONDS of reference solver work — and `infinity`
/// (or `0`, which Z3 reads as unlimited) disables the budget. Faithful
/// mapping onto trust-vc's per-obligation `rlimit_ms` nominal solver budget:
///
/// * `rlimit(N)` (integer or float, matching upstream `f32` parsing) →
///   `N × 1000` ms.
/// * `rlimit(infinity)` and `rlimit(0)` → [`RLIMIT_INFINITY_MS`].
/// * malformed arguments fail closed with the verbatim upstream message
///   "expected number, or `infinity` for rlimit".
/// * duplicate rlimit attributes: the last one wins (upstream `parse_attrs`
///   overwrites `vs.rlimit`).
///
/// This is deliberately distinct from the legacy proc-macro-path
/// `#[trust_vc::rlimit(N)]` attribute, whose N is already in milliseconds
/// (`spec_expand.rs`, #2489) and which is left untouched.
pub(crate) fn extract_function_rlimit_ms(attrs: &[syn::Attribute]) -> TrustVcResult<Option<u64>> {
    let mut rlimit = None;

    for attr in attrs {
        let segments: Vec<_> = attr
            .path()
            .segments
            .iter()
            .map(|s| s.ident.to_string())
            .collect();

        if is_verifier_list_attr(&segments) {
            // Malformed argument LISTS are reported by
            // `extract_function_solver_mode`; only harvest rlimit values here.
            let Ok(args) =
                attr.parse_args_with(Punctuated::<syn::Meta, Token![,]>::parse_terminated)
            else {
                continue;
            };
            for meta in args {
                if let syn::Meta::List(list) = &meta {
                    if is_rlimit_path(&list.path) {
                        rlimit = Some(parse_rlimit_ms(list.tokens.clone())?);
                    }
                }
            }
        } else if verifier_path_option(&segments) == Some("rlimit") {
            let syn::Meta::List(list) = &attr.meta else {
                // Bare `#[verifier::rlimit]` with no argument.
                return Err(rlimit_arg_error());
            };
            rlimit = Some(parse_rlimit_ms(list.tokens.clone())?);
        }
    }

    Ok(rlimit)
}

fn rlimit_arg_error() -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract verifier rlimit",
        // Verbatim upstream message: rust_verify/src/attributes.rs
        // get_rlimit_arg.
        detail: "expected number, or `infinity` for rlimit".to_string(),
    }
}

/// Parse the argument tokens of an `rlimit(...)` attribute to a millisecond
/// budget. Accepts exactly one token: an unsuffixed integer or float literal
/// (upstream parses the text as `f32`), or the ident `infinity`.
fn parse_rlimit_ms(tokens: proc_macro2::TokenStream) -> TrustVcResult<u64> {
    let trees: Vec<proc_macro2::TokenTree> = tokens.into_iter().collect();
    match trees.as_slice() {
        [proc_macro2::TokenTree::Ident(ident)] if ident == "infinity" => Ok(RLIMIT_INFINITY_MS),
        [proc_macro2::TokenTree::Literal(literal)] => {
            let value: f64 = literal
                .to_string()
                .parse()
                .map_err(|_| rlimit_arg_error())?;
            if !value.is_finite() || value < 0.0 {
                return Err(rlimit_arg_error());
            }
            if value == 0.0 {
                // Upstream forwards 0 to Z3, which reads a zero rlimit as
                // unlimited (verifier.rs::set_rlimit).
                return Ok(RLIMIT_INFINITY_MS);
            }
            let ms = (value * 1000.0).round();
            if ms >= RLIMIT_INFINITY_MS as f64 {
                return Ok(RLIMIT_INFINITY_MS);
            }
            Ok((ms as u64).max(1))
        }
        _ => Err(rlimit_arg_error()),
    }
}

fn verifier_path_option(segments: &[String]) -> Option<&str> {
    match segments {
        [prefix, option] if prefix == "verifier" => Some(option.as_str()),
        [prefix, name, option] if prefix == "trust_vc" && name == "verifier" => {
            Some(option.as_str())
        }
        _ => None,
    }
}

fn solver_mode_from_path(path: &syn::Path) -> Option<SolverMode> {
    path.segments
        .last()
        .and_then(|segment| solver_mode_from_name(&segment.ident.to_string()))
}

fn solver_mode_from_name(name: &str) -> Option<SolverMode> {
    match name {
        "nonlinear" | "nonlinear_arith" => Some(SolverMode::NonlinearArith),
        "bit_vector" => Some(SolverMode::BitVector),
        "compute" => Some(SolverMode::Compute),
        _ => None,
    }
}

fn merge_solver_mode(mode: &mut Option<SolverMode>, candidate: SolverMode) -> TrustVcResult<()> {
    match *mode {
        Some(existing) if existing != candidate => Err(TrustVcError::Encoding {
            context: "extract function solver mode",
            detail: format!(
                "conflicting verifier solver modes: {} and {}",
                solver_mode_name(existing),
                solver_mode_name(candidate)
            ),
        }),
        Some(_) => Ok(()),
        None => {
            *mode = Some(candidate);
            Ok(())
        }
    }
}

fn solver_mode_name(mode: SolverMode) -> &'static str {
    match mode {
        SolverMode::Default => "default",
        SolverMode::NonlinearArith => "nonlinear_arith",
        SolverMode::BitVector => "bit_vector",
        SolverMode::Compute => "compute",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_classify_proof_fn() {
        let item: syn::ItemFn = syn::parse_quote! {
            #[trust_vc::proof]
            fn my_proof(x: i32) {}
        };
        assert_eq!(classify_item_fn(&item), FunctionMode::Proof);
    }

    #[test]
    fn test_classify_broadcast_fn() {
        let item: syn::ItemFn = syn::parse_quote! {
            #[trust_vc::broadcast]
            fn lemma(x: i32) {}
        };
        assert_eq!(classify_item_fn(&item), FunctionMode::Proof);
    }

    #[test]
    fn test_classify_spec_fn() {
        let item: syn::ItemFn = syn::parse_quote! {
            #[trust_vc::spec]
            fn my_spec(x: i32) -> i32 { x }
        };
        assert_eq!(classify_item_fn(&item), FunctionMode::Spec);
    }

    #[test]
    fn test_classify_spec_mode_fn() {
        let item: syn::ItemFn = syn::parse_quote! {
            #[trust_vc::spec_mode]
            fn pure_helper(x: i32) -> i32 { x }
        };
        assert_eq!(classify_item_fn(&item), FunctionMode::Spec);
    }

    #[test]
    fn test_classify_exec_fn() {
        let item: syn::ItemFn = syn::parse_quote! {
            fn my_exec(x: i32) -> i32 { x + 1 }
        };
        assert_eq!(classify_item_fn(&item), FunctionMode::Exec);
    }

    #[test]
    fn test_classify_short_form_proof() {
        let item: syn::ItemFn = syn::parse_quote! {
            #[proof]
            fn short_proof() {}
        };
        assert_eq!(classify_item_fn(&item), FunctionMode::Proof);
    }

    #[test]
    fn test_classify_short_form_broadcast() {
        let item: syn::ItemFn = syn::parse_quote! {
            #[broadcast]
            fn short_broadcast() {}
        };
        assert_eq!(classify_item_fn(&item), FunctionMode::Proof);
    }

    #[test]
    fn test_classify_short_form_spec() {
        let item: syn::ItemFn = syn::parse_quote! {
            #[spec]
            fn short_spec() -> bool { true }
        };
        assert_eq!(classify_item_fn(&item), FunctionMode::Spec);
    }

    #[test]
    fn test_classify_short_form_spec_mode() {
        let item: syn::ItemFn = syn::parse_quote! {
            #[spec_mode]
            fn short_spec_mode() -> bool { true }
        };
        assert_eq!(classify_item_fn(&item), FunctionMode::Spec);
    }

    #[test]
    fn test_classify_impl_method_proof() {
        let method: syn::ImplItemFn = syn::parse_quote! {
            #[trust_vc::proof]
            fn my_lemma(&self) {}
        };
        assert_eq!(classify_impl_method(&method), FunctionMode::Proof);
    }

    #[test]
    fn test_classify_impl_method_exec() {
        let method: syn::ImplItemFn = syn::parse_quote! {
            fn regular(&self) -> u64 { 0 }
        };
        assert_eq!(classify_impl_method(&method), FunctionMode::Exec);
    }

    #[test]
    fn test_classify_broadcast_group() {
        let item: syn::ItemFn = syn::parse_quote! {
            #[trust_vc::broadcast_group]
            fn group_lemma() {}
        };
        assert_eq!(classify_item_fn(&item), FunctionMode::Proof);
    }

    #[test]
    fn test_classify_unrelated_attr_returns_exec() {
        let item: syn::ItemFn = syn::parse_quote! {
            #[inline]
            fn fast() {}
        };
        assert_eq!(classify_item_fn(&item), FunctionMode::Exec);
    }

    #[test]
    fn test_classify_unknown_trust_vc_attr_returns_exec() {
        let item: syn::ItemFn = syn::parse_quote! {
            #[trust_vc::decreases]
            fn recursive() {}
        };
        assert_eq!(
            classify_item_fn(&item),
            FunctionMode::Exec,
            "non-mode trust_vc attributes should not change function mode"
        );
    }

    #[test]
    fn test_extract_impl_type_name_simple() {
        let ty: syn::Type = syn::parse_quote! { Tree };
        assert_eq!(extract_impl_type_name(&ty), Some("Tree".to_string()));
    }

    #[test]
    fn test_extract_impl_type_name_path() {
        let ty: syn::Type = syn::parse_quote! { crate::Tree };
        assert_eq!(extract_impl_type_name(&ty), Some("Tree".to_string()));
    }

    #[test]
    fn test_extract_impl_type_name_complex() {
        let ty: syn::Type = syn::parse_quote! { <T as Trait>::Assoc };
        assert_eq!(extract_impl_type_name(&ty), None);
    }

    #[test]
    fn test_extract_function_solver_mode_nonlinear() {
        let item: syn::ItemFn = syn::parse_quote! {
            #[verifier(nonlinear)]
            fn lemma() {}
        };
        assert_eq!(
            extract_function_solver_mode(&item.attrs).unwrap(),
            Some(SolverMode::NonlinearArith)
        );
    }

    #[test]
    fn test_extract_function_solver_mode_nonlinear_arith_alias() {
        let item: syn::ItemFn = syn::parse_quote! {
            #[trust_vc::verifier(nonlinear_arith)]
            fn lemma() {}
        };
        assert_eq!(
            extract_function_solver_mode(&item.attrs).unwrap(),
            Some(SolverMode::NonlinearArith)
        );
    }

    #[test]
    fn test_extract_function_solver_mode_bit_vector_path_form() {
        let item: syn::ItemFn = syn::parse_quote! {
            #[trust_vc::verifier::bit_vector]
            fn lemma() {}
        };
        assert_eq!(
            extract_function_solver_mode(&item.attrs).unwrap(),
            Some(SolverMode::BitVector)
        );
    }

    #[test]
    fn test_extract_function_solver_mode_ignores_spinoff() {
        let item: syn::ItemFn = syn::parse_quote! {
            #[verifier(spinoff_prover)]
            fn lemma() {}
        };
        assert_eq!(extract_function_solver_mode(&item.attrs).unwrap(), None);
    }

    #[test]
    fn test_extract_function_solver_mode_rejects_conflicts() {
        let item: syn::ItemFn = syn::parse_quote! {
            #[verifier(nonlinear)]
            #[verifier(bit_vector)]
            fn lemma() {}
        };
        assert!(extract_function_solver_mode(&item.attrs).is_err());
    }

    #[test]
    fn test_extract_function_solver_mode_accepts_loop_isolation_false_as_noop() {
        // `#[verifier(loop_isolation(false))]` previously failed closed in the
        // argument-carrying `other =>` arm. It is now accepted as a no-op: no
        // solver mode is set (the default isolated loop encoding is retained,
        // which is strictly stronger than the requested context-leak).
        let item: syn::ItemFn = syn::parse_quote! {
            #[verifier(loop_isolation(false))]
            fn lemma() {}
        };
        assert_eq!(extract_function_solver_mode(&item.attrs).unwrap(), None);
    }

    #[test]
    fn test_extract_function_solver_mode_ignored_noops_do_not_mask_conflicts() {
        // The no-op options must not suppress a genuine solver-mode conflict.
        let item: syn::ItemFn = syn::parse_quote! {
            #[verifier(loop_isolation(false))]
            #[verifier(nonlinear)]
            #[verifier(bit_vector)]
            fn lemma() {}
        };
        assert!(extract_function_solver_mode(&item.attrs).is_err());
    }

    #[test]
    fn test_extract_function_solver_mode_still_rejects_unknown_list_option() {
        // A genuinely unrecognized argument-carrying option must STILL fail
        // closed — the no-op set is a closed allow-list, not a blanket accept.
        let item: syn::ItemFn = syn::parse_quote! {
            #[verifier(totally_made_up_option(false))]
            fn lemma() {}
        };
        assert!(extract_function_solver_mode(&item.attrs).is_err());
    }
}
