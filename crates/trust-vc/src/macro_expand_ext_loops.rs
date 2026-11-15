// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Loop-related macro expansions: invariant, invariant_except_break,
//! loop_ensures, loop_decreases, arbitrary, and decreases_to.
//!
//! Split from `macro_expand_ext.rs` for the 500-line limit (#2621).

use quote::quote;

use crate::macro_expand::{
    canonical_expr_ast_string, normalize_expr_tokens, parse_expr_with_chains,
};
use trust_vc_core::expr_to_try_builder_tokens;

/// Expands `invariant!(condition)`.
pub(crate) fn expand_invariant(tokens: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let normalized_tokens = match normalize_expr_tokens(&tokens) {
        Ok(tokens) => tokens,
        Err(err) => return err.to_compile_error(),
    };
    let ast_string = canonical_expr_ast_string(&normalized_tokens);

    // Generate unique name per call site so multiple invariants are distinguishable
    // in counterexample diagnostics. Fixes #1560 finding #5.
    let parsed = parse_expr_with_chains(&normalized_tokens).ok();
    let try_builder = parsed.as_ref().and_then(expr_to_try_builder_tokens);

    let collection = if let Some(builder) = try_builder {
        // Runtime fallback: if variable type lookup fails, use string path. #2233.
        quote! {
            if let Some(__trust_vc_expr) = { #builder } {
                #support_root::verify_macro::collect_obligation_expr(
                    #support_root::vc::ObligationKind::LoopInvariant,
                    format!("loop_invariant_{}_{}", line!(), column!()),
                    #ast_string.to_string(),
                    __trust_vc_expr,
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            } else {
                #support_root::verify_macro::collect_typed_obligation(
                    #support_root::vc::ObligationKind::LoopInvariant,
                    format!("loop_invariant_{}_{}", line!(), column!()),
                    #ast_string.to_string(),
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            }
        }
    } else {
        quote! {
            #support_root::verify_macro::collect_typed_obligation(
                #support_root::vc::ObligationKind::LoopInvariant,
                format!("loop_invariant_{}_{}", line!(), column!()),
                #ast_string.to_string(),
                Some(format!("{}:{}:{}", file!(), line!(), column!())),
            );
        }
    };

    let runtime_check = trust_vc_core::runtime_check_or_typecheck(
        &normalized_tokens,
        trust_vc_core::ClauseArithmetic::FixedWidthChecked,
        quote! {
            assert!(#normalized_tokens, "trust_vc loop invariant failed");
        },
    );

    quote! {
        {
            #[cfg(test)]
            {
                #collection
            }
            #[cfg(trust_mc)]
            {
                let __trust_vc_loop_invariant = #ast_string;
                ::trust_mc::assert!(#normalized_tokens);
            }
            #[cfg(all(not(trust_mc), not(test)))]
            {
                #runtime_check
            }
            #[cfg(all(not(trust_mc), test))]
            {
            }
        }
    }
}

/// Expands `invariant_except_break!(condition)`.
///
/// Same inductive-step verification as `invariant!`, but the fact is NOT
/// available as a post-loop assumption. Part of #2417.
pub(crate) fn expand_invariant_except_break(
    tokens: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let normalized_tokens = match normalize_expr_tokens(&tokens) {
        Ok(tokens) => tokens,
        Err(err) => return err.to_compile_error(),
    };
    let ast_string = canonical_expr_ast_string(&normalized_tokens);

    let parsed = parse_expr_with_chains(&normalized_tokens).ok();
    let try_builder = parsed.as_ref().and_then(expr_to_try_builder_tokens);

    let collection = if let Some(builder) = try_builder {
        quote! {
            if let Some(__trust_vc_expr) = { #builder } {
                #support_root::verify_macro::collect_obligation_expr(
                    #support_root::vc::ObligationKind::InvariantExceptBreak,
                    format!("loop_invariant_except_break_{}_{}", line!(), column!()),
                    #ast_string.to_string(),
                    __trust_vc_expr,
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            } else {
                #support_root::verify_macro::collect_typed_obligation(
                    #support_root::vc::ObligationKind::InvariantExceptBreak,
                    format!("loop_invariant_except_break_{}_{}", line!(), column!()),
                    #ast_string.to_string(),
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            }
        }
    } else {
        quote! {
            #support_root::verify_macro::collect_typed_obligation(
                #support_root::vc::ObligationKind::InvariantExceptBreak,
                format!("loop_invariant_except_break_{}_{}", line!(), column!()),
                #ast_string.to_string(),
                Some(format!("{}:{}:{}", file!(), line!(), column!())),
            );
        }
    };

    let runtime_check = trust_vc_core::runtime_check_or_typecheck(
        &normalized_tokens,
        trust_vc_core::ClauseArithmetic::FixedWidthChecked,
        quote! {
            assert!(#normalized_tokens, "trust_vc invariant_except_break failed");
        },
    );

    quote! {
        {
            #[cfg(test)]
            {
                #collection
            }
            #[cfg(trust_mc)]
            {
                let __trust_vc_loop_invariant_except_break = #ast_string;
                ::trust_mc::assert!(#normalized_tokens);
            }
            #[cfg(all(not(trust_mc), not(test)))]
            {
                #runtime_check
            }
            #[cfg(all(not(trust_mc), test))]
            {
            }
        }
    }
}

/// Expands `loop_ensures!(condition)`.
///
/// Loop postcondition: must hold on loop exit. Verified by assuming all
/// verified invariants. Part of #2417.
pub(crate) fn expand_loop_ensures(tokens: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let normalized_tokens = match normalize_expr_tokens(&tokens) {
        Ok(tokens) => tokens,
        Err(err) => return err.to_compile_error(),
    };
    let ast_string = canonical_expr_ast_string(&normalized_tokens);

    let parsed = parse_expr_with_chains(&normalized_tokens).ok();
    let try_builder = parsed.as_ref().and_then(expr_to_try_builder_tokens);

    let collection = if let Some(builder) = try_builder {
        quote! {
            if let Some(__trust_vc_expr) = { #builder } {
                #support_root::verify_macro::collect_obligation_expr(
                    #support_root::vc::ObligationKind::LoopEnsures,
                    format!("loop_ensures_{}_{}", line!(), column!()),
                    #ast_string.to_string(),
                    __trust_vc_expr,
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            } else {
                #support_root::verify_macro::collect_typed_obligation(
                    #support_root::vc::ObligationKind::LoopEnsures,
                    format!("loop_ensures_{}_{}", line!(), column!()),
                    #ast_string.to_string(),
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            }
        }
    } else {
        quote! {
            #support_root::verify_macro::collect_typed_obligation(
                #support_root::vc::ObligationKind::LoopEnsures,
                format!("loop_ensures_{}_{}", line!(), column!()),
                #ast_string.to_string(),
                Some(format!("{}:{}:{}", file!(), line!(), column!())),
            );
        }
    };

    // loop_ensures is a postcondition — no runtime assertion since it
    // describes post-loop state, not iteration state.
    quote! {
        {
            #[cfg(test)]
            {
                #collection
            }
            #[cfg(trust_mc)]
            {
                let __trust_vc_loop_ensures = #ast_string;
            }
            #[cfg(all(not(trust_mc), not(test)))]
            {
                if false { let _ = || { #normalized_tokens }; }
            }
            #[cfg(all(not(trust_mc), test))]
            {
            }
        }
    }
}

/// Expands `loop_decreases!(measure)`.
///
/// Phase 5 Step 3b (#1866): TrustVcExpr dual-path is N/A for this site.
/// The macro passes the measure string to `collect_loop_decreases_measure`,
/// which creates obligations internally (MeasureNonNegative, MeasureDecreases)
/// from string manipulation. TrustVcExpr upgrade for these internal obligations
/// is deferred to Step 4 (encoder pipeline enhancement).
pub(crate) fn expand_loop_decreases(tokens: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let measure_string = tokens.to_string();
    let runtime_evaluation = trust_vc_core::runtime_check_or_typecheck(
        &tokens,
        trust_vc_core::ClauseArithmetic::Integer,
        quote! { let _ = { #tokens }; },
    );

    quote! {
        {
            #[cfg(test)]
            {
                #support_root::verify_macro::collect_loop_decreases_measure(
                    #measure_string.to_string(),
                    Some("loop_decreases".to_string()),
                );
            }
            #[cfg(trust_mc)]
            {
                let __trust_vc_loop_decreases = #measure_string;
                let __trust_vc_loop_measure = { #tokens };
            }
            #[cfg(not(trust_mc))]
            {
                #runtime_evaluation
            }
        }
    }
}

/// Expands `arbitrary!(T)`.
///
/// Returns a completely unconstrained symbolic value of type T. The value is
/// a fresh ay constant with no constraints — useful for abstract reasoning
/// about unknown inputs. Part of #2518.
///
/// At runtime (non-verification), returns `Default::default()`. In the
/// verification context, the `#[proof]` body extractor recognizes this macro
/// and suppresses the let-binding assumption, leaving the variable unconstrained.
pub(crate) fn expand_arbitrary(ty_tokens: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    quote! {
        {
            <#ty_tokens as ::core::default::Default>::default()
        }
    }
}

/// Expands `decreases_to!(lhs => rhs)`.
pub(crate) fn expand_decreases_to(
    tokens: proc_macro2::TokenStream,
    lhs_exprs: &[proc_macro2::TokenStream],
    rhs_exprs: &[proc_macro2::TokenStream],
) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let relation_string = tokens.to_string();

    quote! {
        {
            let _trust_vc_decreases_to_lhs_rhs = (#relation_string,);

            #[cfg(not(any(trust_mc, test)))]
            { true }

            #[cfg(any(trust_mc, test))]
            {
                #support_root::decreases_to_runtime::lexicographic_decreases(
                    &[#((#lhs_exprs) as i128),*],
                    &[#((#rhs_exprs) as i128),*],
                )
            }
        }
    }
}
