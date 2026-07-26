//! Spec-closure lowering helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #2526.

use super::super::{infer_expr_type, lower_syn_expr_with_depth, LoweringError, TypeEnv};
use crate::ir::TrustVcType;
use crate::ir_expr::TrustVcExpr;

pub(super) fn lower_spec_fn_new(
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    if call.args.len() != 1 {
        return Err(LoweringError::UnsupportedExpr(format!(
            "SpecFn::new expects 1 closure arg, got {}",
            call.args.len()
        )));
    }

    let first = call.args.first().ok_or_else(|| {
        LoweringError::UnsupportedExpr(format!(
            "SpecFn::new expects 1 closure arg, got {}",
            call.args.len()
        ))
    })?;
    let syn::Expr::Closure(closure) = first else {
        return Err(LoweringError::UnsupportedExpr(
            "SpecFn::new arg must be closure".into(),
        ));
    };

    if closure.inputs.is_empty() {
        return Err(LoweringError::UnsupportedExpr(
            "SpecFn::new requires at least one typed closure parameter".into(),
        ));
    }

    // `SpecFn::new` carries no receiver/positional type information, so its
    // closure parameters must be explicitly annotated (no expected-type hints).
    lower_closure_as_spec_fn(closure, env, depth, None)
}

/// Normalize a spec-closure-position argument into a `SpecClosure`.
///
/// This is the implicit `SpecFn::new(...)` wrap used in spec positions where a
/// closure is unambiguously a `SpecFn` (ghost-collection combinator closure
/// slots: `Set::new`, `Seq::new`/`from_fn`, and the `filter`/`map`/`fold`/...
/// method combinators). Behavior by argument shape (after peeling
/// parens/groups):
///
/// * a bare `syn::Expr::Closure` is lowered directly as a spec closure — this is
///   the normalization (== an implicit `SpecFn::new` wrap);
/// * anything else (an explicit `SpecFn::new(...)` call, a named `SpecFn`
///   variable, or a non-`SpecFn` expression) is lowered with the generic
///   lowerer, so already-wrapped arguments are never double-wrapped and
///   non-closure arguments are never spuriously turned into a `SpecFn`.
///
/// `expected_params`, when supplied, provides the spec-fn parameter types for
/// closure binders that lack explicit annotations (the receiver-element types
/// for method combinators). It is only a *hint* for untyped binders: the
/// downstream combinator typing (`extract_spec_fn_signature` / the `Set::new`
/// and `Seq::*` checks) independently re-validates the resulting `SpecFn`
/// signature, so a wrong or missing hint can only cause a fail-closed type
/// error, never an unsound acceptance.
pub(super) fn lower_spec_fn_arg(
    arg: &syn::Expr,
    env: &TypeEnv,
    depth: usize,
    expected_params: Option<&[TrustVcType]>,
) -> Result<TrustVcExpr, LoweringError> {
    let mut peeled = arg;
    loop {
        match peeled {
            syn::Expr::Paren(p) => peeled = &p.expr,
            syn::Expr::Group(g) => peeled = &g.expr,
            _ => break,
        }
    }

    if let syn::Expr::Closure(closure) = peeled {
        return lower_closure_as_spec_fn(closure, env, depth, expected_params);
    }

    // Not a bare closure: keep generic lowering. `SpecFn::new(...)` calls route
    // back through `lower_spec_fn_new` (already a `SpecClosure`), and named
    // `SpecFn` values resolve via `lower_path`; neither is re-wrapped.
    lower_syn_expr_with_depth(arg, env, depth)
}

/// Lower a closure as a `SpecClosure` — the shared core of `SpecFn::new(...)`
/// and the implicit normalization in [`lower_spec_fn_arg`].
fn lower_closure_as_spec_fn(
    closure: &syn::ExprClosure,
    env: &TypeEnv,
    depth: usize,
    expected_params: Option<&[TrustVcType]>,
) -> Result<TrustVcExpr, LoweringError> {
    let params = extract_spec_fn_params(closure, env, expected_params)?;
    let child_env = env.extend(&params);
    let body = Box::new(lower_syn_expr_with_depth(&closure.body, &child_env, depth)?);
    let ty = TrustVcType::SpecFn(
        params.iter().map(|(_, ty)| ty.clone()).collect(),
        Box::new(infer_expr_type(&body)),
    );

    Ok(TrustVcExpr::SpecClosure { params, body, ty })
}

fn extract_spec_fn_params(
    closure: &syn::ExprClosure,
    env: &TypeEnv,
    expected_params: Option<&[TrustVcType]>,
) -> Result<Vec<(String, TrustVcType)>, LoweringError> {
    let mut params = Vec::new();
    for input in &closure.inputs {
        match input {
            syn::Pat::Type(typed) => match (&*typed.pat, &*typed.ty) {
                (syn::Pat::Ident(ident), ty) => {
                    params.push((
                        ident.ident.to_string(),
                        env.resolve_syn_type(ty).map_err(|err| {
                            LoweringError::InvalidType(format!(
                                "SpecFn parameter '{}': {}",
                                ident.ident, err
                            ))
                        })?,
                    ));
                }
                (syn::Pat::Tuple(tuple_pat), syn::Type::Tuple(tuple_ty)) => {
                    if tuple_pat.elems.len() != tuple_ty.elems.len() {
                        return Err(LoweringError::UnsupportedPattern(
                            "SpecFn tuple binder arity/type mismatch".into(),
                        ));
                    }
                    for (pat, ty) in tuple_pat.elems.iter().zip(tuple_ty.elems.iter()) {
                        let syn::Pat::Ident(ident) = pat else {
                            return Err(LoweringError::UnsupportedPattern(
                                "SpecFn tuple binders require simple identifier elements".into(),
                            ));
                        };
                        params.push((
                            ident.ident.to_string(),
                            env.resolve_syn_type(ty).map_err(|err| {
                                LoweringError::InvalidType(format!(
                                    "SpecFn parameter '{}': {}",
                                    ident.ident, err
                                ))
                            })?,
                        ));
                    }
                }
                (syn::Pat::Tuple(_), _) => {
                    return Err(LoweringError::UnsupportedPattern(
                        "SpecFn tuple binder requires tuple type annotation".into(),
                    ));
                }
                _ => {
                    return Err(LoweringError::UnsupportedPattern(
                        "unsupported SpecFn closure parameter pattern".into(),
                    ))
                }
            },
            // Untyped binder (`|i| ...`): permitted only when the combinator
            // position supplies an expected parameter type (the receiver element
            // type). This keeps the Verus-faithful bare form working while
            // failing closed when no type is determinable (e.g. `Set::new`).
            syn::Pat::Ident(ident) => {
                let index = params.len();
                let Some(ty) = expected_params.and_then(|tys| tys.get(index)).cloned() else {
                    return Err(LoweringError::InvalidType(format!(
                        "spec closure parameter '{}' requires an explicit type annotation",
                        ident.ident
                    )));
                };
                params.push((ident.ident.to_string(), ty));
            }
            _ => {
                return Err(LoweringError::UnsupportedPattern(
                    "unsupported SpecFn closure parameter pattern".into(),
                ))
            }
        }
    }
    Ok(params)
}
