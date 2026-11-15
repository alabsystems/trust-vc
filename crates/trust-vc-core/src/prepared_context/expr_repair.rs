//! Cached-expression FnCall return-type repair for prepared contexts.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::ir::{TrustVcExpr, TrustVcType};
use crate::ir_expr_traversal::{fold_expr_children, fold_expr_vec, TrustVcExprFolder};
use crate::ir_lowering::TypeEnv;

/// Folder that corrects FnCall return types using the TypeEnv.
struct FnCallReturnTypeRepair<'a> {
    env: &'a TypeEnv,
}

impl TrustVcExprFolder for FnCallReturnTypeRepair<'_> {
    fn fold_expr(&mut self, expr: TrustVcExpr) -> TrustVcExpr {
        match expr {
            TrustVcExpr::FnCall {
                name,
                args,
                return_ty,
            } => {
                let mut fixed_args = fold_expr_vec(self, args);
                // Type an unsuffixed (default `Int{32}`) literal argument by the
                // function's declared parameter type. The codegen path assigns
                // Int{32} to unsuffixed literals at compile time without access
                // to the TypeEnv. Part of #2658 Category F. Only where that
                // never changes the literal's value
                // (`ir_lowering::untyped_literal_at_peer`): this used to retype
                // any `Int{32}` literal by shape, so `f(300)` with `f(a: u8)`
                // passed a `u8` literal of 300.
                if let Some(param_types) = self.env.lookup_fn_params(&name) {
                    for (arg, param_ty) in fixed_args.iter_mut().zip(param_types.iter()) {
                        if !is_default_int_type(param_ty)
                            && crate::ir_lowering::is_untyped_literal(arg)
                        {
                            if let Some(typed) =
                                crate::ir_lowering::untyped_literal_at_peer(arg, param_ty)
                            {
                                *arg = typed;
                            }
                        }
                    }
                }
                let fixed_ty = self.env.lookup_fn(&name).cloned().unwrap_or(return_ty);
                TrustVcExpr::FnCall {
                    name,
                    args: fixed_args,
                    return_ty: fixed_ty,
                }
            }
            other => fold_expr_children(self, other),
        }
    }
}

/// Returns `true` if `ty` is the default `Int { width: 32 }` assigned by
/// the codegen path to unsuffixed integer literals.
fn is_default_int_type(ty: &TrustVcType) -> bool {
    matches!(ty, TrustVcType::Int { width: 32 })
}

/// Corrects FnCall return types in a pre-built TrustVcExpr using the TypeEnv.
///
/// `expr_codegen.rs::lower_call` hardcodes a default return type for function
/// calls because proc macros run at compile time without type information.
/// This pass walks the TrustVcExpr tree and replaces FnCall `return_ty` with
/// the correct type from the TypeEnv (populated from `helper_functions` and
/// `function_context`). Fixes #2222.
pub(super) fn fix_fn_call_return_types(expr: TrustVcExpr, env: &TypeEnv) -> TrustVcExpr {
    FnCallReturnTypeRepair { env }.fold_expr(expr)
}
