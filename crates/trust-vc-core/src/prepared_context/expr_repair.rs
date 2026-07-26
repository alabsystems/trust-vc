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
                // Coerce IntLit arguments whose type is the default Int{32} to
                // match the function's declared parameter types. The codegen path
                // assigns Int{32} to unsuffixed literals at compile time without
                // access to the TypeEnv. Part of #2658 Category F.
                if let Some(param_types) = self.env.lookup_fn_params(&name) {
                    for (arg, param_ty) in fixed_args.iter_mut().zip(param_types.iter()) {
                        if let TrustVcExpr::IntLit { ty, .. } = arg {
                            if *ty != *param_ty && is_default_int_type(ty) {
                                *ty = param_ty.clone();
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
