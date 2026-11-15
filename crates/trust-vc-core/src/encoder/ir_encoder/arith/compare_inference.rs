//! Type-inference helpers for comparison encoding.
//!
//! Determines effective operand types and detects promoted-int variables
//! so the comparison encoder can choose between BV, Int, and Float paths.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from `compare.rs` for the 500-line limit (#2692).

use crate::{
    error::{TrustVcError, TrustVcResult},
    ir::{TrustVcExpr, TrustVcType},
};

use crate::encoder::AstExpressionParser;

impl<'a> AstExpressionParser<'a> {
    pub(in crate::encoder::ir_encoder) fn classify_float_compare_operands(
        &self,
        left_ty: &TrustVcType,
        right_ty: &TrustVcType,
    ) -> TrustVcResult<Option<u32>> {
        match (left_ty, right_ty) {
            (
                TrustVcType::Float { width: left_width },
                TrustVcType::Float {
                    width: right_width,
                },
            ) if left_width == right_width => Ok(Some(*left_width)),
            (TrustVcType::Float { .. }, TrustVcType::Float { .. })
            | (TrustVcType::Float { .. }, _)
            | (_, TrustVcType::Float { .. }) => Err(TrustVcError::Encoding {
                context: "encode expression",
                detail: format!(
                    "floating-point comparison requires both operands to be float of the same width, got {} and {}",
                    left_ty.to_type_string(),
                    right_ty.to_type_string()
                ),
            }),
            _ => Ok(None),
        }
    }

    pub(in crate::encoder::ir_encoder) fn infer_specialized_fn_call_return_type(
        &self,
        name: &str,
        args: &[TrustVcExpr],
        return_ty: &TrustVcType,
    ) -> Option<TrustVcType> {
        let TrustVcType::TypeParam(return_tp) = return_ty else {
            return None;
        };

        let type_params = match self.function_type_params.and_then(|m| m.get(name)) {
            Some(type_params) if !type_params.is_empty() => type_params,
            _ => return None,
        };
        let param_types = self.function_param_types.and_then(|m| m.get(name))?;

        let mut bindings = std::collections::HashMap::new();
        for (i, param_ty) in param_types.iter().enumerate() {
            let TrustVcType::TypeParam(param_tp) = param_ty else {
                continue;
            };
            if !type_params.contains(param_tp) {
                continue;
            }
            let Some(arg) = args.get(i) else {
                continue;
            };
            let concrete_ty = self.infer_effective_expr_type(arg, None);
            if matches!(concrete_ty, TrustVcType::TypeParam(_) | TrustVcType::Poly) {
                continue;
            }
            bindings.entry(param_tp.clone()).or_insert(concrete_ty);
        }

        bindings.get(return_tp).cloned()
    }

    pub(in crate::encoder::ir_encoder) fn infer_effective_expr_type(
        &self,
        expr: &TrustVcExpr,
        hint_ty: Option<&TrustVcType>,
    ) -> TrustVcType {
        self.infer_expr_type_with_hint(expr, hint_ty, true)
    }

    /// Whether `encode_compare` reads `left OP right` as a float comparison:
    /// either operand's effective type, inferred with the same peer hints
    /// `encode_compare` uses, is a float.
    ///
    /// IEEE 754 order is partial: every comparison with a NaN is false, so
    /// `!(a <= b)` is not `a > b` for floats.
    pub(in crate::encoder::ir_encoder) fn compare_operands_are_float(
        &self,
        left: &TrustVcExpr,
        right: &TrustVcExpr,
    ) -> bool {
        let left_hint_ty = self.infer_effective_expr_type(right, None);
        let right_hint_ty = self.infer_effective_expr_type(left, None);
        let left_ty = self.infer_effective_expr_type(left, Some(&left_hint_ty));
        let right_ty = self.infer_effective_expr_type(right, Some(&right_hint_ty));
        matches!(left_ty, TrustVcType::Float { .. })
            || matches!(right_ty, TrustVcType::Float { .. })
    }

    /// The type of the VALUE `expr` denotes at this use site: the literal
    /// hint coercion applies, but not Route A's `.len()` → `MathInt` routing
    /// label, so a length reports its own IR type.
    ///
    /// This is what an operand's signedness is read from
    /// ([`crate::encoder::width_coercion::ir_type_signedness`]); it is never
    /// read from the operand's hash-consed term.
    pub(in crate::encoder) fn infer_operand_value_type(
        &self,
        expr: &TrustVcExpr,
        hint_ty: Option<&TrustVcType>,
    ) -> TrustVcType {
        self.infer_expr_type_with_hint(expr, hint_ty, false)
    }

    fn infer_expr_type_with_hint(
        &self,
        expr: &TrustVcExpr,
        hint_ty: Option<&TrustVcType>,
        len_as_math_int: bool,
    ) -> TrustVcType {
        if let Some(hint_ty) = hint_ty {
            if let Some(coerced) = Self::coerce_default_int_literal(expr, hint_ty) {
                return self.infer_expr_type_with_hint(&coerced, None, len_as_math_int);
            }
        }

        // Route A (#2779): spec-collection `.len()` is an unbounded Int, so
        // report MathInt and let the comparison encoder use Int semantics
        // instead of attempting BV comparison on an Int-sorted length term.
        // Mirrors native-seq/native-strings; see `len_op_yields_int`.
        if len_as_math_int && Self::len_op_yields_int(expr) {
            return TrustVcType::MathInt;
        }

        match expr {
            TrustVcExpr::FnCall {
                name,
                args,
                return_ty,
            } => self
                .infer_specialized_fn_call_return_type(name, args, return_ty)
                .unwrap_or_else(|| crate::ir_lowering::infer_expr_type(expr)),
            _ => crate::ir_lowering::infer_expr_type(expr),
        }
    }

    pub(in crate::encoder::ir_encoder) fn expr_references_promoted_int_var(
        &self,
        expr: &TrustVcExpr,
    ) -> bool {
        fn update_promoted_scope(
            scope: &std::collections::HashSet<String>,
            name: &str,
            ty: &TrustVcType,
        ) -> std::collections::HashSet<String> {
            let mut next = scope.clone();
            next.remove(name);
            if matches!(ty, TrustVcType::MathInt | TrustVcType::Nat) {
                next.insert(name.to_string());
            }
            next
        }

        fn update_promoted_scope_many(
            scope: &std::collections::HashSet<String>,
            names: impl Iterator<Item = (String, TrustVcType)>,
        ) -> std::collections::HashSet<String> {
            let mut next = scope.clone();
            for (name, ty) in names {
                next.remove(name.as_str());
                if matches!(ty, TrustVcType::MathInt | TrustVcType::Nat) {
                    next.insert(name);
                }
            }
            next
        }

        fn visit(expr: &TrustVcExpr, promoted_names: &std::collections::HashSet<String>) -> bool {
            match expr {
                TrustVcExpr::Var { name, .. } => promoted_names.contains(name),
                TrustVcExpr::BoolLit(_)
                | TrustVcExpr::UnitLit
                | TrustVcExpr::StringLit(_)
                | TrustVcExpr::IntLit { .. }
                | TrustVcExpr::IntConst { .. }
                | TrustVcExpr::ProphecyNew { .. } => false,
                TrustVcExpr::Arith { left, right, .. }
                | TrustVcExpr::Compare { left, right, .. }
                | TrustVcExpr::Logic { left, right, .. }
                | TrustVcExpr::SpecialArith { left, right, .. }
                | TrustVcExpr::WrappingArith { left, right, .. } => {
                    visit(left, promoted_names) || visit(right, promoted_names)
                }
                TrustVcExpr::Neg(inner)
                | TrustVcExpr::Not(inner)
                | TrustVcExpr::Cast { expr: inner, .. } => visit(inner, promoted_names),
                TrustVcExpr::Implies {
                    premise,
                    conclusion,
                } => visit(premise, promoted_names) || visit(conclusion, promoted_names),
                TrustVcExpr::Ite {
                    cond,
                    then_branch,
                    else_branch,
                    ..
                } => {
                    visit(cond, promoted_names)
                        || visit(then_branch, promoted_names)
                        || visit(else_branch, promoted_names)
                }
                TrustVcExpr::Let {
                    name,
                    ty,
                    value,
                    body,
                } => {
                    visit(value, promoted_names)
                        || visit(
                            body,
                            &update_promoted_scope(promoted_names, name.as_str(), ty),
                        )
                }
                TrustVcExpr::CollectionOp { receiver, args, .. } => {
                    visit(receiver, promoted_names)
                        || args.iter().any(|arg| visit(arg, promoted_names))
                }
                TrustVcExpr::Index {
                    receiver, index, ..
                } => visit(receiver, promoted_names) || visit(index, promoted_names),
                TrustVcExpr::Quantifier {
                    bound_vars,
                    body,
                    triggers,
                    ..
                } => {
                    let scope = update_promoted_scope_many(
                        promoted_names,
                        bound_vars
                            .iter()
                            .map(|(name, ty)| (name.clone(), ty.clone())),
                    );
                    visit(body, &scope)
                        || triggers.as_ref().is_some_and(|groups| {
                            groups
                                .iter()
                                .any(|group| group.iter().any(|t| visit(t, &scope)))
                        })
                }
                TrustVcExpr::FnCall { args, .. } => {
                    args.iter().any(|arg| visit(arg, promoted_names))
                }
                TrustVcExpr::SpecClosure { params, body, .. } => visit(
                    body,
                    &update_promoted_scope_many(
                        promoted_names,
                        params.iter().map(|(name, ty)| (name.clone(), ty.clone())),
                    ),
                ),
                TrustVcExpr::Choose {
                    var_name,
                    var_ty,
                    condition,
                    ..
                } => visit(
                    condition,
                    &update_promoted_scope(promoted_names, var_name.as_str(), var_ty),
                ),
                TrustVcExpr::Match {
                    scrutinee, arms, ..
                } => {
                    visit(scrutinee, promoted_names)
                        || arms.iter().any(|arm| {
                            let mut scope = promoted_names.clone();
                            for name in
                                crate::match_pattern_scope::pattern_bound_names(&arm.pattern)
                            {
                                scope.remove(name.as_str());
                            }
                            visit(&arm.body, &scope)
                        })
                }
                TrustVcExpr::ReadPlace { place, .. } => {
                    place.projections.iter().any(|projection| {
                        if let crate::ir_place::PlaceProjection::Index { index, .. } = projection {
                            visit(index, promoted_names)
                        } else {
                            false
                        }
                    })
                }
                TrustVcExpr::PlaceDisjoint { left, right } => [left, right].iter().any(|place| {
                    place.projections.iter().any(|projection| {
                        if let crate::ir_place::PlaceProjection::Index { index, .. } = projection {
                            visit(index, promoted_names)
                        } else {
                            false
                        }
                    })
                }),
                TrustVcExpr::ProphecyResolve { value, .. } => visit(value, promoted_names),
            }
        }

        let mut promoted_names: std::collections::HashSet<String> = self
            .var_types
            .iter()
            .filter_map(|(name, ty)| {
                matches!(ty, TrustVcType::MathInt | TrustVcType::Nat).then_some(name)
            })
            .cloned()
            .collect();
        for (name, ty) in &self.local_var_types {
            promoted_names.remove(name);
            if matches!(ty, TrustVcType::MathInt | TrustVcType::Nat) {
                promoted_names.insert(name.clone());
            }
        }
        visit(expr, &promoted_names)
    }
}
