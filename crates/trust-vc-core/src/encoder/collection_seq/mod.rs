//! Seq-specific collection encoding (contains, bounds, shifted, concat, flat_map, fold).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod flat_map;
mod fold;
mod map_filter;
mod ops;
mod seq_no_duplicates;
mod seq_transforms;

use ay_dpll::api::Term;

use super::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{TrustVcExpr, TrustVcType};

fn seq_expr_receiver_name(expr: &TrustVcExpr) -> Option<&str> {
    match expr {
        TrustVcExpr::Var { name, .. } => Some(name.as_str()),
        TrustVcExpr::FnCall { name, args, .. } if args.is_empty() => Some(name.as_str()),
        TrustVcExpr::CollectionOp { receiver_name, .. }
        | TrustVcExpr::Index { receiver_name, .. } => receiver_name.as_deref(),
        TrustVcExpr::Cast { expr, .. } => seq_expr_receiver_name(expr),
        _ => None,
    }
}

impl<'a> AstExpressionParser<'a> {
    pub(in crate::encoder) fn coerce_value_for_seq_elem_ty(
        &mut self,
        value: Term,
        elem_ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        let Some(expected_width) = elem_ty.bit_width() else {
            return Ok(value);
        };
        if expected_width == 0 {
            return Ok(value);
        }
        let expected_signed = !elem_ty.is_unsigned();

        // A bit-vector value must arrive at the element type's width (it used
        // to be widened by a `term_widths` sign, or truncated).
        if let Some(value_width) = self.bv_term_width(value) {
            if value_width == expected_width {
                return Ok(value);
            }
            return Err(format!(
                "a {value_width}-bit value cannot be taken as a `{}` sequence element: its own \
                 type is not known here, so it is neither widened nor narrowed",
                elem_ty.to_type_string()
            )
            .into());
        }

        if self.int_mode() {
            self.diagnostics
                .record(super::diagnostics::EncodingApproximation::IntBvCoercion);
            let converted = self.solver.try_int2bv(value, expected_width).map_err(|e| {
                format!(
                    "Failed to coerce Int to BV{} for sequence result coercion: {}",
                    expected_width, e
                )
            })?;
            self.term_widths
                .insert(converted, (expected_width, expected_signed));
            return Ok(converted);
        }

        Ok(value)
    }

    pub(super) fn register_term_width_for_declared_type(&mut self, term: Term, ty: &TrustVcType) {
        if let Some(width) = ty.bit_width() {
            if width > 0 {
                self.term_widths.insert(term, (width, !ty.is_unsigned()));
            }
        }
    }

    pub(super) fn coerce_term_for_declared_type_in_int_mode(
        &mut self,
        term: Term,
        ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        self.register_term_width_for_declared_type(term, ty);
        if !self.int_mode() {
            return Ok(term);
        }

        let Some(width) = ty.bit_width() else {
            return Ok(term);
        };
        if width == 0 {
            return Ok(term);
        }

        let converted = if ty.is_unsigned() {
            self.solver.try_bv2int(term).map_err(|e| e.to_string())?
        } else {
            self.solver
                .try_bv2int_signed(term)
                .map_err(|e| e.to_string())?
        };
        self.term_widths.remove(&converted);
        Ok(converted)
    }
}

#[cfg(test)]
mod tests {
    use crate::ir::{CompareOp, QuantifierKind, TrustVcExpr, TrustVcType};
    use crate::ir_expr_traversal::expr_references_any_name;
    use std::collections::HashSet;

    fn bool_ty() -> TrustVcType {
        TrustVcType::Bool
    }

    fn u32_ty() -> TrustVcType {
        TrustVcType::Uint { width: 32 }
    }

    fn var(name: &str) -> TrustVcExpr {
        TrustVcExpr::Var {
            name: name.to_string(),
            ty: u32_ty(),
        }
    }

    fn fn_call(name: &str, args: Vec<TrustVcExpr>) -> TrustVcExpr {
        TrustVcExpr::FnCall {
            name: name.to_string(),
            args,
            return_ty: u32_ty(),
        }
    }

    fn eq(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
        TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    #[test]
    fn test_expr_references_any_name_let_shadowing_keeps_value_scope() {
        let expr = TrustVcExpr::Let {
            name: "item".to_string(),
            ty: u32_ty(),
            value: Box::new(fn_call("f", vec![var("item")])),
            body: Box::new(fn_call("g", vec![var("item")])),
        };
        let names: HashSet<&str> = ["item"].into_iter().collect();
        assert!(
            expr_references_any_name(&expr, &names),
            "let value should still see the outer binder while the body shadows it"
        );
    }

    #[test]
    fn test_expr_references_any_name_let_body_scoped_out() {
        // Negative test: body-only reference to let-bound name must not match outer scope.
        // Unlike test_let_shadowing_keeps_value_scope which passes regardless of fix
        // (value arm always matches), this test ONLY passes with scoping applied.
        let expr = TrustVcExpr::Let {
            name: "item".to_string(),
            ty: u32_ty(),
            value: Box::new(TrustVcExpr::IntLit {
                value: 42,
                ty: u32_ty(),
            }),
            body: Box::new(fn_call("g", vec![var("item")])),
        };
        let names: HashSet<&str> = ["item"].into_iter().collect();
        assert!(
            !expr_references_any_name(&expr, &names),
            "body-only reference to let-bound item must not satisfy outer scope check"
        );
    }

    #[test]
    fn test_expr_references_any_name_quantifier_shadowing_applies_to_triggers() {
        let expr = TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            bound_vars: vec![("item".to_string(), u32_ty())],
            body: Box::new(eq(var("item"), var("item"))),
            triggers: Some(vec![vec![fn_call("f", vec![var("item")])]]),
            trigger_inference_mode: None,
        };
        let names: HashSet<&str> = ["item"].into_iter().collect();
        assert!(
            !expr_references_any_name(&expr, &names),
            "inner quantifier binders must not satisfy outer flat_map binder checks"
        );
    }

    #[test]
    fn test_expr_references_any_name_choose_shadowing_removes_bound_var() {
        let expr = TrustVcExpr::Choose {
            var_name: "item".to_string(),
            var_ty: u32_ty(),
            condition: Box::new(eq(var("item"), var("item"))),
            key: "collection_seq_choose_shadowing".to_string(),
            also_assert: None,
        };
        let names: HashSet<&str> = ["item"].into_iter().collect();
        assert!(
            !expr_references_any_name(&expr, &names),
            "choose-bound item must not count as the outer flat_map binder"
        );
    }

    #[test]
    fn test_expr_references_any_name_spec_closure_shadowing_removes_params() {
        let expr = TrustVcExpr::SpecClosure {
            params: vec![("item".to_string(), u32_ty())],
            body: Box::new(fn_call("f", vec![var("item")])),
            ty: bool_ty(),
        };
        let names: HashSet<&str> = ["item"].into_iter().collect();
        assert!(
            !expr_references_any_name(&expr, &names),
            "spec-closure params must shadow the outer flat_map binder"
        );
    }
}
