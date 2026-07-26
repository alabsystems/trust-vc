//! Conditional and let-binding encoding for TrustVcExpr IR.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Encodes if-then-else with branch width coercion and let bindings
//! with local-scope variable shadowing.

use ay_dpll::api::Term;

use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{TrustVcExpr, TrustVcType};

impl<'a> AstExpressionParser<'a> {
    /// Encode if-then-else with branch width coercion.
    pub(super) fn encode_ite(
        &mut self,
        cond: &TrustVcExpr,
        then_branch: &TrustVcExpr,
        else_branch: &TrustVcExpr,
        ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        let cond_term = self.encode_subexpr(cond)?;
        let not_cond = self.solver.try_not(cond_term).map_err(|e| e.to_string())?;

        // Branch expressions are encoded eagerly, so guard any overflow checks
        // they emit to preserve branch semantics:
        // - then-branch checks only apply when cond is true  => ¬cond ∨ check
        // - else-branch checks only apply when cond is false => cond ∨ check
        let then_term =
            self.encode_with_overflow_guard(not_cond, |s| s.encode_trust_vc_expr(then_branch))?;
        let else_term =
            self.encode_with_overflow_guard(cond_term, |s| s.encode_trust_vc_expr(else_branch))?;

        // Coerce branch widths to match (same as parse_syn_expr If case)
        let (then_coerced, else_coerced) = self.coerce_bv_widths(then_term, else_term)?;
        let result = self
            .solver
            .try_ite(cond_term, then_coerced, else_coerced)
            .map_err(|e| e.to_string())?;

        // Register term_widths for the ITE result using the actual coerced
        // branch width rather than the declared IR type. When branches have
        // mixed widths (e.g. u8 then, u32 else), coerce_bv_widths widens to
        // u32, but ty may still reflect the narrower type from IR lowering.
        // Using the coerced branch width prevents downstream sort mismatches.
        // Signedness: use ty's signedness (not branch-derived) to avoid
        // then-branch preference when branches have mixed signedness. #2565.
        // Parity: encode_match actual_width tracking. #2131, #2110.
        let branch_info = self
            .term_widths
            .get(&then_coerced)
            .or_else(|| self.term_widths.get(&else_coerced))
            .copied();
        if let Some((w, branch_signed)) = branch_info {
            let signed = ty
                .bit_width()
                .map(|_| !ty.is_unsigned())
                .unwrap_or(branch_signed);
            self.term_widths.insert(result, (w, signed));
        } else if let Some(w) = ty.bit_width() {
            if w > 0 {
                let signed = !ty.is_unsigned();
                self.term_widths.insert(result, (w, signed));
            }
        }

        Ok(result)
    }

    /// Encode a let binding: evaluate value, bind in local scope, encode body.
    pub(super) fn encode_let(
        &mut self,
        name: &str,
        ty: &TrustVcType,
        value: &TrustVcExpr,
        body: &TrustVcExpr,
    ) -> TrustVcResult<Term> {
        let value_term = self.encode_subexpr(value)?;

        // Register term_widths for the let-bound value so downstream checked
        // arithmetic, comparisons, and coercions have correct width/signedness.
        // Parity: expressions.rs string-path parse_block (line 552-555). #2116.
        if let Some(w) = ty.bit_width() {
            if w > 0 {
                let signed = !ty.is_unsigned();
                self.term_widths.insert(value_term, (w, signed));
            }
        }

        // Encode body with the let binding in scope; restore afterward.
        self.with_local_bindings([(name.to_string(), value_term, ty.clone())], |s| {
            s.encode_trust_vc_expr(body)
        })
    }
}
