//! Conditional and let-binding encoding for TrustVcExpr IR.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Encodes if-then-else with branch width coercion and let bindings
//! with local-scope variable shadowing.

use ay_dpll::api::Term;

use crate::encoder::width_coercion::ir_type_signedness;
use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{TrustVcExpr, TrustVcType};
use crate::ir_lowering::IntBinding;

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
        // Each branch is typed like an arithmetic operand (an untyped literal
        // takes the other branch's type only when it fits), and the ITE's type
        // is DERIVED from both branches — never the then-branch's alone.
        let (then_ty, else_ty) =
            crate::ir_lowering::binary_operand_types(then_branch, else_branch, ty);
        let derived = crate::ir_lowering::derive_binary_int_type(then_branch, else_branch, ty);
        let then_term = self.encode_with_overflow_guard(not_cond, |s| {
            s.encode_expr_with_integer_hint(then_branch, Some(&then_ty))
        })?;
        let else_term = self.encode_with_overflow_guard(cond_term, |s| {
            s.encode_expr_with_integer_hint(else_branch, Some(&else_ty))
        })?;

        // Branches of DIFFERENT fixed-width types (`if c { x } else { y }`,
        // `x: u8`, `y: i16`) denote an integer: each branch is lifted to the
        // integer it denotes with its OWN sign. The syn lowering typed this ITE
        // by its then-branch (`u8`), and the `i16` branch's `-1`, widened into
        // a u8-registered result, compared as 65535. So does a fixed-width
        // branch beside an integer-sorted one (`if c { !x } else { y % z }`,
        // `x: u8`, `y: i8`, `z: u128`): the bit-vector branch is lifted by its
        // own sign, never handed to the solver next to an `Int` (a sort
        // mismatch, so `Unknown`). A bit-vector branch whose type fixes no
        // sign is refused by the lift.
        let own_then = self.own_sign(then_branch, Some(&then_ty));
        let own_else = self.own_sign(else_branch, Some(&else_ty));
        let one_side_bit_vector =
            self.bv_term_width(then_term).is_some() != self.bv_term_width(else_term).is_some();
        if one_side_bit_vector
            || (crate::ir_lowering::is_fixed_width_int(&then_ty)
                && crate::ir_lowering::is_fixed_width_int(&else_ty)
                && then_ty != else_ty)
        {
            let then_int = self.lift_bv_operand_to_int(then_term, own_then)?;
            let else_int = self.lift_bv_operand_to_int(else_term, own_else)?;
            return self
                .solver
                .try_ite(cond_term, then_int, else_int)
                .map_err(|e| e.to_string().into());
        }

        // Coerce branch widths to match (same as parse_syn_expr If case). Each
        // branch is widened by the signedness of its OWN type — never the
        // ITE's or the other branch's (a branch whose own type fixes no sign
        // is refused rather than borrowing one), and never a `term_widths`
        // entry a hash-consed constant branch shares with other occurrences.
        let ite_signed = ir_type_signedness(&derived);
        let (then_coerced, else_coerced) =
            self.coerce_bv_widths_signed((then_term, own_then), (else_term, own_else))?;
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
        // Without a signed `ty`, the branches' own types; never a branch
        // term's table entry. Parity: encode_match actual_width tracking.
        // #2131, #2110.
        let branch_width = self
            .bv_term_width(then_coerced)
            .or_else(|| self.bv_term_width(else_coerced));
        if let Some(w) = branch_width {
            if let Some(signed) = ite_signed.or(own_then.get().filter(|_| own_then == own_else)) {
                self.term_widths.insert(result, (w, signed));
            }
        } else if let Some(w) = derived.bit_width() {
            if w > 0 {
                let signed = !derived.is_unsigned();
                self.term_widths.insert(result, (w, signed));
            }
        }

        Ok(result)
    }

    /// Encode a let binding: evaluate value, bind in local scope, encode body.
    ///
    /// The value is bound AT the declared type (`ir_lowering::int_binding`): a
    /// value of that type as is, an untyped literal typed by it where its
    /// value fits, a fixed-width value bound at `int`/`nat` lifted to the
    /// integer it denotes; any other integer value is refused. The value's
    /// term used to be registered at the declared width and sign whatever it
    /// was: `let t: u8 = y` (`y: i16 == -1`) read the 16-bit `-1` as the
    /// unsigned 65535, and `let t: u8 = -1` the 32-bit `-1` as 4294967295, so
    /// `t > 1000` came back `Verified`.
    pub(super) fn encode_let(
        &mut self,
        name: &str,
        ty: &TrustVcType,
        value: &TrustVcExpr,
        body: &TrustVcExpr,
    ) -> TrustVcResult<Term> {
        let value_term = match crate::ir_lowering::int_binding(value, ty) {
            IntBinding::Same | IntBinding::NotInteger => self.encode_subexpr(value)?,
            IntBinding::Literal(typed) => self.encode_subexpr(&typed)?,
            IntBinding::LiftToInt => {
                let term = self.encode_subexpr(value)?;
                let own = self.own_sign(value, None);
                self.lift_bv_operand_to_int(term, own)?
            }
            IntBinding::Mismatch(value_ty) => {
                return Err(format!(
                    "a `let {name}: {}` binding cannot hold a value of type `{}` (Rust and \
                     Verus reject the program; binding it would re-read its bits at the \
                     declared type)",
                    ty.to_type_string(),
                    value_ty.to_type_string()
                )
                .into())
            }
        };

        // Register term_widths for the let-bound value so downstream checked
        // arithmetic, comparisons, and coercions have correct width/signedness.
        // Parity: expressions.rs string-path parse_block (line 552-555). #2116.
        // The value has the declared type (above), so the entry restates it.
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
