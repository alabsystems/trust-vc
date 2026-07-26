//! Int-mode bitwise and shift encoding for quantifier bodies.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::Term;
use num_bigint::BigInt;

use crate::encoder::arith_semantics::resolve_expr_wrap;
use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{SpecialArithOp, TrustVcExpr, TrustVcType};

impl<'a> AstExpressionParser<'a> {
    /// Encode bitwise/shift operations in Int mode (#1822).
    pub(super) fn encode_int_special_arith(
        &mut self,
        op: SpecialArithOp,
        left: &TrustVcExpr,
        right: &TrustVcExpr,
        left_term: Term,
        right_term: Term,
        ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        match op {
            SpecialArithOp::Shl => {
                let n = extract_int_literal(right).ok_or_else(|| {
                    String::from(
                        "Left shift (<<) in quantifier body requires a literal shift amount; \
                         variable shifts need BV mode (use assert_by_bit_vector)",
                    )
                })?;
                let width = require_shift_width(ty, "left shift")?;
                if n < 0 || n >= width {
                    return Err(
                        format!("Shift amount {} out of range for {}-bit type", n, width).into(),
                    );
                }
                let two_pow_n = BigInt::from(1u128) << (n as u32);
                let pow_term = self.solver.int_const_bigint(&two_pow_n);
                let raw = self
                    .solver
                    .try_mul(left_term, pow_term)
                    .map_err(|e| e.to_string())?;
                self.apply_int_shift_wrapping(raw, ty)
            }
            SpecialArithOp::Shr => {
                let n = extract_int_literal(right).ok_or_else(|| {
                    String::from(
                        "Right shift (>>) in quantifier body requires a literal shift amount; \
                         variable shifts need BV mode (use assert_by_bit_vector)",
                    )
                })?;
                let width = require_shift_width(ty, "right shift")?;
                if n < 0 || n >= width {
                    return Err(
                        format!("Shift amount {} out of range for {}-bit type", n, width).into(),
                    );
                }
                let two_pow_n = BigInt::from(1u128) << (n as u32);
                let pow_term = self.solver.int_const_bigint(&two_pow_n);
                self.solver
                    .try_int_div(left_term, pow_term)
                    .map_err(|e| format!("Int-mode right shift failed: {}", e).into())
            }
            SpecialArithOp::BitAnd => {
                if let Some(k) = extract_pow2_mask(right) {
                    let modulus = BigInt::from(1u128) << k;
                    let mod_term = self.solver.int_const_bigint(&modulus);
                    return self
                        .solver
                        .try_modulo(left_term, mod_term)
                        .map_err(|e| format!("Int-mode BitAnd mask failed: {}", e).into());
                }
                if let Some(k) = extract_pow2_mask(left) {
                    let modulus = BigInt::from(1u128) << k;
                    let mod_term = self.solver.int_const_bigint(&modulus);
                    return self
                        .solver
                        .try_modulo(right_term, mod_term)
                        .map_err(|e| format!("Int-mode BitAnd mask failed: {}", e).into());
                }
                Err(
                    "BitAnd (&) in quantifier body only supports power-of-2 masks \
                     (e.g., x & 0xFF); for general bitwise AND, use assert_by_bit_vector"
                        .to_string()
                        .into(),
                )
            }
            SpecialArithOp::BitOr => Err("BitOr (|) not supported in quantifier body (Int mode); \
                 use assert_by_bit_vector for bitwise operations"
                .to_string()
                .into()),
            SpecialArithOp::BitXor => {
                Err("BitXor (^) not supported in quantifier body (Int mode); \
                 use assert_by_bit_vector for bitwise operations"
                    .to_string()
                    .into())
            }
        }
    }

    /// Apply wrapping to an Int-mode left-shift result.
    ///
    /// A fixed-width `<<` is a bit-level operation whose result is ALWAYS
    /// truncated to the operand type's width in two's complement — `1i32 << 31`
    /// is `i32::MIN`, not the out-of-range `+2^31`. Unlike `+`/`-`/`*` (which
    /// honor the `use_int_arithmetic` opt-out into unbounded math), a shift on a
    /// fixed-width type must therefore wrap to that width even in an
    /// `int`/`nat`-seeded session: otherwise a sign-bit-landing left shift models
    /// the raw positive product and a postcondition like `result > 0` falsely
    /// verifies (P1-E shifts cluster). Shifts in pure-`int` contexts never reach
    /// here — `require_shift_width` rejects a width-less type first — so this
    /// only ever truncates a genuine finite-width result.
    fn apply_int_shift_wrapping(&mut self, raw: Term, ty: &TrustVcType) -> TrustVcResult<Term> {
        let scope_sem = self.current_quantifier_wrap_semantics();
        let wrap_ctx = resolve_expr_wrap(ty, scope_sem);
        self.wrap_int_with_ctx(raw, wrap_ctx)
    }
}

/// Require a known bit width from the expression type (#2297).
///
/// Returns an error for types without `bit_width()` (e.g., Opaque, Bool,
/// MathInt) instead of silently defaulting to 32.
fn require_shift_width(ty: &TrustVcType, label: &str) -> TrustVcResult<i128> {
    ty.bit_width()
        .map(|w| w as i128)
        .ok_or_else(|| format!("Int-mode {} requires known bit width", label).into())
}

fn extract_int_literal(expr: &TrustVcExpr) -> Option<i128> {
    match expr {
        TrustVcExpr::IntLit { value, .. } => Some(*value),
        _ => None,
    }
}

fn extract_pow2_mask(expr: &TrustVcExpr) -> Option<u32> {
    let value = extract_int_literal(expr)?;
    if value <= 0 {
        return None;
    }
    let v = value as u128;
    if v & (v + 1) == 0 {
        Some((v + 1).trailing_zeros())
    } else {
        None
    }
}
