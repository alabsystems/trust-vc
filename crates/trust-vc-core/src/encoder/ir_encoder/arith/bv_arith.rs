// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! BV, Real, and bitwise/shift arithmetic encoding.

use ay_dpll::api::Term;

use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{ArithOp, SpecialArithOp, TrustVcExpr, TrustVcType};

impl<'a> AstExpressionParser<'a> {
    fn infer_effective_arith_expr_type(
        &self,
        expr: &TrustVcExpr,
        hint_ty: Option<&TrustVcType>,
    ) -> TrustVcType {
        if let Some(hint_ty) = hint_ty {
            if let Some(coerced) = Self::coerce_default_int_literal(expr, hint_ty) {
                return crate::ir_lowering::infer_expr_type(&coerced);
            }
        }

        // Route A (#2779): spec-collection `.len()` is modelled as an unbounded
        // Int (Seq/Array/Set/Map/Multiset, and strings under native-strings),
        // so report MathInt — this routes through the existing, well-tested
        // Int-arithmetic coercion machinery (`coerce_bv_term_to_int_for_type`)
        // instead of attempting BV arithmetic on an Int-sorted length term.
        // Mirrors what native-seq/native-strings already do for their lengths.
        if Self::len_op_yields_int(expr) {
            return TrustVcType::MathInt;
        }

        crate::ir_lowering::infer_expr_type(expr)
    }

    /// True when `expr` is a collection `.len()` whose term is Int-sorted under
    /// Route A (#2779): Seq/Array/Set/Map/Multiset cardinalities, plus strings
    /// when the native-strings Int length model is active.
    pub(in crate::encoder::ir_encoder) fn len_op_yields_int(expr: &TrustVcExpr) -> bool {
        let TrustVcExpr::CollectionOp {
            op: crate::ir::CollectionOp::Len,
            receiver,
            ..
        } = expr
        else {
            return false;
        };
        let recv_ty = crate::ir_lowering::infer_expr_type(receiver);
        if matches!(
            recv_ty,
            TrustVcType::Seq(_)
                | TrustVcType::Array(_, _)
                | TrustVcType::Set(_)
                | TrustVcType::Map(_, _)
                | TrustVcType::Multiset(_)
        ) {
            return true;
        }
        // Strings only carry an Int length when native-strings is active; the
        // default path keeps a BV string length companion.
        #[cfg(feature = "native-strings")]
        if recv_ty.is_string_like() {
            return true;
        }
        false
    }

    /// Encode a standard arithmetic operation (add, sub, mul, div, rem).
    ///
    /// Signedness is determined from the arithmetic expression type (`ty`)
    /// first, then falls back to operand TrustVcExpr types.
    ///
    /// This avoids `term_widths`-based signedness (which loses type info for
    /// literals) and remains robust even if a caller provides IR without
    /// lowering-time literal coercion (#2070).
    pub(in crate::encoder::ir_encoder) fn encode_arith(
        &mut self,
        op: ArithOp,
        left: &TrustVcExpr,
        right: &TrustVcExpr,
        ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        // Arithmetic semantics follow the expression/result type in Rust.
        // Fallback to operand-type AND semantics only for unexpected non-int
        // `ty` values (defensive path for manually constructed IR).
        let left_hint_ty = self.infer_effective_arith_expr_type(right, None);
        let right_hint_ty = self.infer_effective_arith_expr_type(left, None);
        let left_ty = self.infer_effective_arith_expr_type(left, Some(&left_hint_ty));
        let right_ty = self.infer_effective_arith_expr_type(right, Some(&right_hint_ty));
        let effective_ty = if matches!(ty, TrustVcType::Real)
            || matches!(left_ty, TrustVcType::Real)
            || matches!(right_ty, TrustVcType::Real)
        {
            TrustVcType::Real
        } else if matches!(left_ty, TrustVcType::MathInt | TrustVcType::Nat)
            || matches!(right_ty, TrustVcType::MathInt | TrustVcType::Nat)
        {
            TrustVcType::MathInt
        } else {
            ty.clone()
        };
        let unsigned = match &effective_ty {
            TrustVcType::Uint { .. } => true,
            TrustVcType::Int { .. } => false,
            _ => {
                matches!(left_ty, TrustVcType::Uint { .. })
                    && matches!(right_ty, TrustVcType::Uint { .. })
            }
        };

        let left_term = self.encode_expr_with_integer_hint(left, Some(&left_hint_ty))?;
        let right_term = self.encode_expr_with_integer_hint(right, Some(&right_hint_ty))?;

        let right_is_zero = super::super::is_trust_vc_literal_zero(right);
        let right_is_one = super::super::is_trust_vc_literal_one(right);
        let right_literal = super::super::trust_vc_int_literal_value(right);

        if matches!(effective_ty, TrustVcType::Float { .. })
            || matches!(left_ty, TrustVcType::Float { .. })
            || matches!(right_ty, TrustVcType::Float { .. })
        {
            return self.encode_float_arith(op, left_term, right_term);
        }

        // Real arithmetic: no overflow, no wrapping, exact division.
        if matches!(effective_ty, TrustVcType::Real) {
            // Coerce Int-sorted operands to Real (handles integer literals
            // in Real expressions, e.g., `x + 0` where x: real). #2517.
            let left_term = if !matches!(left_ty, TrustVcType::Real) {
                self.solver
                    .try_int_to_real(left_term)
                    .map_err(|e| e.to_string())?
            } else {
                left_term
            };
            let right_term = if !matches!(right_ty, TrustVcType::Real) {
                self.solver
                    .try_int_to_real(right_term)
                    .map_err(|e| e.to_string())?
            } else {
                right_term
            };
            return self.encode_real_arith(op, left_term, right_term, right_is_zero);
        }

        if matches!(effective_ty, TrustVcType::MathInt | TrustVcType::Nat) {
            let left_term = self.coerce_bv_term_to_int_for_type(left_term, &left_ty)?;
            let right_term = self.coerce_bv_term_to_int_for_type(right_term, &right_ty)?;
            return self.encode_int_arith(
                op,
                left_term,
                right_term,
                right_is_zero,
                right_is_one,
                &effective_ty,
                right_literal,
            );
        }

        if self.int_mode() {
            return self.encode_int_arith(
                op,
                left_term,
                right_term,
                right_is_zero,
                right_is_one,
                &effective_ty,
                right_literal,
            );
        }

        // Route A (#2779): spec-collection `.len()` is Int while a peer integer
        // operand encodes as BV (e.g. `s.len() - n`, `s.len() + t.len()` where a
        // literal is BV). When the actual term sorts are a mixed Int/BV pair,
        // lift the BV operand to Int (unsigned — lengths/usize are non-negative)
        // and use Int arithmetic so length math stays over the unbounded
        // integers (monotone, no wrap). Analogue of the compare-path bridge.
        {
            use ay_dpll::api::Sort;
            let left_sort = self.solver.term_sort(left_term);
            let right_sort = self.solver.term_sort(right_term);
            let mixed_int_bv = matches!(
                (&left_sort, &right_sort),
                (Sort::Int, Sort::BitVec(_)) | (Sort::BitVec(_), Sort::Int)
            );
            if mixed_int_bv {
                let left_int = if matches!(left_sort, Sort::Int) {
                    left_term
                } else {
                    self.solver
                        .try_bv2int(left_term)
                        .map_err(|e| e.to_string())?
                };
                let right_int = if matches!(right_sort, Sort::Int) {
                    right_term
                } else {
                    self.solver
                        .try_bv2int(right_term)
                        .map_err(|e| e.to_string())?
                };
                return self.encode_int_arith(
                    op,
                    left_int,
                    right_int,
                    right_is_zero,
                    right_is_one,
                    &TrustVcType::MathInt,
                    right_literal,
                );
            }
        }

        // Coerce BV widths to match
        let (left_term, right_term) = self.coerce_bv_widths(left_term, right_term)?;

        let coerced_width_info = self
            .term_widths
            .get(&left_term)
            .or_else(|| self.term_widths.get(&right_term))
            .copied();

        // Resolve operand width for div-by-zero checks: prefer coerced width,
        // fall back to TrustVcType from the IR node.
        let operand_width = coerced_width_info
            .map(|(w, _)| w)
            .or_else(|| effective_ty.bit_width());
        let collect_side_checks = self.quantifier_depth == 0;

        let result = match op {
            ArithOp::Add => {
                let result = self
                    .solver
                    .try_bvadd(left_term, right_term)
                    .map_err(|e| e.to_string())?;
                if self.overflow_behavior.should_check()
                    && collect_side_checks
                    && !right_is_zero
                    && !self.try_record_const_fold_overflow(
                        op,
                        left,
                        right,
                        &effective_ty,
                        "addition",
                    )
                {
                    self.add_bv_arith_overflow_check(
                        left_term, right_term, unsigned, "addition", true,
                    )?;
                }
                result
            }
            ArithOp::Sub => {
                let result = self
                    .solver
                    .try_bvsub(left_term, right_term)
                    .map_err(|e| e.to_string())?;
                if self.overflow_behavior.should_check()
                    && collect_side_checks
                    && !right_is_zero
                    && !self.try_record_const_fold_overflow(
                        op,
                        left,
                        right,
                        &effective_ty,
                        "subtraction",
                    )
                {
                    self.add_bv_arith_overflow_check(
                        left_term,
                        right_term,
                        unsigned,
                        "subtraction",
                        false,
                    )?;
                }
                result
            }
            ArithOp::Mul => {
                let result = self
                    .solver
                    .try_bvmul(left_term, right_term)
                    .map_err(|e| e.to_string())?;
                if self.overflow_behavior.should_check()
                    && collect_side_checks
                    && !right_is_zero
                    && !right_is_one
                    && !self.try_record_const_fold_overflow(
                        op,
                        left,
                        right,
                        &effective_ty,
                        "multiplication",
                    )
                {
                    self.add_bv_mul_overflow_check(left_term, right_term, unsigned)?;
                }
                result
            }
            ArithOp::Div => {
                if right_is_zero {
                    return Err("Division by zero: divisor is constant 0".to_string().into());
                }
                if self.div0_behavior.should_check() && collect_side_checks {
                    let w = operand_width.ok_or_else(|| {
                        "Cannot generate div-by-zero check: divisor width unknown".to_string()
                    })?;
                    self.add_div_by_zero_check(right_term, w)?;
                }
                if unsigned {
                    self.solver
                        .try_bvudiv(left_term, right_term)
                        .map_err(|e| e.to_string())?
                } else {
                    let result = self
                        .solver
                        .try_bvsdiv(left_term, right_term)
                        .map_err(|e| e.to_string())?;
                    // Signed `MIN / -1` is a *partiality* panic in checked Rust
                    // (the quotient `-MIN` is unrepresentable), exactly like
                    // division-by-zero. It is therefore gated by `div0_behavior`
                    // (division safety) rather than `overflow_behavior`: in
                    // BitVector mode additive/mul wrapping carries no obligation,
                    // but MIN/-1 must still fail closed when division checks are
                    // on. Gating it on `overflow_behavior` (suppressed in BV
                    // mode) let `i8::MIN / -1` verify unsoundly. (#div0-bv-precheck)
                    if self.div0_behavior.should_check()
                        && collect_side_checks
                        && !self.try_record_const_fold_overflow(
                            op,
                            left,
                            right,
                            &effective_ty,
                            "signed division",
                        )
                    {
                        // Signed division overflow: MIN / -1
                        let no_overflow = self
                            .solver
                            .try_bvsdiv_no_overflow(left_term, right_term)
                            .map_err(|e| {
                                format!("Failed to create signed division overflow check: {}", e)
                            })?;
                        self.overflow_checks
                            .push(("signed division overflow".into(), no_overflow));
                    }
                    result
                }
            }
            ArithOp::Rem => {
                if right_is_zero {
                    return Err("Modulo by zero: divisor is constant 0".to_string().into());
                }
                if self.div0_behavior.should_check() && collect_side_checks {
                    let w = operand_width.ok_or_else(|| {
                        "Cannot generate mod-by-zero check: divisor width unknown".to_string()
                    })?;
                    self.add_div_by_zero_check(right_term, w)?;
                }
                if unsigned {
                    self.solver
                        .try_bvurem(left_term, right_term)
                        .map_err(|e| e.to_string())?
                } else {
                    let result = self
                        .solver
                        .try_bvsrem(left_term, right_term)
                        .map_err(|e| e.to_string())?;
                    // Signed remainder overflow uses the same MIN/-1 guard, and
                    // is likewise a checked-Rust partiality panic gated by
                    // `div0_behavior` (see the signed-division note above).
                    if self.div0_behavior.should_check() && collect_side_checks {
                        let no_overflow = self
                            .solver
                            .try_bvsdiv_no_overflow(left_term, right_term)
                            .map_err(|e| {
                                format!("Failed to create signed remainder overflow check: {}", e)
                            })?;
                        self.overflow_checks
                            .push(("signed remainder overflow".into(), no_overflow));
                    }
                    result
                }
            }
        };

        if let Some(width_info) = coerced_width_info {
            self.term_widths.insert(result, width_info);
        }
        Ok(result)
    }

    fn encode_float_arith(&mut self, op: ArithOp, left: Term, right: Term) -> TrustVcResult<Term> {
        let rne = self
            .solver
            .try_fp_rounding_mode("RNE")
            .map_err(|e| e.to_string())?;
        match op {
            ArithOp::Add => self
                .solver
                .try_fp_add(rne, left, right)
                .map_err(|e| e.to_string().into()),
            ArithOp::Sub => self
                .solver
                .try_fp_sub(rne, left, right)
                .map_err(|e| e.to_string().into()),
            ArithOp::Mul => self
                .solver
                .try_fp_mul(rne, left, right)
                .map_err(|e| e.to_string().into()),
            ArithOp::Div => self
                .solver
                .try_fp_div(rne, left, right)
                .map_err(|e| e.to_string().into()),
            ArithOp::Rem => self
                .solver
                .try_fp_rem(left, right)
                .map_err(|e| e.to_string().into()),
        }
    }

    /// Encode arithmetic for Real-typed operands (spec-level mathematical reals).
    /// No overflow checks, no wrapping. Division is exact (SMT `/`).
    fn encode_real_arith(
        &mut self,
        op: ArithOp,
        left: Term,
        right: Term,
        right_is_zero: bool,
    ) -> TrustVcResult<Term> {
        match op {
            ArithOp::Add => self
                .solver
                .try_add(left, right)
                .map_err(|e| e.to_string().into()),
            ArithOp::Sub => self
                .solver
                .try_sub(left, right)
                .map_err(|e| e.to_string().into()),
            ArithOp::Mul => self
                .solver
                .try_mul(left, right)
                .map_err(|e| e.to_string().into()),
            ArithOp::Div => {
                if right_is_zero {
                    return Err("Division by zero: divisor is constant 0".to_string().into());
                }
                // Real division: exact, uses SMT (/ a b)
                let result = self
                    .solver
                    .try_div(left, right)
                    .map_err(|e| e.to_string())?;

                // Self-cancellation axiom for reals: `a != 0 ==> a / a == 1`.
                // This is the exact, universally-true field fact (guarded by
                // nonzero, so `a / 0` stays unconstrained — it cannot make a
                // false goal such as `a / a == 2` verify, nor does it touch
                // `a / b` for distinct terms). The bare SMT `/` is opaque on
                // a symbolic divisor — `try_div(a, a)` is nonlinear, so ay
                // returns Unknown(incomplete) for `a / a == 1` without it.
                //
                // Only emitted at quantifier depth 0 so a bound variable never
                // leaks into a top-level assertion; self-division inside a
                // quantifier body simply stays fail-closed (sound, less
                // complete).
                if left == right && self.quantifier_depth == 0 {
                    let zero_int = self.solver.int_const(0);
                    let zero_real = self
                        .solver
                        .try_int_to_real(zero_int)
                        .map_err(|e| e.to_string())?;
                    let one_int = self.solver.int_const(1);
                    let one_real = self
                        .solver
                        .try_int_to_real(one_int)
                        .map_err(|e| e.to_string())?;
                    let divisor_nonzero = self
                        .solver
                        .try_neq(right, zero_real)
                        .map_err(|e| e.to_string())?;
                    let quotient_is_one = self
                        .solver
                        .try_eq(result, one_real)
                        .map_err(|e| e.to_string())?;
                    let self_cancel = self
                        .solver
                        .try_implies(divisor_nonzero, quotient_is_one)
                        .map_err(|e| e.to_string())?;
                    self.solver
                        .try_assert_term(self_cancel)
                        .map_err(|e| e.to_string())?;
                }

                Ok(result)
            }
            ArithOp::Rem => Err("Modulo operation is not supported for Real type"
                .to_string()
                .into()),
        }
    }

    /// Encode bitwise and shift operations.
    pub(in crate::encoder::ir_encoder) fn encode_special_arith(
        &mut self,
        op: SpecialArithOp,
        left: &TrustVcExpr,
        right: &TrustVcExpr,
        ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        let left_term = self.encode_subexpr(left)?;
        let right_term = self.encode_subexpr(right)?;

        if self.int_mode() {
            return self.encode_int_special_arith(op, left, right, left_term, right_term, ty);
        }
        let collect_side_checks = self.quantifier_depth == 0;

        if matches!(op, SpecialArithOp::Shl | SpecialArithOp::Shr) {
            return self.encode_bv_shift(
                op,
                left,
                right,
                ty,
                left_term,
                right_term,
                collect_side_checks,
            );
        }

        let (left_term, right_term) = self.coerce_bv_widths(left_term, right_term)?;
        let coerced_width_info = self
            .term_widths
            .get(&left_term)
            .or_else(|| self.term_widths.get(&right_term))
            .copied();

        let result = match op {
            SpecialArithOp::Shl | SpecialArithOp::Shr => unreachable!(),
            SpecialArithOp::BitAnd => self
                .solver
                .try_bvand(left_term, right_term)
                .map_err(|e| e.to_string())?,
            SpecialArithOp::BitOr => self
                .solver
                .try_bvor(left_term, right_term)
                .map_err(|e| e.to_string())?,
            SpecialArithOp::BitXor => self
                .solver
                .try_bvxor(left_term, right_term)
                .map_err(|e| e.to_string())?,
        };

        if let Some(width_info) = coerced_width_info {
            self.term_widths.insert(result, width_info);
        }
        Ok(result)
    }

    #[allow(clippy::too_many_arguments)]
    fn encode_bv_shift(
        &mut self,
        op: SpecialArithOp,
        left: &TrustVcExpr,
        right: &TrustVcExpr,
        ty: &TrustVcType,
        left_term: Term,
        right_term: Term,
        collect_side_checks: bool,
    ) -> TrustVcResult<Term> {
        let left_width_info = self.term_widths.get(&left_term).copied();
        let left_ty = crate::ir_lowering::infer_expr_type(left);
        let lhs_width = left_ty
            .bit_width()
            .or_else(|| ty.bit_width())
            .or_else(|| left_width_info.map(|(w, _)| w))
            .ok_or_else(|| "shift overflow check requires known LHS bit width".to_string())?;
        let result_width_info = ty
            .bit_width()
            .map(|width| (width, !ty.is_unsigned()))
            .or_else(|| {
                left_ty
                    .bit_width()
                    .map(|width| (width, !left_ty.is_unsigned()))
            })
            .or(left_width_info);

        // `by(bit_vector)` (SolverMode::BitVector) interprets the assertion as
        // pure bitvector math: an over-shift is `bvlshr`/`bvshl`/`bvashr`
        // (shift >= width => 0), exactly like Verus, so it carries NO shift-UB
        // obligation — mirroring the arithmetic-overflow suppression in BitVector
        // mode (assertion_bv_reuse.rs). Exec/Default mode keeps the check (shift
        // >= width is Rust UB there). The value is already Verus-correct
        // (coerce_shift_amount only width-adjusts, never masks). Part of #2778
        // (bit_vector_usize_as_32bit shift-by-width parity with Verus).
        let bit_vector_mode = self.solver_mode == Some(crate::vc::SolverMode::BitVector);
        if self.bitshift_behavior.should_check() && collect_side_checks && !bit_vector_mode {
            // Diagnostic-parity (#2778): when the shift amount has a *signed*
            // type it is possibly negative, so the `0 <= b < width` bound that
            // `check_shift_overflow` enforces (via `bvult`, which already
            // rejects a two's-complement-negative amount) is exactly upstream
            // Verus's `possible bit shift underflow/overflow` obligation. Label
            // the check so a failure surfaces the byte-exact upstream message
            // (`possible <label>` ⇒ `possible bit shift underflow/overflow`).
            // This mirrors the already-implemented bit_vector-mode
            // `possibly negative shift` path and changes only the diagnostic
            // text — the solver obligation is identical, so an in-range signed
            // amount still verifies and an out-of-range/negative one still fails
            // closed. Part of #2778 (`bit_shift_underflow`,
            // `bit_shift_unsigned_shift_signed`).
            let rhs_ty = crate::ir_lowering::infer_expr_type(right);
            let check_name = if matches!(rhs_ty, TrustVcType::Int { .. }) {
                "bit shift underflow/overflow"
            } else {
                match op {
                    SpecialArithOp::Shl => "left shift overflow",
                    SpecialArithOp::Shr => "right shift overflow",
                    _ => unreachable!(),
                }
            };
            self.check_shift_overflow(right_term, lhs_width, check_name)?;
        }

        let shift_amount = self.coerce_shift_amount_to_lhs_width(right_term, lhs_width)?;
        let result = match op {
            SpecialArithOp::Shl => self
                .solver
                .try_bvshl(left_term, shift_amount)
                .map_err(|e| e.to_string())?,
            SpecialArithOp::Shr => {
                let unsigned = matches!(left_ty, TrustVcType::Uint { .. })
                    || (!matches!(left_ty, TrustVcType::Int { .. }) && ty.is_unsigned());
                if unsigned {
                    self.solver
                        .try_bvlshr(left_term, shift_amount)
                        .map_err(|e| e.to_string())?
                } else {
                    self.solver
                        .try_bvashr(left_term, shift_amount)
                        .map_err(|e| e.to_string())?
                }
            }
            _ => unreachable!(),
        };

        if let Some(width_info) = result_width_info {
            self.term_widths.insert(result, width_info);
        }
        Ok(result)
    }

    fn coerce_shift_amount_to_lhs_width(
        &mut self,
        shift_amount: Term,
        lhs_width: u32,
    ) -> TrustVcResult<Term> {
        if lhs_width == 0 {
            return Err("shift amount coercion requires nonzero LHS bit width"
                .to_string()
                .into());
        }
        let Some((rhs_width, rhs_signed)) = self.term_widths.get(&shift_amount).copied() else {
            return Ok(shift_amount);
        };
        if rhs_width == lhs_width {
            return Ok(shift_amount);
        }
        if rhs_width < lhs_width {
            let extended = self.extend_term(shift_amount, lhs_width - rhs_width, rhs_signed)?;
            self.term_widths.insert(extended, (lhs_width, rhs_signed));
            return Ok(extended);
        }
        let narrowed = self
            .solver
            .try_bvextract(shift_amount, lhs_width - 1, 0)
            .map_err(|e| e.to_string())?;
        self.term_widths.insert(narrowed, (lhs_width, rhs_signed));
        Ok(narrowed)
    }
}
