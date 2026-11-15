// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! BV, Real, and bitwise/shift arithmetic encoding.

use ay_dpll::api::Term;

use crate::encoder::width_coercion::{ir_type_signedness, OwnSign};
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

    /// True when `expr` is built ONLY from default-width (`Int { width: 32 }`)
    /// integer literals — suffixed `i32` or unsuffixed, which lower
    /// identically — combined by `+ - * / %`, `& | ^` and unary `-`, with every
    /// interior node itself typed `Int { width: 32 }`. Such a tree has one
    /// value, fixed by its IR width; see
    /// `default_int_literal_narrowing_suppressed`. Shifts, casts, calls,
    /// variables and every other shape return `false` (encoded unchanged).
    fn is_closed_default_int_literal_tree(expr: &TrustVcExpr) -> bool {
        match expr {
            TrustVcExpr::IntLit {
                ty: TrustVcType::Int { width: 32 },
                ..
            } => true,
            TrustVcExpr::Neg(inner) => Self::is_closed_default_int_literal_tree(inner),
            TrustVcExpr::Arith {
                left,
                right,
                ty: TrustVcType::Int { width: 32 },
                ..
            } => {
                Self::is_closed_default_int_literal_tree(left)
                    && Self::is_closed_default_int_literal_tree(right)
            }
            TrustVcExpr::SpecialArith {
                op: SpecialArithOp::BitAnd | SpecialArithOp::BitOr | SpecialArithOp::BitXor,
                left,
                right,
                ty: TrustVcType::Int { width: 32 },
            } => {
                Self::is_closed_default_int_literal_tree(left)
                    && Self::is_closed_default_int_literal_tree(right)
            }
            _ => false,
        }
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
        // The operation's type is DERIVED from both operands
        // (`ir_lowering::types`), never taken from `ty` alone: one fixed-width
        // type `T` computes in `T`; operands of different fixed-width types
        // (`x: u8 + y: i16`, `29878u16 * -256i32`) compute EXACTLY over the
        // integers, each operand read with its own type's signedness. `ty` said
        // `u8`/`u16` there (the syn lowering copied the left operand's type;
        // a typed producer may say anything), and the wider result was then
        // read unsigned: `0u8 + (-1i16)` compared as 65535.
        //
        // Each operand's hint is the type its VALUE has at this use site: an
        // untyped literal takes its peer's type only when it fits
        // (`coerce_default_int_literal`).
        self.check_untyped_conditional_operation_in_every_type(op, left, right, ty)?;
        let (left_hint_ty, right_hint_ty) =
            crate::ir_lowering::binary_operand_types(left, right, ty);
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
            crate::ir_lowering::derive_binary_int_type(left, right, ty)
        };
        let unsigned = match &effective_ty {
            TrustVcType::Uint { .. } => true,
            TrustVcType::Int { .. } => false,
            _ => {
                matches!(left_ty, TrustVcType::Uint { .. })
                    && matches!(right_ty, TrustVcType::Uint { .. })
            }
        };
        // The signedness each BV operand DENOTES: its OWN type at this use
        // site — never its peer's or the operation's (an operand whose type
        // fixes none is refused where it would be widened or lifted), and
        // never `term_widths` (see `term_widths.rs`).
        let left_signed = self.own_sign(left, Some(&left_hint_ty));
        let right_signed = self.own_sign(right, Some(&right_hint_ty));

        // SOUNDNESS (rank-5 cluster, member 31): a CLOSED default-width literal
        // operation (`21i32 * 21i32`, `100 + 100`, `(31i32 - 10i32) * (..)`)
        // must be computed at its IR width. Context narrowing of its literal
        // leaves would compute — and silently wrap — it at the most common
        // variable width (BV8 `21 * 21 == 185` next to an `i8` variable),
        // while the constant-fold overflow verdict below is taken at 32 bits,
        // so no obligation catches the wrap. Suppress the narrowing for the
        // operands only; every other operand shape is encoded unchanged.
        //
        // NARROWING (rank-5 regression): do NOT suppress when this tree sits in
        // a narrower-typed operand position (`z + (100 + 100)` with `z: u8`,
        // `y == 100 + 100` with `y: i8`). There the literals really are typed at
        // the peer's narrow width, and suppressing would compute the ENCLOSING
        // narrow operation at 32 bits, dropping its overflow obligation. See
        // `narrow_typed_literal_operand_context`.
        let closed_literal_operation = matches!(ty, TrustVcType::Int { width: 32 })
            && !self.narrow_typed_literal_operand_context
            && Self::is_closed_default_int_literal_tree(left)
            && Self::is_closed_default_int_literal_tree(right);
        if closed_literal_operation {
            self.default_int_literal_narrowing_suppressed += 1;
        }
        let operand_terms = self
            .encode_expr_with_integer_hint(left, Some(&left_hint_ty))
            .and_then(|left_term| {
                self.encode_expr_with_integer_hint(right, Some(&right_hint_ty))
                    .map(|right_term| (left_term, right_term))
            });
        if closed_literal_operation {
            self.default_int_literal_narrowing_suppressed -= 1;
        }
        let (left_term, right_term) = operand_terms?;

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
            let left_term = self.lift_bv_operand_to_int(left_term, left_signed)?;
            let right_term = self.lift_bv_operand_to_int(right_term, right_signed)?;
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
        // lift the BV operand to the integer it DENOTES and use Int arithmetic
        // so length math stays over the unbounded integers (monotone, no wrap).
        // Analogue of the compare-path bridge.
        //
        // The lift takes the BV operand's own signedness. It used to be
        // unsigned unconditionally ("lengths/usize are non-negative"), but the
        // BV operand is the PEER of the length, not the length: `a.len() +
        // (-3i64)` was `a.len() + 2^64 - 3`, so `a.len() == 2` entailed
        // `a.len() + (-3) > 100` (Verified, false) and refuted
        // `a.len() + (-3) < 0` (true) — tests/operand_signedness_soundness.rs.
        {
            use ay_dpll::api::Sort;
            let left_sort = self.solver.term_sort(left_term);
            let right_sort = self.solver.term_sort(right_term);
            let mixed_int_bv = matches!(
                (&left_sort, &right_sort),
                (Sort::Int, Sort::BitVec(_)) | (Sort::BitVec(_), Sort::Int)
            );
            if mixed_int_bv {
                let left_int = self.lift_bv_operand_to_int(left_term, left_signed)?;
                let right_int = self.lift_bv_operand_to_int(right_term, right_signed)?;
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

        // Coerce BV widths to match, each operand extended by its own sign.
        let (left_term, right_term) =
            self.coerce_bv_widths_signed((left_term, left_signed), (right_term, right_signed))?;

        // The result's width is the coerced operands' (their sort); its
        // signedness is the operation's — never an operand term's
        // `term_widths` entry, which a hash-consed constant shares with every
        // other occurrence of the same bits.
        let coerced_width_info = self
            .bv_term_width(left_term)
            .or_else(|| self.bv_term_width(right_term))
            .map(|width| (width, !unsigned));

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

    /// An untyped literal operation that holds a CONDITIONAL and meets no peer
    /// here (`(if c { 2 } else { 2 }) * 200`, still at the `i32` placeholder)
    /// is computed at `i32`, Rust's default; but the peer that fixes its type
    /// may be one this encoding does not see — a later use of the binding it
    /// initializes (`let a = ..; let z: u8 = a;`), the parameter of the call
    /// it is an argument of — and Rust then computes it, and checks it, in
    /// that type. Its overflow obligation therefore also holds in EVERY
    /// fixed-width type all its literals fit (each such encoding raises its
    /// own checks; its value is discarded). Checked only at `i32`, `let mut w
    /// = 0; if c { w = 200; } w = w + 100; let z: u8 = w;` was `Verified`
    /// while the `u8` addition overflows. A constant form needs none of this:
    /// the compiler rejects an overflow in it.
    fn check_untyped_conditional_operation_in_every_type(
        &mut self,
        op: ArithOp,
        left: &TrustVcExpr,
        right: &TrustVcExpr,
        ty: &TrustVcType,
    ) -> TrustVcResult<()> {
        if !self.overflow_behavior.should_check() || self.quantifier_depth > 0 {
            return Ok(());
        }
        let node = TrustVcExpr::Arith {
            op,
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
            ty: ty.clone(),
        };
        self.check_untyped_nonconstant_form_in_every_type(&node, ty)
    }

    /// The every-type check of [`Self::check_untyped_conditional_operation_in_every_type`]
    /// for any untyped literal form `node` (typed `ty`) whose value is not a
    /// constant: one holding a conditional, or a SHIFT by an amount that is
    /// not a literal (`1 << k`), whose amount obligation depends on the width
    /// the form takes — `g8(1 << k)` shifts a `u8`, and panics at `k == 8`.
    fn check_untyped_nonconstant_form_in_every_type(
        &mut self,
        node: &TrustVcExpr,
        ty: &TrustVcType,
    ) -> TrustVcResult<()> {
        if !self.overflow_behavior.should_check() || self.quantifier_depth > 0 {
            return Ok(());
        }
        if !crate::ir_lowering::is_untyped_literal(node)
            || !crate::ir_lowering::untyped_form_is_conditional(node)
        {
            return Ok(());
        }
        // A form whose only conditionals are an untyped binding's one-valued
        // ones (`ir_lowering::untyped_site`) is a CONSTANT whose type is not
        // determined here: refused when it panics in a type it may take,
        // and otherwise left to its `i32` reading.
        let collapsed = crate::ir_lowering::collapse_undetermined_forms(node);
        if !crate::ir_lowering::untyped_form_is_conditional(&collapsed) {
            if let Some(panics_in) = crate::ir_lowering::constant_form_panicking_type(&collapsed) {
                return Err(format!(
                    "an untyped integer literal form bound to a name whose type is not \
                     determined here panics as `{}`",
                    panics_in.to_type_string()
                )
                .into());
            }
            return Ok(());
        }
        for width in [8, 16, 32, 64, 128] {
            for candidate in [TrustVcType::Int { width }, TrustVcType::Uint { width }] {
                if candidate == *ty {
                    continue;
                }
                if let Some(typed) = crate::ir_lowering::untyped_literal_at_peer(node, &candidate) {
                    self.encode_subexpr(&typed)?;
                }
            }
        }
        Ok(())
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
            // Rust `%` on floats is C `fmod`, NOT SMT-LIB `fp.rem` (the IEEE
            // remainder): `fp.rem` plus an exact one-step correction.
            ArithOp::Rem => self.encode_float_fmod(left, right),
        }
    }

    /// Rust's float `%` exactly: C `fmod` / LLVM `frem`, the TRUNCATING
    /// remainder `x - trunc(x / y) * y`, which has the dividend's sign
    /// (`5.0 % 3.0 == 2.0`, `-5.0 % 3.0 == -2.0`, `-6.0 % 3.0 == -0.0`).
    ///
    /// SMT-LIB `fp.rem` is a different function, the IEEE 754 remainder
    /// `x - n * y` with `n = roundTiesToEven(x / y)`: `fp.rem(5, 3) = -1`.
    /// Lowering `%` to `fp.rem` alone verified the false `5 % 3 < 0` (f32
    /// and f64) and refuted the true `5 % 3 == 2` and `0 <= x => 0 <= x % 3`
    /// (TRUST-VC-FREM-1; the same defect as trust-ir's TRUST-IR-AY-FREM-1,
    /// whose encoding and proof this mirrors). The encoding is
    ///
    /// ```text
    /// r    = fp.rem(x, y)
    /// fmod = ite(!isZero(r) && !isNaN(r) && isNegative(r) != isNegative(x),
    ///            fp.add(RNE, r, ite(isNegative(x), -|y|, |y|)),
    ///            r)
    /// ```
    ///
    /// **Why this is `fmod` (finite `x`, finite nonzero `y`).** Both functions
    /// are odd in `x` (negating `x` negates the quotient; round-to-nearest-even
    /// and truncation are both symmetric about zero) and even in `y`
    /// (negating `y` negates `n`, so `n * y` is unchanged); a zero result
    /// takes the sign of `x` in both. With `a = |x|`, `b = |y|` and `s` the
    /// sign of `x`: `fmod(x, y) = s * fmod(a, b)` and
    /// `fp.rem(x, y) = s * rem(a, b)`. Let `t = floor(a / b)`, so
    /// `fmod(a, b) = a - t * b`, in `[0, b)`. Round-to-nearest picks `n = t`
    /// or `n = t + 1` (a tie lands on either, by parity).
    ///
    /// * `n = t`: `rem(a, b) = fmod(a, b) >= 0`, so `r` is zero or has the
    ///   sign of `x`, and is already `fmod`.
    /// * `n = t + 1`: `rem(a, b) = fmod(a, b) - b`, in `[-b/2, 0)`: nonzero,
    ///   opposite in sign to `a`, and `fmod(a, b) = rem(a, b) + b`.
    ///
    /// So "`r` nonzero, not NaN, and opposite in sign to `x`" is exactly the
    /// `n = t + 1` case, where `fmod(x, y) = r + copysign(|y|, x)`.
    /// `copysign` is spelled with `isNegative(x)`, sound because `x` is not
    /// NaN whenever `r` is not.
    ///
    /// **Why the add is EXACT.** Its real sum is `fmod(x, y)`, which is a
    /// float, so RNE (any rounding mode) returns it unrounded. It is a float:
    /// with `Q` the smaller of the operands' quanta, `a`, `b` and
    /// `a - t * b` are integer multiples of `Q`, and `fmod(a, b) <= a`,
    /// `fmod(a, b) < b`; divided by `Q` it is at most the integral
    /// significand of the operand with quantum `Q`, below `2^p`. A multiple
    /// of `Q` (at or above the format's least quantum) with fewer than `p`
    /// significant bits is representable. The sum lies in `s * [b/2, b)`:
    /// nonzero, so no signed-zero rounding question arises.
    ///
    /// **Special operands** never take the corrected branch, and `fp.rem`
    /// already agrees with `fmod` on them: `x` or `y` NaN, `x` infinite, or
    /// `y` zero give NaN (the guard excludes a NaN `r`); `y` infinite with `x`
    /// finite gives `x` in both (same sign as `x`, branch not taken); a zero
    /// `x` with nonzero `y`, and an exact multiple, give a zero with the sign
    /// of `x` in both (excluded by `isZero(r)`).
    ///
    /// `encoder/tests/float_rem_fmod.rs` pins concrete cases bit for bit to
    /// Rust's own `%`, and `tests/float_rem_fmod_soundness.rs` the end-to-end
    /// verdicts.
    fn encode_float_fmod(&mut self, x: Term, y: Term) -> TrustVcResult<Term> {
        fp_fmod(self.solver, x, y).map_err(|e| e.to_string().into())
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
        let is_shift = matches!(op, SpecialArithOp::Shl | SpecialArithOp::Shr);
        // A closed untyped-literal tree that met no peer and holds a value
        // beyond `i32` (`4294967295 ^ 2`) has no `i32` reading: it is its exact
        // value (`ir_lowering::types`).
        if !is_shift {
            let node = TrustVcExpr::SpecialArith {
                op,
                left: Box::new(left.clone()),
                right: Box::new(right.clone()),
                ty: ty.clone(),
            };
            if crate::ir_lowering::is_untyped_literal(&node)
                && !crate::ir_lowering::untyped_literal_fits(&node, &TrustVcType::Int { width: 32 })
            {
                if let Some(value) = crate::ir_lowering::untyped_literal_value(&node) {
                    return self.encode_int_lit(value, &TrustVcType::MathInt);
                }
            }
        }
        if is_shift {
            let node = TrustVcExpr::SpecialArith {
                op,
                left: Box::new(left.clone()),
                right: Box::new(right.clone()),
                ty: ty.clone(),
            };
            self.check_untyped_nonconstant_form_in_every_type(&node, ty)?;
        }
        // Bitwise operands are typed like arithmetic operands: an untyped
        // literal takes its peer's type only when it fits (`encode_arith`).
        // A shift's amount is independent of its value operand.
        let (left_hint_ty, right_hint_ty) = if is_shift {
            (None, None)
        } else {
            let (l, r) = crate::ir_lowering::binary_operand_types(left, right, ty);
            (Some(l), Some(r))
        };
        let left_term = self.encode_expr_with_integer_hint(left, left_hint_ty.as_ref())?;
        let right_term = self.encode_expr_with_integer_hint(right, right_hint_ty.as_ref())?;

        if self.int_mode() {
            return self.encode_int_special_arith(op, left, right, left_term, right_term, ty);
        }
        let collect_side_checks = self.quantifier_depth == 0;

        if is_shift {
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

        let (left_value_ty, right_value_ty) = (
            left_hint_ty.unwrap_or(TrustVcType::Unit),
            right_hint_ty.unwrap_or(TrustVcType::Unit),
        );
        // Operands of DIFFERENT fixed-width types (`x: u8 | y: i16`): the
        // derived type is `int`, and the value is the exact two's-complement
        // result over the integers — each operand extended by its OWN sign to a
        // width holding both (`max(w + [unsigned])`), where `& | ^` cannot
        // overflow, then read signed. The node's `ty` (which the syn lowering
        // copied from the left operand) used to register the wider result as
        // unsigned: `0u8 | (-1i16)` compared as 65535.
        if crate::ir_lowering::is_fixed_width_int(&left_value_ty)
            && crate::ir_lowering::is_fixed_width_int(&right_value_ty)
            && left_value_ty != right_value_ty
        {
            let own_left = self.own_sign(left, Some(&left_value_ty));
            let own_right = self.own_sign(right, Some(&right_value_ty));
            return self.encode_mixed_bitwise_exact(
                op,
                (left_term, own_left),
                (right_term, own_right),
            );
        }
        let derived = crate::ir_lowering::derive_binary_int_type(left, right, ty);
        // Each operand is widened by its OWN type's signedness only (an
        // operand whose own type fixes none is refused, never given its
        // peer's or the derived type's), and the result carries the derived
        // type's.
        let own_left = self.own_sign(left, Some(&left_value_ty));
        let own_right = self.own_sign(right, Some(&right_value_ty));
        let (left_term, right_term) =
            self.coerce_bv_widths_signed((left_term, own_left), (right_term, own_right))?;
        let result_signed =
            ir_type_signedness(&derived).or(own_left.get().filter(|_| own_left == own_right));
        let coerced_width_info = self
            .bv_term_width(left_term)
            .or_else(|| self.bv_term_width(right_term))
            .zip(result_signed);

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

    /// `left op right` for `& | ^` over operands of two DIFFERENT fixed-width
    /// types, as the exact integer (Int-sorted): each operand is extended by
    /// its own type's sign to `W = max(width + [unsigned])` bits, where every
    /// value of both types is a signed `W`-bit number and the bitwise result of
    /// two such numbers is one too, and the result is read signed.
    fn encode_mixed_bitwise_exact(
        &mut self,
        op: SpecialArithOp,
        (left, left_own): (Term, OwnSign),
        (right, right_own): (Term, OwnSign),
    ) -> TrustVcResult<Term> {
        let needed = |this: &Self, term: Term, own: OwnSign| -> TrustVcResult<u32> {
            let width = this
                .bv_term_width(term)
                .ok_or_else(|| "mixed-type bitwise operand is not a bit-vector".to_string())?;
            let signed = own
                .get()
                .ok_or_else(|| "mixed-type bitwise operand has no signedness".to_string())?;
            Ok(width + u32::from(!signed))
        };
        let width = needed(self, left, left_own)?.max(needed(self, right, right_own)?);
        let left = self.widen_bv_to(left, width, left_own)?;
        let right = self.widen_bv_to(right, width, right_own)?;
        let bits = match op {
            SpecialArithOp::BitAnd => self.solver.try_bvand(left, right),
            SpecialArithOp::BitOr => self.solver.try_bvor(left, right),
            SpecialArithOp::BitXor => self.solver.try_bvxor(left, right),
            SpecialArithOp::Shl | SpecialArithOp::Shr => {
                return Err("shift is not a mixed-type bitwise operation"
                    .to_string()
                    .into())
            }
        }
        .map_err(|e| e.to_string())?;
        // Built here as a two's-complement pattern of both operands' signed
        // `width`-bit readings: read signed by construction.
        self.lift_bv_operand_to_int(bits, OwnSign::of_constructed(true))
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
        let left_ty = crate::ir_lowering::infer_expr_type(left);
        let lhs_width = left_ty
            .bit_width()
            .or_else(|| ty.bit_width())
            .or_else(|| self.bv_term_width(left_term))
            .ok_or_else(|| "shift overflow check requires known LHS bit width".to_string())?;
        // Width and signedness from the IR types only: with neither `ty` nor
        // the LHS type fixing them, the result is left unregistered rather
        // than inheriting whatever `term_widths` says about a hash-consed LHS.
        let result_width_info = ty
            .bit_width()
            .map(|width| (width, !ty.is_unsigned()))
            .or_else(|| {
                left_ty
                    .bit_width()
                    .map(|width| (width, !left_ty.is_unsigned()))
            });

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

        let rhs_own = self.own_sign(right, None);
        let shift_amount = self.coerce_shift_amount_to_lhs_width(right_term, lhs_width, rhs_own)?;
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

    /// Bring a shift amount to the LHS width without changing what it shifts.
    ///
    /// The width is the amount's sort; the extension sign is its IR type's
    /// (`rhs_signed`), never a `term_widths` entry. SMT-LIB reads a shift
    /// amount as UNSIGNED, and an amount whose sign bit is set is at least
    /// `2^(w-1) >= 128` for every `w >= 8`, which already exceeds every LHS
    /// width either extension could produce — so an amount whose type fixes
    /// no sign is zero-extended with no change of meaning.
    fn coerce_shift_amount_to_lhs_width(
        &mut self,
        shift_amount: Term,
        lhs_width: u32,
        rhs_own: OwnSign,
    ) -> TrustVcResult<Term> {
        if lhs_width == 0 {
            return Err("shift amount coercion requires nonzero LHS bit width"
                .to_string()
                .into());
        }
        let Some(rhs_width) = self.bv_term_width(shift_amount) else {
            return Ok(shift_amount);
        };
        // The amount's own sign; one whose type fixes none is read as SMT-LIB
        // reads every amount — unsigned (same shift, see above).
        let rhs_own = if rhs_own.get().is_some() {
            rhs_own
        } else {
            OwnSign::of_constructed(false)
        };
        if rhs_width == lhs_width {
            return Ok(shift_amount);
        }
        if rhs_width < lhs_width {
            return self.widen_bv_to(shift_amount, lhs_width, rhs_own);
        }
        // An amount WIDER than the value is never truncated. Bit extraction
        // made `1u8 << 256u16` the shift by `256 mod 256 == 0`, so it verified
        // `== 1` while `1u8 << 8u32` verified `== 0` — two semantics at once.
        // The one semantics (SMT-LIB's, which `by(bit_vector)` documents and
        // Verus uses): the amount is read unsigned at its own width, and an
        // amount `>= lhs_width` shifts every bit out. Saturate it to
        // `lhs_width` (representable in `lhs_width` bits) before narrowing, so
        // `bvshl`/`bvlshr` give 0 and `bvashr` the sign fill, exactly as the
        // full-width amount would.
        let solver = &mut *self.solver;
        let saturated = (|| {
            let bound = solver.try_bv_const(i64::from(lhs_width), rhs_width)?;
            let over = solver.try_bvuge(shift_amount, bound)?;
            let low = solver.try_bvextract(shift_amount, lhs_width - 1, 0)?;
            let full = solver.try_bv_const(i64::from(lhs_width), lhs_width)?;
            solver.try_ite(over, full, low)
        })()
        .map_err(|e| e.to_string())?;
        self.term_widths.insert(saturated, (lhs_width, false));
        Ok(saturated)
    }
}

/// The term [`AstExpressionParser::encode_float_fmod`] documents: Rust's float
/// `%` (C `fmod`) over the FloatingPoint terms `x` and `y`, built as
/// `fp.rem(x, y)` plus its exact one-step correction.
fn fp_fmod(
    solver: &mut ay_dpll::api::Solver,
    x: Term,
    y: Term,
) -> Result<Term, ay_dpll::api::SolverError> {
    let r = solver.try_fp_rem(x, y)?;
    let r_zero = solver.try_fp_is_zero(r)?;
    let r_nan = solver.try_fp_is_nan(r)?;
    let r_unadjusted = solver.try_or(r_zero, r_nan)?;
    let r_ordinary = solver.try_not(r_unadjusted)?;
    let r_negative = solver.try_fp_is_negative(r)?;
    let x_negative = solver.try_fp_is_negative(x)?;
    let sign_differs = solver.try_xor(r_negative, x_negative)?;
    let overshot = solver.try_and(r_ordinary, sign_differs)?;
    // copysign(|y|, x)
    let y_magnitude = solver.try_fp_abs(y)?;
    let y_magnitude_negated = solver.try_fp_neg(y_magnitude)?;
    let step = solver.try_ite(x_negative, y_magnitude_negated, y_magnitude)?;
    let rne = solver.try_fp_rounding_mode("RNE")?;
    let corrected = solver.try_fp_add(rne, r, step)?;
    solver.try_ite(overshot, corrected, r)
}
