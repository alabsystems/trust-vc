// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::types::fits_in_signed_bv;
use super::super::AYEncoder;

impl AYEncoder {
    /// Attempts to evaluate a prepared typed condition as a constant boolean.
    ///
    /// Returns `Some(true)` for conditions that are trivially true (e.g.,
    /// `BoolLit(true)`, integer comparisons on literals). This allows the
    /// solver short-circuit in `verify_assertion` to work with the typed
    /// path now that string-based const-eval is no longer reachable (#1927).
    ///
    /// `context_width` is the inferred BV width from the variable context.
    /// Unsuffixed integer literals default to `Int{32}`, but the verification
    /// context may use a narrower type (e.g., `i8`). When both operands are
    /// default-typed, the context width prevents false constant folding
    /// (e.g., `128 > 127` is true in i32 but false in i8 where 128 wraps
    /// to -128). Fixes #2094.
    pub(in super::super) fn try_const_eval_typed(
        expr: &crate::ir::TrustVcExpr,
        context_width: u32,
    ) -> Option<bool> {
        use crate::ir::{TrustVcExpr, TrustVcType};
        match expr {
            TrustVcExpr::BoolLit(b) => Some(*b),
            TrustVcExpr::Compare { op, left, right } => {
                if matches!(
                    (left.as_ref(), right.as_ref()),
                    (TrustVcExpr::UnitLit, TrustVcExpr::UnitLit)
                ) {
                    use crate::ir::CompareOp;
                    return match op {
                        CompareOp::Eq => Some(true),
                        CompareOp::Ne => Some(false),
                        _ => None,
                    };
                }
                if let Some(result) = try_compare_by_computed_value(op, left, right) {
                    return Some(result);
                }
                if let Some(result) = try_compare_by_datatype_constructor_fields(op, left, right) {
                    return Some(result);
                }
                if let (
                    TrustVcExpr::IntLit { value: l, ty: l_ty },
                    TrustVcExpr::IntLit { value: r, ty: r_ty },
                ) = (left.as_ref(), right.as_ref())
                {
                    if !Self::value_fits_in_type(*l, l_ty) || !Self::value_fits_in_type(*r, r_ty) {
                        return None;
                    }
                    if context_width < 32 {
                        let l_default = matches!(l_ty, TrustVcType::Int { width: 32 });
                        let r_default = matches!(r_ty, TrustVcType::Int { width: 32 });
                        if (l_default && !fits_in_signed_bv(*l, context_width))
                            || (r_default && !fits_in_signed_bv(*r, context_width))
                        {
                            return None;
                        }
                    }
                    use crate::ir::CompareOp;
                    let unsigned = matches!(l_ty, TrustVcType::Uint { .. })
                        && matches!(r_ty, TrustVcType::Uint { .. });
                    if unsigned {
                        let lu = *l as u128;
                        let ru = *r as u128;
                        Some(match op {
                            CompareOp::Eq => lu == ru,
                            CompareOp::Ne => lu != ru,
                            CompareOp::Lt => lu < ru,
                            CompareOp::Le => lu <= ru,
                            CompareOp::Gt => lu > ru,
                            CompareOp::Ge => lu >= ru,
                        })
                    } else {
                        Some(match op {
                            CompareOp::Eq => l == r,
                            CompareOp::Ne => l != r,
                            CompareOp::Lt => l < r,
                            CompareOp::Le => l <= r,
                            CompareOp::Gt => l > r,
                            CompareOp::Ge => l >= r,
                        })
                    }
                } else {
                    None
                }
            }
            TrustVcExpr::Logic { op, left, right } => {
                use crate::ir::LogicOp;
                let l = Self::try_const_eval_typed(left, context_width);
                match (op, l) {
                    (LogicOp::And, Some(false)) => return Some(false),
                    (LogicOp::Or, Some(true)) => return Some(true),
                    _ => {}
                }
                let r = Self::try_const_eval_typed(right, context_width);
                match (op, l, r) {
                    (LogicOp::And, Some(l), Some(r)) => Some(l && r),
                    (LogicOp::Or, Some(l), Some(r)) => Some(l || r),
                    (LogicOp::And, _, Some(false)) => Some(false),
                    (LogicOp::Or, _, Some(true)) => Some(true),
                    _ => None,
                }
            }
            TrustVcExpr::Not(inner) => Self::try_const_eval_typed(inner, context_width).map(|b| !b),
            TrustVcExpr::Implies {
                premise,
                conclusion,
            } => {
                let p = Self::try_const_eval_typed(premise, context_width);
                if p == Some(false) {
                    return Some(true);
                }
                let c = Self::try_const_eval_typed(conclusion, context_width);
                if c == Some(true) {
                    return Some(true);
                }
                match (p, c) {
                    (Some(p), Some(c)) => Some(!p || c),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Recursively evaluate a TrustVcExpr to an integer value.
    ///
    /// Used by Compute mode to fully reduce arithmetic expressions before
    /// comparison. Returns `None` for symbolic variables, function calls,
    /// or any expression that cannot be reduced to a concrete integer.
    /// Part of #2405.
    pub(in super::super) fn try_reduce_to_int(expr: &crate::ir::TrustVcExpr) -> Option<i128> {
        use crate::ir::TrustVcExpr;
        match expr {
            TrustVcExpr::IntLit { value, ty } => {
                Self::value_fits_in_type(*value, ty).then_some(*value)
            }
            TrustVcExpr::Neg(inner) => Self::try_reduce_to_int(inner).and_then(|v| v.checked_neg()),
            TrustVcExpr::Not(inner) => try_reduce_bitwise_not(inner),
            TrustVcExpr::Arith {
                op,
                left,
                right,
                ty,
            } => {
                let l = Self::try_reduce_to_int(left)?;
                let r = Self::try_reduce_to_int(right)?;
                let left_ty = crate::ir_lowering::infer_expr_type(left);
                let right_ty = crate::ir_lowering::infer_expr_type(right);
                if !Self::value_fits_in_type(l, &left_ty) || !Self::value_fits_in_type(r, &right_ty)
                {
                    return None;
                }
                let value = try_reduce_arith_op(*op, l, r, ty)?;
                Self::value_fits_in_type(value, ty).then_some(value)
            }
            TrustVcExpr::Ite {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let c = Self::try_compute_eval(cond)?;
                if c {
                    Self::try_reduce_to_int(then_branch)
                } else {
                    Self::try_reduce_to_int(else_branch)
                }
            }
            TrustVcExpr::Let {
                name,
                ty,
                value,
                body,
            } => {
                if !let_value_reduces(value, ty) {
                    return None;
                }
                let substituted = substitute_let_binding(name, value, body);
                Self::try_reduce_to_int(&substituted)
            }
            TrustVcExpr::SpecialArith {
                op,
                left,
                right,
                ty,
            } => try_reduce_special_arith(*op, left, right, ty),
            TrustVcExpr::Cast { expr, to_ty, .. } => {
                let value = Self::try_reduce_to_int(expr)?;
                Self::value_fits_in_type(value, to_ty).then_some(value)
            }
            TrustVcExpr::CollectionOp { .. } | TrustVcExpr::Index { .. } => {
                match try_reduce_to_value(expr)? {
                    ComputedValue::Int(value) => Some(value),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Evaluate a boolean TrustVcExpr by reducing arithmetic sub-expressions.
    ///
    /// More aggressive than `try_const_eval_typed`: attempts to reduce
    /// arithmetic operands to integers before comparing, enabling evaluation
    /// of `2 + 3 == 5` which `try_const_eval_typed` cannot handle (it
    /// requires both sides to already be `IntLit`). Part of #2405.
    pub(in super::super) fn try_compute_eval(expr: &crate::ir::TrustVcExpr) -> Option<bool> {
        use crate::ir::{CompareOp, TrustVcExpr};
        match expr {
            TrustVcExpr::BoolLit(b) => Some(*b),
            TrustVcExpr::Compare { op, left, right } => {
                if matches!(
                    (left.as_ref(), right.as_ref()),
                    (TrustVcExpr::UnitLit, TrustVcExpr::UnitLit)
                ) {
                    return match op {
                        CompareOp::Eq => Some(true),
                        CompareOp::Ne => Some(false),
                        _ => None,
                    };
                }
                if let Some(result) = try_compare_by_structural_equality(op, left, right) {
                    return Some(result);
                }
                if let Some(result) = try_compare_by_computed_value(op, left, right) {
                    return Some(result);
                }
                if let Some(result) = try_compare_by_datatype_constructor_fields(op, left, right) {
                    return Some(result);
                }
                let l = Self::try_reduce_to_int(left)?;
                let r = Self::try_reduce_to_int(right)?;
                Some(match op {
                    CompareOp::Eq => l == r,
                    CompareOp::Ne => l != r,
                    CompareOp::Lt => l < r,
                    CompareOp::Le => l <= r,
                    CompareOp::Gt => l > r,
                    CompareOp::Ge => l >= r,
                })
            }
            TrustVcExpr::Logic { op, left, right } => {
                use crate::ir::LogicOp;
                let l = Self::try_compute_eval(left);
                match (op, l) {
                    (LogicOp::And, Some(false)) => return Some(false),
                    (LogicOp::Or, Some(true)) => return Some(true),
                    _ => {}
                }
                let r = Self::try_compute_eval(right);
                match (op, l, r) {
                    (LogicOp::And, Some(l), Some(r)) => Some(l && r),
                    (LogicOp::Or, Some(l), Some(r)) => Some(l || r),
                    (LogicOp::And, _, Some(false)) => Some(false),
                    (LogicOp::Or, _, Some(true)) => Some(true),
                    _ => None,
                }
            }
            TrustVcExpr::Not(inner) => Self::try_compute_eval(inner).map(|b| !b),
            TrustVcExpr::Implies {
                premise,
                conclusion,
            } => {
                let p = Self::try_compute_eval(premise);
                if p == Some(false) {
                    return Some(true);
                }
                let c = Self::try_compute_eval(conclusion);
                if c == Some(true) {
                    return Some(true);
                }
                match (p, c) {
                    (Some(p), Some(c)) => Some(!p || c),
                    _ => None,
                }
            }
            TrustVcExpr::Ite {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                if Self::try_compute_eval(cond)? {
                    Self::try_compute_eval(then_branch)
                } else {
                    Self::try_compute_eval(else_branch)
                }
            }
            TrustVcExpr::Let {
                name,
                ty,
                value,
                body,
            } => {
                if !let_value_reduces(value, ty) {
                    return None;
                }
                let substituted = substitute_let_binding(name, value, body);
                Self::try_compute_eval(&substituted)
            }
            TrustVcExpr::CollectionOp { .. }
            | TrustVcExpr::FnCall { .. }
            | TrustVcExpr::Index { .. }
            | TrustVcExpr::Match { .. } => match try_reduce_to_value(expr)? {
                ComputedValue::Bool(value) => Some(value),
                _ => None,
            },
            TrustVcExpr::Quantifier {
                kind,
                bound_vars,
                body,
                triggers,
                ..
            } => try_compute_bounded_quantifier(*kind, bound_vars, body, triggers.as_ref()),
            _ => None,
        }
    }

    /// Returns true if `value` can be represented in the BV range for `ty`.
    pub(in super::super) fn value_fits_in_type(value: i128, ty: &crate::ir::TrustVcType) -> bool {
        use crate::ir::TrustVcType;
        match ty {
            TrustVcType::Int { width } => fits_in_signed_bv(value, *width),
            TrustVcType::Uint { width } => {
                if *width == 0 {
                    return false;
                }
                if value < 0 {
                    return false;
                }
                if *width >= 128 {
                    return true;
                }
                (value as u128) < (1u128 << width)
            }
            TrustVcType::Char => is_unicode_scalar_value(value),
            TrustVcType::MathInt => true,
            TrustVcType::Nat => value >= 0,
            _ => false,
        }
    }

    /// Constant-fold the overflow verdict for an all-constant fixed-width
    /// arithmetic operation.
    ///
    /// When both operands reduce to concrete integers and the result type is a
    /// finite-width integer (`iN`/`uN`), this computes the *exact* unbounded
    /// mathematical result and reports whether it lies outside the result
    /// type's range — i.e. whether the bare `+`/`-`/`*` would overflow in exec
    /// mode. This is a sound shortcut for the symbolic
    /// `bvadd_no_overflow`/etc. checks, which currently return SAT with an
    /// empty model for fully-ground queries (an ay-dpll CEGQI artifact rather
    /// than a real verdict).
    ///
    /// Returns `None` when any operand is non-constant, the result type is not
    /// a fixed-width integer, or the exact result cannot be represented in
    /// `i128` (e.g. `u128 * u128`) — in which case the caller keeps the
    /// symbolic solver check and never claims a constant-folded verdict.
    ///
    /// Soundness: only literal operands whose values fit their own declared
    /// types are folded, and the exact-fit decision uses the same range
    /// predicate (`value_fits_in_type`) as the rest of the encoder. Mirrors
    /// Rust/Verus fixed-width overflow semantics exactly (#2778, upstream
    /// `overflow.rs` `test_const_fail`/`test_static_fail`/
    /// `test_literal_out_of_range`).
    pub(in super::super) fn try_const_fold_arith_overflow(
        op: crate::ir::ArithOp,
        left: &crate::ir::TrustVcExpr,
        right: &crate::ir::TrustVcExpr,
        result_ty: &crate::ir::TrustVcType,
    ) -> Option<ConstFoldOverflowVerdict> {
        use crate::ir::{ArithOp, TrustVcType};

        // Only fixed-width integer results carry overflow obligations. MathInt,
        // Nat, Real, etc. never overflow and must not be folded here.
        let (width, _unsigned) = match result_ty {
            TrustVcType::Int { width } => (*width, false),
            TrustVcType::Uint { width } => (*width, true),
            _ => return None,
        };
        if width == 0 {
            return None;
        }

        let l = Self::try_reduce_to_int(left)?;
        let r = Self::try_reduce_to_int(right)?;

        // Guard: operand literals must themselves fit their declared types.
        // `try_reduce_to_int` already enforces this, but the operand types may
        // differ from `result_ty` (mixed-width arithmetic, casts). We require
        // the *operands* to be representable in `result_ty` too, since the
        // exec-mode obligation is over the result type's width. Default-typed
        // (`i32`) bare literals are coerced to the result type below.
        let exact = exact_unbounded_result(op, l, r)?;

        let overflows = !Self::value_fits_in_type(exact, result_ty);

        // Division/remainder by a constant zero is a separate (div-by-zero)
        // obligation, not an arithmetic-overflow one; let the dedicated
        // div0 path own that case rather than reporting it as overflow.
        if matches!(op, ArithOp::Div | ArithOp::Rem) && r == 0 {
            return None;
        }

        Some(ConstFoldOverflowVerdict {
            exact,
            overflows,
            width,
        })
    }
}

/// Definite, constant-folded overflow verdict for an all-constant fixed-width
/// arithmetic operation. See [`AYEncoder::try_const_fold_arith_overflow`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in super::super) struct ConstFoldOverflowVerdict {
    /// Exact unbounded mathematical result of the operation.
    pub(in super::super) exact: i128,
    /// Whether `exact` lies outside the result type's representable range.
    pub(in super::super) overflows: bool,
    /// Bit width of the result type (for diagnostics).
    pub(in super::super) width: u32,
}

/// Exact unbounded integer result of `left op right`, or `None` if it cannot
/// be represented in `i128` (so the caller defers to the symbolic check).
fn exact_unbounded_result(op: crate::ir::ArithOp, left: i128, right: i128) -> Option<i128> {
    use crate::ir::ArithOp;
    match op {
        ArithOp::Add => left.checked_add(right),
        ArithOp::Sub => left.checked_sub(right),
        ArithOp::Mul => left.checked_mul(right),
        // Division/remainder can only overflow in the signed MIN / -1 case,
        // which is exactly captured by the exact i128 quotient escaping the
        // result range (e.g. i8::MIN / -1 == 128, outside i8). `checked_div`
        // already rules out the divide-by-zero panic; a zero divisor is
        // handled by the div0 obligation and filtered out by the caller.
        ArithOp::Div => left.checked_div(right),
        ArithOp::Rem => left.checked_rem(right),
    }
}

fn is_unicode_scalar_value(value: i128) -> bool {
    u32::try_from(value).ok().and_then(char::from_u32).is_some()
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ComputedValue {
    Bool(bool),
    Int(i128),
    Unit,
    Seq(Vec<ComputedValue>),
    Datatype {
        type_name: String,
        variant_name: String,
        fields: Vec<(String, ComputedValue)>,
    },
}

fn try_reduce_to_value(expr: &crate::ir::TrustVcExpr) -> Option<ComputedValue> {
    use crate::ir::TrustVcExpr;

    match expr {
        TrustVcExpr::BoolLit(value) => Some(ComputedValue::Bool(*value)),
        TrustVcExpr::IntLit { value, ty } => {
            AYEncoder::value_fits_in_type(*value, ty).then_some(ComputedValue::Int(*value))
        }
        TrustVcExpr::UnitLit => Some(ComputedValue::Unit),
        TrustVcExpr::Arith { .. }
        | TrustVcExpr::Neg(_)
        | TrustVcExpr::SpecialArith { .. }
        | TrustVcExpr::WrappingArith { .. } => {
            AYEncoder::try_reduce_to_int(expr).map(ComputedValue::Int)
        }
        TrustVcExpr::Cast {
            expr,
            from_ty,
            to_ty,
        } => {
            if matches!(
                to_ty,
                crate::ir::TrustVcType::Seq(_) | crate::ir::TrustVcType::Array(_, _)
            ) {
                return try_reduce_collection_cast_to_value(expr, from_ty, to_ty);
            }
            let value = AYEncoder::try_reduce_to_int(expr)?;
            AYEncoder::value_fits_in_type(value, to_ty).then_some(ComputedValue::Int(value))
        }
        TrustVcExpr::Not(inner) => {
            if let Some(value) = try_reduce_to_bool_value(inner) {
                Some(ComputedValue::Bool(!value))
            } else {
                AYEncoder::try_reduce_to_int(expr).map(ComputedValue::Int)
            }
        }
        TrustVcExpr::Compare { op, left, right } => {
            try_compute_compare(*op, left, right).map(ComputedValue::Bool)
        }
        TrustVcExpr::Logic { op, left, right } => {
            use crate::ir::LogicOp;
            let left = try_reduce_to_bool_value(left);
            match (op, left) {
                (LogicOp::And, Some(false)) => return Some(ComputedValue::Bool(false)),
                (LogicOp::Or, Some(true)) => return Some(ComputedValue::Bool(true)),
                _ => {}
            }
            let right = try_reduce_to_bool_value(right);
            match (op, left, right) {
                (LogicOp::And, Some(left), Some(right)) => Some(ComputedValue::Bool(left && right)),
                (LogicOp::Or, Some(left), Some(right)) => Some(ComputedValue::Bool(left || right)),
                (LogicOp::And, _, Some(false)) => Some(ComputedValue::Bool(false)),
                (LogicOp::Or, _, Some(true)) => Some(ComputedValue::Bool(true)),
                _ => None,
            }
        }
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            let premise = try_reduce_to_bool_value(premise);
            if premise == Some(false) {
                return Some(ComputedValue::Bool(true));
            }
            let conclusion = try_reduce_to_bool_value(conclusion);
            if conclusion == Some(true) {
                return Some(ComputedValue::Bool(true));
            }
            match (premise, conclusion) {
                (Some(premise), Some(conclusion)) => {
                    Some(ComputedValue::Bool(!premise || conclusion))
                }
                _ => None,
            }
        }
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            if try_reduce_to_bool_value(cond)? {
                try_reduce_to_value(then_branch)
            } else {
                try_reduce_to_value(else_branch)
            }
        }
        TrustVcExpr::Let {
            name,
            ty,
            value,
            body,
        } => {
            if !let_value_reduces(value, ty) {
                return None;
            }
            let substituted = substitute_let_binding(name, value, body);
            try_reduce_to_value(&substituted)
        }
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } if args.is_empty()
            && AYEncoder::collection_constructor_is_empty(name)
            && matches!(
                return_ty,
                crate::ir::TrustVcType::Seq(_) | crate::ir::TrustVcType::Array(_, _)
            ) =>
        {
            Some(ComputedValue::Seq(Vec::new()))
        }
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => try_reduce_datatype_call_to_value(name, args, return_ty),
        TrustVcExpr::CollectionOp { .. } => try_reduce_collection_to_value(expr),
        TrustVcExpr::Index { .. } => try_reduce_index_to_value(expr),
        TrustVcExpr::Match {
            scrutinee, arms, ..
        } => try_reduce_match_to_value(scrutinee, arms),
        TrustVcExpr::Quantifier {
            kind,
            bound_vars,
            body,
            triggers,
            ..
        } => try_compute_bounded_quantifier(*kind, bound_vars, body, triggers.as_ref())
            .map(ComputedValue::Bool),
        TrustVcExpr::Var { .. }
        | TrustVcExpr::StringLit(_)
        | TrustVcExpr::IntConst { .. }
        | TrustVcExpr::SpecClosure { .. }
        | TrustVcExpr::Choose { .. }
        | TrustVcExpr::ReadPlace { .. }
        | TrustVcExpr::PlaceDisjoint { .. }
        | TrustVcExpr::ProphecyNew { .. }
        | TrustVcExpr::ProphecyResolve { .. } => None,
    }
}

const COMPUTE_QUANTIFIER_ENUM_LIMIT: usize = 512;

fn try_compute_bounded_quantifier(
    kind: crate::ir::QuantifierKind,
    bound_vars: &[(String, crate::ir::TrustVcType)],
    body: &crate::ir::TrustVcExpr,
    triggers: Option<&Vec<Vec<crate::ir::TrustVcExpr>>>,
) -> Option<bool> {
    if triggers.is_some_and(|groups| !groups.is_empty()) {
        return None;
    }
    let [(var_name, var_ty)] = bound_vars else {
        return None;
    };
    let (guard, value_body) = split_bounded_quantifier_body(kind, body);
    let values = bounded_integer_witnesses(var_name, var_ty, guard)?;

    match kind {
        crate::ir::QuantifierKind::Forall => {
            for value in values {
                if !eval_quantifier_instance(var_name, var_ty, value_body, value)? {
                    return Some(false);
                }
            }
            Some(true)
        }
        crate::ir::QuantifierKind::Exists => {
            for value in values {
                if eval_quantifier_instance(var_name, var_ty, value_body, value)? {
                    return Some(true);
                }
            }
            Some(false)
        }
    }
}

fn split_bounded_quantifier_body(
    kind: crate::ir::QuantifierKind,
    body: &crate::ir::TrustVcExpr,
) -> (Option<&crate::ir::TrustVcExpr>, &crate::ir::TrustVcExpr) {
    match (kind, body) {
        (
            crate::ir::QuantifierKind::Forall,
            crate::ir::TrustVcExpr::Implies {
                premise,
                conclusion,
            },
        ) => (Some(premise), conclusion),
        (
            crate::ir::QuantifierKind::Forall,
            crate::ir::TrustVcExpr::Logic {
                op: crate::ir::LogicOp::Or,
                left,
                right,
            },
        ) => match (left.as_ref(), right.as_ref()) {
            (crate::ir::TrustVcExpr::Not(guard), value_body) => (Some(guard), value_body),
            (value_body, crate::ir::TrustVcExpr::Not(guard)) => (Some(guard), value_body),
            _ => (None, body),
        },
        _ => (None, body),
    }
}

fn eval_quantifier_instance(
    var_name: &str,
    var_ty: &crate::ir::TrustVcType,
    body: &crate::ir::TrustVcExpr,
    value: i128,
) -> Option<bool> {
    let value_expr = crate::ir::TrustVcExpr::IntLit {
        value,
        ty: var_ty.clone(),
    };
    let substituted = substitute_let_binding(var_name, &value_expr, body);
    AYEncoder::try_compute_eval(&substituted)
}

fn bounded_integer_witnesses(
    var_name: &str,
    var_ty: &crate::ir::TrustVcType,
    guard: Option<&crate::ir::TrustVcExpr>,
) -> Option<Vec<i128>> {
    let mut range = IntegerRange::from_type(var_ty)?;
    if let Some(guard) = guard {
        collect_integer_range_constraints(var_name, var_ty, guard, &mut range)?;
    }
    range.to_values(COMPUTE_QUANTIFIER_ENUM_LIMIT)
}

#[derive(Debug, Clone, Copy)]
struct IntegerRange {
    lower: Option<i128>,
    upper: Option<i128>,
}

impl IntegerRange {
    fn from_type(ty: &crate::ir::TrustVcType) -> Option<Self> {
        use crate::ir::TrustVcType;
        match ty {
            TrustVcType::Uint { width } => {
                let upper = if *width < 127 {
                    Some((1i128 << *width) - 1)
                } else {
                    None
                };
                Some(Self {
                    lower: Some(0),
                    upper,
                })
            }
            TrustVcType::Int { width } => {
                if *width == 0 {
                    return None;
                }
                let (lower, upper) = if *width >= 128 {
                    (i128::MIN, i128::MAX)
                } else {
                    let half = 1i128 << (*width - 1);
                    (-half, half - 1)
                };
                Some(Self {
                    lower: Some(lower),
                    upper: Some(upper),
                })
            }
            TrustVcType::Nat => Some(Self {
                lower: Some(0),
                upper: None,
            }),
            TrustVcType::MathInt => Some(Self {
                lower: None,
                upper: None,
            }),
            _ => None,
        }
    }

    fn tighten_lower(&mut self, value: i128) {
        self.lower = Some(self.lower.map_or(value, |current| current.max(value)));
    }

    fn tighten_upper(&mut self, value: i128) {
        self.upper = Some(self.upper.map_or(value, |current| current.min(value)));
    }

    fn to_values(self, limit: usize) -> Option<Vec<i128>> {
        let lower = self.lower?;
        let upper = self.upper?;
        if lower > upper {
            return Some(Vec::new());
        }
        let len = upper.checked_sub(lower)?.checked_add(1)?;
        let len = usize::try_from(len).ok()?;
        if len > limit {
            return None;
        }
        Some((0..len).map(|offset| lower + offset as i128).collect())
    }
}

fn collect_integer_range_constraints(
    var_name: &str,
    var_ty: &crate::ir::TrustVcType,
    expr: &crate::ir::TrustVcExpr,
    range: &mut IntegerRange,
) -> Option<()> {
    match expr {
        crate::ir::TrustVcExpr::Logic {
            op: crate::ir::LogicOp::And,
            left,
            right,
        } => {
            collect_integer_range_constraints(var_name, var_ty, left, range)?;
            collect_integer_range_constraints(var_name, var_ty, right, range)
        }
        crate::ir::TrustVcExpr::Compare { op, left, right } => {
            apply_integer_range_constraint(var_name, var_ty, *op, left, right, range)
        }
        _ => None,
    }
}

fn apply_integer_range_constraint(
    var_name: &str,
    var_ty: &crate::ir::TrustVcType,
    op: crate::ir::CompareOp,
    left: &crate::ir::TrustVcExpr,
    right: &crate::ir::TrustVcExpr,
    range: &mut IntegerRange,
) -> Option<()> {
    if is_var_named(var_name, left) {
        let value = range_constant_for_type(right, var_ty)?;
        return apply_normalized_integer_constraint(op, value, range);
    }
    if is_var_named(var_name, right) {
        let value = range_constant_for_type(left, var_ty)?;
        return apply_normalized_integer_constraint(flip_compare_op(op), value, range);
    }
    None
}

fn is_var_named(var_name: &str, expr: &crate::ir::TrustVcExpr) -> bool {
    matches!(expr, crate::ir::TrustVcExpr::Var { name, .. } if name == var_name)
}

fn range_constant_for_type(
    expr: &crate::ir::TrustVcExpr,
    var_ty: &crate::ir::TrustVcType,
) -> Option<i128> {
    let value = AYEncoder::try_reduce_to_int(expr)?;
    AYEncoder::value_fits_in_type(value, var_ty).then_some(value)
}

fn apply_normalized_integer_constraint(
    op: crate::ir::CompareOp,
    value: i128,
    range: &mut IntegerRange,
) -> Option<()> {
    match op {
        crate::ir::CompareOp::Eq => {
            range.tighten_lower(value);
            range.tighten_upper(value);
            Some(())
        }
        crate::ir::CompareOp::Lt => {
            range.tighten_upper(value.checked_sub(1)?);
            Some(())
        }
        crate::ir::CompareOp::Le => {
            range.tighten_upper(value);
            Some(())
        }
        crate::ir::CompareOp::Gt => {
            range.tighten_lower(value.checked_add(1)?);
            Some(())
        }
        crate::ir::CompareOp::Ge => {
            range.tighten_lower(value);
            Some(())
        }
        crate::ir::CompareOp::Ne => None,
    }
}

fn flip_compare_op(op: crate::ir::CompareOp) -> crate::ir::CompareOp {
    match op {
        crate::ir::CompareOp::Eq => crate::ir::CompareOp::Eq,
        crate::ir::CompareOp::Ne => crate::ir::CompareOp::Ne,
        crate::ir::CompareOp::Lt => crate::ir::CompareOp::Gt,
        crate::ir::CompareOp::Le => crate::ir::CompareOp::Ge,
        crate::ir::CompareOp::Gt => crate::ir::CompareOp::Lt,
        crate::ir::CompareOp::Ge => crate::ir::CompareOp::Le,
    }
}

fn try_reduce_datatype_call_to_value(
    name: &str,
    args: &[crate::ir::TrustVcExpr],
    return_ty: &crate::ir::TrustVcType,
) -> Option<ComputedValue> {
    try_reduce_datatype_selector_to_value(name, args)
        .or_else(|| try_reduce_datatype_tester_to_value(name, args))
        .or_else(|| try_reduce_datatype_constructor_to_value(name, args, return_ty))
}

fn try_reduce_datatype_constructor_to_value(
    name: &str,
    args: &[crate::ir::TrustVcExpr],
    return_ty: &crate::ir::TrustVcType,
) -> Option<ComputedValue> {
    let crate::ir::TrustVcType::Datatype {
        name: type_name,
        variants,
    } = return_ty
    else {
        return None;
    };
    let variant = variants.iter().find(|variant| {
        name == crate::encoder::datatype::variant_symbol_name(type_name, &variant.name)
    })?;
    if variant.fields.len() != args.len() {
        return None;
    }
    let fields = variant
        .fields
        .iter()
        .zip(args)
        .map(|((field_name, _), arg)| Some((field_name.clone(), try_reduce_to_value(arg)?)))
        .collect::<Option<Vec<_>>>()?;

    Some(ComputedValue::Datatype {
        type_name: type_name.clone(),
        variant_name: variant.name.clone(),
        fields,
    })
}

fn try_reduce_datatype_selector_to_value(
    name: &str,
    args: &[crate::ir::TrustVcExpr],
) -> Option<ComputedValue> {
    let [receiver] = args else {
        return None;
    };
    let ComputedValue::Datatype {
        type_name,
        variant_name,
        fields,
    } = try_reduce_to_value(receiver)?
    else {
        return None;
    };

    fields
        .into_iter()
        .enumerate()
        .find_map(|(index, (field_name, value))| {
            let selector = crate::encoder::datatype::selector_symbol_name(
                &type_name,
                &variant_name,
                &field_name,
                index,
            );
            (name == selector).then_some(value)
        })
}

fn try_reduce_datatype_tester_to_value(
    name: &str,
    args: &[crate::ir::TrustVcExpr],
) -> Option<ComputedValue> {
    let [receiver] = args else {
        return None;
    };
    let ComputedValue::Datatype {
        type_name,
        variant_name,
        ..
    } = try_reduce_to_value(receiver)?
    else {
        return None;
    };
    let crate::ir::TrustVcType::Datatype {
        name: receiver_type_name,
        variants,
    } = crate::ir_lowering::infer_expr_type(receiver)
    else {
        return None;
    };
    if receiver_type_name != type_name {
        return None;
    }

    variants.iter().find_map(|variant| {
        let tester = crate::encoder::datatype::tester_symbol_name(&type_name, &variant.name);
        (name == tester).then_some(ComputedValue::Bool(variant.name == variant_name))
    })
}

fn try_reduce_match_to_value(
    scrutinee: &crate::ir::TrustVcExpr,
    arms: &[crate::ir_expr::MatchArm],
) -> Option<ComputedValue> {
    let scrutinee_value = try_reduce_to_value(scrutinee)?;
    let scrutinee_ty = crate::ir_lowering::infer_expr_type(scrutinee);
    for arm in arms {
        if let Some(bindings) =
            match_pattern_bindings(&arm.pattern, &scrutinee_value, &scrutinee_ty)
        {
            // Take a guarded arm only when its guard reduces to `true`; on a concrete
            // `false` fall through; if the guard cannot be reduced, bail (fail closed
            // to symbolic) rather than pick the arm ignoring the guard (TRAP #3).
            if let Some(guard) = &arm.guard {
                let guard_expr = substitute_match_bindings(&bindings, guard);
                match try_reduce_to_value(&guard_expr) {
                    Some(ComputedValue::Bool(true)) => {}
                    Some(ComputedValue::Bool(false)) => continue,
                    _ => return None,
                }
            }
            let body = substitute_match_bindings(&bindings, &arm.body);
            return try_reduce_to_value(&body);
        }
    }
    None
}

fn match_pattern_bindings(
    pattern: &crate::ir_expr::MatchPattern,
    value: &ComputedValue,
    value_ty: &crate::ir::TrustVcType,
) -> Option<std::collections::BTreeMap<String, crate::ir::TrustVcExpr>> {
    use crate::ir_expr::MatchPattern;
    match pattern {
        MatchPattern::Wildcard => Some(std::collections::BTreeMap::new()),
        MatchPattern::Ident(name) => {
            let expr = computed_value_to_expr(value, value_ty)?;
            Some(std::collections::BTreeMap::from([(name.clone(), expr)]))
        }
        MatchPattern::Lit(lit) => {
            (try_reduce_to_value(lit)? == *value).then(std::collections::BTreeMap::new)
        }
        MatchPattern::Constructor {
            variant_name,
            bindings,
            has_rest,
        } => match_constructor_pattern_bindings(variant_name, bindings, *has_rest, value, value_ty),
        MatchPattern::Struct {
            variant_name,
            fields,
            ..
        } => match_struct_pattern_bindings(variant_name, fields, value, value_ty),
        MatchPattern::Or(patterns) => patterns
            .iter()
            .find_map(|pattern| match_pattern_bindings(pattern, value, value_ty)),
    }
}

fn match_constructor_pattern_bindings(
    variant_name: &str,
    bindings: &[String],
    has_rest: bool,
    value: &ComputedValue,
    value_ty: &crate::ir::TrustVcType,
) -> Option<std::collections::BTreeMap<String, crate::ir::TrustVcExpr>> {
    let ComputedValue::Datatype {
        variant_name: value_variant,
        fields,
        ..
    } = value
    else {
        return None;
    };
    // A trailing `..` rest binds only the leading fields; the `zip` below
    // truncates to `bindings.len()`, so relax exact arity to `bindings <=
    // fields` when `has_rest`.
    let arity_ok = if has_rest {
        bindings.len() <= fields.len()
    } else {
        fields.len() == bindings.len()
    };
    if value_variant != variant_name || !arity_ok {
        return None;
    }
    let field_tys = datatype_variant_field_tys(value_ty, variant_name)?;
    let mut result = std::collections::BTreeMap::new();
    for ((binding, (_, field_value)), field_ty) in bindings.iter().zip(fields).zip(field_tys) {
        if crate::match_pattern_scope::is_ignored_match_binding(binding) {
            continue;
        }
        result.insert(
            binding.clone(),
            computed_value_to_expr(field_value, field_ty)?,
        );
    }
    Some(result)
}

fn match_struct_pattern_bindings(
    variant_name: &str,
    fields: &[crate::ir_expr::StructPatternField],
    value: &ComputedValue,
    value_ty: &crate::ir::TrustVcType,
) -> Option<std::collections::BTreeMap<String, crate::ir::TrustVcExpr>> {
    let ComputedValue::Datatype {
        variant_name: value_variant,
        fields: value_fields,
        ..
    } = value
    else {
        return None;
    };
    if value_variant != variant_name {
        return None;
    }
    let mut result = std::collections::BTreeMap::new();
    for field in fields {
        let Some(binding) = &field.binding else {
            continue;
        };
        let (_, field_value) = value_fields
            .iter()
            .find(|(field_name, _)| field_name == &field.field_name)?;
        let field_ty = datatype_field_ty(value_ty, variant_name, field.field_name.as_str())?;
        result.insert(
            binding.clone(),
            computed_value_to_expr(field_value, field_ty)?,
        );
    }
    Some(result)
}

fn datatype_variant_field_tys<'a>(
    ty: &'a crate::ir::TrustVcType,
    variant_name: &str,
) -> Option<Vec<&'a crate::ir::TrustVcType>> {
    let crate::ir::TrustVcType::Datatype { variants, .. } = ty else {
        return None;
    };
    let variant = variants
        .iter()
        .find(|variant| variant.name == variant_name)?;
    Some(
        variant
            .fields
            .iter()
            .map(|(_, field_ty)| field_ty)
            .collect(),
    )
}

fn datatype_field_ty<'a>(
    ty: &'a crate::ir::TrustVcType,
    variant_name: &str,
    field_name: &str,
) -> Option<&'a crate::ir::TrustVcType> {
    let crate::ir::TrustVcType::Datatype { variants, .. } = ty else {
        return None;
    };
    variants
        .iter()
        .find(|variant| variant.name == variant_name)?
        .fields
        .iter()
        .find_map(|(candidate, field_ty)| (candidate == field_name).then_some(field_ty))
}

fn computed_value_to_expr(
    value: &ComputedValue,
    ty: &crate::ir::TrustVcType,
) -> Option<crate::ir::TrustVcExpr> {
    match (value, ty) {
        (ComputedValue::Bool(value), crate::ir::TrustVcType::Bool) => {
            Some(crate::ir::TrustVcExpr::BoolLit(*value))
        }
        (ComputedValue::Int(value), ty)
            if ty.is_integer()
                || matches!(
                    ty,
                    crate::ir::TrustVcType::MathInt | crate::ir::TrustVcType::Nat
                ) =>
        {
            Some(crate::ir::TrustVcExpr::IntLit {
                value: *value,
                ty: ty.clone(),
            })
        }
        (ComputedValue::Unit, crate::ir::TrustVcType::Unit) => {
            Some(crate::ir::TrustVcExpr::UnitLit)
        }
        (
            ComputedValue::Datatype {
                type_name,
                variant_name,
                fields,
            },
            crate::ir::TrustVcType::Datatype { name, variants },
        ) if type_name == name => {
            let variant = variants
                .iter()
                .find(|candidate| candidate.name == *variant_name)?;
            if variant.fields.len() != fields.len() {
                return None;
            }
            let args = fields
                .iter()
                .zip(variant.fields.iter())
                .map(|((_, value), (_, field_ty))| computed_value_to_expr(value, field_ty))
                .collect::<Option<Vec<_>>>()?;
            Some(crate::ir::TrustVcExpr::FnCall {
                name: crate::encoder::datatype::variant_symbol_name(name, variant_name),
                args,
                return_ty: ty.clone(),
            })
        }
        _ => None,
    }
}

fn substitute_match_bindings(
    bindings: &std::collections::BTreeMap<String, crate::ir::TrustVcExpr>,
    body: &crate::ir::TrustVcExpr,
) -> crate::ir::TrustVcExpr {
    let subst = bindings
        .iter()
        .map(|(name, value)| (name.as_str(), value))
        .collect::<std::collections::HashMap<_, _>>();
    super::substitution::substitute_vars_in_expr(body, &subst)
}

fn try_reduce_to_bool_value(expr: &crate::ir::TrustVcExpr) -> Option<bool> {
    match try_reduce_to_value(expr)? {
        ComputedValue::Bool(value) => Some(value),
        _ => None,
    }
}

fn try_compute_compare(
    op: crate::ir::CompareOp,
    left: &crate::ir::TrustVcExpr,
    right: &crate::ir::TrustVcExpr,
) -> Option<bool> {
    use crate::ir::CompareOp;

    if matches!(
        (left, right),
        (
            crate::ir::TrustVcExpr::UnitLit,
            crate::ir::TrustVcExpr::UnitLit
        )
    ) {
        return match op {
            CompareOp::Eq => Some(true),
            CompareOp::Ne => Some(false),
            _ => None,
        };
    }
    if let Some(result) = try_compare_by_computed_value(&op, left, right) {
        return Some(result);
    }
    if let Some(result) = try_compare_by_datatype_constructor_fields(&op, left, right) {
        return Some(result);
    }
    if let Some(result) = try_compare_by_structural_equality(&op, left, right) {
        return Some(result);
    }
    let left = AYEncoder::try_reduce_to_int(left)?;
    let right = AYEncoder::try_reduce_to_int(right)?;
    Some(match op {
        CompareOp::Eq => left == right,
        CompareOp::Ne => left != right,
        CompareOp::Lt => left < right,
        CompareOp::Le => left <= right,
        CompareOp::Gt => left > right,
        CompareOp::Ge => left >= right,
    })
}

fn try_compare_by_computed_value(
    op: &crate::ir::CompareOp,
    left: &crate::ir::TrustVcExpr,
    right: &crate::ir::TrustVcExpr,
) -> Option<bool> {
    use crate::ir::CompareOp;

    if !matches!(op, CompareOp::Eq | CompareOp::Ne) {
        return None;
    }
    let left = try_reduce_to_value(left)?;
    let right = try_reduce_to_value(right)?;
    let equal = left == right;
    Some(matches!(op, CompareOp::Eq) == equal)
}

fn try_compare_by_datatype_constructor_fields(
    op: &crate::ir::CompareOp,
    left: &crate::ir::TrustVcExpr,
    right: &crate::ir::TrustVcExpr,
) -> Option<bool> {
    use crate::ir::CompareOp;

    if !matches!(op, CompareOp::Eq | CompareOp::Ne) {
        return None;
    }
    let left_ctor = datatype_constructor_call(left)?;
    let right_ctor = datatype_constructor_call(right)?;
    if left_ctor.type_name != right_ctor.type_name {
        return None;
    }

    let equal = if left_ctor.variant_name != right_ctor.variant_name {
        false
    } else {
        let mut all_fields_equal = true;
        for (left_arg, right_arg) in left_ctor.args.iter().zip(right_ctor.args.iter()) {
            match try_compute_compare(CompareOp::Eq, left_arg, right_arg) {
                Some(true) => {}
                Some(false) => return Some(matches!(op, CompareOp::Ne)),
                None => all_fields_equal = false,
            }
        }
        if !all_fields_equal {
            return None;
        }
        true
    };

    Some(matches!(op, CompareOp::Eq) == equal)
}

struct DatatypeConstructorCall<'a> {
    type_name: &'a str,
    variant_name: &'a str,
    args: &'a [crate::ir::TrustVcExpr],
}

fn datatype_constructor_call(expr: &crate::ir::TrustVcExpr) -> Option<DatatypeConstructorCall<'_>> {
    let crate::ir::TrustVcExpr::FnCall {
        name,
        args,
        return_ty:
            crate::ir::TrustVcType::Datatype {
                name: type_name,
                variants,
            },
    } = expr
    else {
        return None;
    };
    let variant = variants.iter().find(|variant| {
        name == &crate::encoder::datatype::variant_symbol_name(type_name, &variant.name)
            && variant.fields.len() == args.len()
    })?;
    Some(DatatypeConstructorCall {
        type_name,
        variant_name: &variant.name,
        args,
    })
}

fn try_reduce_collection_to_value(expr: &crate::ir::TrustVcExpr) -> Option<ComputedValue> {
    use crate::ir::{CollectionOp, TrustVcExpr};

    let TrustVcExpr::CollectionOp {
        op, receiver, args, ..
    } = expr
    else {
        return None;
    };

    match op {
        CollectionOp::View => {
            if !args.is_empty() {
                return None;
            }
            try_reduce_to_sequence(receiver).map(ComputedValue::Seq)
        }
        CollectionOp::Len => {
            if !args.is_empty() {
                return None;
            }
            let len = try_reduce_to_sequence(receiver)?.len();
            i128::try_from(len).ok().map(ComputedValue::Int)
        }
        CollectionOp::IsEmpty => {
            if !args.is_empty() {
                return None;
            }
            Some(ComputedValue::Bool(
                try_reduce_to_sequence(receiver)?.is_empty(),
            ))
        }
        CollectionOp::Push => {
            let [arg] = args.as_slice() else {
                return None;
            };
            let mut values = try_reduce_to_sequence(receiver)?;
            values.push(try_reduce_to_value(arg)?);
            Some(ComputedValue::Seq(values))
        }
        CollectionOp::Concat | CollectionOp::Add => {
            let [arg] = args.as_slice() else {
                return None;
            };
            let mut values = try_reduce_to_sequence(receiver)?;
            values.extend(try_reduce_to_sequence(arg)?);
            Some(ComputedValue::Seq(values))
        }
        CollectionOp::Get => {
            let [index] = args.as_slice() else {
                return None;
            };
            let values = try_reduce_to_sequence(receiver)?;
            let index = try_reduce_to_index(index)?;
            values.get(index).cloned()
        }
        CollectionOp::First => {
            if !args.is_empty() {
                return None;
            }
            try_reduce_to_sequence(receiver)?.first().cloned()
        }
        CollectionOp::Last => {
            if !args.is_empty() {
                return None;
            }
            try_reduce_to_sequence(receiver)?.last().cloned()
        }
        CollectionOp::Contains => {
            let [arg] = args.as_slice() else {
                return None;
            };
            let values = try_reduce_to_sequence(receiver)?;
            let needle = try_reduce_to_value(arg)?;
            Some(ComputedValue::Bool(
                values.iter().any(|value| value == &needle),
            ))
        }
        CollectionOp::Update => {
            let [index, value] = args.as_slice() else {
                return None;
            };
            let mut values = try_reduce_to_sequence(receiver)?;
            let index = try_reduce_to_index(index)?;
            let slot = values.get_mut(index)?;
            *slot = try_reduce_to_value(value)?;
            Some(ComputedValue::Seq(values))
        }
        CollectionOp::Subrange => {
            let [start, end] = args.as_slice() else {
                return None;
            };
            let values = try_reduce_to_sequence(receiver)?;
            let start = try_reduce_to_index(start)?;
            let end = try_reduce_to_index(end)?;
            if start > end || end > values.len() {
                return None;
            }
            Some(ComputedValue::Seq(values[start..end].to_vec()))
        }
        _ => None,
    }
}

fn try_reduce_index_to_value(expr: &crate::ir::TrustVcExpr) -> Option<ComputedValue> {
    let crate::ir::TrustVcExpr::Index {
        receiver, index, ..
    } = expr
    else {
        return None;
    };
    let values = try_reduce_to_sequence(receiver)?;
    let index = try_reduce_to_index(index)?;
    values.get(index).cloned()
}

fn try_reduce_to_sequence(expr: &crate::ir::TrustVcExpr) -> Option<Vec<ComputedValue>> {
    match try_reduce_to_value(expr)? {
        ComputedValue::Seq(values) => Some(values),
        _ => None,
    }
}

fn try_reduce_collection_cast_to_value(
    expr: &crate::ir::TrustVcExpr,
    from_ty: &crate::ir::TrustVcType,
    to_ty: &crate::ir::TrustVcType,
) -> Option<ComputedValue> {
    let values = try_reduce_to_sequence(expr)?;
    if !collection_cast_preserves_values(from_ty, to_ty, values.len()) {
        return None;
    }
    Some(ComputedValue::Seq(values))
}

fn collection_cast_preserves_values(
    from_ty: &crate::ir::TrustVcType,
    to_ty: &crate::ir::TrustVcType,
    len: usize,
) -> bool {
    match (from_ty, to_ty) {
        (crate::ir::TrustVcType::Seq(from), crate::ir::TrustVcType::Seq(to)) => from == to,
        (crate::ir::TrustVcType::Array(from, from_len), crate::ir::TrustVcType::Seq(to)) => {
            from == to && *from_len == len
        }
        (crate::ir::TrustVcType::Seq(from), crate::ir::TrustVcType::Array(to, to_len)) => {
            from == to && *to_len == len
        }
        (
            crate::ir::TrustVcType::Array(from, from_len),
            crate::ir::TrustVcType::Array(to, to_len),
        ) => from == to && from_len == to_len && *from_len == len,
        _ => false,
    }
}

fn try_reduce_to_index(expr: &crate::ir::TrustVcExpr) -> Option<usize> {
    let value = AYEncoder::try_reduce_to_int(expr)?;
    let ty = crate::ir_lowering::infer_expr_type(expr);
    if !AYEncoder::value_fits_in_type(value, &ty) {
        return None;
    }
    usize::try_from(value).ok()
}

fn try_compare_by_structural_equality(
    op: &crate::ir::CompareOp,
    left: &crate::ir::TrustVcExpr,
    right: &crate::ir::TrustVcExpr,
) -> Option<bool> {
    use crate::ir::CompareOp;

    if !matches!(op, CompareOp::Eq | CompareOp::Ne) {
        return None;
    }
    if left != right || !is_total_structural_expr(left) {
        return None;
    }

    Some(matches!(op, CompareOp::Eq))
}

fn is_total_structural_expr(expr: &crate::ir::TrustVcExpr) -> bool {
    use crate::ir::TrustVcExpr;

    match expr {
        TrustVcExpr::UnitLit
        | TrustVcExpr::BoolLit(_)
        | TrustVcExpr::StringLit(_)
        | TrustVcExpr::IntLit { .. }
        | TrustVcExpr::Var { .. }
        | TrustVcExpr::IntConst { .. } => true,
        TrustVcExpr::Compare { left, right, .. } | TrustVcExpr::Logic { left, right, .. } => {
            is_total_structural_expr(left) && is_total_structural_expr(right)
        }
        TrustVcExpr::Not(inner) => is_total_structural_expr(inner),
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => is_total_structural_expr(premise) && is_total_structural_expr(conclusion),
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            is_total_structural_expr(cond)
                && is_total_structural_expr(then_branch)
                && is_total_structural_expr(else_branch)
        }
        TrustVcExpr::Let { value, body, .. } => {
            is_total_structural_expr(value) && is_total_structural_expr(body)
        }
        TrustVcExpr::Cast { expr, .. } => is_total_structural_expr(expr),
        TrustVcExpr::FnCall { args, .. } => args.iter().all(is_total_structural_expr),
        TrustVcExpr::Arith { .. }
        | TrustVcExpr::Neg(_)
        | TrustVcExpr::Match { .. }
        | TrustVcExpr::CollectionOp { .. }
        | TrustVcExpr::Index { .. }
        | TrustVcExpr::Quantifier { .. }
        | TrustVcExpr::SpecialArith { .. }
        | TrustVcExpr::WrappingArith { .. }
        | TrustVcExpr::SpecClosure { .. }
        | TrustVcExpr::Choose { .. }
        | TrustVcExpr::ReadPlace { .. }
        | TrustVcExpr::PlaceDisjoint { .. }
        | TrustVcExpr::ProphecyNew { .. }
        | TrustVcExpr::ProphecyResolve { .. } => false,
    }
}

fn let_value_reduces(value: &crate::ir::TrustVcExpr, ty: &crate::ir::TrustVcType) -> bool {
    match ty {
        crate::ir::TrustVcType::Bool => AYEncoder::try_compute_eval(value).is_some(),
        crate::ir::TrustVcType::Int { .. }
        | crate::ir::TrustVcType::Uint { .. }
        | crate::ir::TrustVcType::MathInt
        | crate::ir::TrustVcType::Nat => AYEncoder::try_reduce_to_int(value).is_some(),
        crate::ir::TrustVcType::Char => AYEncoder::try_reduce_to_int(value)
            .is_some_and(|value| AYEncoder::value_fits_in_type(value, ty)),
        crate::ir::TrustVcType::Unit => matches!(value, crate::ir::TrustVcExpr::UnitLit),
        crate::ir::TrustVcType::Seq(_) => {
            matches!(try_reduce_to_value(value), Some(ComputedValue::Seq(_)))
        }
        crate::ir::TrustVcType::Array(_, len) => {
            matches!(try_reduce_to_value(value), Some(ComputedValue::Seq(values)) if values.len() == *len)
        }
        crate::ir::TrustVcType::Datatype { .. } => {
            matches!(
                try_reduce_to_value(value),
                Some(value) if datatype_value_matches_type(&value, ty)
            )
        }
        _ => false,
    }
}

fn datatype_value_matches_type(value: &ComputedValue, ty: &crate::ir::TrustVcType) -> bool {
    let (
        ComputedValue::Datatype {
            type_name,
            variant_name,
            fields,
        },
        crate::ir::TrustVcType::Datatype { name, variants },
    ) = (value, ty)
    else {
        return false;
    };
    if type_name != name {
        return false;
    }
    let Some(variant) = variants
        .iter()
        .find(|candidate| &candidate.name == variant_name)
    else {
        return false;
    };
    variant.fields.len() == fields.len()
        && variant
            .fields
            .iter()
            .zip(fields)
            .all(|((expected_name, _), (actual_name, _))| expected_name == actual_name)
}

fn try_reduce_arith_op(
    op: crate::ir::ArithOp,
    left: i128,
    right: i128,
    ty: &crate::ir::TrustVcType,
) -> Option<i128> {
    if matches!(
        ty,
        crate::ir::TrustVcType::MathInt | crate::ir::TrustVcType::Nat
    ) {
        return try_reduce_math_integer_arith_op(op, left, right);
    }

    use crate::ir::ArithOp;
    match op {
        ArithOp::Add => left.checked_add(right),
        ArithOp::Sub => left.checked_sub(right),
        ArithOp::Mul => left.checked_mul(right),
        ArithOp::Div => left.checked_div(right),
        ArithOp::Rem => left.checked_rem(right),
    }
}

fn try_reduce_math_integer_arith_op(
    op: crate::ir::ArithOp,
    left: i128,
    right: i128,
) -> Option<i128> {
    use crate::ir::ArithOp;
    match op {
        ArithOp::Add => left.checked_add(right),
        ArithOp::Sub => left.checked_sub(right),
        ArithOp::Mul => left.checked_mul(right),
        ArithOp::Div => checked_div_euclid_i128(left, right),
        ArithOp::Rem => checked_rem_euclid_i128(left, right),
    }
}

fn checked_div_euclid_i128(left: i128, right: i128) -> Option<i128> {
    let quotient = left.checked_div(right)?;
    let remainder = left.checked_rem(right)?;
    if remainder < 0 {
        if right > 0 {
            quotient.checked_sub(1)
        } else {
            quotient.checked_add(1)
        }
    } else {
        Some(quotient)
    }
}

fn checked_rem_euclid_i128(left: i128, right: i128) -> Option<i128> {
    let remainder = left.checked_rem(right)?;
    if remainder < 0 {
        remainder.checked_add(right.checked_abs()?)
    } else {
        Some(remainder)
    }
}

fn substitute_let_binding(
    name: &str,
    value: &crate::ir::TrustVcExpr,
    body: &crate::ir::TrustVcExpr,
) -> crate::ir::TrustVcExpr {
    let subst = std::collections::HashMap::from([(name, value)]);
    super::substitution::substitute_vars_in_expr(body, &subst)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct FiniteInt {
    bits: u128,
    width: u32,
    is_unsigned: bool,
}

impl FiniteInt {
    fn from_expr(expr: &crate::ir::TrustVcExpr) -> Option<Self> {
        let value = AYEncoder::try_reduce_to_int(expr)?;
        let ty = crate::ir_lowering::infer_expr_type(expr);
        Self::from_value(value, &ty)
    }

    fn from_value(value: i128, ty: &crate::ir::TrustVcType) -> Option<Self> {
        use crate::ir::TrustVcType;

        let (width, is_unsigned) = match ty {
            TrustVcType::Int { width } => (*width, false),
            TrustVcType::Uint { width } => (*width, true),
            _ => return None,
        };
        if !AYEncoder::value_fits_in_type(value, ty) {
            return None;
        }
        let mask = mask_for_width(width)?;
        Some(Self {
            bits: (value as u128) & mask,
            width,
            is_unsigned,
        })
    }

    fn from_bits_for_type(bits: u128, ty: &crate::ir::TrustVcType) -> Option<Self> {
        use crate::ir::TrustVcType;

        let (width, is_unsigned) = match ty {
            TrustVcType::Int { width } => (*width, false),
            TrustVcType::Uint { width } => (*width, true),
            _ => return None,
        };
        let mask = mask_for_width(width)?;
        Some(Self {
            bits: bits & mask,
            width,
            is_unsigned,
        })
    }

    fn same_type_shape(self, other: Self) -> bool {
        self.width == other.width && self.is_unsigned == other.is_unsigned
    }

    fn with_bits(self, bits: u128) -> Option<Self> {
        let mask = mask_for_width(self.width)?;
        Some(Self {
            bits: bits & mask,
            ..self
        })
    }

    fn to_i128(self) -> Option<i128> {
        if self.is_unsigned {
            if self.bits <= i128::MAX as u128 {
                Some(self.bits as i128)
            } else {
                None
            }
        } else {
            bits_to_signed_i128(self.bits, self.width)
        }
    }
}

fn try_reduce_bitwise_not(expr: &crate::ir::TrustVcExpr) -> Option<i128> {
    let value = FiniteInt::from_expr(expr)?;
    value.with_bits(!value.bits)?.to_i128()
}

fn try_reduce_special_arith(
    op: crate::ir::SpecialArithOp,
    left: &crate::ir::TrustVcExpr,
    right: &crate::ir::TrustVcExpr,
    ty: &crate::ir::TrustVcType,
) -> Option<i128> {
    use crate::ir::SpecialArithOp;

    let left_value = FiniteInt::from_expr(left)?;
    let result_type = FiniteInt::from_bits_for_type(0, ty)?;
    if !left_value.same_type_shape(result_type) {
        return None;
    }

    let result_bits = match op {
        SpecialArithOp::BitAnd | SpecialArithOp::BitOr | SpecialArithOp::BitXor => {
            let right_value = FiniteInt::from_expr(right)?;
            if !left_value.same_type_shape(right_value) {
                return None;
            }
            match op {
                SpecialArithOp::BitAnd => left_value.bits & right_value.bits,
                SpecialArithOp::BitOr => left_value.bits | right_value.bits,
                SpecialArithOp::BitXor => left_value.bits ^ right_value.bits,
                _ => unreachable!(),
            }
        }
        SpecialArithOp::Shl => {
            let amount = checked_shift_amount(right, left_value.width)?;
            left_value.bits.checked_shl(amount)?
        }
        SpecialArithOp::Shr => {
            let amount = checked_shift_amount(right, left_value.width)?;
            if left_value.is_unsigned {
                left_value.bits >> amount
            } else {
                let shifted = left_value.to_i128()?.checked_shr(amount)?;
                (shifted as u128) & mask_for_width(left_value.width)?
            }
        }
    };

    result_type.with_bits(result_bits)?.to_i128()
}

fn checked_shift_amount(expr: &crate::ir::TrustVcExpr, width: u32) -> Option<u32> {
    let value = AYEncoder::try_reduce_to_int(expr)?;
    let ty = crate::ir_lowering::infer_expr_type(expr);
    FiniteInt::from_value(value, &ty)?;
    if value < 0 || value >= i128::from(width) {
        return None;
    }
    u32::try_from(value).ok()
}

fn mask_for_width(width: u32) -> Option<u128> {
    match width {
        0 => None,
        1..=127 => Some((1u128 << width) - 1),
        128 => Some(u128::MAX),
        _ => None,
    }
}

fn bits_to_signed_i128(bits: u128, width: u32) -> Option<i128> {
    let bits = bits & mask_for_width(width)?;
    if width == 128 {
        return Some(bits as i128);
    }

    let sign_bit = 1u128 << (width - 1);
    if bits & sign_bit == 0 {
        return i128::try_from(bits).ok();
    }

    let modulus = 1u128 << width;
    let magnitude = modulus.checked_sub(bits)?;
    i128::try_from(magnitude).ok()?.checked_neg()
}
