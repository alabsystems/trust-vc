//! The value of an exec arithmetic-safety SITE whose type this obligation
//! does not see (design-trust-proof-backend.md §5b rule 2).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! A panic-safety obligation for an exec arithmetic site is the reflexive
//! `(v) == (v)` over the site's value alone, cut out of the expression it
//! stands in: the call it is an argument of, the field it initializes, the
//! comparison it is an operand of, the binding a later use types. When `v`
//! is an UNTYPED literal form (`200 + 100`, or `*r + 100` once `let a = 200;
//! let r = &a;` is substituted), Rust types its literals by that context,
//! which the obligation does not hold, so the form meets no peer here and is
//! computed at its `i32` placeholder. A form that holds a conditional is
//! checked in every width by the encoder; a CONSTANT one used to be left to
//! the compiler, whose `arithmetic_overflow` lint neither sees through a
//! borrow or a closure capture (`g8(*r + 100)`) nor fires where the lint is
//! allowed (`#[allow(arithmetic_overflow)] g8(200 + 100)`) — both compile
//! and panic, and both were `Verified`.
//!
//! A constant form at such a site is therefore evaluated, with Rust's checked
//! semantics, in every fixed-width type all its literals fit; if it panics
//! in any of them its type decides the verdict, and the obligation is
//! refused (`Unknown`). Its `i32` reading is still checked by the encoder.
//! A site whose slot type the extractor reads (a parameter, an inferred
//! binding type) is typed there instead (`__trust_vc_slot_typed::<T>`), and
//! never reaches this marker as an untyped form.
//!
//! The BINDING an unascribed `let a = 200;` makes has one type, which Rust
//! infers from all its uses; the extractor binds its value at that type
//! where the uses determine it, and otherwise marks it
//! (`__trust_vc_untyped_binding`): the value is lowered as a conditional with
//! one value, `if true { 200 } else { 200 }`, so wherever it meets no peer the
//! encoder checks it in every type it may take
//! (`check_untyped_nonconstant_form_in_every_type`), where a form that is a
//! constant once such conditionals are collapsed is refused when it panics
//! in one of them. Read bare, `let a = 200; let r = &a; assert!(*r + 100 >
//! 0); g8(a);` checked `200 + 100` in `i32` and was `Verified`.

use super::{
    infer_expr_type, is_untyped_literal, lower_syn_expr_with_depth,
    trust_vc_type_from_syn_type_with_env, untyped_form_is_conditional, untyped_literal_at_peer,
    untyped_literal_fits, LoweringError, TypeEnv, SLOT_TYPED_MARKER, UNTYPED_BINDING_MARKER,
    UNTYPED_SITE_MARKER,
};
use crate::ir::TrustVcType;
use crate::ir_expr::{ArithOp, SpecialArithOp, TrustVcExpr};

/// Lower `__trust_vc_untyped_site(value)`: `value`, refused when it is a
/// constant untyped literal form that panics in a fixed-width type it may
/// take (module doc). `None` for any other call.
pub(super) fn lower_untyped_site_marker(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    if path.qself.is_some()
        || path.path.segments.len() != 1
        || path.path.segments[0].ident != UNTYPED_SITE_MARKER
    {
        return Ok(None);
    }
    let (Some(value), 1) = (call.args.first(), call.args.len()) else {
        return Err(LoweringError::TypeInference(
            "arithmetic-site marker takes one value".into(),
        ));
    };
    let lowered = lower_syn_expr_with_depth(value, env, depth)?;
    if let Some(ty) = constant_form_panicking_type(&lowered) {
        return Err(LoweringError::UnsupportedExpr(format!(
            "`{}` is an untyped integer literal form whose type is fixed where its value \
             is used (a parameter, a field, a binding typed by a later use), which this \
             check does not read; it panics as `{}`",
            quote::ToTokens::to_token_stream(value),
            ty.to_type_string()
        )));
    }
    Ok(Some(lowered))
}

/// Lower `__trust_vc_slot_typed::<T>(value)`: an untyped literal form
/// `value` typed at the fixed-width `T` of the slot it fills (refused when a
/// literal of it does not fit `T`: Rust rejects the literal, or wraps it
/// where the lint is allowed); any other value as it is — its own type is
/// the slot's in a program the compiler accepts. `None` for any other call.
pub(super) fn lower_slot_typed_marker(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let Some(segment) = path.path.segments.last() else {
        return Ok(None);
    };
    if path.qself.is_some() || path.path.segments.len() != 1 || segment.ident != SLOT_TYPED_MARKER {
        return Ok(None);
    }
    let slot = match &segment.arguments {
        syn::PathArguments::AngleBracketed(args) if args.args.len() == 1 => {
            match args.args.first() {
                Some(syn::GenericArgument::Type(ty)) => {
                    trust_vc_type_from_syn_type_with_env(ty, env)?
                }
                _ => {
                    return Err(LoweringError::TypeInference(
                        "slot marker takes one type".into(),
                    ))
                }
            }
        }
        _ => {
            return Err(LoweringError::TypeInference(
                "slot marker takes one type".into(),
            ))
        }
    };
    let (Some(value), 1) = (call.args.first(), call.args.len()) else {
        return Err(LoweringError::TypeInference(
            "slot marker takes one value".into(),
        ));
    };
    let lowered = lower_syn_expr_with_depth(value, env, depth)?;
    if !is_untyped_literal(&lowered) {
        return Ok(Some(lowered));
    }
    match untyped_literal_at_peer(&lowered, &slot) {
        Some(typed) => Ok(Some(pin_untyped_at_i32(typed))),
        None => Err(LoweringError::UnsupportedExpr(format!(
            "`{}` is an untyped integer literal form filling a slot of type `{}` that one of \
             its literals does not fit",
            quote::ToTokens::to_token_stream(value),
            slot.to_type_string()
        ))),
    }
}

/// `value` — an untyped literal form typed at a slot — pinned by an identity
/// cast when that slot is `i32`, whose literals are the untyped placeholder:
/// a form the source types `i32` is no untyped form a later peer may retype
/// (§5b rule 7). Any other value is returned unchanged.
pub(crate) fn pin_untyped_at_i32(value: TrustVcExpr) -> TrustVcExpr {
    let i32_ty = TrustVcType::Int { width: 32 };
    if !is_untyped_literal(&value) || infer_expr_type(&value) != i32_ty {
        return value;
    }
    TrustVcExpr::Cast {
        expr: Box::new(value),
        from_ty: i32_ty.clone(),
        to_ty: i32_ty,
    }
}

/// Lower `__trust_vc_untyped_binding(value)`: an untyped literal form
/// `value` as the one-valued conditional `if true { value } else { value }`
/// (module doc); any other value as it is. `None` for any other call.
pub(super) fn lower_untyped_binding_marker(
    path: &syn::ExprPath,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    if path.qself.is_some()
        || path.path.segments.len() != 1
        || path.path.segments[0].ident != UNTYPED_BINDING_MARKER
    {
        return Ok(None);
    }
    let (Some(value), 1) = (call.args.first(), call.args.len()) else {
        return Err(LoweringError::TypeInference(
            "untyped-binding marker takes one value".into(),
        ));
    };
    let lowered = lower_syn_expr_with_depth(value, env, depth)?;
    if !is_untyped_literal(&lowered) {
        return Ok(Some(lowered));
    }
    Ok(Some(TrustVcExpr::Ite {
        cond: Box::new(TrustVcExpr::BoolLit(true)),
        then_branch: Box::new(lowered.clone()),
        ty: infer_expr_type(&lowered),
        else_branch: Box::new(lowered),
    }))
}

/// Whether `expr` holds the one-valued conditional of an untyped binding
/// (`lower_untyped_binding_marker`) anywhere: the element of an array whose
/// element type its uses do not determine.
pub(crate) fn holds_undetermined_form(expr: &TrustVcExpr) -> bool {
    use crate::ir_expr_traversal::{walk_expr, TrustVcExprVisitor};
    struct Finder {
        found: bool,
    }
    impl TrustVcExprVisitor for Finder {
        fn visit_expr(&mut self, expr: &TrustVcExpr) {
            if let TrustVcExpr::Ite {
                cond,
                then_branch,
                else_branch,
                ..
            } = expr
            {
                if matches!(cond.as_ref(), TrustVcExpr::BoolLit(true))
                    && then_branch == else_branch
                    && is_untyped_literal(then_branch)
                {
                    self.found = true;
                    return;
                }
            }
            walk_expr(self, expr);
        }
    }
    let mut finder = Finder { found: false };
    finder.visit_expr(expr);
    finder.found
}

/// `expr` with every one-valued conditional of an untyped binding
/// (`lower_untyped_binding_marker`'s `if true { v } else { v }`) replaced by
/// its value, through the operations of an untyped literal form.
pub(crate) fn collapse_undetermined_forms(expr: &TrustVcExpr) -> TrustVcExpr {
    match expr {
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ..
        } if matches!(cond.as_ref(), TrustVcExpr::BoolLit(true)) && then_branch == else_branch => {
            collapse_undetermined_forms(then_branch)
        }
        TrustVcExpr::Neg(inner) => TrustVcExpr::Neg(Box::new(collapse_undetermined_forms(inner))),
        TrustVcExpr::Arith {
            op,
            left,
            right,
            ty,
        } => TrustVcExpr::Arith {
            op: *op,
            left: Box::new(collapse_undetermined_forms(left)),
            right: Box::new(collapse_undetermined_forms(right)),
            ty: ty.clone(),
        },
        TrustVcExpr::SpecialArith {
            op,
            left,
            right,
            ty,
        } => TrustVcExpr::SpecialArith {
            op: *op,
            left: Box::new(collapse_undetermined_forms(left)),
            right: Box::new(collapse_undetermined_forms(right)),
            ty: ty.clone(),
        },
        other => other.clone(),
    }
}

/// A fixed-width type other than the `i32` placeholder that the CONSTANT
/// untyped literal form `expr` (once its untyped bindings' one-valued
/// conditionals are collapsed) may take and in which evaluating it panics.
/// `None` for any other value.
pub(crate) fn constant_form_panicking_type(expr: &TrustVcExpr) -> Option<TrustVcType> {
    let expr = &collapse_undetermined_forms(expr);
    if !is_untyped_literal(expr) || untyped_form_is_conditional(expr) {
        return None;
    }
    for width in [8, 16, 32, 64, 128] {
        for ty in [TrustVcType::Int { width }, TrustVcType::Uint { width }] {
            if ty == infer_expr_type(expr) || !untyped_literal_fits(expr, &ty) {
                continue;
            }
            if checked_value_in(expr, &ty).is_none() {
                return Some(ty);
            }
        }
    }
    None
}

/// `expr` (an untyped literal form that fits `ty`) evaluated in `ty` as
/// overflow-checked Rust evaluates it: `None` where Rust panics — an
/// operation whose result `ty` cannot hold, a zero divisor, a signed `MIN /
/// -1` or `MIN % -1`, a shift by an amount of at least `ty`'s width or a
/// negative one, a negated unsigned value — and where the `i128` oracle
/// cannot hold a value.
fn checked_value_in(expr: &TrustVcExpr, ty: &TrustVcType) -> Option<i128> {
    let (width, signed) = match ty {
        TrustVcType::Int { width } => (*width, true),
        TrustVcType::Uint { width } => (*width, false),
        _ => return None,
    };
    let holds = |value: i128| super::type_holds_integer(ty, value) == Some(true);
    let fits = |value: i128| holds(value).then_some(value);
    match expr {
        TrustVcExpr::IntLit { value, .. } => Some(*value),
        TrustVcExpr::Neg(inner) => match inner.as_ref() {
            // `-128` is the literal -128 (Rust reads `-128i8` so).
            TrustVcExpr::IntLit { value, .. } => fits(value.checked_neg()?),
            inner => fits(checked_value_in(inner, ty)?.checked_neg()?),
        },
        TrustVcExpr::Arith {
            op, left, right, ..
        } => {
            let (l, r) = (checked_value_in(left, ty)?, checked_value_in(right, ty)?);
            let exact = match op {
                ArithOp::Add => l.checked_add(r)?,
                ArithOp::Sub => l.checked_sub(r)?,
                ArithOp::Mul => l.checked_mul(r)?,
                ArithOp::Div | ArithOp::Rem if r == 0 => return None,
                ArithOp::Div => l.checked_div(r)?,
                // `MIN % -1` panics in Rust although its value (0) fits.
                ArithOp::Rem if signed && r == -1 && !holds(l.checked_neg()?) => return None,
                ArithOp::Rem => l.checked_rem(r)?,
            };
            fits(exact)
        }
        TrustVcExpr::SpecialArith {
            op, left, right, ..
        } => match op {
            SpecialArithOp::BitAnd | SpecialArithOp::BitOr | SpecialArithOp::BitXor => {
                let (l, r) = (checked_value_in(left, ty)?, checked_value_in(right, ty)?);
                fits(match op {
                    SpecialArithOp::BitAnd => l & r,
                    SpecialArithOp::BitOr => l | r,
                    _ => l ^ r,
                })
            }
            SpecialArithOp::Shl | SpecialArithOp::Shr => {
                let value = checked_value_in(left, ty)?;
                let TrustVcExpr::IntLit { value: amount, .. } = right.as_ref() else {
                    return None;
                };
                if *amount < 0 || *amount >= i128::from(width) {
                    return None;
                }
                let amount = u32::try_from(*amount).ok()?;
                let shifted = if matches!(op, SpecialArithOp::Shr) {
                    value >> amount
                } else {
                    value.checked_shl(amount)?
                };
                wrap_into(shifted, width, signed)
            }
        },
        _ => None,
    }
}

/// `value` truncated to `width` bits and read with `signed`'s sign (a left
/// shift's result in Rust).
fn wrap_into(value: i128, width: u32, signed: bool) -> Option<i128> {
    if width >= 128 {
        return Some(value);
    }
    let modulus = 1i128 << width;
    let low = value.rem_euclid(modulus);
    Some(if signed && low >= modulus / 2 {
        low - modulus
    } else {
        low
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(value: i128) -> TrustVcExpr {
        TrustVcExpr::IntLit {
            value,
            ty: TrustVcType::Int { width: 32 },
        }
    }

    fn arith(op: ArithOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
        TrustVcExpr::Arith {
            op,
            left: Box::new(left),
            right: Box::new(right),
            ty: TrustVcType::Int { width: 32 },
        }
    }

    fn shift(op: SpecialArithOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
        TrustVcExpr::SpecialArith {
            op,
            left: Box::new(left),
            right: Box::new(right),
            ty: TrustVcType::Int { width: 32 },
        }
    }

    #[test]
    fn a_constant_form_that_overflows_a_narrow_type_names_it() {
        assert_eq!(
            constant_form_panicking_type(&arith(ArithOp::Add, lit(200), lit(100))),
            Some(TrustVcType::Uint { width: 8 })
        );
        assert_eq!(
            constant_form_panicking_type(&arith(ArithOp::Add, lit(100), lit(100))),
            Some(TrustVcType::Int { width: 8 })
        );
        assert_eq!(
            constant_form_panicking_type(&arith(ArithOp::Sub, lit(1), lit(2))),
            Some(TrustVcType::Uint { width: 8 })
        );
        assert_eq!(
            constant_form_panicking_type(&shift(SpecialArithOp::Shl, lit(1), lit(10))),
            Some(TrustVcType::Int { width: 8 })
        );
        assert_eq!(
            constant_form_panicking_type(&arith(ArithOp::Div, lit(1), lit(0))),
            Some(TrustVcType::Int { width: 8 })
        );
    }

    #[test]
    fn a_constant_form_safe_in_every_type_it_fits_is_kept() {
        assert_eq!(
            constant_form_panicking_type(&arith(ArithOp::Add, lit(20), lit(100))),
            None
        );
        assert_eq!(
            constant_form_panicking_type(&shift(SpecialArithOp::Shl, lit(1), lit(6))),
            None
        );
        // A lone literal, or a value that is not an untyped form, is no site
        // for this check.
        assert_eq!(constant_form_panicking_type(&lit(300)), None);
        assert_eq!(
            constant_form_panicking_type(&TrustVcExpr::IntLit {
                value: 200,
                ty: TrustVcType::Uint { width: 8 },
            }),
            None
        );
    }

    #[test]
    fn a_checked_value_follows_rust_panics() {
        let i8t = TrustVcType::Int { width: 8 };
        assert_eq!(
            checked_value_in(
                &TrustVcExpr::Neg(Box::new(lit(128))),
                &TrustVcType::Int { width: 8 }
            ),
            Some(-128)
        );
        // `-128 / -1` and `-128 % -1` panic in `i8`.
        let min = TrustVcExpr::Neg(Box::new(lit(128)));
        let minus_one = TrustVcExpr::Neg(Box::new(lit(1)));
        assert_eq!(
            checked_value_in(&arith(ArithOp::Div, min.clone(), minus_one.clone()), &i8t),
            None
        );
        assert_eq!(
            checked_value_in(&arith(ArithOp::Rem, min, minus_one), &i8t),
            None
        );
        assert_eq!(
            checked_value_in(
                &shift(SpecialArithOp::Shl, lit(1), lit(7)),
                &TrustVcType::Int { width: 8 }
            ),
            Some(-128)
        );
    }
}
