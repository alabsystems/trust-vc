//! TrustVcExpr type inference: the type of an integer operation is DERIVED.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # Integer typing rules (design-trust-proof-backend.md §5b)
//!
//! The type of an arithmetic (`+ - * / %`), bitwise (`& | ^`) or
//! conditional (`if c { a } else { b }`) node is derived from its OPERANDS —
//! never copied from its left operand, its then-branch, or a producer's
//! `ty` field that disagrees with them:
//!
//! * both operands of ONE fixed-width type `T` → `T` (the machine model:
//!   two's complement in `T`; exec obligations additionally check overflow);
//! * fixed-width operands of DIFFERENT types (`u8 + i16`) → `int`. Rust cannot
//!   express this (it is a type error in exec code); Verus types it as spec
//!   arithmetic over the mathematical integers, so the result is the EXACT
//!   integer — each operand is read with its own type's signedness;
//! * an `int`/`nat` operand or declared type → exact: `nat` when every
//!   operand is a `nat` (and the operation is not `-`), else `int` — a
//!   declared `nat` never makes a join `nat` by itself;
//! * anything else (datatypes, type parameters, …) keeps the declared type and
//!   the encoder refuses what it cannot model.
//!
//! An unsuffixed literal (the `Int { width: 32 }` placeholder) takes the type
//! of the peer it meets ONLY when its value is a value of that type — Rust's
//! own inference for an unsuffixed literal, which never changes the literal's
//! value. A negative literal therefore never becomes unsigned, and a literal
//! out of the peer's range keeps its own (default) type, making the operation
//! mixed → exact. A closed tree of such literals ([`is_untyped_literal`])
//! takes the peer's type when EVERY literal in it does, and its operations are
//! then that type's (Rust types the literals, not the tree's value:
//! `y != 200 + 100` with `y: u8` is `u8` arithmetic, which overflows).

use crate::ir::TrustVcType;
use crate::ir_expr::{ArithOp, SpecialArithOp, TrustVcExpr};

/// Best-effort type inference from a TrustVcExpr.
///
/// Integer operations report their DERIVED type (module doc); every other
/// node reports the type it carries.
pub(crate) fn infer_expr_type(expr: &TrustVcExpr) -> TrustVcType {
    match expr {
        TrustVcExpr::UnitLit => TrustVcType::Unit,
        TrustVcExpr::BoolLit(_)
        | TrustVcExpr::Compare { .. }
        | TrustVcExpr::Logic { .. }
        | TrustVcExpr::Implies { .. }
        | TrustVcExpr::Quantifier { .. } => TrustVcType::Bool,
        // `!` is overloaded: logical-not over a `bool` yields `bool`, but
        // bitwise-not over a finite-width integer (`!x` where `x: i32`) yields
        // that integer type. Reporting `bool` for the bitwise case mis-typed a
        // surrounding `(!x) as i64` cast as `bool as i64`, which routed to the
        // bool→int lowering and fed a `BitVec` term into an `ite` condition
        // ("sort mismatch in ite: expected Bool, got (_ BitVec N)"). Mirror the
        // `Neg` rule: propagate an integer operand's type, fall back to `bool`.
        TrustVcExpr::Not(inner) => {
            let inner_ty = infer_expr_type(inner);
            if inner_ty.is_integer() {
                inner_ty
            } else {
                TrustVcType::Bool
            }
        }
        TrustVcExpr::StringLit(_) => TrustVcType::StrSlice,
        TrustVcExpr::Arith {
            op,
            left,
            right,
            ty,
        } => arith_result_type(*op, derive_binary_int_type(left, right, ty)),
        TrustVcExpr::SpecialArith {
            op: SpecialArithOp::BitAnd | SpecialArithOp::BitOr | SpecialArithOp::BitXor,
            left,
            right,
            ty,
        } => derive_binary_int_type(left, right, ty),
        TrustVcExpr::SpecialArith {
            op: SpecialArithOp::Shl | SpecialArithOp::Shr,
            left,
            ty,
            ..
        } => derive_shift_type(left, ty),
        TrustVcExpr::Ite {
            then_branch,
            else_branch,
            ty,
            ..
        } => derive_binary_int_type(then_branch, else_branch, ty),
        TrustVcExpr::Match { arms, ty, .. } => {
            let bodies = arms.iter().map(|arm| &arm.body).collect::<Vec<_>>();
            derive_arms_int_type(&bodies, ty).1
        }
        TrustVcExpr::IntLit { ty, .. }
        | TrustVcExpr::Var { ty, .. }
        | TrustVcExpr::CollectionOp { ty, .. }
        | TrustVcExpr::SpecClosure { ty, .. }
        | TrustVcExpr::IntConst { ty, .. }
        | TrustVcExpr::WrappingArith { ty, .. } => ty.clone(),
        // The negation of a `nat` is an `int` (`-x` for `x == 1` is not a
        // `nat`); it was typed `nat`, so `let v: nat = -x` was accepted.
        TrustVcExpr::Neg(inner) => match infer_expr_type(inner) {
            TrustVcType::Nat => TrustVcType::MathInt,
            other => other,
        },
        TrustVcExpr::Let { body, .. } => infer_expr_type(body),
        TrustVcExpr::Cast { to_ty, .. } => to_ty.clone(),
        TrustVcExpr::Index { elem_ty, .. } => elem_ty.clone(),
        TrustVcExpr::FnCall { return_ty, .. } => return_ty.clone(),
        TrustVcExpr::Choose { var_ty, .. } => var_ty.clone(),
        TrustVcExpr::ReadPlace { ty, .. } => ty.clone(),
        TrustVcExpr::PlaceDisjoint { .. } => TrustVcType::Bool,
        TrustVcExpr::ProphecyNew { ty, .. } => ty.clone(),
        TrustVcExpr::ProphecyResolve { value, .. } => infer_expr_type(value),
    }
}

/// The unsuffixed-literal placeholder type. A literal the source TYPES `i32`
/// (`200i32`) is pinned by an identity cast (`ir_lowering::atoms::lower_lit`),
/// as is an `i32` value substituted for a variable
/// ([`pin_substituted_value`]): a bare `Int { width: 32 }` literal is read as
/// the placeholder.
pub(crate) const PLACEHOLDER: TrustVcType = TrustVcType::Int { width: 32 };

/// Whether `expr` is an UNTYPED literal form: an `Int { width: 32 }` integer
/// literal, or a tree of them under unary `-`, `+ - * / %`, `& | ^` and the
/// conditionals (`if c { 200 } else { 0 }`, a `match` whose every arm is
/// such a form, whatever the condition or scrutinee), every interior node
/// itself typed `Int { width: 32 }`. Rust types every literal of the form by
/// the one peer the form meets. A conditional used to be read as a value of
/// its placeholder type, so `(if c { 200 } else { 200 }) + y` (`y: u8 ==
/// 100`) was a mixed `i32 + u8`, hence EXACT, addition: no overflow
/// obligation, and `a + y == 300` held.
///
/// A SHIFT whose value operand is such a form (`1 << k`, `255 >> k`) is one
/// too, whatever its amount: its value has its LEFT operand's type, which
/// the peer the shift meets fixes, while the amount is typed apart. Read as
/// an `i32` value, `(1 << k) + y` (`k == 7`, `y: u8 == 200`) was a mixed,
/// hence exact, addition, and `g8(1 << k)` (`k == 8`) never checked the `u8`
/// shift.
pub(crate) fn is_untyped_literal(expr: &TrustVcExpr) -> bool {
    match expr {
        TrustVcExpr::IntLit { ty, .. } => *ty == PLACEHOLDER,
        TrustVcExpr::Neg(inner) => is_untyped_literal(inner),
        TrustVcExpr::SpecialArith {
            op: SpecialArithOp::Shl | SpecialArithOp::Shr,
            left,
            ty,
            ..
        } => *ty == PLACEHOLDER && is_untyped_literal(left),
        TrustVcExpr::Arith {
            left, right, ty, ..
        }
        | TrustVcExpr::SpecialArith {
            op: SpecialArithOp::BitAnd | SpecialArithOp::BitOr | SpecialArithOp::BitXor,
            left,
            right,
            ty,
        } => *ty == PLACEHOLDER && is_untyped_literal(left) && is_untyped_literal(right),
        TrustVcExpr::Ite {
            then_branch,
            else_branch,
            ty,
            ..
        } => {
            *ty == PLACEHOLDER && is_untyped_literal(then_branch) && is_untyped_literal(else_branch)
        }
        TrustVcExpr::Match { arms, ty, .. } => {
            *ty == PLACEHOLDER
                && !arms.is_empty()
                && arms.iter().all(|arm| is_untyped_literal(&arm.body))
        }
        _ => false,
    }
}

/// Whether the untyped literal form `expr` holds a CONDITIONAL: its value is
/// not a constant, so no compile-time check sees an overflow in it. A shift
/// by an amount that is not a literal (`1 << k`) is one too.
pub(crate) fn untyped_form_is_conditional(expr: &TrustVcExpr) -> bool {
    match expr {
        TrustVcExpr::Ite { .. } | TrustVcExpr::Match { .. } => true,
        TrustVcExpr::Neg(inner) => untyped_form_is_conditional(inner),
        TrustVcExpr::SpecialArith {
            op: SpecialArithOp::Shl | SpecialArithOp::Shr,
            left,
            right,
            ..
        } => {
            untyped_form_is_conditional(left)
                || !matches!(right.as_ref(), TrustVcExpr::IntLit { .. })
        }
        TrustVcExpr::Arith { left, right, .. } | TrustVcExpr::SpecialArith { left, right, .. } => {
            untyped_form_is_conditional(left) || untyped_form_is_conditional(right)
        }
        _ => false,
    }
}

/// Whether the untyped literal form `expr` can take the type `peer`: every
/// literal in it is a value of `peer` — `-v` (a negated literal) is the literal
/// `-v`, which is how Rust reads `-128i8` — and every other operation in it
/// exists in `peer` (an unsigned value is never negated). A tree takes only a
/// fixed-width peer's type; a lone literal also takes `int`/`nat`/`Real`, and
/// a conditional takes a type every branch takes.
pub(crate) fn untyped_literal_fits(expr: &TrustVcExpr, peer: &TrustVcType) -> bool {
    let holds = |value: Option<i128>| {
        value.is_some_and(|value| type_holds_integer(peer, value) == Some(true))
    };
    match expr {
        TrustVcExpr::IntLit { value, ty } => *ty == PLACEHOLDER && holds(Some(*value)),
        TrustVcExpr::Neg(inner) => match inner.as_ref() {
            TrustVcExpr::IntLit { value, ty } if *ty == PLACEHOLDER && *value >= 0 => {
                holds(value.checked_neg())
            }
            inner => matches!(peer, TrustVcType::Int { .. }) && untyped_literal_fits(inner, peer),
        },
        // A shift takes the peer's type through its value operand alone.
        TrustVcExpr::SpecialArith {
            op: SpecialArithOp::Shl | SpecialArithOp::Shr,
            left,
            ..
        } => {
            is_fixed_width_int(peer) && is_untyped_literal(expr) && untyped_literal_fits(left, peer)
        }
        TrustVcExpr::Arith { left, right, .. } | TrustVcExpr::SpecialArith { left, right, .. } => {
            is_fixed_width_int(peer)
                && is_untyped_literal(expr)
                && untyped_literal_fits(left, peer)
                && untyped_literal_fits(right, peer)
        }
        TrustVcExpr::Ite {
            then_branch,
            else_branch,
            ..
        } => {
            is_untyped_literal(expr)
                && untyped_literal_fits(then_branch, peer)
                && untyped_literal_fits(else_branch, peer)
        }
        TrustVcExpr::Match { arms, .. } => {
            is_untyped_literal(expr) && arms.iter().all(|arm| untyped_literal_fits(&arm.body, peer))
        }
        _ => false,
    }
}

/// `expr` — an untyped literal form — at the type `peer`, when
/// [`untyped_literal_fits`]: every literal and every operation of the tree
/// retyped, so the tree is computed in `peer`. `None` otherwise (the form
/// keeps its own type, and the operation it sits in is mixed-type).
pub(crate) fn untyped_literal_at_peer(
    expr: &TrustVcExpr,
    peer: &TrustVcType,
) -> Option<TrustVcExpr> {
    untyped_literal_fits(expr, peer).then(|| retype_untyped(expr, peer))
}

fn retype_untyped(expr: &TrustVcExpr, peer: &TrustVcType) -> TrustVcExpr {
    match expr {
        // A shift's amount keeps its own type.
        TrustVcExpr::SpecialArith {
            op: op @ (SpecialArithOp::Shl | SpecialArithOp::Shr),
            left,
            right,
            ..
        } => TrustVcExpr::SpecialArith {
            op: *op,
            left: Box::new(retype_untyped(left, peer)),
            right: right.clone(),
            ty: peer.clone(),
        },
        TrustVcExpr::IntLit { value, .. } => TrustVcExpr::IntLit {
            value: *value,
            ty: peer.clone(),
        },
        TrustVcExpr::Neg(inner) => TrustVcExpr::Neg(Box::new(retype_untyped(inner, peer))),
        TrustVcExpr::Arith {
            op, left, right, ..
        } => TrustVcExpr::Arith {
            op: *op,
            left: Box::new(retype_untyped(left, peer)),
            right: Box::new(retype_untyped(right, peer)),
            ty: peer.clone(),
        },
        TrustVcExpr::SpecialArith {
            op, left, right, ..
        } => TrustVcExpr::SpecialArith {
            op: *op,
            left: Box::new(retype_untyped(left, peer)),
            right: Box::new(retype_untyped(right, peer)),
            ty: peer.clone(),
        },
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ..
        } => TrustVcExpr::Ite {
            cond: cond.clone(),
            then_branch: Box::new(retype_untyped(then_branch, peer)),
            else_branch: Box::new(retype_untyped(else_branch, peer)),
            ty: peer.clone(),
        },
        TrustVcExpr::Match {
            scrutinee, arms, ..
        } => TrustVcExpr::Match {
            scrutinee: scrutinee.clone(),
            arms: arms
                .iter()
                .map(|arm| crate::ir_expr::MatchArm {
                    pattern: arm.pattern.clone(),
                    body: retype_untyped(&arm.body, peer),
                    guard: arm.guard.clone(),
                })
                .collect(),
            ty: peer.clone(),
        },
        other => other.clone(),
    }
}

/// Exact value of an untyped literal form over the integers (`/ %` only over
/// non-negative operands, where truncating and Euclidean division agree).
/// `None` for any other shape, and when the value overflows `i128`. Used only
/// for a form that meets no peer and has no `i32` reading.
pub(crate) fn untyped_literal_value(expr: &TrustVcExpr) -> Option<i128> {
    if !is_untyped_literal(expr) {
        return None;
    }
    match expr {
        TrustVcExpr::IntLit { value, .. } => Some(*value),
        TrustVcExpr::Neg(inner) => untyped_literal_value(inner)?.checked_neg(),
        TrustVcExpr::Arith {
            op, left, right, ..
        } => {
            let (l, r) = (untyped_literal_value(left)?, untyped_literal_value(right)?);
            match op {
                ArithOp::Add => l.checked_add(r),
                ArithOp::Sub => l.checked_sub(r),
                ArithOp::Mul => l.checked_mul(r),
                ArithOp::Div if l >= 0 && r > 0 => Some(l / r),
                ArithOp::Rem if l >= 0 && r > 0 => Some(l % r),
                _ => None,
            }
        }
        TrustVcExpr::SpecialArith {
            op, left, right, ..
        } => {
            let (l, r) = (untyped_literal_value(left)?, untyped_literal_value(right)?);
            match op {
                SpecialArithOp::BitAnd => Some(l & r),
                SpecialArithOp::BitOr => Some(l | r),
                SpecialArithOp::BitXor => Some(l ^ r),
                SpecialArithOp::Shl | SpecialArithOp::Shr => None,
            }
        }
        _ => None,
    }
}

/// Whether `value` is a value of `ty`: `Some(true/false)` for the integer
/// types (`int` holds every value, `nat` the non-negative ones, `Real` every
/// integer), `None` for a type that holds no integers.
pub(crate) fn type_holds_integer(ty: &TrustVcType, value: i128) -> Option<bool> {
    match ty {
        TrustVcType::Int { width } => Some(match *width {
            0 => false,
            width if width >= 128 => true,
            width => {
                let half = 1i128 << (width - 1);
                (-half..half).contains(&value)
            }
        }),
        TrustVcType::Uint { width } => Some(
            value >= 0
                && match *width {
                    0 => false,
                    width if width >= 127 => true,
                    width => value < 1i128 << width,
                },
        ),
        TrustVcType::MathInt | TrustVcType::Real => Some(true),
        TrustVcType::Nat => Some(value >= 0),
        _ => None,
    }
}

/// The type an untyped literal form takes when it meets `peer`: the peer's
/// when it fits ([`untyped_literal_fits`]); otherwise its own default — `i32`
/// when every literal in it is an `i32` (Rust's default for an unconstrained
/// literal), else `int`.
pub(crate) fn untyped_literal_type(expr: &TrustVcExpr, peer: Option<&TrustVcType>) -> TrustVcType {
    match peer {
        Some(peer) if untyped_literal_fits(expr, peer) => peer.clone(),
        _ if untyped_literal_fits(expr, &PLACEHOLDER) => PLACEHOLDER,
        _ => TrustVcType::MathInt,
    }
}

/// The value of an untyped literal OPERATION (`(10 - 4) * -3`) when every type
/// it may take agrees on it. Which type such a form has is settled by the peer
/// it meets (`untyped_literal_at_peer`), which an evaluator of the form alone
/// cannot see; so it is evaluated in EVERY fixed-width type it fits (each
/// operation in that type: two's complement, truncating `/ %`), and in its
/// own default (`i32` arithmetic, or its exact value when a literal is beyond
/// `i32`), and a value is returned only when all of them agree. `200 + 100`
/// is 44 in `u8` and 300 in `u16`: `None`.
pub(crate) fn untyped_operation_value_all_types_agree(expr: &TrustVcExpr) -> Option<i128> {
    let mut agreed: Option<i128> = None;
    let mut agree = |value: Option<i128>| -> bool {
        match (value, agreed) {
            (None, _) => false,
            (Some(value), Some(seen)) => value == seen,
            (Some(value), None) => {
                agreed = Some(value);
                true
            }
        }
    };
    let default_exact = !untyped_literal_fits(expr, &PLACEHOLDER);
    if default_exact && !agree(untyped_literal_value(expr)) {
        return None;
    }
    for width in [8, 16, 32, 64, 128] {
        for ty in [TrustVcType::Int { width }, TrustVcType::Uint { width }] {
            if untyped_literal_fits(expr, &ty) && !agree(eval_untyped_in(expr, &ty)) {
                return None;
            }
        }
    }
    agreed
}

/// `expr` (an untyped literal form that fits `ty`) evaluated in the
/// fixed-width type `ty`: every operation's exact result wrapped into `ty`;
/// `/` and `%` truncate. `None` for a zero divisor, a signed `MIN / -1`, or a
/// value the `i128` oracle cannot hold.
fn eval_untyped_in(expr: &TrustVcExpr, ty: &TrustVcType) -> Option<i128> {
    let wrap = |value: i128| -> Option<i128> {
        let (width, signed) = match ty {
            TrustVcType::Int { width } => (*width, true),
            TrustVcType::Uint { width } => (*width, false),
            _ => return None,
        };
        if width >= 127 {
            return (type_holds_integer(ty, value) == Some(true)).then_some(value);
        }
        let modulus = 1i128 << width;
        let low = value.rem_euclid(modulus);
        Some(if signed && low >= modulus / 2 {
            low - modulus
        } else {
            low
        })
    };
    match expr {
        TrustVcExpr::IntLit { value, .. } => Some(*value),
        TrustVcExpr::Neg(inner) => wrap(eval_untyped_in(inner, ty)?.checked_neg()?),
        TrustVcExpr::Arith {
            op, left, right, ..
        } => {
            let (l, r) = (eval_untyped_in(left, ty)?, eval_untyped_in(right, ty)?);
            let exact = match op {
                ArithOp::Add => l.checked_add(r),
                ArithOp::Sub => l.checked_sub(r),
                ArithOp::Mul => l.checked_mul(r),
                ArithOp::Div | ArithOp::Rem if r == 0 => None,
                ArithOp::Div => l.checked_div(r),
                ArithOp::Rem => l.checked_rem(r),
            }?;
            if matches!(op, ArithOp::Div | ArithOp::Rem)
                && type_holds_integer(ty, exact) != Some(true)
            {
                return None;
            }
            wrap(exact)
        }
        TrustVcExpr::SpecialArith {
            op, left, right, ..
        } => {
            let (l, r) = (eval_untyped_in(left, ty)?, eval_untyped_in(right, ty)?);
            match op {
                SpecialArithOp::BitAnd => Some(l & r),
                SpecialArithOp::BitOr => Some(l | r),
                SpecialArithOp::BitXor => Some(l ^ r),
                SpecialArithOp::Shl | SpecialArithOp::Shr => None,
            }
        }
        _ => None,
    }
}

/// Whether `expr` is an untyped literal form that is an OPERATION — not a
/// lone literal and not a negated literal (`-5`), whose values are fixed.
pub(crate) fn is_untyped_operation(expr: &TrustVcExpr) -> bool {
    is_untyped_literal(expr)
        && !matches!(expr, TrustVcExpr::IntLit { .. })
        && !matches!(expr, TrustVcExpr::Neg(inner)
            if matches!(inner.as_ref(), TrustVcExpr::IntLit { value, .. } if *value >= 0))
}

/// An integer type: fixed-width, `int` or `nat`.
pub(crate) const fn is_integer_type(ty: &TrustVcType) -> bool {
    matches!(
        ty,
        TrustVcType::Int { .. }
            | TrustVcType::Uint { .. }
            | TrustVcType::MathInt
            | TrustVcType::Nat
    )
}

/// A fixed-width integer type: the types whose arithmetic is machine
/// arithmetic.
pub(crate) const fn is_fixed_width_int(ty: &TrustVcType) -> bool {
    matches!(ty, TrustVcType::Int { .. } | TrustVcType::Uint { .. })
}

/// The types two operands of one binary integer operation (or the two
/// branches of a conditional) DENOTE, after the value-preserving untyped
/// literal rule. When both are untyped literals, `declared` (the node's own
/// type) is the peer each may take.
///
/// A node DECLARED `i32` whose untyped-literal operand meets a value of
/// another fixed-width type is read as the producer typed it: the literal is
/// an `i32`, like the node, and the operation is mixed (exact).
/// `Int { width: 32 }` cannot tell a producer's `200i32` from the placeholder
/// `200`, and the placeholder reading contradicts the declaration: it made
/// `Arith { x: u8 == 100, IntLit { 200, i32 }, ty: i32 } == 44` `Verified`
/// (the `u8` sum) where the declared `i32` operand makes it 300. The syn
/// lowering never declares such a node (it types a literal that fits its peer
/// before typing the node, and pins a suffixed `i32` literal by an identity
/// cast); [`derived_node_type`] passes no `i32` pseudo-declaration.
pub(crate) fn binary_operand_types(
    left: &TrustVcExpr,
    right: &TrustVcExpr,
    declared: &TrustVcType,
) -> (TrustVcType, TrustVcType) {
    let literal_meets = |literal: &TrustVcExpr, peer: &TrustVcType| {
        if *declared == PLACEHOLDER && is_fixed_width_int(peer) && *peer != PLACEHOLDER {
            untyped_literal_type(literal, None)
        } else {
            untyped_literal_type(literal, Some(peer))
        }
    };
    match (is_untyped_literal(left), is_untyped_literal(right)) {
        (true, true) => {
            let peer = is_fixed_width_int(declared).then_some(declared);
            (
                untyped_literal_type(left, peer),
                untyped_literal_type(right, peer),
            )
        }
        (true, false) => {
            let right_ty = infer_expr_type(right);
            (literal_meets(left, &right_ty), right_ty)
        }
        (false, true) => {
            let left_ty = infer_expr_type(left);
            let right_ty = literal_meets(right, &left_ty);
            (left_ty, right_ty)
        }
        (false, false) => (infer_expr_type(left), infer_expr_type(right)),
    }
}

/// The derived type of a binary integer operation or conditional whose
/// operands are `left`/`right` and whose producer declared `declared`
/// (module doc). When both operands are untyped literals, `declared` is the
/// peer they may take; a closed untyped-literal tree that meets no peer is
/// therefore `i32` arithmetic — Rust's default literal type — until a peer it
/// meets folds it exactly (`untyped_literal_at_peer`).
pub(crate) fn derive_binary_int_type(
    left: &TrustVcExpr,
    right: &TrustVcExpr,
    declared: &TrustVcType,
) -> TrustVcType {
    if matches!(declared, TrustVcType::Real | TrustVcType::Float { .. }) {
        return declared.clone();
    }
    let (left_ty, right_ty) = binary_operand_types(left, right, declared);
    for ty in [&left_ty, &right_ty] {
        if matches!(ty, TrustVcType::Real | TrustVcType::Float { .. }) {
            return ty.clone();
        }
    }
    if let Some(exact) = exact_join_type(&[&left_ty, &right_ty], declared) {
        return exact;
    }
    if is_fixed_width_int(&left_ty) && is_fixed_width_int(&right_ty) {
        return if left_ty == right_ty {
            left_ty
        } else {
            TrustVcType::MathInt
        };
    }
    declared.clone()
}

/// The type of an EXACT integer join — an operation or conditional one of
/// whose operands, or whose declared type, is `int`/`nat` — over integer
/// operands of types `operands`: `nat` when EVERY operand is a `nat`, else
/// `int`; `None` when the join is not exact (no `int`/`nat` in sight) or an
/// operand is not an integer.
///
/// A `nat` holds only non-negative values (§5b rule 6), so only operands can
/// make a join `nat`, never the node's declared type: a declared `nat` used to
/// be returned whatever the operands were, so `nat + int` and `nat / int` were
/// `nat` — `let v: nat = x1 + x2` (`x2 == -9`) held -2, and the oracle's own
/// default seed decided `let v: nat = x1 / x2` (`x2: int`). Subtraction and
/// negation leave `nat` even over two `nat`s ([`arith_node_type`],
/// [`infer_expr_type`]).
fn exact_join_type(operands: &[&TrustVcType], declared: &TrustVcType) -> Option<TrustVcType> {
    let unbounded = |ty: &TrustVcType| matches!(ty, TrustVcType::MathInt | TrustVcType::Nat);
    if !unbounded(declared) && !operands.iter().any(|ty| unbounded(ty)) {
        return None;
    }
    if *declared == TrustVcType::MathInt {
        return Some(TrustVcType::MathInt);
    }
    if !operands.iter().all(|ty| is_integer_type(ty)) {
        // A non-integer operand under a declared `nat` (a type parameter, a
        // datatype): nothing here decides it; the encoder refuses what it
        // cannot model.
        return (!operands.iter().any(|ty| unbounded(ty))).then(|| declared.clone());
    }
    Some(
        if !operands.is_empty() && operands.iter().all(|ty| **ty == TrustVcType::Nat) {
            TrustVcType::Nat
        } else {
            TrustVcType::MathInt
        },
    )
}

/// The type of an arithmetic node `left op right` from its derived join
/// type: a difference of two `nat`s is an `int` (Verus types `nat - nat` as
/// `int`; `0 - 1` is not a `nat`). Every other operator keeps the join's type.
fn arith_result_type(op: ArithOp, join: TrustVcType) -> TrustVcType {
    if op == ArithOp::Sub && join == TrustVcType::Nat {
        TrustVcType::MathInt
    } else {
        join
    }
}

/// The type a lowered arithmetic node `left op right` carries:
/// [`derived_node_type`], with a `nat` difference an `int`
/// ([`arith_result_type`]).
pub(crate) fn arith_node_type(op: ArithOp, left: &TrustVcExpr, right: &TrustVcExpr) -> TrustVcType {
    arith_result_type(op, derived_node_type(left, right))
}

/// The type a lowered binary integer node carries: DERIVED from both operands
/// ([`derive_binary_int_type`]) — except that a node over two untyped literals
/// stays the untyped placeholder, so the closed literal tree it starts is
/// typed, literal by literal, by the peer it eventually meets. Shared by the
/// syn lowering and the codegen builders (`ir_builder::arith_inferred`, …),
/// which must type a node exactly as the lowering does.
///
/// The node is declared with its typed operand's type: a literal operand's
/// own `Int { width: 32 }` is not a declaration (see
/// [`binary_operand_types`]), so `(200 + 100) + x` with `x: u8` stays `u8`
/// arithmetic.
pub(crate) fn derived_node_type(left: &TrustVcExpr, right: &TrustVcExpr) -> TrustVcType {
    let declared = if is_untyped_literal(left) {
        infer_expr_type(right)
    } else {
        infer_expr_type(left)
    };
    if is_untyped_literal(left) && is_untyped_literal(right) {
        return declared;
    }
    derive_binary_int_type(left, right, &declared)
}

/// The value type of every arm of a `match`, and the match's derived type:
/// the conditional rule ([`derive_binary_int_type`]) over any number of arms.
///
/// The arms that are not untyped literals fix the type; when they all have
/// one type, an untyped-literal arm takes it if its value fits (else keeps
/// its own), and when there is none, `declared` is the peer. Then: all arms of
/// one fixed-width type `T` → `T`; fixed-width arms of different types that
/// the declared fixed-width type holds every value of → the declared type; an
/// `int`/`nat` arm or declared type, or any other mix of fixed-width types →
/// `int` (each arm the integer it denotes); anything else keeps `declared`. A match used to carry its
/// declared (first-arm / target) type, so `match s { 0 => x_u8, _ => y_i16 }`
/// read `-1` as the `u8` 65535.
pub(crate) fn derive_arms_int_type(
    bodies: &[&TrustVcExpr],
    declared: &TrustVcType,
) -> (Vec<TrustVcType>, TrustVcType) {
    let typed = bodies
        .iter()
        .filter(|body| !is_untyped_literal(body))
        .map(|body| infer_expr_type(body))
        .collect::<Vec<_>>();
    let peer = match typed.split_first() {
        Some((first, rest)) => rest.iter().all(|ty| ty == first).then_some(first),
        None => is_fixed_width_int(declared).then_some(declared),
    };
    let arm_types = bodies
        .iter()
        .map(|body| {
            if is_untyped_literal(body) {
                untyped_literal_type(body, peer)
            } else {
                infer_expr_type(body)
            }
        })
        .collect::<Vec<_>>();
    if matches!(declared, TrustVcType::Real | TrustVcType::Float { .. }) {
        return (arm_types, declared.clone());
    }
    if let Some(float) = arm_types
        .iter()
        .find(|ty| matches!(ty, TrustVcType::Real | TrustVcType::Float { .. }))
    {
        let float = float.clone();
        return (arm_types, float);
    }
    let exact = exact_join_type(&arm_types.iter().collect::<Vec<_>>(), declared);
    let derived = if arm_types.is_empty() {
        declared.clone()
    } else if let Some(exact) = exact {
        exact
    } else if arm_types.iter().all(is_fixed_width_int) {
        if arm_types.iter().all(|ty| *ty == arm_types[0]) {
            arm_types[0].clone()
        } else if is_fixed_width_int(declared)
            && arm_types
                .iter()
                .all(|ty| fixed_width_type_within(ty, declared))
        {
            // Every arm's values are values of the declared type (`u8` and
            // `u32` arms of a `u32` match): the match is that type, each arm
            // widened by its own sign — the same integers, kept bit-vectors.
            declared.clone()
        } else {
            TrustVcType::MathInt
        }
    } else {
        declared.clone()
    };
    (arm_types, derived)
}

/// Whether every value of the fixed-width type `inner` is a value of the
/// fixed-width type `outer` (`u8` in `u32`, `u8` in `i16`, `i8` in `i32`; never
/// a signed type in an unsigned one).
pub(crate) fn fixed_width_type_within(inner: &TrustVcType, outer: &TrustVcType) -> bool {
    match (inner, outer) {
        (TrustVcType::Uint { width: i }, TrustVcType::Uint { width: o })
        | (TrustVcType::Int { width: i }, TrustVcType::Int { width: o }) => i <= o,
        (TrustVcType::Uint { width: i }, TrustVcType::Int { width: o }) => i < o,
        _ => false,
    }
}

/// How a value is bound at a declared integer type — a `let x: T = v`, or a
/// spec function's result `f(..) == body` at its declared result type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum IntBinding {
    /// The value has the declared type.
    Same,
    /// An untyped literal form, typed at the declared type without changing
    /// its value.
    Literal(Box<TrustVcExpr>),
    /// A fixed-width value bound at `int`/`nat`: the integer it denotes.
    LiftToInt,
    /// The value's type is another integer type the declared one cannot hold
    /// (Rust and Verus reject the program).
    Mismatch(TrustVcType),
    /// Not an integer binding; nothing to check here.
    NotInteger,
}

/// See [`IntBinding`]. An `int` binding holds every integer; a `nat` one an
/// unsigned or `nat` value; a fixed-width `T` binding only a value of type `T`
/// (or an untyped literal form that fits `T`). The binding used to register
/// the value's term at the declared width and sign whatever it was, so
/// `let t: u8 = y` (`y: i16 == -1`) read the 16-bit `-1` as the `u8`-signed
/// 65535, and `let t: u8 = -1` read the 32-bit `-1` as 4294967295.
pub(crate) fn int_binding(value: &TrustVcExpr, target: &TrustVcType) -> IntBinding {
    if !is_integer_type(target) {
        return IntBinding::NotInteger;
    }
    if is_untyped_literal(value) {
        return match bind_untyped_literal(value, target) {
            Some(typed) => IntBinding::Literal(Box::new(typed)),
            None => IntBinding::Mismatch(untyped_literal_type(value, None)),
        };
    }
    let value_ty = infer_expr_type(value);
    if value_ty == *target {
        return IntBinding::Same;
    }
    if !is_integer_type(&value_ty) {
        return IntBinding::NotInteger;
    }
    match target {
        TrustVcType::MathInt => match value_ty {
            TrustVcType::Nat => IntBinding::Same,
            _ => IntBinding::LiftToInt,
        },
        TrustVcType::Nat => match value_ty {
            TrustVcType::Uint { .. } => IntBinding::LiftToInt,
            other => IntBinding::Mismatch(other),
        },
        _ => IntBinding::Mismatch(value_ty),
    }
}

/// An UNTYPED literal form (`-1`, `200 + 100`) bound at the integer type
/// `target`, or `None` when `target` cannot hold it — the one literal rule of
/// every binding site ([`int_binding`], [`bind_call_argument`]). It is typed
/// by `target` literal by literal where every literal fits (rule 2: a closed
/// tree is then `target`'s arithmetic); an `int` takes its exact value, and a
/// `nat` only a value it holds. `int_binding` used to bind ANY literal form
/// at a `nat` as the exact integer, so `spec fn gneg() -> nat { -1 }`
/// verified `gneg() == -1` and `let v: nat = -1; v == -1` was `Verified`.
fn bind_untyped_literal(value: &TrustVcExpr, target: &TrustVcType) -> Option<TrustVcExpr> {
    if let Some(typed) = untyped_literal_at_peer(value, target) {
        return Some(typed);
    }
    // A conditional is bound branch by branch (`if c { 1 + 1 } else { 0 }` at
    // `nat`: each branch's exact value).
    match value {
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            return Some(TrustVcExpr::Ite {
                cond: cond.clone(),
                then_branch: Box::new(bind_untyped_literal(then_branch, target)?),
                else_branch: Box::new(bind_untyped_literal(else_branch, target)?),
                ty: target.clone(),
            })
        }
        TrustVcExpr::Match {
            scrutinee, arms, ..
        } => {
            return Some(TrustVcExpr::Match {
                scrutinee: scrutinee.clone(),
                arms: arms
                    .iter()
                    .map(|arm| {
                        Some(crate::ir_expr::MatchArm {
                            pattern: arm.pattern.clone(),
                            body: bind_untyped_literal(&arm.body, target)?,
                            guard: arm.guard.clone(),
                        })
                    })
                    .collect::<Option<Vec<_>>>()?,
                ty: target.clone(),
            })
        }
        _ => {}
    }
    let exact = || retype_untyped(value, &TrustVcType::MathInt);
    match target {
        TrustVcType::MathInt => Some(exact()),
        TrustVcType::Nat if untyped_literal_value(value).is_some_and(|v| v >= 0) => Some(exact()),
        _ => None,
    }
}

/// A call argument bound at its parameter's type (design-trust-proof-backend.md
/// §5b rule 6, the call-argument clause): `Ok` with the argument AT the
/// parameter's type, or `Err` with the argument's type when the parameter
/// type cannot hold it (refused — Rust and Verus reject the call).
///
/// The parameter type must HOLD THE VALUE:
/// * an argument of the parameter's type is itself;
/// * a literal form — unsuffixed or suffixed, `-v` included — whose value
///   the parameter type holds is that literal at the parameter's type; any
///   other literal is refused;
/// * a fixed-width argument whose EVERY value the fixed-width parameter type
///   holds (`u8` into `u32` or `i16`, `i8` into `i64`) is widened by ITS OWN
///   sign — a cast, which extends by the source type's sign;
/// * a fixed-width (or `nat`) argument at an `int` parameter, and an
///   unsigned (or `nat`) one at a `nat` parameter, is lifted to the integer
///   it denotes;
/// * anything else of an integer type is refused;
/// * a COMPOSITE parameter (a collection, a tuple, a datatype) holding an
///   integer takes only a value of the same integer type at every integer
///   position, in both directions — a composite is a carrier of BITS, so a
///   `Seq<i8>` passed for a `Seq<u8>` parameter re-read every element at the
///   other sign (`g0(p: Seq<u8>) -> u8 { p[0] }` applied to `t: Seq<i8>`,
///   `t[0] == -56`, gave `g0(t) == 200` `Verified`); a
///   parameter that mentions a type parameter is instantiated at the call and
///   passes; any other argument or parameter is not an integer binding and
///   passes unchanged.
///
/// Measured before the rule: `spec fn inc32(x: i32) ->
/// int { x + 1 }` verified `inc32(255u8) == 0` — the `u8` argument's 8-bit
/// term met `x + 1` unbound and wrapped at 8 bits, where binding it at `i32`
/// (rule 3) and the exact `int` body (rule 8) both give 256; and a literal
/// the parameter type cannot hold was wrapped when negative (`id8s(-1) ==
/// 255`, `x: u8`) but kept exact when too large (`id8s(300) == 300`).
pub(crate) fn bind_call_argument(
    arg: &TrustVcExpr,
    param: &TrustVcType,
) -> Result<TrustVcExpr, TrustVcType> {
    if !is_integer_type(param) {
        let arg_ty = infer_expr_type(arg);
        let generic = super::typing_check::mentions_type_parameter(param)
            || super::typing_check::mentions_type_parameter(&arg_ty);
        let composite = |ty: &TrustVcType| {
            !is_integer_type(ty) && super::typing_check::type_holds_an_integer(ty)
        };
        // One type spelled alike is the same type (a recursive datatype's
        // self-reference is a variant-less stub beside its full declaration).
        let spelled_alike = arg_ty.to_type_string() == param.to_type_string();
        if !generic
            && !spelled_alike
            && (composite(param) || composite(&arg_ty))
            && !(super::typing_check::integer_positions_agree(&arg_ty, param)
                && super::typing_check::integer_positions_agree(param, &arg_ty))
        {
            return Err(arg_ty);
        }
        return Ok(arg.clone());
    }
    if is_untyped_literal(arg) {
        return bind_untyped_literal(arg, param).ok_or_else(|| untyped_literal_type(arg, None));
    }
    // A SUFFIXED literal is bound by its value.
    if let Some(value) = typed_literal_form_value(arg) {
        if type_holds_integer(param, value) != Some(true) {
            return Err(infer_expr_type(arg));
        }
        return Ok(typed_literal(value, param));
    }
    let arg_ty = infer_expr_type(arg);
    if arg_ty == *param || !is_integer_type(&arg_ty) {
        return Ok(arg.clone());
    }
    let cast = || TrustVcExpr::Cast {
        expr: Box::new(arg.clone()),
        from_ty: arg_ty.clone(),
        to_ty: param.clone(),
    };
    let holds_every_value = match (param, &arg_ty) {
        (TrustVcType::MathInt, _) => true,
        (TrustVcType::Nat, TrustVcType::Uint { .. } | TrustVcType::Nat) => true,
        (TrustVcType::Nat, _) => false,
        _ => {
            is_fixed_width_int(param)
                && is_fixed_width_int(&arg_ty)
                && fixed_width_type_within(&arg_ty, param)
        }
    };
    if holds_every_value {
        Ok(cast())
    } else {
        Err(arg_ty)
    }
}

/// The value of a SUFFIXED literal form: `IntLit`, `-IntLit` of an integer
/// type, and the identity cast that pins a source `200i32` (§5b rule 7).
fn typed_literal_form_value(expr: &TrustVcExpr) -> Option<i128> {
    match expr {
        TrustVcExpr::IntLit { value, ty } if is_integer_type(ty) => Some(*value),
        TrustVcExpr::Neg(inner) => match inner.as_ref() {
            TrustVcExpr::IntLit { value, ty } if is_integer_type(ty) => value.checked_neg(),
            _ => None,
        },
        TrustVcExpr::Cast {
            expr,
            from_ty,
            to_ty,
        } if from_ty == to_ty && is_fixed_width_int(from_ty) => typed_literal_form_value(expr),
        _ => None,
    }
}

/// The literal `value` at the type `ty` (`-v` as a negated literal, as a
/// source spells it).
fn typed_literal(value: i128, ty: &TrustVcType) -> TrustVcExpr {
    match value.checked_neg() {
        Some(magnitude) if value < 0 => TrustVcExpr::Neg(Box::new(TrustVcExpr::IntLit {
            value: magnitude,
            ty: ty.clone(),
        })),
        _ => TrustVcExpr::IntLit {
            value,
            ty: ty.clone(),
        },
    }
}

/// The type of a slot whose WITNESS (the value an unascribed binding was
/// first bound to, or a projection of it) is `witness`, written with a value
/// of type `value_ty` (`__trust_vc_bind_like`, §5b rule 12): the witness's
/// own type, except at a position where the witness IS an untyped literal
/// form (`0`, `if c { 0 } else { 1 }`, a component of a tuple literal, a
/// sequence literal of such literals) — Rust types that literal from the
/// write, so the position takes the value's type there. Decided by the
/// witness's SHAPE, never by a literal it merely mentions: the index of
/// `s[0]` fixes nothing about the element's type, and reading it as an
/// untyped witness left `w = x` bare for `let mut w = s[0]` (`s: Seq<int>`,
/// `x: u8 == 255`), so `w + 1 == 0` was `Verified`.
pub(crate) fn slot_type_like(witness: &TrustVcExpr, value_ty: &TrustVcType) -> TrustVcType {
    if witness_fixes_no_type(witness) {
        return value_ty.clone();
    }
    if let TrustVcExpr::FnCall {
        name,
        args,
        return_ty:
            TrustVcType::Datatype {
                name: datatype_name,
                variants,
            },
    } = witness
    {
        let value_fields = match value_ty {
            TrustVcType::Datatype {
                variants: value_variants,
                ..
            } => match value_variants.as_slice() {
                [variant] if variant.name == crate::ir_expr::TUPLE_VARIANT_NAME => {
                    Some(&variant.fields)
                }
                _ => None,
            },
            _ => None,
        };
        if let ([variant], Some(value_fields)) = (variants.as_slice(), value_fields) {
            if variant.name == crate::ir_expr::TUPLE_VARIANT_NAME
                && *name
                    == crate::encoder::datatype::variant_symbol_name(
                        datatype_name,
                        crate::ir_expr::TUPLE_VARIANT_NAME,
                    )
                && args.len() == value_fields.len()
            {
                return crate::ir_expr::tuple_datatype_type(
                    args.iter()
                        .zip(value_fields)
                        .map(|(arg, (_, field_ty))| slot_type_like(arg, field_ty))
                        .collect(),
                );
            }
        }
    }
    infer_expr_type(witness)
}

/// Whether the witness `witness` is an untyped literal form as a WHOLE — a
/// literal, a conditional of literals, a sequence literal of literals — whose
/// type Rust infers from what the binding holds: it fixes no slot type.
pub(crate) fn witness_fixes_no_type(witness: &TrustVcExpr) -> bool {
    is_untyped_literal(witness) || untyped_seq_literal(witness)
}

/// A sequence literal (`seq![0, 1]`, `[0, 1]`: pushes onto an empty
/// `Seq<i32>` constructor) every element of which is an untyped literal form.
fn untyped_seq_literal(expr: &TrustVcExpr) -> bool {
    match expr {
        TrustVcExpr::CollectionOp {
            op: crate::ir_expr::CollectionOp::Push,
            receiver,
            args,
            ..
        } => {
            matches!(args.as_slice(), [element] if is_untyped_literal(element))
                && untyped_seq_literal(receiver)
        }
        TrustVcExpr::FnCall {
            args, return_ty, ..
        } => args.is_empty() && *return_ty == TrustVcType::Seq(Box::new(PLACEHOLDER)),
        _ => false,
    }
}

/// The value that stands for a variable of type `var_ty` when a substitution
/// replaces it — an axiom instantiated at a witness, an inlined call's
/// argument for its parameter, an equality-pinned variable, a candidate
/// model's value. The value keeps the VARIABLE's type.
///
/// An untyped literal form ([`is_untyped_literal`]) is retyped to the
/// variable's type when every literal in it fits ([`untyped_literal_at_peer`];
/// an `int`/`nat` variable takes a literal tree as exact arithmetic). For
/// `i32` that retyping is the identity — an `i32` literal IS the placeholder —
/// so the value is pinned by an identity cast; a form that fits nothing is
/// pinned at its own `i32` type the same way. Substituted bare, the literal
/// was typed by whatever peer it met at the use site: `v(x: i32) -> int { (x +
/// 2147483647) * 2i64 }` instantiated at `x := 3` made the closed tree `3 +
/// 2147483647`, which the `i64` peer typed as `i64` arithmetic (2147483650)
/// where the axiom's `i32` sum wraps (-2147483646) — two readings of one
/// definition, so every VC mentioning `v` came back `Verified`.
///
/// Every other replacement is returned unchanged.
pub(crate) fn pin_substituted_value(
    var_ty: &TrustVcType,
    replacement: &TrustVcExpr,
) -> TrustVcExpr {
    if !is_integer_type(var_ty) || !is_untyped_literal(replacement) {
        return replacement.clone();
    }
    let pin_i32 = |value: TrustVcExpr| TrustVcExpr::Cast {
        expr: Box::new(value),
        from_ty: PLACEHOLDER,
        to_ty: PLACEHOLDER,
    };
    match int_binding(replacement, var_ty) {
        IntBinding::Literal(typed) if *var_ty == PLACEHOLDER => pin_i32(*typed),
        IntBinding::Literal(typed) => *typed,
        _ if untyped_literal_fits(replacement, &PLACEHOLDER) => pin_i32(replacement.clone()),
        _ => replacement.clone(),
    }
}

/// The derived type of `left << k` / `left >> k`: the LEFT operand's (Rust
/// shifts take the value's type; the amount's type is independent). An
/// untyped literal LEFT operand takes `declared` when its value fits it.
pub(crate) fn derive_shift_type(left: &TrustVcExpr, declared: &TrustVcType) -> TrustVcType {
    match is_untyped_literal(left) {
        true => untyped_literal_type(left, is_fixed_width_int(declared).then_some(declared)),
        false => {
            let left_ty = infer_expr_type(left);
            if is_fixed_width_int(&left_ty) {
                left_ty
            } else {
                declared.clone()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
        TrustVcExpr::IntLit { value, ty }
    }
    fn var(name: &str, ty: TrustVcType) -> TrustVcExpr {
        TrustVcExpr::Var {
            name: name.to_string(),
            ty,
        }
    }
    fn arith(op: ArithOp, l: TrustVcExpr, r: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
        TrustVcExpr::Arith {
            op,
            left: Box::new(l),
            right: Box::new(r),
            ty,
        }
    }
    const U8: TrustVcType = TrustVcType::Uint { width: 8 };
    const U16: TrustVcType = TrustVcType::Uint { width: 16 };
    const I16: TrustVcType = TrustVcType::Int { width: 16 };

    #[test]
    fn mixed_operands_derive_int_whatever_the_node_declares() {
        // `x + y` with x: u8, y: i16 — the syn lowering used to type this by
        // its LEFT operand (u8), and a typed producer may say anything.
        for declared in [U8, I16, U16] {
            let e = arith(ArithOp::Add, var("x", U8), var("y", I16), declared);
            assert_eq!(infer_expr_type(&e), TrustVcType::MathInt);
        }
    }

    #[test]
    fn one_fixed_type_derives_that_type() {
        let e = arith(ArithOp::Mul, var("x", U8), var("y", U8), I16);
        assert_eq!(infer_expr_type(&e), U8);
    }

    #[test]
    fn untyped_literal_takes_the_peer_only_when_its_value_fits() {
        let fits = arith(ArithOp::Add, var("x", U8), lit(255, PLACEHOLDER), U8);
        assert_eq!(infer_expr_type(&fits), U8);
        // -1 has no u8 reading; 256 is not a u8: the operation is mixed.
        for value in [-1, 256] {
            let e = arith(ArithOp::Add, var("x", U8), lit(value, PLACEHOLDER), U8);
            assert_eq!(infer_expr_type(&e), TrustVcType::MathInt, "{value}");
        }
        let neg = TrustVcExpr::Neg(Box::new(lit(1, PLACEHOLDER)));
        let e = arith(ArithOp::Add, var("x", U8), neg, U8);
        assert_eq!(infer_expr_type(&e), TrustVcType::MathInt);
    }

    #[test]
    fn ite_takes_both_branches() {
        let ite = TrustVcExpr::Ite {
            cond: Box::new(TrustVcExpr::BoolLit(true)),
            then_branch: Box::new(var("x", U8)),
            else_branch: Box::new(var("y", I16)),
            ty: U8,
        };
        assert_eq!(infer_expr_type(&ite), TrustVcType::MathInt);
    }

    #[test]
    fn untyped_literal_tree_takes_a_peer_literal_by_literal() {
        let i8t = TrustVcType::Int { width: 8 };
        // `-(-128)`: the literal -128 is an i8, and negating it is i8
        // arithmetic — the tree is typed, never re-valued.
        let neg128 = TrustVcExpr::Neg(Box::new(lit(-128, PLACEHOLDER)));
        assert!(untyped_literal_fits(&neg128, &i8t));
        // `-(1)` is the literal -1: no unsigned type holds it.
        let minus_one = TrustVcExpr::Neg(Box::new(lit(1, PLACEHOLDER)));
        assert!(!untyped_literal_fits(&minus_one, &U8));
        assert_eq!(untyped_literal_at_peer(&minus_one, &U8), None);
        // `200 + 100` next to a u8: both literals are u8s, so the SUM is u8
        // arithmetic (Rust's typing), not the integer 300.
        let sum = arith(
            ArithOp::Add,
            lit(200, PLACEHOLDER),
            lit(100, PLACEHOLDER),
            PLACEHOLDER,
        );
        assert_eq!(
            untyped_literal_at_peer(&sum, &U8),
            Some(arith(ArithOp::Add, lit(200, U8), lit(100, U8), U8))
        );
        // A literal out of the peer's range keeps the whole tree untyped.
        let wide = arith(
            ArithOp::Add,
            lit(200, PLACEHOLDER),
            lit(300, PLACEHOLDER),
            PLACEHOLDER,
        );
        assert_eq!(untyped_literal_at_peer(&wide, &U8), None);
        let tree = arith(
            ArithOp::Sub,
            arith(
                ArithOp::Sub,
                lit(i128::from(i32::MIN), PLACEHOLDER),
                lit(0, PLACEHOLDER),
                PLACEHOLDER,
            ),
            lit(256_908_456, PLACEHOLDER),
            PLACEHOLDER,
        );
        assert_eq!(untyped_literal_value(&tree), Some(-2_404_392_104));
    }

    fn arm(body: TrustVcExpr) -> crate::ir_expr::MatchArm {
        crate::ir_expr::MatchArm {
            pattern: crate::ir_expr::MatchPattern::Wildcard,
            body,
            guard: None,
        }
    }

    #[test]
    fn match_is_typed_from_its_arms() {
        let u32t = TrustVcType::Uint { width: 32 };
        let m = |arms: Vec<TrustVcExpr>, ty: TrustVcType| TrustVcExpr::Match {
            scrutinee: Box::new(var("s", U8)),
            arms: arms.into_iter().map(arm).collect(),
            ty,
        };
        // u8 and i16 arms: no fixed-width type holds both -> int, whatever
        // the match declares.
        for declared in [U8, I16] {
            let e = m(vec![var("x", U8), var("y", I16)], declared.clone());
            let expected = if declared == I16 {
                I16
            } else {
                TrustVcType::MathInt
            };
            assert_eq!(infer_expr_type(&e), expected, "declared {declared:?}");
        }
        // u8 and u32 arms of a u32 match: every arm value is a u32.
        let e = m(vec![var("x", U8), var("y", u32t.clone())], u32t.clone());
        assert_eq!(infer_expr_type(&e), u32t);
        // An untyped-literal arm takes the other arms' type when it fits.
        let e = m(vec![var("x", U8), lit(7, PLACEHOLDER)], U8);
        assert_eq!(infer_expr_type(&e), U8);
        let e = m(vec![var("x", U8), lit(-1, PLACEHOLDER)], U8);
        assert_eq!(infer_expr_type(&e), TrustVcType::MathInt);
    }

    #[test]
    fn a_binding_holds_only_a_value_of_its_type() {
        assert_eq!(int_binding(&var("y", U8), &U8), IntBinding::Same);
        assert_eq!(
            int_binding(&lit(7, PLACEHOLDER), &U8),
            IntBinding::Literal(Box::new(lit(7, U8)))
        );
        assert_eq!(
            int_binding(&TrustVcExpr::Neg(Box::new(lit(1, PLACEHOLDER))), &U8),
            IntBinding::Mismatch(PLACEHOLDER)
        );
        assert_eq!(int_binding(&var("y", I16), &U8), IntBinding::Mismatch(I16));
        let mixed = arith(ArithOp::Add, var("x", U8), var("y", I16), U8);
        assert_eq!(
            int_binding(&mixed, &U8),
            IntBinding::Mismatch(TrustVcType::MathInt)
        );
        assert_eq!(
            int_binding(&var("y", I16), &TrustVcType::MathInt),
            IntBinding::LiftToInt
        );
        assert_eq!(
            int_binding(&var("y", U8), &TrustVcType::Nat),
            IntBinding::LiftToInt
        );
        assert_eq!(
            int_binding(&var("y", I16), &TrustVcType::Nat),
            IntBinding::Mismatch(I16)
        );
        assert_eq!(
            int_binding(&TrustVcExpr::BoolLit(true), &TrustVcType::Bool),
            IntBinding::NotInteger
        );
        // A conditional over untyped literals is typed branch by branch.
        let ite = |t: TrustVcExpr, e: TrustVcExpr, ty: TrustVcType| TrustVcExpr::Ite {
            cond: Box::new(var("c", TrustVcType::Bool)),
            then_branch: Box::new(t),
            else_branch: Box::new(e),
            ty,
        };
        let u64t = TrustVcType::Uint { width: 64 };
        assert_eq!(
            int_binding(
                &ite(lit(7, PLACEHOLDER), lit(0, PLACEHOLDER), PLACEHOLDER),
                &u64t
            ),
            IntBinding::Literal(Box::new(ite(
                lit(7, u64t.clone()),
                lit(0, u64t.clone()),
                u64t
            )))
        );
        let minus_one = TrustVcExpr::Neg(Box::new(lit(1, PLACEHOLDER)));
        assert!(matches!(
            int_binding(&ite(minus_one, lit(0, PLACEHOLDER), PLACEHOLDER), &U8),
            IntBinding::Mismatch(_)
        ));
    }

    #[test]
    fn a_substituted_literal_keeps_the_variable_type() {
        let pinned = |e: TrustVcExpr| TrustVcExpr::Cast {
            expr: Box::new(e),
            from_ty: PLACEHOLDER,
            to_ty: PLACEHOLDER,
        };
        // An `i32` variable: the literal is pinned (it IS the placeholder).
        assert_eq!(
            pin_substituted_value(&PLACEHOLDER, &lit(3, PLACEHOLDER)),
            pinned(lit(3, PLACEHOLDER))
        );
        // A `u8` variable: the literal is a `u8`.
        assert_eq!(pin_substituted_value(&U8, &lit(3, PLACEHOLDER)), lit(3, U8));
        // A value the variable's type cannot hold stays the `i32` it is.
        assert_eq!(
            pin_substituted_value(&U8, &lit(300, PLACEHOLDER)),
            pinned(lit(300, PLACEHOLDER))
        );
        // Anything else is substituted as is.
        assert_eq!(pin_substituted_value(&U8, &var("y", U8)), var("y", U8));
    }

    #[test]
    fn a_node_declared_i32_reads_its_i32_literal_as_i32() {
        // Declared `i32` beside a `u8`: the literal is the producer's `i32`,
        // and the operation is mixed (exact).
        let e = arith(
            ArithOp::Add,
            var("x", U8),
            lit(200, PLACEHOLDER),
            PLACEHOLDER,
        );
        assert_eq!(infer_expr_type(&e), TrustVcType::MathInt);
        // Declared `u8`: the placeholder takes the `u8` peer.
        let e = arith(ArithOp::Add, var("x", U8), lit(200, PLACEHOLDER), U8);
        assert_eq!(infer_expr_type(&e), U8);
        // The lowering never declares a node with a literal's own type.
        assert_eq!(derived_node_type(&lit(200, PLACEHOLDER), &var("x", U8)), U8);
    }

    /// §5b rule 6: only operands make an exact join `nat`; a declared `nat`
    /// does not (`nat + int` and `nat / int` were `nat`), and a difference or
    /// negation of `nat`s is an `int`.
    #[test]
    fn a_nat_join_needs_nat_operands() {
        let nat = TrustVcType::Nat;
        let int = TrustVcType::MathInt;
        let n = || var("n", TrustVcType::Nat);
        for (op, right, expected) in [
            (ArithOp::Add, var("i", int.clone()), int.clone()),
            (ArithOp::Div, var("i", int.clone()), int.clone()),
            (ArithOp::Add, var("x", U8), int.clone()),
            (ArithOp::Add, n(), nat.clone()),
            (ArithOp::Mul, n(), nat.clone()),
            (ArithOp::Rem, n(), nat.clone()),
            (ArithOp::Add, lit(1, PLACEHOLDER), nat.clone()),
            (ArithOp::Sub, n(), int.clone()),
            (ArithOp::Sub, lit(1, PLACEHOLDER), int.clone()),
            (ArithOp::Add, lit(-1, PLACEHOLDER), int.clone()),
        ] {
            let e = arith(op, n(), right.clone(), nat.clone());
            assert_eq!(infer_expr_type(&e), expected, "{op:?} {right:?}");
            assert_eq!(
                arith_node_type(op, &n(), &right),
                expected,
                "{op:?} {right:?}"
            );
        }
        assert_eq!(infer_expr_type(&TrustVcExpr::Neg(Box::new(n()))), int);
        let ite = |t: TrustVcExpr, e: TrustVcExpr| TrustVcExpr::Ite {
            cond: Box::new(var("c", TrustVcType::Bool)),
            then_branch: Box::new(t),
            else_branch: Box::new(e),
            ty: TrustVcType::Nat,
        };
        assert_eq!(infer_expr_type(&ite(n(), lit(0, PLACEHOLDER))), nat);
        assert_eq!(infer_expr_type(&ite(n(), var("i", int.clone()))), int);
        let m = TrustVcExpr::Match {
            scrutinee: Box::new(var("s", U8)),
            arms: vec![arm(n()), arm(var("i", int.clone()))],
            ty: TrustVcType::Nat,
        };
        assert_eq!(infer_expr_type(&m), int);
        // A `nat` binding holds a literal only when its value is one.
        assert!(matches!(
            int_binding(&lit(3, PLACEHOLDER), &nat),
            IntBinding::Literal(_)
        ));
        assert_eq!(
            int_binding(&TrustVcExpr::Neg(Box::new(lit(1, PLACEHOLDER))), &nat),
            IntBinding::Mismatch(PLACEHOLDER)
        );
        assert_eq!(
            bind_call_argument(&TrustVcExpr::Neg(Box::new(lit(1, PLACEHOLDER))), &nat),
            Err(PLACEHOLDER)
        );
    }
}
