//! The per-node claim checks of the IR typing validator: each compares a
//! node's DECLARED type with what its (already validated) children derive.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::ir::{CollectionOp, MatchPattern, TrustVcType};
use crate::ir_expr::TrustVcExpr;

use super::super::dispatch::infer_collection_op_type;
use super::super::types::{
    bind_call_argument, derive_binary_int_type, infer_expr_type, int_binding, is_integer_type,
    is_untyped_literal, type_holds_integer, IntBinding, PLACEHOLDER,
};
use super::positions::{integer_positions_agree, type_holds_an_integer};
use super::Binder;

/// A literal is a value of its declared type. The unsuffixed placeholder
/// (`Int { width: 32 }`) is typed by the peer it meets and holds any value.
pub(super) fn literal_holds(value: i128, ty: &TrustVcType) -> Result<(), String> {
    let holds = match ty {
        _ if *ty == PLACEHOLDER => true,
        TrustVcType::Char => {
            (0..=0x10_FFFF).contains(&value) && !(0xD800..=0xDFFF).contains(&value)
        }
        other => type_holds_integer(other, value) != Some(false),
    };
    if holds {
        Ok(())
    } else {
        Err(format!(
            "the literal {value} declared `{}`: a literal is a value of its type",
            ty.to_type_string()
        ))
    }
}

/// An integer node's declared type is the type its operands derive — unless
/// it is the untyped placeholder over untyped operands (an unsuffixed literal
/// tree, typed later by the peer it meets).
pub(super) fn derived_agrees(
    expr: &TrustVcExpr,
    declared: &TrustVcType,
    operands: &[&TrustVcExpr],
) -> Result<(), String> {
    if is_untyped_literal(expr) || untyped_placeholder_join(declared, operands) {
        return Ok(());
    }
    let derived = match expr {
        TrustVcExpr::Ite {
            then_branch,
            else_branch,
            ty,
            ..
        } => derive_binary_int_type(then_branch, else_branch, ty),
        _ => infer_expr_type(expr),
    };
    integer_claim_agrees(declared, &derived, || expr_label(expr))
}

/// A join (conditional, `match`) declared at the placeholder whose every
/// integer branch is an untyped literal form: it is typed where it is bound.
pub(super) fn untyped_placeholder_join(declared: &TrustVcType, operands: &[&TrustVcExpr]) -> bool {
    *declared == PLACEHOLDER && operands.iter().all(|operand| untyped_form(operand))
}

/// An untyped literal form, or a conditional every branch of which is one.
pub(super) fn untyped_form(expr: &TrustVcExpr) -> bool {
    match expr {
        TrustVcExpr::Ite {
            then_branch,
            else_branch,
            ..
        } => untyped_form(then_branch) && untyped_form(else_branch),
        TrustVcExpr::Match { arms, .. } => {
            !arms.is_empty() && arms.iter().all(|arm| untyped_form(&arm.body))
        }
        other => is_untyped_literal(other),
    }
}

pub(super) fn integer_claim_agrees(
    declared: &TrustVcType,
    derived: &TrustVcType,
    label: impl FnOnce() -> String,
) -> Result<(), String> {
    if !is_integer_type(declared) || !is_integer_type(derived) || declared == derived {
        return Ok(());
    }
    Err(format!(
        "{} declared `{}` derives `{}` from its operands",
        label(),
        declared.to_type_string(),
        derived.to_type_string()
    ))
}

pub(super) fn expr_label(expr: &TrustVcExpr) -> String {
    match expr {
        TrustVcExpr::Arith { op, .. } => format!("an arithmetic `{op}`"),
        TrustVcExpr::SpecialArith { op, .. } => format!("a bitwise `{op:?}`"),
        TrustVcExpr::Ite { .. } => "a conditional".to_string(),
        TrustVcExpr::Match { .. } => "a `match`".to_string(),
        _ => "a node".to_string(),
    }
}

/// A composite value built from `sources` (a conditional's branches, a
/// `match`'s arms) is a value of the declared composite type at every integer
/// position — in BOTH directions ([`same_integer_positions`]): a join
/// declared at a type that holds no integer (a type parameter, `Poly`, an
/// opaque type) over a `Seq<u8>` FORGETS the element type, and a later read
/// at `i8` re-read 200 as -56.
pub(super) fn composite_holds<'e>(
    declared: &TrustVcType,
    sources: impl IntoIterator<Item = &'e TrustVcExpr>,
    what: &str,
) -> Result<(), String> {
    for source in sources {
        let source_ty = infer_expr_type(source);
        if !same_integer_positions(&source_ty, declared) {
            return Err(format!(
                "a {what} declared `{}` over a value of type `{}`: a composite's integer \
                 positions keep the types of the values it holds",
                declared.to_type_string(),
                source_ty.to_type_string()
            ));
        }
    }
    Ok(())
}

/// Whether two types hold one integer type at every integer position, in
/// both directions: a type that holds no integer agrees only with another
/// that holds none.
pub(super) fn same_integer_positions(left: &TrustVcType, right: &TrustVcType) -> bool {
    integer_positions_agree(left, right) && integer_positions_agree(right, left)
}

/// Two COMPOSITES compared (`==`, `!=`) hold one integer type at every
/// integer position. Two integers of different types compare as the integers
/// they denote (rule 4); two collections compare as carriers, element BITS
/// against element bits, so a `Seq<u8>` equal to a `Seq<i8>` re-read every
/// element at the other sign (`spec fn as_i8(s: Seq<u8>) -> Seq<i8> { s }`
/// made `as_i8(s)[0] == -56` `Verified` for `s[0] == 200`) — and so does a
/// value of a type that holds no integer compared with one that does.
pub(super) fn composites_compare(left: &TrustVcExpr, right: &TrustVcExpr) -> Result<(), String> {
    let (left_ty, right_ty) = (infer_expr_type(left), infer_expr_type(right));
    if is_integer_type(&left_ty)
        || is_integer_type(&right_ty)
        || same_integer_positions(&left_ty, &right_ty)
    {
        return Ok(());
    }
    Err(format!(
        "a `{}` compared with a `{}`: two composites compare element by element at one type",
        left_ty.to_type_string(),
        right_ty.to_type_string()
    ))
}

/// A `let` (typed-seam) binds a value its declared type holds (rule 6): an
/// integer binding by `int_binding`, a composite one at every integer
/// position.
pub(super) fn binding_holds(
    value: &TrustVcExpr,
    ty: &TrustVcType,
    name: &str,
) -> Result<(), String> {
    match int_binding(value, ty) {
        IntBinding::Mismatch(found) => Err(format!(
            "a `let {name}: {}` of a value of type `{}`: a value is bound only at a type that \
             holds it",
            ty.to_type_string(),
            found.to_type_string()
        )),
        IntBinding::NotInteger => {
            let found = infer_expr_type(value);
            if same_integer_positions(&found, ty) {
                Ok(())
            } else {
                Err(format!(
                    "a `let {name}: {}` of a value of type `{}`: a composite's integer \
                     positions keep the types of the values it holds",
                    ty.to_type_string(),
                    found.to_type_string()
                ))
            }
        }
        _ => Ok(()),
    }
}

/// A cast reads its operand at the operand's OWN type: `from_ty` is the
/// type the operand derives, whatever that type is. The encoder reads the
/// operand's bits by `from_ty` (a sign, an element sign, a `char`'s range),
/// so a `from_ty` that is not the operand's type is a second reading of one
/// value: with `s: Seq<u8>`, `s[0] == 200`, a cast `s as Seq<i8>` declared
/// `from_ty: Seq<i8>` re-reads the element as -56, and `y: i8 == -56` cast
/// from a declared `char` to `u32` is 200 beside the honest 4294967240. The
/// unsuffixed placeholder literal is typed by its cast.
pub(super) fn cast_operand_agrees(
    operand: &TrustVcExpr,
    from_ty: &TrustVcType,
) -> Result<(), String> {
    let own = infer_expr_type(operand);
    let scalar = |ty: &TrustVcType| is_integer_type(ty) || matches!(ty, TrustVcType::Char);
    let agrees = own == *from_ty
        || (*from_ty == PLACEHOLDER && is_untyped_literal(operand))
        || (!scalar(&own) && !scalar(from_ty) && same_integer_positions(&own, from_ty));
    if agrees {
        return Ok(());
    }
    Err(format!(
        "a cast from `{}` of a value of type `{}`: a cast reads its operand at the operand's \
         own type",
        from_ty.to_type_string(),
        own.to_type_string()
    ))
}

/// A `wrapping_*`/`saturating_*` operand at the method's type `ty`.
pub(super) fn wrapping_operand(operand: &TrustVcExpr, ty: &TrustVcType) -> IntBinding {
    if !is_integer_type(ty) {
        return IntBinding::Same;
    }
    match int_binding(operand, ty) {
        IntBinding::LiftToInt => IntBinding::Mismatch(infer_expr_type(operand)),
        other => other,
    }
}

/// A collection operation's RESULT is the type the lowering's one typing
/// rule (`infer_collection_op_type`) derives from its receiver and
/// arguments — the element type of `first`/`get`/`choose`, the receiver's
/// type for `push`/`take`/`insert`, `Set<T>` for a `Seq<T>`'s `to_set`,
/// `Seq<R>` for a `map_values` whose closure returns `R`, the accumulator's
/// type for a fold. A node declaring any other type at an integer position
/// is refused; a receiver or argument the rule cannot type (a type
/// parameter, an opaque receiver) is refused when the node claims an
/// integer anywhere. Only the RECEIVER's element type used to be checked,
/// and only for element reads and receiver-typed operations, so with `s:
/// Seq<u8>`, `s[0] == 200`, a `to_set` declared `Set<i8>` contained -56, and
/// so did `to_multiset`/`dom`/`view`/`map_values`/`fold_left`/`Set::map`/
/// `Map::map_values` results declared at `i8`.
pub(super) fn collection_op_agrees(
    op: CollectionOp,
    receiver: &TrustVcExpr,
    args: &[TrustVcExpr],
    ty: &TrustVcType,
) -> Result<(), String> {
    let receiver_ty = infer_expr_type(receiver);
    let derived = match infer_collection_op_type(&op, &receiver_ty, args) {
        Ok(derived) => derived,
        Err(_) if !type_holds_an_integer(ty) => return Ok(()),
        Err(error) => {
            return Err(format!(
                "a `{op:?}` of a `{}` declared `{}`, which its receiver and arguments do not \
                 type: {error}",
                receiver_ty.to_type_string(),
                ty.to_type_string()
            ))
        }
    };
    let agrees = if matches!(op, CollectionOp::Len | CollectionOp::Count) {
        // A length or a count is an `Int` term, read at its own value
        // whatever integer type it is declared at (the driver declares a
        // `str` length `i64`).
        is_integer_type(ty)
    } else if is_integer_type(ty) || is_integer_type(&derived) {
        *ty == derived
    } else {
        same_integer_positions(&derived, ty)
    };
    if !agrees {
        return Err(format!(
            "a `{op:?}` of a `{}` declared `{}` is a value of type `{}`",
            receiver_ty.to_type_string(),
            ty.to_type_string(),
            derived.to_type_string()
        ));
    }
    // The other collection of a binary operation is a value of the same type
    // (a subset/superset test compared the carriers' BITS: `st: Set<u8> ∋
    // 200`, `st ⊆ t: Set<i8>` made `t.contains(-56i8)` `Verified`).
    if matches!(
        op,
        CollectionOp::Concat
            | CollectionOp::Add
            | CollectionOp::Union
            | CollectionOp::Intersect
            | CollectionOp::Difference
            | CollectionOp::Subset
            | CollectionOp::Superset
    ) {
        for other in args {
            let other_ty = infer_expr_type(other);
            if !same_integer_positions(&other_ty, &receiver_ty) {
                return Err(format!(
                    "a `{op:?}` of a `{}` with a `{}`: both operands hold one element type",
                    receiver_ty.to_type_string(),
                    other_ty.to_type_string()
                ));
            }
        }
    }
    Ok(())
}

/// An element READ `receiver[index]` is a value of its receiver's ELEMENT
/// type (§5b rule 10) — a sequence's or an array's element, a map's value, a
/// string's `char` — and a MAP key is bound at the map's key type
/// (`bind_call_argument`: `m[-56i8]` of a `Map<u8, u8>` read the key 200). A
/// read whose receiver has no element type this rule derives (a type
/// parameter, `Poly`, an opaque or a datatype receiver) is refused when it
/// is declared at a type that holds an integer. The receiver's own type is
/// itself a derived, validated claim (the walk is bottom-up), so a lie one
/// level up — `s.take(1)` of a `Seq<u8>` declared `Seq<i8>` — is refused
/// where it is made.
pub(super) fn element_read_agrees(
    receiver: &TrustVcExpr,
    index: &TrustVcExpr,
    declared: &TrustVcType,
) -> Result<(), String> {
    let receiver_ty = infer_expr_type(receiver);
    let char_ty = TrustVcType::Char;
    let element = match &receiver_ty {
        TrustVcType::Seq(element) | TrustVcType::Array(element, _) => element.as_ref(),
        TrustVcType::Map(key, element) => {
            if let Err(found) = bind_call_argument(index, key) {
                return Err(format!(
                    "a `{}` indexed by a key of type `{}`: a key is a value of the map's key \
                     type",
                    receiver_ty.to_type_string(),
                    found.to_type_string()
                ));
            }
            element.as_ref()
        }
        TrustVcType::String | TrustVcType::StrSlice => &char_ty,
        _ if !type_holds_an_integer(declared) => return Ok(()),
        _ => {
            return Err(format!(
                "an element of a `{}` read at type `{}`: the receiver has no element type",
                receiver_ty.to_type_string(),
                declared.to_type_string()
            ))
        }
    };
    let agrees = if is_integer_type(element) || is_integer_type(declared) {
        element == declared
    } else {
        same_integer_positions(element, declared)
    };
    if !agrees {
        return Err(format!(
            "an element of a `{}` read at type `{}`: an element is a value of its \
             collection's element type",
            receiver_ty.to_type_string(),
            declared.to_type_string()
        ));
    }
    Ok(())
}

/// A spec closure's declared `SpecFn` type is its parameters' types and the
/// type its body derives: `|x: u8| -> i8 { x }` mapped over a `Seq<u8>`
/// holding 200 gave the element -56. An integer result binds
/// the body by `int_binding` (a literal the result type holds, a lift to
/// `int`/`nat`); any other disagreement is refused.
pub(super) fn spec_closure_agrees(
    params: &[(String, TrustVcType)],
    body: &TrustVcExpr,
    ty: &TrustVcType,
) -> Result<(), String> {
    // A closure of another declared type is typed where it is applied
    // (`infer_collection_op_type` refuses a combinator it cannot type).
    let TrustVcType::SpecFn(arg_tys, ret) = ty else {
        return Ok(());
    };
    let params_agree = arg_tys.len() == params.len()
        && arg_tys
            .iter()
            .zip(params)
            .all(|(arg, (_, param))| arg == param || same_integer_positions(arg, param));
    let body_ty = infer_expr_type(body);
    let body_agrees = match int_binding(body, ret) {
        IntBinding::Mismatch(_) => false,
        IntBinding::NotInteger => {
            !is_integer_type(&body_ty) && same_integer_positions(&body_ty, ret)
        }
        IntBinding::Same | IntBinding::Literal(_) | IntBinding::LiftToInt => true,
    };
    if params_agree && body_agrees {
        return Ok(());
    }
    Err(format!(
        "a closure declared `{}` over parameters `({})` and a body of type `{}`",
        ty.to_type_string(),
        params
            .iter()
            .map(|(_, param)| param.to_type_string())
            .collect::<Vec<_>>()
            .join(", "),
        body_ty.to_type_string()
    ))
}

/// The names a `match` pattern binds: an identifier binds the scrutinee (at
/// its type); a constructor or struct pattern binds fields at types this
/// validator does not derive (they shadow, unchecked here).
pub(super) fn pattern_binders(pattern: &MatchPattern, scrutinee_ty: &TrustVcType) -> Vec<Binder> {
    match pattern {
        MatchPattern::Ident(name) => vec![(name.clone(), Some(scrutinee_ty.clone()))],
        MatchPattern::Constructor { bindings, .. } => {
            bindings.iter().map(|name| (name.clone(), None)).collect()
        }
        MatchPattern::Struct { fields, .. } => fields
            .iter()
            .filter_map(|field| field.binding.clone())
            .map(|name| (name, None))
            .collect(),
        MatchPattern::Or(alternatives) => alternatives
            .iter()
            .flat_map(|alternative| pattern_binders(alternative, scrutinee_ty))
            .map(|(name, _)| (name, None))
            .collect(),
        MatchPattern::Lit(_) | MatchPattern::Wildcard => Vec::new(),
    }
}
