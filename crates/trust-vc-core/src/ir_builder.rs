//! Builder API for constructing `TrustVcExpr` trees.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Provides ergonomic constructors for `TrustVcExpr` variants. Intended
//! for use in proc macro codegen (Step 3b of #1866 Phase 5) where
//! emitting raw struct literals is verbose and error-prone.
//!
//! All functions are pure constructors and perform no
//! validation — the encoder validates during encoding.

use crate::ir::TrustVcType;
use crate::ir_expr::{
    ArithOp, CollectionOp, CompareOp, IntConstKind, LogicOp, QuantifierKind, SpecialArithOp,
    TrustVcExpr, WrappingMode,
};

// ========================================================================
// Literals
// ========================================================================

/// Boolean literal.
#[must_use]
pub fn bool_lit(value: bool) -> TrustVcExpr {
    TrustVcExpr::BoolLit(value)
}

/// Unit literal.
#[must_use]
pub fn unit_lit() -> TrustVcExpr {
    TrustVcExpr::UnitLit
}

/// Integer literal with explicit type.
#[must_use]
pub fn int_lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty }
}

/// Signed integer literal (defaults to `Int { width: 32 }`).
#[must_use]
pub fn i32_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: TrustVcType::Int { width: 32 },
    }
}

/// Unsigned integer literal (defaults to `Uint { width: 32 }`).
#[must_use]
pub fn u32_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: TrustVcType::Uint { width: 32 },
    }
}

/// Unbounded mathematical integer literal.
#[must_use]
pub fn math_int_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: TrustVcType::MathInt,
    }
}

// ========================================================================
// Variables
// ========================================================================

/// Variable reference with explicit type.
#[must_use]
pub fn var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}

/// Injectively encode a string into a symbol-safe component.
///
/// Replacing punctuation with `_` is not provenance-preserving: distinct
/// source types such as `a::B` and `a__B`, or distinct argument partitions
/// such as `[A_B, C]` and `[A, B_C]`, then share one solver symbol. Hex keeps
/// the complete UTF-8 spelling, and contains no `_`, so the `_` separator in
/// [`arg_type_key`] is unambiguous as well.
fn encode_symbol_component(input: &str) -> String {
    use std::fmt::Write;

    let mut encoded = String::with_capacity(1 + input.len() * 2);
    encoded.push('x');
    for byte in input.as_bytes() {
        write!(&mut encoded, "{byte:02x}").expect("writing to String cannot fail");
    }
    encoded
}

/// Length-frame recursive type-key components so user-controlled nominal names
/// cannot erase variant or child boundaries.
fn framed_type_key(tag: &str, components: &[String]) -> String {
    use std::fmt::Write;

    let mut key = String::new();
    write!(&mut key, "{tag}@{};", components.len()).expect("writing to String cannot fail");
    for component in components {
        write!(&mut key, "{}:", component.len()).expect("writing to String cannot fail");
        key.push_str(component);
    }
    key
}

/// A recursive identity for the complete typed IR shape used by closure UFs.
/// `TrustVcType::to_type_string()` is intentionally presentation-oriented and
/// maps distinct variants such as `TypeParam("T")`, `Datatype { name: "T" }`,
/// and `Opaque("T")` to the same spelling. Closure UF provenance must retain
/// those distinctions, including when they occur below a collection type.
fn closure_uf_type_key(ty: &TrustVcType) -> String {
    match ty {
        TrustVcType::Unit
        | TrustVcType::Bool
        | TrustVcType::Char
        | TrustVcType::StrSlice
        | TrustVcType::String
        | TrustVcType::MathInt
        | TrustVcType::Nat
        | TrustVcType::Real => ty.to_type_string(),
        TrustVcType::Int { width } => framed_type_key("int", &[width.to_string()]),
        TrustVcType::Uint { width } => framed_type_key("uint", &[width.to_string()]),
        TrustVcType::Float { width } => framed_type_key("float", &[width.to_string()]),
        TrustVcType::Seq(element) => {
            framed_type_key("seq", &[closure_uf_type_key(element.as_ref())])
        }
        TrustVcType::Array(element, len) => framed_type_key(
            "array",
            &[closure_uf_type_key(element.as_ref()), len.to_string()],
        ),
        TrustVcType::Set(element) => {
            framed_type_key("set", &[closure_uf_type_key(element.as_ref())])
        }
        TrustVcType::Multiset(element) => {
            framed_type_key("multiset", &[closure_uf_type_key(element.as_ref())])
        }
        TrustVcType::Map(key, value) => framed_type_key(
            "map",
            &[
                closure_uf_type_key(key.as_ref()),
                closure_uf_type_key(value.as_ref()),
            ],
        ),
        TrustVcType::SpecFn(args, ret) => {
            let mut components = args.iter().map(closure_uf_type_key).collect::<Vec<_>>();
            components.push(closure_uf_type_key(ret.as_ref()));
            framed_type_key("spec_fn", &components)
        }
        TrustVcType::Datatype { name, .. } => {
            framed_type_key("datatype", std::slice::from_ref(name))
        }
        TrustVcType::RecursiveRef(name) => {
            framed_type_key("recursive_ref", std::slice::from_ref(name))
        }
        TrustVcType::TypeParam(name) => framed_type_key("type_param", std::slice::from_ref(name)),
        TrustVcType::Poly => "poly".to_string(),
        TrustVcType::Opaque(name) => framed_type_key("opaque", std::slice::from_ref(name)),
    }
}

/// The injective, `_`-joined key of a `SpecFn` value's argument types, shared by
/// every per-signature UF symbol below.
fn arg_type_key(arg_tys: &[TrustVcType]) -> String {
    arg_tys
        .iter()
        .map(closure_uf_type_key)
        .map(|ty| encode_symbol_component(&ty))
        .collect::<Vec<_>>()
        .join("_")
}

/// Reserved prefixes for closure UFs synthesized by this module. The encoder
/// validates their exact receiver/signature shape and fails closed if a source
/// function collides with one of these names.
pub(crate) const SPEC_FN_APPLY_PREFIX: &str = "__trust_vc_spec_fn_apply_";
pub(crate) const CALL_REQUIRES_PREFIX: &str = "__trust_vc_call_requires_";
pub(crate) const CALL_ENSURES_PREFIX: &str = "__trust_vc_call_ensures_";

#[must_use]
pub fn spec_fn_apply_symbol(arg_tys: &[TrustVcType], ret_ty: &TrustVcType) -> String {
    format!(
        "{SPEC_FN_APPLY_PREFIX}{}_to_{}",
        arg_type_key(arg_tys),
        encode_symbol_component(&closure_uf_type_key(ret_ty))
    )
}

/// Stable UF symbol for the OPAQUE reflection predicate `call_requires%(f, args)`
/// — the closure's WRITTEN precondition reflected over a first-class `SpecFn`
/// value. Disjoint from `spec_fn_apply` and from `call_ensures`, so its
/// definitional axiom is a conservative extension that can neither contaminate
/// nor rescue any other obligation. Phase C closure reflection.
#[must_use]
pub fn call_requires_symbol(arg_tys: &[TrustVcType]) -> String {
    format!("{CALL_REQUIRES_PREFIX}{}", arg_type_key(arg_tys))
}

/// Stable UF symbol for the OPAQUE reflection predicate
/// `call_ensures%(f, args, result)` — the closure's WRITTEN postcondition
/// reflected over a first-class `SpecFn` value. Disjoint UF (see
/// [`call_requires_symbol`]). Phase C closure reflection.
#[must_use]
pub fn call_ensures_symbol(arg_tys: &[TrustVcType], ret_ty: &TrustVcType) -> String {
    format!(
        "{CALL_ENSURES_PREFIX}{}_to_{}",
        arg_type_key(arg_tys),
        encode_symbol_component(&closure_uf_type_key(ret_ty))
    )
}

/// Reflect the WRITTEN precondition of a first-class `SpecFn` value: the Bool UF
/// predicate `call_requires%(function, args..)`. Its meaning is fixed ONLY by the
/// definitional axiom co-emitted at the closure literal; direct application is
/// deferred, so this symbol never connects to a real return value. Phase C.
#[must_use]
pub fn call_requires(
    function: TrustVcExpr,
    arg_tys: &[TrustVcType],
    args: Vec<TrustVcExpr>,
) -> TrustVcExpr {
    let mut fn_args = Vec::with_capacity(args.len() + 1);
    fn_args.push(function);
    fn_args.extend(args);
    TrustVcExpr::FnCall {
        name: call_requires_symbol(arg_tys),
        args: fn_args,
        return_ty: TrustVcType::Bool,
    }
}

/// Reflect the WRITTEN postcondition of a first-class `SpecFn` value: the Bool UF
/// predicate `call_ensures%(function, args.., result)`. Definitional-axiom-only
/// meaning (see [`call_requires`]); says NOTHING about whether the closure body
/// establishes the postcondition — the independent def-side obligation forces
/// that. Phase C.
#[must_use]
pub fn call_ensures(
    function: TrustVcExpr,
    arg_tys: &[TrustVcType],
    args: Vec<TrustVcExpr>,
    result: TrustVcExpr,
    ret_ty: &TrustVcType,
) -> TrustVcExpr {
    let mut fn_args = Vec::with_capacity(args.len() + 2);
    fn_args.push(function);
    fn_args.extend(args);
    fn_args.push(result);
    TrustVcExpr::FnCall {
        name: call_ensures_symbol(arg_tys, ret_ty),
        args: fn_args,
        return_ty: TrustVcType::Bool,
    }
}

/// Apply a first-class `SpecFn` value to already-lowered arguments.
#[must_use]
pub fn spec_fn_apply(
    function: TrustVcExpr,
    arg_tys: &[TrustVcType],
    args: Vec<TrustVcExpr>,
    ret_ty: TrustVcType,
) -> TrustVcExpr {
    let mut fn_args = Vec::with_capacity(args.len() + 1);
    fn_args.push(function);
    fn_args.extend(args);
    TrustVcExpr::FnCall {
        name: spec_fn_apply_symbol(arg_tys, &ret_ty),
        args: fn_args,
        return_ty: ret_ty,
    }
}

// ========================================================================
// Arithmetic
// ========================================================================

/// Generic arithmetic expression.
#[must_use]
pub fn arith(op: ArithOp, left: TrustVcExpr, right: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty,
    }
}

/// Addition: `left + right`.
#[must_use]
pub fn add(left: TrustVcExpr, right: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    arith(ArithOp::Add, left, right, ty)
}

/// Subtraction: `left - right`.
#[must_use]
pub fn sub(left: TrustVcExpr, right: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    arith(ArithOp::Sub, left, right, ty)
}

/// Multiplication: `left * right`.
#[must_use]
pub fn mul(left: TrustVcExpr, right: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    arith(ArithOp::Mul, left, right, ty)
}

/// Division: `left / right`.
#[must_use]
pub fn div(left: TrustVcExpr, right: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    arith(ArithOp::Div, left, right, ty)
}

/// Remainder: `left % right`.
#[must_use]
pub fn rem(left: TrustVcExpr, right: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    arith(ArithOp::Rem, left, right, ty)
}

/// Arithmetic negation: `-expr`.
#[must_use]
pub fn neg(expr: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Neg(Box::new(expr))
}

// ========================================================================
// Comparison
// ========================================================================

/// Generic comparison.
#[must_use]
pub fn compare(op: CompareOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}

/// Equal: `left == right`.
#[must_use]
pub fn eq(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    compare(CompareOp::Eq, left, right)
}

/// Not equal: `left != right`.
#[must_use]
pub fn ne(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    compare(CompareOp::Ne, left, right)
}

/// Less than: `left < right`.
#[must_use]
pub fn lt(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    compare(CompareOp::Lt, left, right)
}

/// Less or equal: `left <= right`.
#[must_use]
pub fn le(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    compare(CompareOp::Le, left, right)
}

/// Greater than: `left > right`.
#[must_use]
pub fn gt(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    compare(CompareOp::Gt, left, right)
}

/// Greater or equal: `left >= right`.
#[must_use]
pub fn ge(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    compare(CompareOp::Ge, left, right)
}

// ========================================================================
// Logic
// ========================================================================

/// Logical AND: `left && right`.
#[must_use]
pub fn and(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(left),
        right: Box::new(right),
    }
}

/// Logical OR: `left || right`.
#[must_use]
pub fn or(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: LogicOp::Or,
        left: Box::new(left),
        right: Box::new(right),
    }
}

/// Logical NOT: `!expr`.
#[must_use]
pub fn not(expr: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Not(Box::new(expr))
}

/// Logical implication: `premise ==> conclusion`.
#[must_use]
pub fn implies(premise: TrustVcExpr, conclusion: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Implies {
        premise: Box::new(premise),
        conclusion: Box::new(conclusion),
    }
}

// ========================================================================
// Control flow
// ========================================================================

/// If-then-else: `if cond { then_branch } else { else_branch }`.
#[must_use]
pub fn ite(
    cond: TrustVcExpr,
    then_branch: TrustVcExpr,
    else_branch: TrustVcExpr,
    ty: TrustVcType,
) -> TrustVcExpr {
    TrustVcExpr::Ite {
        cond: Box::new(cond),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
        ty,
    }
}

/// Let binding: `let name: ty = value; body`.
#[must_use]
pub fn let_bind(name: &str, ty: TrustVcType, value: TrustVcExpr, body: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Let {
        name: name.to_string(),
        ty,
        value: Box::new(value),
        body: Box::new(body),
    }
}

// ========================================================================
// Type casts
// ========================================================================

/// Type cast: `expr as to_ty`.
#[must_use]
pub fn cast(expr: TrustVcExpr, from_ty: TrustVcType, to_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Cast {
        expr: Box::new(expr),
        from_ty,
        to_ty,
    }
}

// ========================================================================
// Collections
// ========================================================================

/// Collection operation on a named receiver.
#[must_use]
pub fn collection_op(
    op: CollectionOp,
    receiver: TrustVcExpr,
    receiver_name: Option<&str>,
    args: Vec<TrustVcExpr>,
    ty: TrustVcType,
) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op,
        receiver: Box::new(receiver),
        receiver_name: receiver_name.map(str::to_string),
        args,
        ty,
    }
}

/// Seq/array indexing: `receiver[index]`.
#[must_use]
pub fn index(
    receiver: TrustVcExpr,
    index_expr: TrustVcExpr,
    receiver_name: Option<&str>,
    elem_ty: TrustVcType,
) -> TrustVcExpr {
    TrustVcExpr::Index {
        receiver: Box::new(receiver),
        index: Box::new(index_expr),
        receiver_name: receiver_name.map(str::to_string),
        elem_ty,
    }
}

// ========================================================================
// Quantifiers
// ========================================================================

/// Universal quantifier: `forall |vars| body`.
#[must_use]
pub fn forall(
    bound_vars: Vec<(String, TrustVcType)>,
    body: TrustVcExpr,
    triggers: Option<Vec<Vec<TrustVcExpr>>>,
) -> TrustVcExpr {
    TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars,
        body: Box::new(body),
        triggers,
        trigger_inference_mode: crate::broadcast_state::get_trigger_inference_mode(),
    }
}

/// Existential quantifier: `exists |vars| body`.
#[must_use]
pub fn exists(
    bound_vars: Vec<(String, TrustVcType)>,
    body: TrustVcExpr,
    triggers: Option<Vec<Vec<TrustVcExpr>>>,
) -> TrustVcExpr {
    TrustVcExpr::Quantifier {
        kind: QuantifierKind::Exists,
        bound_vars,
        body: Box::new(body),
        triggers,
        trigger_inference_mode: crate::broadcast_state::get_trigger_inference_mode(),
    }
}

// ========================================================================
// Function calls
// ========================================================================

/// Named function call (uninterpreted or proof function).
#[must_use]
pub fn fn_call(name: &str, args: Vec<TrustVcExpr>, return_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: name.to_string(),
        args,
        return_ty,
    }
}

// ========================================================================
// Integer constants
// ========================================================================

/// `T::MIN` for integer type `ty`.
#[must_use]
pub fn int_min(ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntConst {
        ty,
        kind: IntConstKind::Min,
    }
}

/// `T::MAX` for integer type `ty`.
#[must_use]
pub fn int_max(ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntConst {
        ty,
        kind: IntConstKind::Max,
    }
}

/// `T::BITS` for integer type `ty`.
#[must_use]
pub fn int_bits(ty: TrustVcType) -> TrustVcExpr {
    let width = ty.bit_width().unwrap_or(0);
    TrustVcExpr::IntLit {
        value: i128::from(width),
        ty: TrustVcType::Uint { width: 32 },
    }
}

// ========================================================================
// Bitwise / shift
// ========================================================================

/// Bitwise or shift operation.
#[must_use]
pub fn special_arith(
    op: SpecialArithOp,
    left: TrustVcExpr,
    right: TrustVcExpr,
    ty: TrustVcType,
) -> TrustVcExpr {
    TrustVcExpr::SpecialArith {
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty,
    }
}

// ========================================================================
// Wrapping / checked / saturating arithmetic
// ========================================================================

/// Wrapping/checked/saturating arithmetic method call.
#[must_use]
pub fn wrapping_arith(
    mode: WrappingMode,
    op: ArithOp,
    left: TrustVcExpr,
    right: TrustVcExpr,
    ty: TrustVcType,
) -> TrustVcExpr {
    TrustVcExpr::WrappingArith {
        mode,
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty,
    }
}

#[path = "ir_builder_inferred.rs"]
mod inferred;

pub use inferred::{
    arith_inferred, cast_inferred, ite_inferred, special_arith_inferred, wrapping_arith_inferred,
};

#[cfg(test)]
#[path = "ir_builder_tests.rs"]
mod tests;
