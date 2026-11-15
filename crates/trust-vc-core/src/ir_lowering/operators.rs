//! Binary and unary operator lowering for TrustVcExpr IR.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #1550 Phase 3 (#1864).

use super::{
    env::{OptionBindingMeta, OptionBindingState},
    infer_expr_type, lower_syn_expr_with_depth, LoweringError, TypeEnv,
};
use crate::encoder::datatype::{selector_symbol_name, tester_symbol_name};
use crate::ir::TrustVcType;
use crate::ir_expr::{ArithOp, CollectionOp, CompareOp, LogicOp, SpecialArithOp, TrustVcExpr};

/// Lowers a `syn::ExprBinary` into a `TrustVcExpr`.
pub(super) fn lower_binary(
    bin: &syn::ExprBinary,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    // An arithmetic operation or comparison over UNSUFFIXED float literals
    // alone (`0.1 + 0.2`, and `a + b == 0.3` once `let a = 0.1; let b = 0.2;`
    // is substituted) has a Rust float type — `f64` unless a use the lowering
    // does not see makes it `f32` — never an exact real. Such a literal is
    // lowered as the exact `real` it is next to a `real` peer, so `0.1 + 0.2
    // == 0.3` was `Verified` where `f64` arithmetic makes it false. Refused,
    // except a comparison of one form with ITSELF (the extractor's reflexive
    // `(-0.0) == (-0.0)` safety obligation), whose operands are one float
    // and one real alike; an operation inside it is refused on its own.
    let reflexive = quote::ToTokens::to_token_stream(&*bin.left).to_string()
        == quote::ToTokens::to_token_stream(&*bin.right).to_string();
    let arithmetic_or_comparison = match &bin.op {
        syn::BinOp::Add(_)
        | syn::BinOp::Sub(_)
        | syn::BinOp::Mul(_)
        | syn::BinOp::Div(_)
        | syn::BinOp::Rem(_) => true,
        syn::BinOp::Eq(_)
        | syn::BinOp::Ne(_)
        | syn::BinOp::Lt(_)
        | syn::BinOp::Le(_)
        | syn::BinOp::Gt(_)
        | syn::BinOp::Ge(_) => !reflexive,
        _ => false,
    };
    if arithmetic_or_comparison
        && is_unsuffixed_float_literal_tree(&bin.left)
        && is_unsuffixed_float_literal_tree(&bin.right)
    {
        return Err(LoweringError::UnsupportedExpr(format!(
            "`{}` operates on unsuffixed float literals only: its type is a Rust float \
             (`f64` by default), whose rounding an exact real does not model",
            quote::ToTokens::to_token_stream(bin)
        )));
    }
    let left = Box::new(lower_syn_expr_with_depth(&bin.left, env, depth)?);
    let guarded_env = match &bin.op {
        syn::BinOp::And(_) => env_with_option_is_some_guard(&bin.left, env),
        _ => None,
    };
    let right_env = guarded_env.as_ref().unwrap_or(env);
    let right = Box::new(lower_syn_expr_with_depth(&bin.right, right_env, depth)?);

    // SOUNDNESS GATE (never a false `Verified`): `==` / `!=` on a datatype that has
    // a hand-written `impl PartialEq` (directly, or transitively via a field) must
    // NOT lower to the structural SMT equality. Such a type's EXEC `==` calls that
    // custom impl, which may be non-structural (e.g. `fn eq(..) -> bool { false }`),
    // so `a == a` structural-lowering to `true` while the impl returns `false` is a
    // false-verify. A `#[derive(PartialEq)]` datatype (structural) — and a datatype
    // with NO `PartialEq` at all (only reachable via spec `==`, which IS extensional
    // structural equality in Verus) — are unaffected. This complements the `.eq()`
    // METHOD gate (dispatch/methods.rs), closing the operator side of the same hole.
    if matches!(&bin.op, syn::BinOp::Eq(_) | syn::BinOp::Ne(_)) {
        let left_ty = infer_expr_type(&left);
        let mut visited = std::collections::BTreeSet::new();
        if let Some(name) = datatype_with_manual_partial_eq(&left_ty, env, &mut visited) {
            // THE IMPL'S OWN `eq` (2026-09-11, rows 385/489): when the LEFT type
            // itself carries the hand-written impl and its `eq` is registered as
            // an inherent method (a `Type__eq` UF with the body axiom the `.eq()`
            // METHOD call already lowers to), `a == b` IS `PartialEq::eq(&a, &b)`
            // in Rust, so lower it to that call; `a != b` is `PartialEq::ne`,
            // which is the impl's `ne` when written and `!eq` otherwise — the
            // exact dispatch. A manual impl reached only through a FIELD of a
            // derived-PartialEq datatype has no axiom for the outer comparison
            // and keeps failing closed below.
            let left_type_name = left_ty.to_type_string();
            if name == left_type_name {
                if let Some(expr) =
                    lower_manual_partial_eq_operator(&bin.op, &left_type_name, env, left, right)
                {
                    return Ok(expr);
                }
                return Err(LoweringError::UnsupportedExpr(format!(
                    "`==`/`!=` on datatype `{name}` has a hand-written `PartialEq` impl \
                     whose `eq` is not registered as an inherent method (a non-structural \
                     custom `eq` would make structural lowering unsound) — call `.eq()` \
                     in exec code or compare fields explicitly"
                )));
            }
            return Err(LoweringError::UnsupportedExpr(format!(
                "`==`/`!=` on datatype `{name}` has a hand-written `PartialEq` impl \
                 (a non-structural custom `eq` would make structural lowering unsound) \
                 — call `.eq()` in exec code or compare fields explicitly"
            )));
        }
        // The left operand's type can be less precise than the right one's
        // (`None == o`), so both are checked from here on.
        let right_ty = infer_expr_type(&right);
        let mut visited = std::collections::BTreeSet::new();
        if let Some(name) = datatype_with_manual_partial_eq(&right_ty, env, &mut visited) {
            return Err(LoweringError::UnsupportedExpr(format!(
                "`==`/`!=` on a value that holds datatype `{name}`, which has a hand-written \
                 `PartialEq` impl (a non-structural custom `eq` would make structural \
                 lowering unsound) — compare fields explicitly"
            )));
        }
        // SOUNDNESS GATE: a float inside a compound value. Rust's `PartialEq` for
        // a derived struct or enum, a tuple, `Option`, `Result`, an array or a
        // `Vec` compares a float component with IEEE equality, under which
        // `NaN != NaN` and `0.0 == -0.0`. Structural equality says a value always
        // equals itself and tells `0.0` from `-0.0`, so it answers both of those
        // the other way. A bare float is not affected: its `==` lowers to IEEE
        // equality.
        let float_holder = [&left_ty, &right_ty]
            .into_iter()
            .find(|ty| float_inside_compound(ty, env))
            .cloned();
        if let Some(ty) = float_holder {
            return Err(LoweringError::UnsupportedExpr(format!(
                "`==`/`!=` on `{}` compares a float inside a compound value: Rust's \
                 `PartialEq` compares it with IEEE equality (NaN is not equal to itself, \
                 0.0 equals -0.0), which structural equality does not model — compare \
                 the float components explicitly",
                ty.to_type_string()
            )));
        }
    }

    lower_binop(&bin.op, left, right)
}

/// Whether `expr` is built from UNSUFFIXED float literals alone (`0.1`,
/// `-(1.5)`, `(0.1 + 0.2) * 3.0`): a closed form whose type only a peer fixes.
/// A conditional, `match` or block whose every value is such a form is one
/// too (`if c { 0.1 } else { 0.2 }`), and so is a value written to a binding
/// whose witness is one (`__trust_vc_bind_like((0.0), 0.1)`, the rendering of
/// `let mut a = 0.0; a = 0.1;`): its type is the untyped float's.
pub(super) fn is_unsuffixed_float_literal_tree(expr: &syn::Expr) -> bool {
    match unparen_expr(expr) {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Float(lit),
            ..
        }) => lit.suffix().is_empty(),
        syn::Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Neg(_)) => {
            is_unsuffixed_float_literal_tree(&unary.expr)
        }
        syn::Expr::Binary(binary) => {
            matches!(
                binary.op,
                syn::BinOp::Add(_)
                    | syn::BinOp::Sub(_)
                    | syn::BinOp::Mul(_)
                    | syn::BinOp::Div(_)
                    | syn::BinOp::Rem(_)
            ) && is_unsuffixed_float_literal_tree(&binary.left)
                && is_unsuffixed_float_literal_tree(&binary.right)
        }
        syn::Expr::If(expr_if) => match &expr_if.else_branch {
            Some((_, else_branch)) => {
                block_value_is_unsuffixed_float_form(&expr_if.then_branch)
                    && is_unsuffixed_float_literal_tree(else_branch)
            }
            None => false,
        },
        syn::Expr::Match(expr_match) => {
            !expr_match.arms.is_empty()
                && expr_match
                    .arms
                    .iter()
                    .all(|arm| is_unsuffixed_float_literal_tree(&arm.body))
        }
        syn::Expr::Block(block) => block_value_is_unsuffixed_float_form(&block.block),
        syn::Expr::Call(call) => {
            matches!(
                &*call.func,
                syn::Expr::Path(path)
                    if path.qself.is_none()
                        && path.path.is_ident(crate::ir_lowering::BIND_LIKE_MARKER)
            ) && call.args.len() == 2
                && call.args.iter().all(is_unsuffixed_float_literal_tree)
        }
        _ => false,
    }
}

/// Whether `block`'s value (its tail expression) is an unsuffixed float form.
fn block_value_is_unsuffixed_float_form(block: &syn::Block) -> bool {
    matches!(block.stmts.last(), Some(syn::Stmt::Expr(tail, None))
        if is_unsuffixed_float_literal_tree(tail))
}

/// Whether `ty` holds a float below its top level: in a field of a datatype
/// (a struct, an enum payload, a tuple, `Option`, `Result`), an element of a
/// sequence, array, set or multiset, or a key or value of a map. A bare float
/// is not reported, since its `==` lowers to IEEE equality.
pub(crate) fn float_inside_compound(ty: &TrustVcType, env: &TypeEnv) -> bool {
    !matches!(ty, TrustVcType::Float { .. }) && type_is_or_holds_float(ty, Some(env))
}

/// Whether `ty` is a float or holds one anywhere inside it. `env` looks up a
/// recursive reference's datatype; a recursive reference to a datatype that is
/// neither being walked nor found in `env` counts as holding a float, because
/// its fields cannot be checked.
pub(crate) fn type_is_or_holds_float(ty: &TrustVcType, env: Option<&TypeEnv>) -> bool {
    type_holds_float(ty, env, &mut std::collections::BTreeSet::new())
}

fn type_holds_float(
    ty: &TrustVcType,
    env: Option<&TypeEnv>,
    visited: &mut std::collections::BTreeSet<String>,
) -> bool {
    match ty {
        TrustVcType::Float { .. } => true,
        TrustVcType::Seq(inner)
        | TrustVcType::Array(inner, _)
        | TrustVcType::Set(inner)
        | TrustVcType::Multiset(inner) => type_holds_float(inner, env, visited),
        TrustVcType::Map(key, value) => {
            type_holds_float(key, env, visited) || type_holds_float(value, env, visited)
        }
        TrustVcType::Datatype { name, variants } => {
            if !visited.insert(name.clone()) {
                return false;
            }
            variants.iter().any(|variant| {
                variant
                    .fields
                    .iter()
                    .any(|(_, field_ty)| type_holds_float(field_ty, env, visited))
            })
        }
        TrustVcType::RecursiveRef(name) => {
            if visited.contains(name) {
                return false;
            }
            match env.and_then(|env| env.lookup_type_alias(name)).cloned() {
                Some(resolved) => type_holds_float(&resolved, env, visited),
                None => true,
            }
        }
        _ => false,
    }
}

/// Why `==` on an element of this type is not the solver's structural equality,
/// if it is not: the element is or holds a float, or holds a datatype with a
/// hand-written `PartialEq`. `Vec::contains` and slice `contains` call the
/// element's `PartialEq`, so a membership test over such elements cannot be
/// read as structural membership.
pub(crate) fn element_equality_not_structural(elem: &TrustVcType, env: &TypeEnv) -> Option<String> {
    if matches!(elem, TrustVcType::Float { .. }) || float_inside_compound(elem, env) {
        return Some(format!(
            "its element type `{}` is or holds a float, which Rust's `PartialEq` compares \
             with IEEE equality (NaN is not equal to itself, 0.0 equals -0.0)",
            elem.to_type_string()
        ));
    }
    let mut visited = std::collections::BTreeSet::new();
    datatype_with_manual_partial_eq(elem, env, &mut visited).map(|name| {
        format!(
            "its element type `{}` holds datatype `{name}`, which has a hand-written \
             `PartialEq` impl",
            elem.to_type_string()
        )
    })
}

/// `a == b` / `a != b` on a datatype whose hand-written `PartialEq` methods are
/// registered as inherent-method UFs: `eq` → `Type__eq(a, b)`, `ne` → the
/// written `Type__ne(a, b)` when it exists, else `!Type__eq(a, b)` (Rust's
/// default `ne`). `None` when the impl's `eq` is not registered (the caller
/// keeps the structural gate's fail-closed error). Both operands are passed
/// bare — a `PartialEq` impl on a concrete type never takes the trait UF's
/// `Poly` self-domain, and the method's `&other` borrow is erased exactly as
/// the `.eq(&other)` method-call path erases it.
fn lower_manual_partial_eq_operator(
    op: &syn::BinOp,
    type_name: &str,
    env: &TypeEnv,
    left: Box<TrustVcExpr>,
    right: Box<TrustVcExpr>,
) -> Option<TrustVcExpr> {
    let eq_meta = env.lookup_method(type_name, "eq")?;
    if eq_meta.box_receiver.is_some() {
        return None;
    }
    let call = |meta: &crate::ir_lowering::env::MethodMeta| TrustVcExpr::FnCall {
        name: meta.uf_name.clone(),
        args: vec![(*left).clone(), (*right).clone()],
        return_ty: meta.return_type.clone(),
    };
    match op {
        syn::BinOp::Eq(_) => Some(call(eq_meta)),
        syn::BinOp::Ne(_) => match env.lookup_method(type_name, "ne") {
            Some(ne_meta) if ne_meta.box_receiver.is_none() => Some(call(ne_meta)),
            _ => Some(TrustVcExpr::Not(Box::new(call(eq_meta)))),
        },
        _ => None,
    }
}

/// If `ty` is a datatype that carries a hand-written `impl PartialEq` — directly,
/// or transitively through a field — or a collection whose elements (a map's
/// keys or values) hold one, return the name of the offending datatype. `==` on
/// a `Vec` or a map calls the elements' `PartialEq`, so a hand-written one
/// there makes the collection's `==` non-structural too.
/// Recursion is cycle-guarded (recursive datatypes like `enum Nat { Succ(Box<Nat>) }`
/// re-enter their own name). A datatype with only `#[derive(PartialEq)]` (or no
/// `PartialEq`) yields `None`, so its `==` still lowers to structural equality.
fn datatype_with_manual_partial_eq(
    ty: &TrustVcType,
    env: &TypeEnv,
    visited: &mut std::collections::BTreeSet<String>,
) -> Option<String> {
    let (name, variants) = match ty {
        TrustVcType::Datatype { name, variants } => (name, variants),
        TrustVcType::Seq(inner)
        | TrustVcType::Array(inner, _)
        | TrustVcType::Set(inner)
        | TrustVcType::Multiset(inner) => {
            return datatype_with_manual_partial_eq(inner, env, visited);
        }
        TrustVcType::Map(key, value) => {
            return datatype_with_manual_partial_eq(key, env, visited)
                .or_else(|| datatype_with_manual_partial_eq(value, env, visited));
        }
        _ => return None,
    };
    if env.has_manual_partial_eq(name) {
        return Some(name.clone());
    }
    if !visited.insert(name.clone()) {
        return None;
    }
    variants.iter().find_map(|variant| {
        variant
            .fields
            .iter()
            .find_map(|(_, field_ty)| datatype_with_manual_partial_eq(field_ty, env, visited))
    })
}

fn env_with_option_is_some_guard(left: &syn::Expr, env: &TypeEnv) -> Option<TypeEnv> {
    let (name, ty) = option_var_guarded_by_is_some(left, env)?;
    let mut guarded = env.clone();
    guarded.insert_option_binding(
        name,
        OptionBindingMeta {
            ty,
            state: OptionBindingState::Some { value: None },
        },
    );
    Some(guarded)
}

fn option_var_guarded_by_is_some(left: &syn::Expr, env: &TypeEnv) -> Option<(String, TrustVcType)> {
    let syn::Expr::MethodCall(method_call) = unparen_expr(left) else {
        return None;
    };
    if method_call.method != "is_some" || !method_call.args.is_empty() {
        return None;
    }
    let syn::Expr::Path(receiver_path) = unparen_expr(&method_call.receiver) else {
        return None;
    };
    if receiver_path.path.segments.len() != 1 {
        return None;
    }
    let name = receiver_path.path.segments[0].ident.to_string();
    let ty = env.lookup(&name)?.clone();
    match &ty {
        TrustVcType::Datatype { name, .. } if name.starts_with("Option<") => {
            Some((receiver_path.path.segments[0].ident.to_string(), ty))
        }
        _ => None,
    }
}

fn unparen_expr(expr: &syn::Expr) -> &syn::Expr {
    let mut current = expr;
    while let syn::Expr::Paren(paren) = current {
        current = &paren.expr;
    }
    current
}

fn lower_binop(
    op: &syn::BinOp,
    left: Box<TrustVcExpr>,
    right: Box<TrustVcExpr>,
) -> Result<TrustVcExpr, LoweringError> {
    match op {
        // Arithmetic
        syn::BinOp::Add(_) => Ok(lower_arith(ArithOp::Add, left, right)),
        syn::BinOp::Sub(_) => Ok(lower_arith(ArithOp::Sub, left, right)),
        syn::BinOp::Mul(_) => Ok(lower_arith(ArithOp::Mul, left, right)),
        syn::BinOp::Div(_) => Ok(lower_arith(ArithOp::Div, left, right)),
        syn::BinOp::Rem(_) => Ok(lower_arith(ArithOp::Rem, left, right)),
        // Comparison
        syn::BinOp::Eq(_) => Ok(lower_cmp(CompareOp::Eq, left, right)),
        syn::BinOp::Ne(_) => Ok(lower_cmp(CompareOp::Ne, left, right)),
        syn::BinOp::Lt(_) => Ok(lower_cmp(CompareOp::Lt, left, right)),
        syn::BinOp::Le(_) => Ok(lower_cmp(CompareOp::Le, left, right)),
        syn::BinOp::Gt(_) => Ok(lower_cmp(CompareOp::Gt, left, right)),
        syn::BinOp::Ge(_) => Ok(lower_cmp(CompareOp::Ge, left, right)),
        // Short-circuit logical
        syn::BinOp::And(_) => Ok(TrustVcExpr::Logic {
            op: LogicOp::And,
            left,
            right,
        }),
        syn::BinOp::Or(_) => Ok(TrustVcExpr::Logic {
            op: LogicOp::Or,
            left,
            right,
        }),
        // Bitwise and shift
        syn::BinOp::BitAnd(_) => Ok(lower_special(SpecialArithOp::BitAnd, left, right)),
        syn::BinOp::BitOr(_) => Ok(lower_special(SpecialArithOp::BitOr, left, right)),
        syn::BinOp::BitXor(_) if operands_are_bool(&left, &right) => {
            Ok(lower_cmp(CompareOp::Ne, left, right))
        }
        syn::BinOp::BitXor(_) => Ok(lower_special(SpecialArithOp::BitXor, left, right)),
        syn::BinOp::Shl(_) => Ok(lower_special(SpecialArithOp::Shl, left, right)),
        syn::BinOp::Shr(_) => Ok(lower_special(SpecialArithOp::Shr, left, right)),
        // Compound assignment — not supported in verification
        syn::BinOp::AddAssign(_)
        | syn::BinOp::SubAssign(_)
        | syn::BinOp::MulAssign(_)
        | syn::BinOp::DivAssign(_)
        | syn::BinOp::RemAssign(_)
        | syn::BinOp::BitAndAssign(_)
        | syn::BinOp::BitOrAssign(_)
        | syn::BinOp::BitXorAssign(_)
        | syn::BinOp::ShlAssign(_)
        | syn::BinOp::ShrAssign(_) => Err(LoweringError::UnsupportedBinOp(
            "compound assignment not supported in verification".into(),
        )),
        _ => Err(LoweringError::UnsupportedBinOp(
            "unknown binary operator".into(),
        )),
    }
}

fn operands_are_bool(left: &TrustVcExpr, right: &TrustVcExpr) -> bool {
    matches!(infer_expr_type(left), TrustVcType::Bool)
        && matches!(infer_expr_type(right), TrustVcType::Bool)
}

fn lower_arith(op: ArithOp, left: Box<TrustVcExpr>, right: Box<TrustVcExpr>) -> TrustVcExpr {
    // Coerce unsuffixed literals bidirectionally, same as lower_cmp (#2071).
    // Without this, `0 + x` where `x: u32` produces ty=Int{32} (signed)
    // because the literal defaults to Int{32} and left-only inference picks it up.
    let left_ty = infer_expr_type(&left);
    let right_ty = infer_expr_type(&right);
    if matches!(op, ArithOp::Add) && matches!(left_ty, TrustVcType::Seq(_)) && left_ty == right_ty {
        let receiver_name = collection_receiver_name(&left);
        return TrustVcExpr::CollectionOp {
            op: CollectionOp::Add,
            receiver: left,
            receiver_name,
            args: vec![*right],
            ty: left_ty,
        };
    }
    let left = Box::new(coerce_unsuffixed_literal(*left, &right_ty));
    let right = Box::new(coerce_unsuffixed_literal(*right, &left_ty));
    // The node's type is DERIVED from both operands (`types.rs`), never copied
    // from the left one: `x + y` with `x: u8`, `y: i16` is Verus spec
    // arithmetic over the integers, not a `u8` — typing it `u8` made a
    // comparison read the (wider, signed) sum as unsigned, so `0u8 + (-1i16)`
    // compared as 65535 and `x + y >= 256` came back Verified. A difference
    // of two `nat`s is an `int`.
    let ty = super::arith_node_type(op, &left, &right);
    TrustVcExpr::Arith {
        op,
        left,
        right,
        ty,
    }
}

fn collection_receiver_name(expr: &TrustVcExpr) -> Option<String> {
    match expr {
        TrustVcExpr::Var { name, .. } => Some(name.clone()),
        TrustVcExpr::FnCall { name, args, .. } if args.is_empty() => Some(name.clone()),
        TrustVcExpr::CollectionOp {
            receiver_name,
            receiver,
            ..
        } => receiver_name
            .clone()
            .or_else(|| collection_receiver_name(receiver)),
        TrustVcExpr::Index { .. } => None,
        TrustVcExpr::Cast { expr, .. } => collection_receiver_name(expr),
        _ => None,
    }
}

fn lower_cmp(op: CompareOp, left: Box<TrustVcExpr>, right: Box<TrustVcExpr>) -> TrustVcExpr {
    let left_ty = infer_expr_type(&left);
    let right_ty = infer_expr_type(&right);
    // Coerce unsuffixed integer literals to match the other operand's type (#2068).
    let left = Box::new(coerce_unsuffixed_literal(*left, &right_ty));
    let right = Box::new(coerce_unsuffixed_literal(*right, &left_ty));
    if matches!(op, CompareOp::Eq | CompareOp::Ne) {
        if let Some(option) = finite_integer_option_type_info(&infer_expr_type(&left)) {
            if infer_expr_type(&right) == option.datatype_ty() {
                let eq = option_structural_eq_expr(&option, *left, *right);
                return if matches!(op, CompareOp::Eq) {
                    eq
                } else {
                    TrustVcExpr::Not(Box::new(eq))
                };
            }
        }
    }
    TrustVcExpr::Compare { op, left, right }
}

struct OptionTypeInfo {
    datatype_name: String,
    value_ty: TrustVcType,
}

impl OptionTypeInfo {
    fn datatype_ty(&self) -> TrustVcType {
        TrustVcType::Datatype {
            name: self.datatype_name.clone(),
            variants: vec![
                crate::ir::DatatypeVariant::new("None", vec![]),
                crate::ir::DatatypeVariant::new(
                    "Some",
                    vec![("0".to_string(), self.value_ty.clone())],
                ),
            ],
        }
    }
}

fn finite_integer_option_type_info(ty: &TrustVcType) -> Option<OptionTypeInfo> {
    let TrustVcType::Datatype { name, variants } = ty else {
        return None;
    };
    if !name.starts_with("Option<") {
        return None;
    }
    let value_ty = variants
        .iter()
        .find(|variant| variant.name == "Some")
        .and_then(|variant| variant.fields.first())
        .map(|(_, field_ty)| field_ty.clone())?;
    value_ty.is_integer().then(|| OptionTypeInfo {
        datatype_name: name.clone(),
        value_ty,
    })
}

fn option_structural_eq_expr(
    option: &OptionTypeInfo,
    left: TrustVcExpr,
    right: TrustVcExpr,
) -> TrustVcExpr {
    let left_none = option_tester_call(option, "None", left.clone());
    let right_none = option_tester_call(option, "None", right.clone());
    let left_some = option_tester_call(option, "Some", left.clone());
    let right_some = option_tester_call(option, "Some", right.clone());
    let value_eq = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(option_some_selector(option, left)),
        right: Box::new(option_some_selector(option, right)),
    };

    TrustVcExpr::Logic {
        op: LogicOp::Or,
        left: Box::new(TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(left_none),
            right: Box::new(right_none),
        }),
        right: Box::new(TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(left_some),
            right: Box::new(TrustVcExpr::Logic {
                op: LogicOp::And,
                left: Box::new(right_some),
                right: Box::new(value_eq),
            }),
        }),
    }
}

fn option_tester_call(
    option: &OptionTypeInfo,
    variant: &str,
    receiver: TrustVcExpr,
) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: tester_symbol_name(&option.datatype_name, variant),
        args: vec![receiver],
        return_ty: TrustVcType::Bool,
    }
}

fn option_some_selector(option: &OptionTypeInfo, receiver: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: selector_symbol_name(&option.datatype_name, "Some", "0", 0),
        args: vec![receiver],
        return_ty: option.value_ty.clone(),
    }
}

/// Coerce an unsuffixed integer literal's type to match a peer operand —
/// only where that never changes its value.
///
/// Coerces `IntLit` nodes and `Neg(IntLit)` nodes with the default `Int{32}`
/// type — suffixed literals and non-literal expressions are left unchanged.
/// Used by comparisons (#2068), arithmetic (#2071), and bitwise/shift operators.
///
/// VALUE-PRESERVING: the literal takes the peer's type only when the value it
/// denotes (for `Neg(IntLit v)`, `-v`) is a value of that type
/// (`types::untyped_literal_fits`). `(-1)` next to a `u8` used to become
/// `Neg(IntLit { 1, u8 })` — the `u8` negation of 1, i.e. 255 — and `300` next
/// to a `u8` a `u8` literal the type cannot hold. Such a literal now keeps its
/// own type, which makes the enclosing operation mixed-type and therefore
/// exact (`types.rs`).
pub(crate) fn coerce_unsuffixed_literal(expr: TrustVcExpr, peer_ty: &TrustVcType) -> TrustVcExpr {
    let literal = match &expr {
        TrustVcExpr::IntLit { .. } => true,
        TrustVcExpr::Neg(inner) => matches!(inner.as_ref(), TrustVcExpr::IntLit { .. }),
        _ => false,
    };
    if !literal {
        return expr;
    }
    super::untyped_literal_at_peer(&expr, peer_ty).unwrap_or(expr)
}

fn lower_special(
    op: SpecialArithOp,
    left: Box<TrustVcExpr>,
    right: Box<TrustVcExpr>,
) -> TrustVcExpr {
    // Shifts (`<<`/`>>`) have INDEPENDENT operand types: the result type and
    // signedness follow the LEFT operand only, and the shift-amount type is
    // unrelated. Coercing the LEFT (value) operand toward the amount type — as
    // the bitwise operators below do bidirectionally — is unsound: it would
    // flip a suffixed `1i32`/`-1i32` LHS to the amount's `u32` type, so a signed
    // left-shift onto the sign bit folds to the out-of-range `+2^31` instead of
    // `i32::MIN`, and a signed `>>` lowers to logical `bvlshr` instead of
    // arithmetic `bvashr` (P1-E shifts cluster). So leave the LEFT operand at its
    // lowered type and take the result type from it.
    //
    // The amount (RIGHT) is still coerced toward the LEFT type: an unsuffixed
    // shift amount defaults to `Int{32}` (signed), which the BV encoder rejects
    // as a "possibly negative shift". Coercing it to the LHS type is
    // value-preserving (the amount is unchanged) and keeps `1u64 << 35` etc.
    // verifying — the amount's signedness never affects the shifted value.
    if matches!(op, SpecialArithOp::Shl | SpecialArithOp::Shr) {
        let left_ty = infer_expr_type(&left);
        let right = Box::new(coerce_unsuffixed_literal(*right, &left_ty));
        return TrustVcExpr::SpecialArith {
            op,
            left,
            right,
            ty: left_ty,
        };
    }

    // Bitwise AND/OR/XOR: both operands share a single type in Rust, so coerce
    // unsuffixed literals bidirectionally (#2071).
    let left_ty = infer_expr_type(&left);
    let right_ty = infer_expr_type(&right);
    let left = Box::new(coerce_unsuffixed_literal(*left, &right_ty));
    let right = Box::new(coerce_unsuffixed_literal(*right, &left_ty));
    // Derived from both operands, as for arithmetic (`lower_arith`).
    let ty = super::derived_node_type(&left, &right);
    TrustVcExpr::SpecialArith {
        op,
        left,
        right,
        ty,
    }
}

/// Unwraps `Paren`/`Group` wrappers to reach the underlying expression.
fn peel_paren_group(expr: &syn::Expr) -> &syn::Expr {
    match expr {
        syn::Expr::Paren(p) => peel_paren_group(&p.expr),
        syn::Expr::Group(g) => peel_paren_group(&g.expr),
        other => other,
    }
}

/// Lowers `-<int-literal>` with diagnostic-parity range checking (#2778).
///
/// When the operand of a leading unary negation is a suffixed integer literal,
/// the *negated* value is the thing Rust/Verus range-check against the type
/// (`in_negative_literal`): `-128i8` is `i8::MIN` and valid even though the bare
/// literal `128i8` would not fit `i8`. We therefore parse the literal here and
/// run the range check on `-value`, bypassing `lower_lit`'s *positive*-literal
/// check, then build `Neg(IntLit { value, ty })` so downstream encoding is
/// unchanged. Returns `None` when the operand is not a direct integer literal,
/// in which case the caller lowers it normally.
fn lower_negated_int_literal(operand: &syn::Expr) -> Result<Option<TrustVcExpr>, LoweringError> {
    let syn::Expr::Lit(syn::ExprLit {
        lit: syn::Lit::Int(int_lit),
        ..
    }) = peel_paren_group(operand)
    else {
        return Ok(None);
    };
    let value: i128 = int_lit
        .base10_parse()
        .map_err(|e| LoweringError::InvalidLiteral(format!("integer parse: {}", e)))?;
    let suffix = int_lit.suffix();
    let ty = super::atoms::type_from_int_suffix(suffix)?;
    let negated = value
        .checked_neg()
        .ok_or_else(|| LoweringError::InvalidLiteral("integer literal negation overflow".into()))?;
    // Range-check the *negated* value against the declared type, matching
    // upstream `check_lit_int(in_negative_literal = true, ...)`. Only suffixed
    // literals carry a resolved finite-width type at lowering time; unsuffixed
    // literals use the `Int { width: 32 }` placeholder and are coerced later,
    // so they must not be range-checked here (see `lower_lit`).
    if !suffix.is_empty() {
        super::diagnostic_parity::check_int_literal_in_range(negated, &ty)?;
    }
    if suffix == "i32" {
        // `-128i32` is the `i32` literal -128, pinned like `128i32`
        // (`atoms::typed_int_literal`).
        return Ok(Some(super::atoms::typed_int_literal(
            TrustVcExpr::IntLit { value: negated, ty },
            suffix,
        )));
    }
    Ok(Some(TrustVcExpr::Neg(Box::new(TrustVcExpr::IntLit {
        value,
        ty,
    }))))
}

/// Lowers a `syn::ExprUnary` into a `TrustVcExpr`.
pub(super) fn lower_unary(
    un: &syn::ExprUnary,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    // Diagnostic parity (#2778): `-<int-literal>` is range-checked against the
    // negated value, so handle it before lowering the inner literal (which
    // would otherwise reject e.g. `128i8` inside the valid `-128i8`).
    if matches!(un.op, syn::UnOp::Neg(_)) {
        if let Some(expr) = lower_negated_int_literal(&un.expr)? {
            return Ok(expr);
        }
    }
    let inner = Box::new(lower_syn_expr_with_depth(&un.expr, env, depth)?);
    // A bitwise `!` over an UNSUFFIXED integer literal form (`!0`, `!w` once
    // `let w = 0` is substituted, a branch value of one) is a value of the
    // type the peer it meets gives it (`!0` is 255 in `u8`, -1 in `i32`), but
    // it is not an untyped form: it stays an `i32` value, and next to a `u8`
    // peer made a mixed, hence EXACT, operation — `!0 + y` raised no overflow
    // obligation. Refused.
    if matches!(un.op, syn::UnOp::Not(_)) && super::is_untyped_literal(&inner) {
        return Err(LoweringError::UnsupportedExpr(format!(
            "`{}` is a bitwise `!` of an unsuffixed integer literal, whose value depends on \
             the type a peer gives it",
            quote::ToTokens::to_token_stream(un)
        )));
    }
    match &un.op {
        syn::UnOp::Not(_) => Ok(TrustVcExpr::Not(inner)),
        syn::UnOp::Neg(_) => Ok(TrustVcExpr::Neg(inner)),
        syn::UnOp::Deref(_) => {
            if let syn::Expr::Path(path) = &*un.expr {
                if path.path.segments.len() == 1 {
                    if let Some(segment) = path.path.segments.last() {
                        let name = segment.ident.to_string();
                        if env.is_erased_shared_ref_var(&name) {
                            return Ok(*inner);
                        }
                    }
                }
            }
            Err(LoweringError::UnsupportedUnOp(
                "dereference expressions are not supported in verification syntax; \
                 dereference expressions are only supported for erased immutable reference \
                 variables; use the referent variable directly instead of `*x`"
                    .into(),
            ))
        }
        _ => Err(LoweringError::UnsupportedUnOp(
            "unknown unary operator".into(),
        )),
    }
}
