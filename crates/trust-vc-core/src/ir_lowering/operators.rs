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
            return Err(LoweringError::UnsupportedExpr(format!(
                "`==`/`!=` on datatype `{name}` has a hand-written `PartialEq` impl \
                 (a non-structural custom `eq` would make structural lowering unsound) \
                 — call `.eq()` in exec code or compare fields explicitly"
            )));
        }
    }

    lower_binop(&bin.op, left, right)
}

/// If `ty` is a datatype that carries a hand-written `impl PartialEq` — directly,
/// or transitively through a field — return the name of the offending datatype.
/// Recursion is cycle-guarded (recursive datatypes like `enum Nat { Succ(Box<Nat>) }`
/// re-enter their own name). A datatype with only `#[derive(PartialEq)]` (or no
/// `PartialEq`) yields `None`, so its `==` still lowers to structural equality.
fn datatype_with_manual_partial_eq(
    ty: &TrustVcType,
    env: &TypeEnv,
    visited: &mut std::collections::BTreeSet<String>,
) -> Option<String> {
    let TrustVcType::Datatype { name, variants } = ty else {
        return None;
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
    let ty = infer_expr_type(&left);
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

/// Coerce an unsuffixed integer literal's type to match a peer operand.
///
/// Coerces `IntLit` nodes and `Neg(IntLit)` nodes with the default `Int{32}`
/// type — suffixed literals and non-literal expressions are left unchanged.
/// Used by comparisons (#2068), arithmetic (#2071), and bitwise/shift operators.
///
/// The `Neg(IntLit)` case handles expressions like `(-1)` in `x + (-1)` where
/// `x: u8`. Without this, `-1` stays as `Int{32}` (width 32) while `x` is
/// `Uint{8}` (width 8), causing a width mismatch in BV encoding (#2067).
pub(crate) fn coerce_unsuffixed_literal(expr: TrustVcExpr, peer_ty: &TrustVcType) -> TrustVcExpr {
    match expr {
        TrustVcExpr::IntLit {
            value,
            ty: TrustVcType::Int { width: 32 },
        } if matches!(
            peer_ty,
            TrustVcType::Uint { .. }
                | TrustVcType::Int { .. }
                | TrustVcType::MathInt
                | TrustVcType::Nat
                | TrustVcType::Real
        ) =>
        {
            TrustVcExpr::IntLit {
                value,
                ty: peer_ty.clone(),
            }
        }
        TrustVcExpr::Neg(inner)
            if matches!(
                inner.as_ref(),
                TrustVcExpr::IntLit {
                    ty: TrustVcType::Int { width: 32 },
                    ..
                }
            ) && matches!(
                peer_ty,
                TrustVcType::Uint { .. }
                    | TrustVcType::Int { .. }
                    | TrustVcType::MathInt
                    | TrustVcType::Nat
                    | TrustVcType::Real
            ) =>
        {
            if matches!(peer_ty, TrustVcType::Nat) {
                return TrustVcExpr::Neg(inner);
            }
            TrustVcExpr::Neg(Box::new(coerce_unsuffixed_literal(*inner, peer_ty)))
        }
        other => other,
    }
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
    let ty = infer_expr_type(&left);
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
