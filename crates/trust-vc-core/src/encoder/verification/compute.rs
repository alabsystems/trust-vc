// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Bounded symbolic compute interpreter for `assert_by_compute!`.
//!
//! Collects equality bindings from in-scope assumptions, substitutes into
//! the target assertion, then runs the existing concrete evaluator. This
//! upgrades compute mode from "constant folding" to "bounded proof by
//! computation" without introducing a second solver path.
//!
//! Part of #2454.

use std::collections::{HashMap, HashSet};

use crate::encoder::AYEncoder;
use crate::ir::{ArithOp, CompareOp, LogicOp, TrustVcExpr, TrustVcType};
use crate::ir_expr::{MatchArm, MatchPattern, StructPatternField};
use crate::match_pattern_scope::is_ignored_match_binding;
use crate::prepared_context::PreparedObligation;

use super::super::ir_encoder::normalize::accumulate_equality_binding;

const COMPUTE_UNFOLD_LIMIT: usize = 32;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ComputeValue {
    Bool(bool),
    Int(i128),
    Unit,
    /// A fully-reduced algebraic datatype value (tuples and structs are
    /// single-variant datatypes; enums carry the matched variant). Fields are
    /// stored in declaration order so projection and reconstruction stay
    /// deterministic. Mirrors the concrete evaluator's `Datatype` value in
    /// `const_eval.rs`; kept here so the unfolding body interpreter can fold
    /// constructor/selector/tester calls and `Match` without a second solver
    /// path. Part of backlog #4 by(compute) Phase 1.
    Datatype {
        type_name: String,
        variant_name: String,
        fields: Vec<(String, ComputeValue)>,
    },
}

impl ComputeValue {
    fn to_expr(&self, ty: &TrustVcType) -> Option<TrustVcExpr> {
        match self {
            Self::Bool(value) if matches!(ty, TrustVcType::Bool) => {
                Some(TrustVcExpr::BoolLit(*value))
            }
            // Only a value the type HOLDS becomes a literal of it (§5b rule 6):
            // an out-of-range value is not re-read at the type (`IntLit { -1,
            // u8 }` has two readings), so the evaluation declines.
            Self::Int(value)
                if matches!(
                    ty,
                    TrustVcType::Int { .. }
                        | TrustVcType::Uint { .. }
                        | TrustVcType::MathInt
                        | TrustVcType::Nat
                ) && crate::ir_lowering::type_holds_integer(ty, *value) == Some(true) =>
            {
                Some(TrustVcExpr::IntLit {
                    value: *value,
                    ty: ty.clone(),
                })
            }
            Self::Unit if matches!(ty, TrustVcType::Unit) => Some(TrustVcExpr::UnitLit),
            Self::Datatype {
                type_name,
                variant_name,
                fields,
            } => {
                let TrustVcType::Datatype { name, variants } = ty else {
                    return None;
                };
                if type_name != name {
                    return None;
                }
                let variant = variants
                    .iter()
                    .find(|candidate| candidate.name == *variant_name)?;
                if variant.fields.len() != fields.len() {
                    return None;
                }
                let args = fields
                    .iter()
                    .zip(variant.fields.iter())
                    .map(|((_, value), (_, field_ty))| {
                        // A self-recursive child field is declared `RecursiveRef(name)`,
                        // which carries no variant metadata; resolve it back to the
                        // owning datatype so the nested value reconstructs too.
                        value.to_expr(resolve_self_recursive_ref(field_ty, ty))
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(TrustVcExpr::FnCall {
                    name: crate::encoder::datatype::variant_symbol_name(name, variant_name),
                    args,
                    return_ty: ty.clone(),
                })
            }
            _ => None,
        }
    }
}

/// Wrap a computed integer to its fixed-width type in two's complement.
///
/// Mirrors the symbolic encoder's `wrap_int_to_explicit_range`:
/// - `Uint { width }`  → `value mod 2^width`            (range `[0, 2^width)`)
/// - `Int { width }`   → `((value + 2^(w-1)) mod 2^w) - 2^(w-1)`
///   (range `[-2^(w-1), 2^(w-1))`)
/// - any width-less type (`MathInt`/`Nat`/`Real`/…) → unchanged (unbounded math)
///
/// Returns `None` (fail closed) only when the value cannot be represented without
/// `i128` overflow for the requested width (width ≥ 128, or an unsigned result
/// that would exceed `i128::MAX`). The common finite widths (8/16/32/64) always
/// succeed, so a genuine wrap (e.g. `255u8 + 1 → 0`) is computed exactly rather
/// than dropped. Keeping it consistent with the symbolic path is what prevents
/// `recover_assert_by_incompleteness_via_compute` from manufacturing a spurious
/// `Verified` on an overflowing fixed-width spec-fn body.
fn wrap_compute_int_to_type(value: i128, ty: &TrustVcType) -> Option<i128> {
    let (width, is_unsigned) = match ty {
        TrustVcType::Uint { width } => (*width, true),
        TrustVcType::Int { width } => (*width, false),
        // No fixed width (MathInt / Nat / Real / Bool / …): unbounded, no wrap.
        _ => return Some(value),
    };
    if width == 0 {
        return Some(0);
    }
    // `2^width` (the modulus) must fit in a positive i128. `1i128 << 127`
    // overflows, so for width >= 127 (only u128/i128 in practice) fall closed
    // rather than wrap against a bogus modulus.
    if width >= 127 {
        return None;
    }
    let modulus = 1i128 << width;
    if is_unsigned {
        Some(value.rem_euclid(modulus))
    } else {
        let half = 1i128 << (width - 1);
        Some((value + half).rem_euclid(modulus) - half)
    }
}

/// Resolves a self-recursive child field type to its owning datatype.
///
/// The IR models only self-recursive carriers, so a `RecursiveRef(name)` field
/// always refers back to the datatype that declares it (`owner`). The bare
/// `RecursiveRef` carries no variant metadata, so [`ComputeValue::to_expr`] cannot
/// reconstruct a value under it; swapping in the full `Datatype` owner lets a
/// recursive datatype value round-trip to an expression.
fn resolve_self_recursive_ref<'a>(
    field_ty: &'a TrustVcType,
    owner: &'a TrustVcType,
) -> &'a TrustVcType {
    if let (
        TrustVcType::RecursiveRef(name),
        TrustVcType::Datatype {
            name: owner_name, ..
        },
    ) = (field_ty, owner)
    {
        if name == owner_name {
            return owner;
        }
    }
    field_ty
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ComputeCallKey {
    name: String,
    args: Vec<ComputeValue>,
}

struct ComputeEvaluator<'a> {
    body_catalog: &'a HashMap<String, super::body_support::ExtractedBodyAxiom>,
    memo: HashMap<ComputeCallKey, ComputeValue>,
    active: HashSet<ComputeCallKey>,
}

impl<'a> ComputeEvaluator<'a> {
    fn new(body_catalog: &'a HashMap<String, super::body_support::ExtractedBodyAxiom>) -> Self {
        Self {
            body_catalog,
            memo: HashMap::new(),
            active: HashSet::new(),
        }
    }

    fn eval_bool(&mut self, expr: &TrustVcExpr) -> Option<bool> {
        match self.eval_expr(expr, COMPUTE_UNFOLD_LIMIT)? {
            ComputeValue::Bool(value) => Some(value),
            _ => None,
        }
    }

    fn eval_expr(&mut self, expr: &TrustVcExpr, remaining_calls: usize) -> Option<ComputeValue> {
        match expr {
            TrustVcExpr::BoolLit(value) => Some(ComputeValue::Bool(*value)),
            TrustVcExpr::IntLit { value, .. } => Some(ComputeValue::Int(*value)),
            TrustVcExpr::UnitLit => Some(ComputeValue::Unit),
            // An untyped literal OPERATION (`200 + 100`) is computed in the type
            // of the peer it meets, which this evaluator does not see: its value
            // is known only when every type agrees on it; otherwise decline.
            TrustVcExpr::Neg(_) | TrustVcExpr::Arith { .. }
                if crate::ir_lowering::is_untyped_operation(expr) =>
            {
                crate::ir_lowering::untyped_operation_value_all_types_agree(expr)
                    .map(ComputeValue::Int)
            }
            TrustVcExpr::Neg(inner) => {
                let value = self.eval_int(inner, remaining_calls)?;
                let negated = value.checked_neg()?;
                // SOUNDNESS (round-2 audit, compute-fallback): fixed-width negation
                // wraps in two's complement (`-(-128i8) == -128i8`, NOT 128). The
                // `Neg` IR node carries no width, so infer the operand type and wrap
                // to it (matching the symbolic `encode_neg`). Without this the
                // evaluator computes the unbounded `128` and
                // `recover_assert_by_incompleteness_via_compute` promotes a
                // genuinely-false goal (`-(-128i8) >= 0`) to Verified. Width-less
                // `int`/`nat` negation is exact (`wrap_compute_int_to_type` no-op).
                let ty = crate::ir_lowering::infer_expr_type(inner);
                Some(ComputeValue::Int(wrap_compute_int_to_type(negated, &ty)?))
            }
            TrustVcExpr::Arith {
                op, left, right, ..
            } => {
                // The DERIVED type (`ir_lowering::types`), as the symbolic
                // encoder uses: operands of two different fixed-width types
                // compute exactly (`int`), whatever the node declares.
                let ty = &crate::ir_lowering::infer_expr_type(expr);
                let left = self.eval_int(left, remaining_calls)?;
                let right = self.eval_int(right, remaining_calls)?;
                let value = match op {
                    ArithOp::Add => left.checked_add(right),
                    ArithOp::Sub => left.checked_sub(right),
                    ArithOp::Mul => left.checked_mul(right),
                    // `int`/`nat` (width-less) division and remainder are EUCLIDEAN,
                    // matching the symbolic encoder (`int_euclidean_div` /
                    // `int_euclidean_mod`): a negative `int` dividend yields a
                    // NON-NEGATIVE remainder and a quotient floored toward negative
                    // infinity (`-7 / 2 == -4`, `-7 % 2 == 1`, `-8 % 3 == 1`). Using
                    // Rust's TRUNCATING `checked_div`/`checked_rem` (`-7 / 2 == -3`,
                    // `-7 % 2 == -1`) diverged from the solver, so the compute fallback
                    // (`recover_assert_by_incompleteness_via_compute`) manufactured a
                    // spurious `Verified` on genuinely-false negative-`int` div/mod
                    // goals (round-2 audit, compute-fallback cluster). Fixed-WIDTH
                    // `/`/`%` stay Rust-truncating (then wrapped) for exec semantics.
                    ArithOp::Div => {
                        if matches!(ty, TrustVcType::Uint { .. } | TrustVcType::Int { .. }) {
                            left.checked_div(right)
                        } else {
                            left.checked_div_euclid(right)
                        }
                    }
                    ArithOp::Rem => {
                        if matches!(ty, TrustVcType::Uint { .. } | TrustVcType::Int { .. }) {
                            left.checked_rem(right)
                        } else {
                            left.checked_rem_euclid(right)
                        }
                    }
                }?;
                // Fixed-width arithmetic wraps in two's complement, matching the
                // symbolic encoder (`wrap_int_to_explicit_range`). Without this the
                // interpreter computes the UNBOUNDED result, so e.g. `x + 1 > x`
                // for `x: u8` folds to `true` even at `x == 255` (where the wrapped
                // value is `0`), letting `recover_assert_by_incompleteness_via_compute`
                // promote a genuinely-false recursive-spec-fn goal to Verified
                // (P1-E shifts cluster, recursive-u8). `int`/`nat`/`Real` stay
                // unbounded (no width). Part of #2454 soundness follow-up.
                Some(ComputeValue::Int(wrap_compute_int_to_type(value, ty)?))
            }
            TrustVcExpr::Compare { op, left, right } => {
                self.eval_compare(*op, left, right, remaining_calls)
            }
            TrustVcExpr::Logic { op, left, right } => {
                self.eval_logic(*op, left, right, remaining_calls)
            }
            TrustVcExpr::Not(inner) => {
                let value = self.eval_bool_at(inner, remaining_calls)?;
                Some(ComputeValue::Bool(!value))
            }
            TrustVcExpr::Implies {
                premise,
                conclusion,
            } => {
                let premise = self.eval_bool_at(premise, remaining_calls)?;
                if !premise {
                    return Some(ComputeValue::Bool(true));
                }
                self.eval_bool_at(conclusion, remaining_calls)
                    .map(ComputeValue::Bool)
            }
            TrustVcExpr::Ite {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                if self.eval_bool_at(cond, remaining_calls)? {
                    self.eval_expr(then_branch, remaining_calls)
                } else {
                    self.eval_expr(else_branch, remaining_calls)
                }
            }
            TrustVcExpr::Let {
                name,
                ty,
                value,
                body,
            } => {
                let value = self.eval_expr(value, remaining_calls)?;
                let value_expr = value.to_expr(ty)?;
                let substituted =
                    substitute_compute_vars(body, &HashMap::from([(name.clone(), value_expr)]));
                self.eval_expr(&substituted, remaining_calls)
            }
            TrustVcExpr::Cast { expr, to_ty, .. } => {
                let value = self.eval_int(expr, remaining_calls)?;
                if AYEncoder::value_fits_in_type(value, to_ty) {
                    Some(ComputeValue::Int(value))
                } else {
                    None
                }
            }
            TrustVcExpr::FnCall {
                name,
                args,
                return_ty,
            } => {
                // Datatype constructor/selector/tester calls (tuples and
                // structs are single-variant datatypes) are folded directly
                // against reduced argument values before falling through to the
                // body-catalog unfolding path. Part of backlog #4 Phase 1.
                if let Some(value) = self.eval_datatype_call(name, args, return_ty, remaining_calls)
                {
                    return Some(value);
                }
                self.eval_call(name, args, return_ty, remaining_calls)
            }
            TrustVcExpr::Match {
                scrutinee, arms, ..
            } => self.eval_match(scrutinee, arms, remaining_calls),
            TrustVcExpr::SpecialArith { .. } | TrustVcExpr::WrappingArith { .. } => {
                let reduced = self.rewrite_calls_to_literals(expr, remaining_calls)?;
                AYEncoder::try_reduce_to_int(&reduced).map(ComputeValue::Int)
            }
            TrustVcExpr::Var { .. }
            | TrustVcExpr::StringLit(_)
            | TrustVcExpr::IntConst { .. }
            | TrustVcExpr::CollectionOp { .. }
            | TrustVcExpr::Index { .. }
            | TrustVcExpr::Quantifier { .. }
            | TrustVcExpr::SpecClosure { .. }
            | TrustVcExpr::Choose { .. }
            | TrustVcExpr::ReadPlace { .. }
            | TrustVcExpr::PlaceDisjoint { .. }
            | TrustVcExpr::ProphecyNew { .. }
            | TrustVcExpr::ProphecyResolve { .. } => None,
        }
    }

    fn eval_int(&mut self, expr: &TrustVcExpr, remaining_calls: usize) -> Option<i128> {
        match self.eval_expr(expr, remaining_calls)? {
            ComputeValue::Int(value) => Some(value),
            _ => None,
        }
    }

    fn eval_bool_at(&mut self, expr: &TrustVcExpr, remaining_calls: usize) -> Option<bool> {
        match self.eval_expr(expr, remaining_calls)? {
            ComputeValue::Bool(value) => Some(value),
            _ => None,
        }
    }

    fn eval_compare(
        &mut self,
        op: CompareOp,
        left: &TrustVcExpr,
        right: &TrustVcExpr,
        remaining_calls: usize,
    ) -> Option<ComputeValue> {
        if matches!(op, CompareOp::Eq | CompareOp::Ne) {
            let left_value = self.eval_expr(left, remaining_calls);
            let right_value = self.eval_expr(right, remaining_calls);
            if let (Some(left_value), Some(right_value)) = (&left_value, &right_value) {
                let eq = left_value == right_value;
                return Some(ComputeValue::Bool(matches!(op, CompareOp::Eq) == eq));
            }
        }

        let left = self.eval_int(left, remaining_calls)?;
        let right = self.eval_int(right, remaining_calls)?;
        let result = match op {
            CompareOp::Eq => left == right,
            CompareOp::Ne => left != right,
            CompareOp::Lt => left < right,
            CompareOp::Le => left <= right,
            CompareOp::Gt => left > right,
            CompareOp::Ge => left >= right,
        };
        Some(ComputeValue::Bool(result))
    }

    fn eval_logic(
        &mut self,
        op: LogicOp,
        left: &TrustVcExpr,
        right: &TrustVcExpr,
        remaining_calls: usize,
    ) -> Option<ComputeValue> {
        let left = self.eval_bool_at(left, remaining_calls)?;
        match op {
            LogicOp::And if !left => Some(ComputeValue::Bool(false)),
            LogicOp::Or if left => Some(ComputeValue::Bool(true)),
            LogicOp::And => self
                .eval_bool_at(right, remaining_calls)
                .map(|right| ComputeValue::Bool(left && right)),
            LogicOp::Or => self
                .eval_bool_at(right, remaining_calls)
                .map(|right| ComputeValue::Bool(left || right)),
        }
    }

    fn eval_call(
        &mut self,
        name: &str,
        args: &[TrustVcExpr],
        return_ty: &TrustVcType,
        remaining_calls: usize,
    ) -> Option<ComputeValue> {
        if remaining_calls == 0 {
            return None;
        }
        let body_axiom = self.body_catalog.get(name)?;
        if body_axiom.param_names.len() != args.len() {
            return None;
        }

        let arg_values = args
            .iter()
            .map(|arg| self.eval_expr(arg, remaining_calls))
            .collect::<Option<Vec<_>>>()?;
        let key = ComputeCallKey {
            name: name.to_string(),
            args: arg_values.clone(),
        };
        if let Some(value) = self.memo.get(&key) {
            return Some(value.clone());
        }
        if !self.active.insert(key.clone()) {
            return None;
        }

        let mut subst = HashMap::new();
        for ((param, arg), value) in body_axiom.param_names.iter().zip(args).zip(&arg_values) {
            let ty = crate::ir_lowering::infer_expr_type(arg);
            subst.insert(param.clone(), value.to_expr(&ty)?);
        }
        let body = substitute_compute_vars(&body_axiom.body, &subst);
        let result = self.eval_expr(&body, remaining_calls - 1);
        self.active.remove(&key);

        let value = result?;
        if let ComputeValue::Int(value) = value {
            if !AYEncoder::value_fits_in_type(value, return_ty) {
                return None;
            }
            let value = ComputeValue::Int(value);
            self.memo.insert(key, value.clone());
            return Some(value);
        }
        self.memo.insert(key, value.clone());
        Some(value)
    }

    /// Fold a datatype constructor, selector (field projection), or tester
    /// call against reduced argument values.
    ///
    /// Tuples and structs are single-variant datatypes, so this one path covers
    /// tuple/struct construction, field projection, and `Option`/`Result`-style
    /// enum operations. Returns `None` (so the caller falls back to the
    /// body-catalog path) when the call is not a recognizable datatype
    /// operation, when any argument fails to reduce to a concrete value, or when
    /// the receiver's variant does not expose the requested field — never a
    /// spurious value. Part of backlog #4 by(compute) Phase 1.
    fn eval_datatype_call(
        &mut self,
        name: &str,
        args: &[TrustVcExpr],
        return_ty: &TrustVcType,
        remaining_calls: usize,
    ) -> Option<ComputeValue> {
        // Selector / tester both take exactly one receiver argument.
        if let [receiver] = args {
            if let Some(value) = self.eval_datatype_selector(name, receiver, remaining_calls) {
                return Some(value);
            }
            if let Some(value) = self.eval_datatype_tester(name, receiver, remaining_calls) {
                return Some(value);
            }
        }
        self.eval_datatype_constructor(name, args, return_ty, remaining_calls)
    }

    fn eval_datatype_constructor(
        &mut self,
        name: &str,
        args: &[TrustVcExpr],
        return_ty: &TrustVcType,
        remaining_calls: usize,
    ) -> Option<ComputeValue> {
        let TrustVcType::Datatype {
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
            .map(|((field_name, _), arg)| {
                Some((field_name.clone(), self.eval_expr(arg, remaining_calls)?))
            })
            .collect::<Option<Vec<_>>>()?;
        Some(ComputeValue::Datatype {
            type_name: type_name.clone(),
            variant_name: variant.name.clone(),
            fields,
        })
    }

    fn eval_datatype_selector(
        &mut self,
        name: &str,
        receiver: &TrustVcExpr,
        remaining_calls: usize,
    ) -> Option<ComputeValue> {
        let ComputeValue::Datatype {
            type_name,
            variant_name,
            fields,
        } = self.eval_expr(receiver, remaining_calls)?
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

    fn eval_datatype_tester(
        &mut self,
        name: &str,
        receiver: &TrustVcExpr,
        remaining_calls: usize,
    ) -> Option<ComputeValue> {
        let ComputeValue::Datatype {
            type_name,
            variant_name,
            ..
        } = self.eval_expr(receiver, remaining_calls)?
        else {
            return None;
        };
        let TrustVcType::Datatype {
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
            (name == tester).then_some(ComputeValue::Bool(variant.name == variant_name))
        })
    }

    /// Evaluate a `match` by reducing the scrutinee to a concrete datatype
    /// value, then selecting the first arm whose pattern matches.
    ///
    /// Fails closed (`None`) whenever the scrutinee cannot reduce to a concrete
    /// constructor or no arm matches, so an unfoldable scrutinee never silently
    /// reduces. Part of backlog #4 by(compute) Phase 1.
    fn eval_match(
        &mut self,
        scrutinee: &TrustVcExpr,
        arms: &[MatchArm],
        remaining_calls: usize,
    ) -> Option<ComputeValue> {
        let scrutinee_value = self.eval_expr(scrutinee, remaining_calls)?;
        let scrutinee_ty = crate::ir_lowering::infer_expr_type(scrutinee);
        for arm in arms {
            if let Some(bindings) =
                self.match_pattern_bindings(&arm.pattern, &scrutinee_value, &scrutinee_ty)
            {
                // A guarded arm is taken only when its guard reduces to `true`. If the
                // guard is concretely false, fall through to the next arm; if it can
                // NOT be reduced to a concrete boolean, bail out of constant folding
                // (fail closed to the symbolic ITE encoding) rather than pick the arm
                // ignoring the guard — that would be a false-verify (TRAP #3).
                if let Some(guard) = &arm.guard {
                    let guard_expr = substitute_compute_vars(guard, &bindings);
                    match self.eval_expr(&guard_expr, remaining_calls) {
                        Some(ComputeValue::Bool(true)) => {}
                        Some(ComputeValue::Bool(false)) => continue,
                        _ => return None,
                    }
                }
                let body = substitute_compute_vars(&arm.body, &bindings);
                return self.eval_expr(&body, remaining_calls);
            }
        }
        None
    }

    fn match_pattern_bindings(
        &mut self,
        pattern: &MatchPattern,
        value: &ComputeValue,
        value_ty: &TrustVcType,
    ) -> Option<HashMap<String, TrustVcExpr>> {
        match pattern {
            MatchPattern::Wildcard => Some(HashMap::new()),
            MatchPattern::Ident(name) => {
                let expr = value.to_expr(value_ty)?;
                Some(HashMap::from([(name.clone(), expr)]))
            }
            MatchPattern::Lit(lit) => {
                let lit_value = self.eval_expr(lit, 0)?;
                (&lit_value == value).then(HashMap::new)
            }
            MatchPattern::Constructor {
                variant_name,
                bindings,
                has_rest,
            } => self.match_constructor_pattern(variant_name, bindings, *has_rest, value, value_ty),
            MatchPattern::Struct {
                variant_name,
                fields,
                ..
            } => self.match_struct_pattern(variant_name, fields, value, value_ty),
            MatchPattern::Or(patterns) => patterns
                .iter()
                .find_map(|pattern| self.match_pattern_bindings(pattern, value, value_ty)),
        }
    }

    fn match_constructor_pattern(
        &self,
        variant_name: &str,
        bindings: &[String],
        has_rest: bool,
        value: &ComputeValue,
        value_ty: &TrustVcType,
    ) -> Option<HashMap<String, TrustVcExpr>> {
        let ComputeValue::Datatype {
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
        let mut result = HashMap::new();
        for ((binding, (_, field_value)), field_ty) in bindings.iter().zip(fields).zip(field_tys) {
            if is_ignored_match_binding(binding) {
                continue;
            }
            // A self-recursive child field (`Box<Self>` → `RecursiveRef`) carries no
            // variant metadata; resolve it to the owning datatype so the bound child
            // value can round-trip to an expression.
            let field_ty = resolve_self_recursive_ref(field_ty, value_ty);
            result.insert(binding.clone(), field_value.to_expr(field_ty)?);
        }
        Some(result)
    }

    fn match_struct_pattern(
        &self,
        variant_name: &str,
        fields: &[StructPatternField],
        value: &ComputeValue,
        value_ty: &TrustVcType,
    ) -> Option<HashMap<String, TrustVcExpr>> {
        let ComputeValue::Datatype {
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
        let mut result = HashMap::new();
        for field in fields {
            let Some(binding) = &field.binding else {
                continue;
            };
            let (_, field_value) = value_fields
                .iter()
                .find(|(field_name, _)| field_name == &field.field_name)?;
            let field_ty = datatype_field_ty(value_ty, variant_name, field.field_name.as_str())?;
            let field_ty = resolve_self_recursive_ref(field_ty, value_ty);
            result.insert(binding.clone(), field_value.to_expr(field_ty)?);
        }
        Some(result)
    }

    fn rewrite_calls_to_literals(
        &mut self,
        expr: &TrustVcExpr,
        remaining_calls: usize,
    ) -> Option<TrustVcExpr> {
        match expr {
            TrustVcExpr::FnCall { return_ty, .. } => {
                self.eval_expr(expr, remaining_calls)?.to_expr(return_ty)
            }
            TrustVcExpr::SpecialArith {
                op,
                left,
                right,
                ty,
            } => Some(TrustVcExpr::SpecialArith {
                op: *op,
                left: Box::new(self.rewrite_calls_to_literals(left, remaining_calls)?),
                right: Box::new(self.rewrite_calls_to_literals(right, remaining_calls)?),
                ty: ty.clone(),
            }),
            TrustVcExpr::WrappingArith {
                mode,
                op,
                left,
                right,
                ty,
            } => Some(TrustVcExpr::WrappingArith {
                mode: *mode,
                op: *op,
                left: Box::new(self.rewrite_calls_to_literals(left, remaining_calls)?),
                right: Box::new(self.rewrite_calls_to_literals(right, remaining_calls)?),
                ty: ty.clone(),
            }),
            _ => Some(expr.clone()),
        }
    }
}

/// Build a pure binding environment from in-scope assumptions for compute mode.
///
/// Iterates over assumptions, verified assert_by obligations, and scoped
/// assumptions, extracting simple `var == expr` equality bindings. Non-equality
/// assumptions and unsupported expression shapes are silently ignored
/// (fail-closed). Part of #2454.
pub(in crate::encoder) fn build_compute_bindings(
    assumptions: &[&PreparedObligation],
    verified_assert_by: &[&PreparedObligation],
    scoped_assumptions: &[&PreparedObligation],
) -> HashMap<String, TrustVcExpr> {
    let mut bindings = HashMap::new();
    for ob in assumptions
        .iter()
        .chain(verified_assert_by.iter())
        .chain(scoped_assumptions.iter())
    {
        accumulate_equality_binding(&ob.expr, &mut bindings);
    }
    bindings
}

/// Attempt compute-mode verification with binding substitution.
///
/// 1. Collects equality bindings from in-scope assumptions
/// 2. Substitutes bindings into the assertion expression
/// 3. Runs the existing concrete evaluator on the rewritten expression
///
/// Returns:
/// - `Some(true)` if the rewritten expression evaluates to true
/// - `Some(false)` if it evaluates to false
/// - `None` if symbolic residue remains after substitution
///
/// Part of #2454.
pub(in crate::encoder) fn try_compute_with_bindings(
    assertion_expr: &TrustVcExpr,
    assumptions: &[&PreparedObligation],
    broadcast_assumptions: &[&PreparedObligation],
    verified_assert_by: &[&PreparedObligation],
    scoped_assumptions: &[&PreparedObligation],
    revealed_fns: &std::collections::HashSet<String>,
    hidden_fns: &std::collections::HashSet<String>,
) -> Option<bool> {
    // The IR evaluator reads declared types as the encoder does: a goal the
    // one IR typing validator refuses is not evaluated either (§5b rule 13).
    let unscoped = crate::ir_lowering::TypingScope {
        variables: None,
        locals: None,
        functions: None,
        parameters: None,
    };
    if crate::ir_lowering::validate_ir_typing(assertion_expr, &unscoped).is_err() {
        return None;
    }
    let bindings = build_compute_bindings(assumptions, verified_assert_by, scoped_assumptions);
    let rewritten = if bindings.is_empty() {
        assertion_expr.clone()
    } else {
        substitute_compute_vars(assertion_expr, &bindings)
    };

    if let Some(result) = AYEncoder::try_compute_eval(&rewritten) {
        return Some(result);
    }

    let body_catalog = build_compute_body_catalog(broadcast_assumptions, revealed_fns, hidden_fns);
    if body_catalog.is_empty() {
        return None;
    }
    ComputeEvaluator::new(&body_catalog).eval_bool(&rewritten)
}

/// Builds the concrete-evaluation body catalog with the SAME visibility rule
/// as the broadcast gate and the demand-inline catalog:
///   visible ⟺ (!is_opaque && !hidden) || revealed
/// Evaluating a hidden (`hide!`) body here would let the compute recovery
/// prove a goal from a body the user re-opaqued — the same
/// proves-more-than-Verus leak the opaque filter closes — and, symmetrically,
/// a REVEALED opaque body is legitimately evaluable (the reveal makes its
/// definitional equality part of the query).
fn build_compute_body_catalog(
    broadcast_assumptions: &[&PreparedObligation],
    revealed_fns: &std::collections::HashSet<String>,
    hidden_fns: &std::collections::HashSet<String>,
) -> HashMap<String, super::body_support::ExtractedBodyAxiom> {
    broadcast_assumptions
        .iter()
        .filter(|obligation| {
            let suppressed = obligation.is_opaque
                || super::body_support::body_axiom_fn_named_in(obligation, hidden_fns);
            !suppressed || super::body_support::body_axiom_fn_named_in(obligation, revealed_fns)
        })
        .filter_map(|obligation| super::body_support::extracted_body_axiom(obligation))
        .map(|body_axiom| (body_axiom.function_name.clone(), body_axiom))
        .collect()
}

fn substitute_compute_vars(
    expr: &TrustVcExpr,
    bindings: &HashMap<String, TrustVcExpr>,
) -> TrustVcExpr {
    use crate::ir::TrustVcExpr;

    if bindings.is_empty() {
        return expr.clone();
    }

    let rec = |expr: &TrustVcExpr| substitute_compute_vars(expr, bindings);
    match expr {
        TrustVcExpr::Var { name, ty } => bindings.get(name).map_or_else(
            || expr.clone(),
            |replacement| crate::ir_lowering::pin_substituted_value(ty, replacement),
        ),
        TrustVcExpr::Arith {
            op,
            left,
            right,
            ty,
        } => TrustVcExpr::Arith {
            op: *op,
            left: Box::new(rec(left)),
            right: Box::new(rec(right)),
            ty: ty.clone(),
        },
        TrustVcExpr::SpecialArith {
            op,
            left,
            right,
            ty,
        } => TrustVcExpr::SpecialArith {
            op: *op,
            left: Box::new(rec(left)),
            right: Box::new(rec(right)),
            ty: ty.clone(),
        },
        TrustVcExpr::WrappingArith {
            mode,
            op,
            left,
            right,
            ty,
        } => TrustVcExpr::WrappingArith {
            mode: *mode,
            op: *op,
            left: Box::new(rec(left)),
            right: Box::new(rec(right)),
            ty: ty.clone(),
        },
        TrustVcExpr::Neg(inner) => TrustVcExpr::Neg(Box::new(rec(inner))),
        TrustVcExpr::Compare { op, left, right } => TrustVcExpr::Compare {
            op: *op,
            left: Box::new(rec(left)),
            right: Box::new(rec(right)),
        },
        TrustVcExpr::Logic { op, left, right } => TrustVcExpr::Logic {
            op: *op,
            left: Box::new(rec(left)),
            right: Box::new(rec(right)),
        },
        TrustVcExpr::Not(inner) => TrustVcExpr::Not(Box::new(rec(inner))),
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => TrustVcExpr::Implies {
            premise: Box::new(rec(premise)),
            conclusion: Box::new(rec(conclusion)),
        },
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ty,
        } => TrustVcExpr::Ite {
            cond: Box::new(rec(cond)),
            then_branch: Box::new(rec(then_branch)),
            else_branch: Box::new(rec(else_branch)),
            ty: ty.clone(),
        },
        TrustVcExpr::Let {
            name,
            ty,
            value,
            body,
        } => {
            let value = rec(value);
            if bindings.contains_key(name) {
                TrustVcExpr::Let {
                    name: name.clone(),
                    ty: ty.clone(),
                    value: Box::new(value),
                    body: body.clone(),
                }
            } else {
                TrustVcExpr::Let {
                    name: name.clone(),
                    ty: ty.clone(),
                    value: Box::new(value),
                    body: Box::new(rec(body)),
                }
            }
        }
        TrustVcExpr::Cast {
            expr,
            from_ty,
            to_ty,
        } => TrustVcExpr::Cast {
            expr: Box::new(rec(expr)),
            from_ty: from_ty.clone(),
            to_ty: to_ty.clone(),
        },
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => TrustVcExpr::FnCall {
            name: name.clone(),
            args: args.iter().map(rec).collect(),
            return_ty: return_ty.clone(),
        },
        TrustVcExpr::Match {
            scrutinee,
            arms,
            ty,
        } => TrustVcExpr::Match {
            scrutinee: Box::new(rec(scrutinee)),
            arms: arms
                .iter()
                .map(|arm| {
                    // Names introduced by the arm's pattern shadow outer
                    // bindings inside that arm's body, so drop them from the
                    // substitution before descending. Keeps substitution
                    // capture-avoiding and the interpreter sound.
                    let shadowed = pattern_bound_names(&arm.pattern);
                    let (body, guard) = if shadowed.is_empty() {
                        (rec(&arm.body), arm.guard.as_ref().map(rec))
                    } else {
                        let inner: HashMap<String, TrustVcExpr> = bindings
                            .iter()
                            .filter(|(name, _)| !shadowed.contains(name.as_str()))
                            .map(|(name, value)| (name.clone(), value.clone()))
                            .collect();
                        (
                            substitute_compute_vars(&arm.body, &inner),
                            // The guard is bound by the same pattern names as the body,
                            // so substitute it under the identical shadow-filtered map.
                            arm.guard
                                .as_ref()
                                .map(|g| substitute_compute_vars(g, &inner)),
                        )
                    };
                    MatchArm {
                        pattern: arm.pattern.clone(),
                        body,
                        guard,
                    }
                })
                .collect(),
            ty: ty.clone(),
        },
        _ => expr.clone(),
    }
}

/// Names bound by a match pattern (ignored `__`-prefixed bindings excluded —
/// they never appear in a body and so cannot shadow). Used to keep
/// substitution capture-avoiding when descending into match arms.
fn pattern_bound_names(pattern: &MatchPattern) -> HashSet<String> {
    let mut names = HashSet::new();
    collect_pattern_bound_names(pattern, &mut names);
    names
}

fn collect_pattern_bound_names(pattern: &MatchPattern, names: &mut HashSet<String>) {
    match pattern {
        MatchPattern::Wildcard | MatchPattern::Lit(_) => {}
        MatchPattern::Ident(name) => {
            names.insert(name.clone());
        }
        MatchPattern::Constructor { bindings, .. } => {
            for binding in bindings {
                if !is_ignored_match_binding(binding) {
                    names.insert(binding.clone());
                }
            }
        }
        MatchPattern::Struct { fields, .. } => {
            for field in fields {
                if let Some(binding) = &field.binding {
                    names.insert(binding.clone());
                }
            }
        }
        MatchPattern::Or(patterns) => {
            for pattern in patterns {
                collect_pattern_bound_names(pattern, names);
            }
        }
    }
}

fn datatype_variant_field_tys<'a>(
    ty: &'a TrustVcType,
    variant_name: &str,
) -> Option<Vec<&'a TrustVcType>> {
    let TrustVcType::Datatype { variants, .. } = ty else {
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
    ty: &'a TrustVcType,
    variant_name: &str,
    field_name: &str,
) -> Option<&'a TrustVcType> {
    let TrustVcType::Datatype { variants, .. } = ty else {
        return None;
    };
    variants
        .iter()
        .find(|variant| variant.name == variant_name)?
        .fields
        .iter()
        .find_map(|(candidate, field_ty)| (candidate == field_name).then_some(field_ty))
}

#[cfg(test)]
mod tests {
    //! Tests for the by(compute) value-domain extension to tuples, structs,
    //! field projection, and datatype `Match` (backlog #4 Phase 1).
    //!
    //! These exercise the unfolding `ComputeEvaluator` directly (the secondary
    //! body-catalog path). Soundness is the priority: an unfoldable term must
    //! stay `None` and never spuriously reduce to a value.

    use super::*;
    use crate::ir::{ArithOp, DatatypeVariant, TrustVcType};
    use crate::ir_expr::{MatchArm, MatchPattern, StructPatternField};

    fn i32_ty() -> TrustVcType {
        TrustVcType::Int { width: 32 }
    }

    fn i32_lit(value: i128) -> TrustVcExpr {
        TrustVcExpr::IntLit {
            value,
            ty: i32_ty(),
        }
    }

    fn bool_lit(value: bool) -> TrustVcExpr {
        TrustVcExpr::BoolLit(value)
    }

    fn datatype_ty(name: &str, variants: Vec<(&str, Vec<(&str, TrustVcType)>)>) -> TrustVcType {
        TrustVcType::Datatype {
            name: name.to_string(),
            variants: variants
                .into_iter()
                .map(|(variant, fields)| {
                    DatatypeVariant::new(
                        variant,
                        fields
                            .into_iter()
                            .map(|(field_name, field_ty)| (field_name.to_string(), field_ty))
                            .collect(),
                    )
                })
                .collect(),
        }
    }

    /// A two-element tuple `(i32, bool)` is a single-variant datatype.
    fn pair_ty() -> TrustVcType {
        datatype_ty(
            "(i32, bool)",
            vec![("tuple%2", vec![("0", i32_ty()), ("1", TrustVcType::Bool)])],
        )
    }

    fn point_ty() -> TrustVcType {
        datatype_ty(
            "Point",
            vec![("Point", vec![("x", i32_ty()), ("y", i32_ty())])],
        )
    }

    fn option_i32_ty() -> TrustVcType {
        datatype_ty(
            "Option<i32>",
            vec![("Some", vec![("0", i32_ty())]), ("None", vec![])],
        )
    }

    fn ctor(ty: &TrustVcType, variant: &str, args: Vec<TrustVcExpr>) -> TrustVcExpr {
        let TrustVcType::Datatype { name, .. } = ty else {
            panic!("ctor helper requires a datatype type");
        };
        TrustVcExpr::FnCall {
            name: crate::encoder::datatype::variant_symbol_name(name, variant),
            args,
            return_ty: ty.clone(),
        }
    }

    fn selector(
        receiver: TrustVcExpr,
        receiver_ty: &TrustVcType,
        variant: &str,
        field_name: &str,
        field_index: usize,
        field_ty: TrustVcType,
    ) -> TrustVcExpr {
        let TrustVcType::Datatype { name, .. } = receiver_ty else {
            panic!("selector helper requires a datatype type");
        };
        TrustVcExpr::FnCall {
            name: crate::encoder::datatype::selector_symbol_name(
                name,
                variant,
                field_name,
                field_index,
            ),
            args: vec![receiver],
            return_ty: field_ty,
        }
    }

    fn tester(receiver: TrustVcExpr, receiver_ty: &TrustVcType, variant: &str) -> TrustVcExpr {
        let TrustVcType::Datatype { name, .. } = receiver_ty else {
            panic!("tester helper requires a datatype type");
        };
        TrustVcExpr::FnCall {
            name: crate::encoder::datatype::tester_symbol_name(name, variant),
            args: vec![receiver],
            return_ty: TrustVcType::Bool,
        }
    }

    /// Evaluate a boolean expression with an empty body catalog.
    fn eval_bool(expr: &TrustVcExpr) -> Option<bool> {
        let catalog = HashMap::new();
        ComputeEvaluator::new(&catalog).eval_bool(expr)
    }

    /// Evaluate to a raw `ComputeValue` with an empty body catalog.
    fn eval_value(expr: &TrustVcExpr) -> Option<ComputeValue> {
        let catalog = HashMap::new();
        ComputeEvaluator::new(&catalog).eval_expr(expr, COMPUTE_UNFOLD_LIMIT)
    }

    fn symbolic_i32(name: &str) -> TrustVcExpr {
        TrustVcExpr::Var {
            name: name.to_string(),
            ty: i32_ty(),
        }
    }

    // --- Tuple / struct field projection ---

    #[test]
    fn tuple_field_projection_reduces_to_concrete_field() {
        let ty = pair_ty();
        let value = ctor(&ty, "tuple%2", vec![i32_lit(7), bool_lit(true)]);
        let first = selector(value.clone(), &ty, "tuple%2", "0", 0, i32_ty());
        let second = selector(value, &ty, "tuple%2", "1", 1, TrustVcType::Bool);

        assert_eq!(eval_value(&first), Some(ComputeValue::Int(7)));
        assert_eq!(eval_value(&second), Some(ComputeValue::Bool(true)));
    }

    #[test]
    fn struct_field_projection_reduces_to_concrete_field() {
        let ty = point_ty();
        let value = ctor(&ty, "Point", vec![i32_lit(3), i32_lit(9)]);
        let x = selector(value.clone(), &ty, "Point", "x", 0, i32_ty());
        let y = selector(value, &ty, "Point", "y", 1, i32_ty());

        assert_eq!(eval_value(&x), Some(ComputeValue::Int(3)));
        assert_eq!(eval_value(&y), Some(ComputeValue::Int(9)));
    }

    #[test]
    fn projection_then_arith_reduces_through_compare() {
        // (1, 2).0 + (1, 2).1 == 3
        let ty = datatype_ty(
            "(i32, i32)",
            vec![("tuple%2", vec![("0", i32_ty()), ("1", i32_ty())])],
        );
        let value = ctor(&ty, "tuple%2", vec![i32_lit(1), i32_lit(2)]);
        let sum = TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(selector(value.clone(), &ty, "tuple%2", "0", 0, i32_ty())),
            right: Box::new(selector(value, &ty, "tuple%2", "1", 1, i32_ty())),
            ty: i32_ty(),
        };
        let assertion = TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(sum),
            right: Box::new(i32_lit(3)),
        };
        assert_eq!(eval_bool(&assertion), Some(true));
    }

    // --- Tester ---

    #[test]
    fn tester_distinguishes_concrete_variants() {
        let ty = option_i32_ty();
        let some = ctor(&ty, "Some", vec![i32_lit(5)]);
        let none = ctor(&ty, "None", vec![]);

        assert_eq!(
            eval_value(&tester(some.clone(), &ty, "Some")),
            Some(ComputeValue::Bool(true))
        );
        assert_eq!(
            eval_value(&tester(some, &ty, "None")),
            Some(ComputeValue::Bool(false))
        );
        assert_eq!(
            eval_value(&tester(none.clone(), &ty, "None")),
            Some(ComputeValue::Bool(true))
        );
        assert_eq!(
            eval_value(&tester(none, &ty, "Some")),
            Some(ComputeValue::Bool(false))
        );
    }

    // --- Datatype Match (constructor patterns) ---

    #[test]
    fn match_on_concrete_some_binds_payload() {
        let ty = option_i32_ty();
        // match Some(4) { Some(v) => v == 4, _ => false }
        let expr = TrustVcExpr::Match {
            scrutinee: Box::new(ctor(&ty, "Some", vec![i32_lit(4)])),
            arms: vec![
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "Some".to_string(),
                        bindings: vec!["v".to_string()],
                        has_rest: false,
                    },
                    TrustVcExpr::Compare {
                        op: CompareOp::Eq,
                        left: Box::new(symbolic_i32("v")),
                        right: Box::new(i32_lit(4)),
                    },
                ),
                MatchArm::new(MatchPattern::Wildcard, bool_lit(false)),
            ],
            ty: TrustVcType::Bool,
        };
        assert_eq!(eval_bool(&expr), Some(true));
    }

    #[test]
    fn match_on_concrete_none_takes_wildcard_arm() {
        let ty = option_i32_ty();
        // match None { Some(v) => v == 0, _ => true }
        let expr = TrustVcExpr::Match {
            scrutinee: Box::new(ctor(&ty, "None", vec![])),
            arms: vec![
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "Some".to_string(),
                        bindings: vec!["v".to_string()],
                        has_rest: false,
                    },
                    TrustVcExpr::Compare {
                        op: CompareOp::Eq,
                        left: Box::new(symbolic_i32("v")),
                        right: Box::new(i32_lit(0)),
                    },
                ),
                MatchArm::new(MatchPattern::Wildcard, bool_lit(true)),
            ],
            ty: TrustVcType::Bool,
        };
        assert_eq!(eval_bool(&expr), Some(true));
    }

    #[test]
    fn match_struct_pattern_binds_named_field() {
        let ty = point_ty();
        // match Point { x: 2, y: 5 } { Point { x, y } => x + y == 7 }
        let expr = TrustVcExpr::Match {
            scrutinee: Box::new(ctor(&ty, "Point", vec![i32_lit(2), i32_lit(5)])),
            arms: vec![MatchArm::new(
                MatchPattern::Struct {
                    variant_name: "Point".to_string(),
                    fields: vec![
                        StructPatternField::new("x", Some("x".to_string())),
                        StructPatternField::new("y", Some("y".to_string())),
                    ],
                    has_rest: false,
                },
                TrustVcExpr::Compare {
                    op: CompareOp::Eq,
                    left: Box::new(TrustVcExpr::Arith {
                        op: ArithOp::Add,
                        left: Box::new(symbolic_i32("x")),
                        right: Box::new(symbolic_i32("y")),
                        ty: i32_ty(),
                    }),
                    right: Box::new(i32_lit(7)),
                },
            )],
            ty: TrustVcType::Bool,
        };
        assert_eq!(eval_bool(&expr), Some(true));
    }

    #[test]
    fn match_lit_pattern_selects_matching_arm() {
        let ty = option_i32_ty();
        // match Some(2) { Some(1) => false, Some(2) => true, _ => false }
        let expr = TrustVcExpr::Match {
            scrutinee: Box::new(ctor(&ty, "Some", vec![i32_lit(2)])),
            arms: vec![
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "Some".to_string(),
                        bindings: vec!["a".to_string()],
                        has_rest: false,
                    },
                    TrustVcExpr::Match {
                        scrutinee: Box::new(symbolic_i32("a")),
                        arms: vec![
                            MatchArm::new(MatchPattern::Lit(i32_lit(1)), bool_lit(false)),
                            MatchArm::new(MatchPattern::Lit(i32_lit(2)), bool_lit(true)),
                            MatchArm::new(MatchPattern::Wildcard, bool_lit(false)),
                        ],
                        ty: TrustVcType::Bool,
                    },
                ),
                MatchArm::new(MatchPattern::Wildcard, bool_lit(false)),
            ],
            ty: TrustVcType::Bool,
        };
        assert_eq!(eval_bool(&expr), Some(true));
    }

    #[test]
    fn match_or_pattern_agrees_on_either_variant() {
        let ty = datatype_ty("Tri", vec![("A", vec![]), ("B", vec![]), ("C", vec![])]);
        // match B { A | B => true, _ => false }
        let expr = TrustVcExpr::Match {
            scrutinee: Box::new(ctor(&ty, "B", vec![])),
            arms: vec![
                MatchArm::new(
                    MatchPattern::Or(vec![
                        MatchPattern::Constructor {
                            variant_name: "A".to_string(),
                            bindings: vec![],
                            has_rest: false,
                        },
                        MatchPattern::Constructor {
                            variant_name: "B".to_string(),
                            bindings: vec![],
                            has_rest: false,
                        },
                    ]),
                    bool_lit(true),
                ),
                MatchArm::new(MatchPattern::Wildcard, bool_lit(false)),
            ],
            ty: TrustVcType::Bool,
        };
        assert_eq!(eval_bool(&expr), Some(true));
    }

    // --- Nested values round-trip ---

    #[test]
    fn nested_tuple_equality_reduces() {
        // ((1, 2), 3) == ((1, 2), 3)
        let inner_ty = datatype_ty(
            "(i32, i32)",
            vec![("tuple%2", vec![("0", i32_ty()), ("1", i32_ty())])],
        );
        let outer_ty = datatype_ty(
            "((i32, i32), i32)",
            vec![("tuple%2", vec![("0", inner_ty.clone()), ("1", i32_ty())])],
        );
        let build = || {
            ctor(
                &outer_ty,
                "tuple%2",
                vec![
                    ctor(&inner_ty, "tuple%2", vec![i32_lit(1), i32_lit(2)]),
                    i32_lit(3),
                ],
            )
        };
        let expr = TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(build()),
            right: Box::new(build()),
        };
        assert_eq!(eval_bool(&expr), Some(true));

        let differ = TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(build()),
            right: Box::new(ctor(
                &outer_ty,
                "tuple%2",
                vec![
                    ctor(&inner_ty, "tuple%2", vec![i32_lit(1), i32_lit(9)]),
                    i32_lit(3),
                ],
            )),
        };
        assert_eq!(eval_bool(&differ), Some(false));
    }

    #[test]
    fn projection_of_match_result_reduces() {
        // (match Some(1) { Some(v) => (v, v + 1), None => (0, 0) }).1 == 2
        let opt_ty = option_i32_ty();
        let pair = datatype_ty(
            "(i32, i32)",
            vec![("tuple%2", vec![("0", i32_ty()), ("1", i32_ty())])],
        );
        let matched = TrustVcExpr::Match {
            scrutinee: Box::new(ctor(&opt_ty, "Some", vec![i32_lit(1)])),
            arms: vec![
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "Some".to_string(),
                        bindings: vec!["v".to_string()],
                        has_rest: false,
                    },
                    ctor(
                        &pair,
                        "tuple%2",
                        vec![
                            symbolic_i32("v"),
                            TrustVcExpr::Arith {
                                op: ArithOp::Add,
                                left: Box::new(symbolic_i32("v")),
                                right: Box::new(i32_lit(1)),
                                ty: i32_ty(),
                            },
                        ],
                    ),
                ),
                MatchArm::new(
                    MatchPattern::Wildcard,
                    ctor(&pair, "tuple%2", vec![i32_lit(0), i32_lit(0)]),
                ),
            ],
            ty: pair.clone(),
        };
        let assertion = TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(selector(matched, &pair, "tuple%2", "1", 1, i32_ty())),
            right: Box::new(i32_lit(2)),
        };
        assert_eq!(eval_bool(&assertion), Some(true));
    }

    // --- Soundness: unfoldable terms must stay None ---

    fn symbolic_datatype(name: &str, ty: &TrustVcType) -> TrustVcExpr {
        TrustVcExpr::Var {
            name: name.to_string(),
            ty: ty.clone(),
        }
    }

    #[test]
    fn match_on_symbolic_scrutinee_fails_closed() {
        let ty = option_i32_ty();
        // The scrutinee is a bare symbolic variable: the interpreter cannot know
        // which variant it is, so no arm may be selected.
        let expr = TrustVcExpr::Match {
            scrutinee: Box::new(symbolic_datatype("opt", &ty)),
            arms: vec![
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "Some".to_string(),
                        bindings: vec!["v".to_string()],
                        has_rest: false,
                    },
                    bool_lit(true),
                ),
                MatchArm::new(MatchPattern::Wildcard, bool_lit(false)),
            ],
            ty: TrustVcType::Bool,
        };
        assert_eq!(
            eval_bool(&expr),
            None,
            "match on a symbolic scrutinee must not reduce"
        );
    }

    #[test]
    fn selector_on_symbolic_receiver_fails_closed() {
        let ty = pair_ty();
        let receiver = symbolic_datatype("p", &ty);
        let first = selector(receiver, &ty, "tuple%2", "0", 0, i32_ty());
        assert_eq!(
            eval_value(&first),
            None,
            "field projection of a symbolic value must not reduce"
        );
    }

    #[test]
    fn tester_on_symbolic_receiver_fails_closed() {
        let ty = option_i32_ty();
        let receiver = symbolic_datatype("opt", &ty);
        assert_eq!(
            eval_value(&tester(receiver, &ty, "Some")),
            None,
            "tester on a symbolic value must not reduce"
        );
    }

    #[test]
    fn unknown_field_selector_fails_closed() {
        // A selector whose name matches no field of the concrete value must not
        // fold to an arbitrary field.
        let ty = pair_ty();
        let value = ctor(&ty, "tuple%2", vec![i32_lit(1), bool_lit(true)]);
        let bogus = TrustVcExpr::FnCall {
            name: "no_such_selector".to_string(),
            args: vec![value],
            return_ty: i32_ty(),
        };
        assert_eq!(eval_value(&bogus), None);
    }

    #[test]
    fn constructor_arity_mismatch_fails_closed() {
        // A constructor call whose argument count disagrees with the variant
        // must not build a value.
        let ty = option_i32_ty();
        let TrustVcType::Datatype { name, .. } = &ty else {
            unreachable!()
        };
        let bad = TrustVcExpr::FnCall {
            name: crate::encoder::datatype::variant_symbol_name(name, "Some"),
            args: vec![i32_lit(1), i32_lit(2)],
            return_ty: ty.clone(),
        };
        assert_eq!(eval_value(&bad), None);
    }

    #[test]
    fn match_with_no_matching_arm_fails_closed() {
        let ty = datatype_ty("Two", vec![("A", vec![]), ("B", vec![])]);
        // match B { A => true } — no arm matches B
        let expr = TrustVcExpr::Match {
            scrutinee: Box::new(ctor(&ty, "B", vec![])),
            arms: vec![MatchArm::new(
                MatchPattern::Constructor {
                    variant_name: "A".to_string(),
                    bindings: vec![],
                    has_rest: false,
                },
                bool_lit(true),
            )],
            ty: TrustVcType::Bool,
        };
        assert_eq!(eval_bool(&expr), None);
    }

    // --- Integration through the body-catalog unfolding path ---

    #[test]
    fn body_axiom_returning_tuple_projects_through_unfold() {
        // fn mk() -> (i32, bool) { (10, true) }
        // assert: mk().0 == 10
        let ty = pair_ty();
        let body = ctor(&ty, "tuple%2", vec![i32_lit(10), bool_lit(true)]);
        let axiom = super::super::body_support::ExtractedBodyAxiom {
            function_name: "mk".to_string(),
            param_names: vec![],
            param_types: vec![],
            body,
        };
        let mut catalog = HashMap::new();
        catalog.insert("mk".to_string(), axiom);

        let call = TrustVcExpr::FnCall {
            name: "mk".to_string(),
            args: vec![],
            return_ty: ty.clone(),
        };
        let assertion = TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(selector(call, &ty, "tuple%2", "0", 0, i32_ty())),
            right: Box::new(i32_lit(10)),
        };
        assert_eq!(
            ComputeEvaluator::new(&catalog).eval_bool(&assertion),
            Some(true)
        );
    }

    #[test]
    fn body_axiom_match_substitutes_parameters_through_unfold() {
        // fn is_some(o: Option<i32>) -> bool {
        //     match o { Some(_) => true, None => false }
        // }
        // assert: is_some(Some(3)) == true
        let opt_ty = option_i32_ty();
        let match_body = TrustVcExpr::Match {
            scrutinee: Box::new(TrustVcExpr::Var {
                name: "o".to_string(),
                ty: opt_ty.clone(),
            }),
            arms: vec![
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "Some".to_string(),
                        bindings: vec![format!(
                            "{}ignored",
                            crate::match_pattern_scope::IGNORED_MATCH_BINDING_PREFIX
                        )],
                        has_rest: false,
                    },
                    bool_lit(true),
                ),
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "None".to_string(),
                        bindings: vec![],
                        has_rest: false,
                    },
                    bool_lit(false),
                ),
            ],
            ty: TrustVcType::Bool,
        };
        let axiom = super::super::body_support::ExtractedBodyAxiom {
            function_name: "is_some".to_string(),
            param_names: vec!["o".to_string()],
            // param_types unused by this compute test; empty is zero-impact
            // (the call-site monomorphizer zips defensively, producing no bindings).
            param_types: vec![],
            body: match_body,
        };
        let mut catalog = HashMap::new();
        catalog.insert("is_some".to_string(), axiom);

        let call = TrustVcExpr::FnCall {
            name: "is_some".to_string(),
            args: vec![ctor(&opt_ty, "Some", vec![i32_lit(3)])],
            return_ty: TrustVcType::Bool,
        };
        assert_eq!(ComputeEvaluator::new(&catalog).eval_bool(&call), Some(true));

        let call_none = TrustVcExpr::FnCall {
            name: "is_some".to_string(),
            args: vec![ctor(&opt_ty, "None", vec![])],
            return_ty: TrustVcType::Bool,
        };
        assert_eq!(
            ComputeEvaluator::new(&catalog).eval_bool(&call_none),
            Some(false)
        );
    }

    #[test]
    fn body_axiom_match_capture_avoiding_shadow() {
        // fn pick(p: (i32, i32)) -> i32 {
        //     match p { (x, y) => x }
        // }
        // The arm binds `x`/`y`, which must shadow during substitution.
        // assert: pick((4, 9)) == 4
        let pair = datatype_ty(
            "(i32, i32)",
            vec![("tuple%2", vec![("0", i32_ty()), ("1", i32_ty())])],
        );
        let match_body = TrustVcExpr::Match {
            scrutinee: Box::new(TrustVcExpr::Var {
                name: "p".to_string(),
                ty: pair.clone(),
            }),
            arms: vec![MatchArm::new(
                MatchPattern::Constructor {
                    variant_name: "tuple%2".to_string(),
                    bindings: vec!["x".to_string(), "y".to_string()],
                    has_rest: false,
                },
                symbolic_i32("x"),
            )],
            ty: i32_ty(),
        };
        let axiom = super::super::body_support::ExtractedBodyAxiom {
            function_name: "pick".to_string(),
            param_names: vec!["p".to_string()],
            // param_types unused by this compute test; empty is zero-impact.
            param_types: vec![],
            body: match_body,
        };
        let mut catalog = HashMap::new();
        catalog.insert("pick".to_string(), axiom);

        let call = TrustVcExpr::FnCall {
            name: "pick".to_string(),
            args: vec![ctor(&pair, "tuple%2", vec![i32_lit(4), i32_lit(9)])],
            return_ty: i32_ty(),
        };
        let assertion = TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(call),
            right: Box::new(i32_lit(4)),
        };
        assert_eq!(
            ComputeEvaluator::new(&catalog).eval_bool(&assertion),
            Some(true)
        );
    }

    // --- Fixed-width arithmetic wrapping (P1-E shifts cluster, recursive-u8) ---

    fn u8_ty() -> TrustVcType {
        TrustVcType::Uint { width: 8 }
    }

    fn i8_ty() -> TrustVcType {
        TrustVcType::Int { width: 8 }
    }

    /// `wrap_compute_int_to_type` mirrors the symbolic encoder: unsigned wraps
    /// `mod 2^w`, signed wraps two's complement, math integers stay unbounded.
    #[test]
    fn wrap_compute_matches_two_complement() {
        // u8: 256 -> 0, 255 -> 255, 257 -> 1
        assert_eq!(wrap_compute_int_to_type(256, &u8_ty()), Some(0));
        assert_eq!(wrap_compute_int_to_type(255, &u8_ty()), Some(255));
        assert_eq!(wrap_compute_int_to_type(257, &u8_ty()), Some(1));
        // i8: 128 -> -128 (sign bit), -129 -> 127
        assert_eq!(wrap_compute_int_to_type(128, &i8_ty()), Some(-128));
        assert_eq!(wrap_compute_int_to_type(-129, &i8_ty()), Some(127));
        assert_eq!(wrap_compute_int_to_type(127, &i8_ty()), Some(127));
        // i32: 2^31 -> i32::MIN (the shift sign-bit value)
        assert_eq!(
            wrap_compute_int_to_type(2147483648, &i32_ty()),
            Some(-2147483648)
        );
        // Math integers are unbounded — no wrap.
        assert_eq!(
            wrap_compute_int_to_type(2147483648, &TrustVcType::MathInt),
            Some(2147483648)
        );
        assert_eq!(
            wrap_compute_int_to_type(99999, &TrustVcType::Nat),
            Some(99999)
        );
        // 128-bit and wider fall closed (cannot wrap against a representable modulus).
        assert_eq!(
            wrap_compute_int_to_type(1, &TrustVcType::Uint { width: 128 }),
            None
        );
    }

    /// The `Arith` arm of the interpreter wraps an overflowing fixed-width add:
    /// `255u8 + 1u8 > 255u8` is FALSE (wraps to `0 > 255`), not `true`.
    #[test]
    fn arith_arm_wraps_overflowing_u8_add() {
        let add = TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(TrustVcExpr::IntLit {
                value: 255,
                ty: u8_ty(),
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 1,
                ty: u8_ty(),
            }),
            ty: u8_ty(),
        };
        // The wrapped sum is 0, so `255 + 1 > 255` evaluates to false.
        let gt = TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(add.clone()),
            right: Box::new(TrustVcExpr::IntLit {
                value: 255,
                ty: u8_ty(),
            }),
        };
        assert_eq!(eval_bool(&gt), Some(false));

        // And the wrapped value really is 0.
        let eq_zero = TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(add),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: u8_ty(),
            }),
        };
        assert_eq!(eval_bool(&eq_zero), Some(true));
    }

    /// A non-overflowing fixed-width add is unchanged: `100u8 + 1u8 > 100u8`.
    #[test]
    fn arith_arm_keeps_non_overflowing_u8_add() {
        let gt = TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(TrustVcExpr::IntLit {
                    value: 100,
                    ty: u8_ty(),
                }),
                right: Box::new(TrustVcExpr::IntLit {
                    value: 1,
                    ty: u8_ty(),
                }),
                ty: u8_ty(),
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 100,
                ty: u8_ty(),
            }),
        };
        assert_eq!(eval_bool(&gt), Some(true));
    }
}
