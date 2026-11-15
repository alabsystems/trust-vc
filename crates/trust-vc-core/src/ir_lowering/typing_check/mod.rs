//! The ONE typing validator of the IR handed to the encoder
//! (design-trust-proof-backend.md §5b).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Every node of a `TrustVcExpr` that carries a type — a literal's `ty`, an
//! arithmetic node's `ty`, a conditional's `ty`, a collection operation's
//! result `ty`, an element read's `elem_ty`, a `let`'s `ty`, a cast's
//! `from_ty`, a variable's `ty`, a call's `return_ty` — is a PRODUCER'S CLAIM.
//! The encoder reads some of those claims (the sign an element is widened by
//! comes from the collection it was read from; a literal's bits come from its
//! declared width), so a claim that disagrees with what the node's children
//! make it is a second reading of one value, and a second reading is how a
//! false goal comes back `Verified`.
//!
//! [`validate_ir_typing`] re-derives every node's type from its children,
//! BOTTOM-UP, at every depth, and refuses (`Err`, hence `Unknown`) any claim
//! that disagrees:
//!
//! * a LITERAL whose value its declared type cannot hold (`IntLit { -1, nat }`
//!   read `-1 < 0` as a `nat` fact; `IntLit { -1, u8 }` was the `u8` 255);
//!   only the unsuffixed placeholder `Int { width: 32 }` holds any value — it
//!   is typed by the peer it meets (rule 2);
//! * an integer operation or conditional whose declared integer type is not
//!   the type its operands DERIVE (`infer_expr_type`, rule 1);
//! * a collection operation's result that is not the type the lowering's one
//!   typing rule derives from its receiver and arguments
//!   (`infer_collection_op_type`: `s.take(1)` of a `Seq<u8>` declared
//!   `Seq<i8>`, a `to_set` declared `Set<i8>`, then read at `i8`, gave -56
//!   for the element 200), and a closure whose `SpecFn` type is not its
//!   parameters' and its body's;
//! * a `let`, a conditional or a `match` whose declared type and whose
//!   operands' types disagree at an integer position, in EITHER direction —
//!   one declared at a type parameter, `Poly` or an opaque type over a
//!   `Seq<u8>` forgot the element type;
//! * an element read (`s[i]`, `get`, `first`, `last`, `choose`) declared at
//!   another type than its receiver's element type, or of a receiver with no
//!   element type, and a map key of another integer type (rule 10);
//! * a cast whose `from_ty` is not its operand's type, whatever the type (a
//!   `char`, a type parameter, a collection);
//! * a call argument its parameter's declared type cannot hold
//!   (`bind_call_argument`), checked at the root before an inline body is
//!   substituted;
//! * the other collection of a binary operation (`concat`, `union`,
//!   `subset_of`, ...) of another element type;
//! * a variable whose declared type is not its binder's (a `let`, a
//!   quantifier, a `choose`, a `match` identifier, a closure parameter, or the
//!   context's declaration);
//! * a `wrapping_*`/`saturating_*` operand that is not a value of the
//!   method's type (rule 6), and a `let` binding its type cannot hold.
//!
//! Because each node's claim is checked against its children's claims, and
//! the leaves (literals, variables) are checked against their values and
//! binders, every claim a parent reads through `infer_expr_type` has itself
//! been derived: a lie one level up (the receiver of the receiver) cannot
//! slip past. The validator runs on the tree the encoder reads — each root
//! as given and again after inline expansion (`AYEncoder::prepare_root`),
//! before equality substitution or normalization — and on each goal the
//! `by(compute)` evaluator or the constant evaluator is asked to decide, so
//! both frontends — the syn lowering and the typed seam — pass through it.

mod claims;
mod positions;
#[cfg(test)]
mod tests;

use std::collections::HashMap;

use crate::ir::{MatchPattern, TrustVcType};
use crate::ir_expr::{SpecialArithOp, TrustVcExpr};

use super::types::{
    bind_call_argument, derive_arms_int_type, derive_shift_type, infer_expr_type, is_integer_type,
    IntBinding,
};
use claims::{
    binding_holds, cast_operand_agrees, collection_op_agrees, composite_holds, composites_compare,
    derived_agrees, element_read_agrees, expr_label, integer_claim_agrees, literal_holds,
    pattern_binders, spec_closure_agrees, untyped_placeholder_join, wrapping_operand,
};
pub(crate) use positions::{
    integer_positions_agree, mentions_type_parameter, type_holds_an_integer,
};

/// The declarations the validator reads that the expression itself does not
/// carry: the context's variables and the declared result types of functions.
pub(crate) struct TypingScope<'a> {
    /// Context variables (parameters, locals the encoder declared).
    pub(crate) variables: Option<&'a HashMap<String, TrustVcType>>,
    /// Variables bound by the caller around this root (a quantifier body
    /// encoded on its own).
    pub(crate) locals: Option<&'a HashMap<String, TrustVcType>>,
    /// Declared result types of the functions a call may name.
    pub(crate) functions: Option<&'a HashMap<String, TrustVcType>>,
    /// Declared parameter types of the functions a call may name.
    pub(crate) parameters: Option<&'a HashMap<String, Vec<TrustVcType>>>,
}

/// Validate the typing of the whole of `expr` (module doc). `Err` names the
/// first disagreement found, innermost first.
pub(crate) fn validate_ir_typing(
    expr: &TrustVcExpr,
    scope: &TypingScope<'_>,
) -> Result<(), String> {
    let mut walker = Walker {
        scope,
        binders: Vec::new(),
    };
    walker.expr(expr)
}

/// A binder introduced inside the expression: `Some(type)`, or `None` for a
/// name a pattern binds at a type the validator does not derive (a datatype
/// field) — it shadows any outer name and is left to the encoder.
pub(super) type Binder = (String, Option<TrustVcType>);

struct Walker<'s, 'a> {
    scope: &'s TypingScope<'a>,
    binders: Vec<Binder>,
}

impl Walker<'_, '_> {
    fn with_binders<R>(
        &mut self,
        binders: impl IntoIterator<Item = Binder>,
        body: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let mark = self.binders.len();
        self.binders.extend(binders);
        let result = body(self);
        self.binders.truncate(mark);
        result
    }

    /// The type a variable of this name is declared at by its binder:
    /// `Some(Some(ty))` for a typed binder, `Some(None)` for a binder whose
    /// type is not derived here, `None` when nothing in sight binds it.
    fn binder_type(&self, name: &str) -> Option<Option<&TrustVcType>> {
        if let Some((_, ty)) = self.binders.iter().rev().find(|(n, _)| n == name) {
            return Some(ty.as_ref());
        }
        if let Some(ty) = self.scope.locals.and_then(|locals| locals.get(name)) {
            return Some(Some(ty));
        }
        self.scope
            .variables
            .and_then(|variables| variables.get(name))
            .map(Some)
    }

    #[allow(clippy::too_many_lines)] // one exhaustive match over the IR
    fn expr(&mut self, expr: &TrustVcExpr) -> Result<(), String> {
        match expr {
            TrustVcExpr::UnitLit
            | TrustVcExpr::BoolLit(_)
            | TrustVcExpr::StringLit(_)
            | TrustVcExpr::IntConst { .. }
            | TrustVcExpr::PlaceDisjoint { .. }
            | TrustVcExpr::ProphecyNew { .. } => Ok(()),
            TrustVcExpr::ReadPlace { .. } => Ok(()),
            TrustVcExpr::IntLit { value, ty } => literal_holds(*value, ty),
            TrustVcExpr::Var { name, ty } => self.var(name, ty),
            TrustVcExpr::Arith {
                left, right, ty, ..
            } => {
                self.expr(left)?;
                self.expr(right)?;
                derived_agrees(expr, ty, &[left, right])
            }
            TrustVcExpr::SpecialArith {
                op,
                left,
                right,
                ty,
            } => {
                self.expr(left)?;
                self.expr(right)?;
                match op {
                    SpecialArithOp::Shl | SpecialArithOp::Shr => {
                        let derived = derive_shift_type(left, ty);
                        integer_claim_agrees(ty, &derived, || expr_label(expr))
                    }
                    SpecialArithOp::BitAnd | SpecialArithOp::BitOr | SpecialArithOp::BitXor => {
                        derived_agrees(expr, ty, &[left, right])
                    }
                }
            }
            TrustVcExpr::Compare { left, right, .. } => {
                self.expr(left)?;
                self.expr(right)?;
                composites_compare(left, right)
            }
            TrustVcExpr::Logic { left, right, .. } => {
                self.expr(left)?;
                self.expr(right)
            }
            // `-128i8` is `Neg(IntLit { 128, i8 })`: the literal under a
            // negation is a MAGNITUDE, and it is the negated value its signed
            // type must hold (Rust reads `-128i8` as the literal -128).
            TrustVcExpr::Neg(inner) => match inner.as_ref() {
                TrustVcExpr::IntLit { value, ty }
                    if matches!(ty, TrustVcType::Int { .. }) && *value > 0 =>
                {
                    literal_holds(value.checked_neg().unwrap_or(i128::MIN), ty)
                }
                _ => self.expr(inner),
            },
            TrustVcExpr::Not(inner) => self.expr(inner),
            TrustVcExpr::Implies {
                premise,
                conclusion,
            } => {
                self.expr(premise)?;
                self.expr(conclusion)
            }
            TrustVcExpr::Ite {
                cond,
                then_branch,
                else_branch,
                ty,
            } => {
                self.expr(cond)?;
                self.expr(then_branch)?;
                self.expr(else_branch)?;
                if is_integer_type(ty) {
                    derived_agrees(expr, ty, &[then_branch, else_branch])
                } else {
                    composite_holds(
                        ty,
                        [then_branch.as_ref(), else_branch.as_ref()],
                        "conditional",
                    )
                }
            }
            TrustVcExpr::Match {
                scrutinee,
                arms,
                ty,
            } => {
                self.expr(scrutinee)?;
                let scrutinee_ty = infer_expr_type(scrutinee);
                for arm in arms {
                    let binders = pattern_binders(&arm.pattern, &scrutinee_ty);
                    if let MatchPattern::Lit(literal) = &arm.pattern {
                        self.expr(literal)?;
                    }
                    self.with_binders(binders, |walker| {
                        if let Some(guard) = &arm.guard {
                            walker.expr(guard)?;
                        }
                        walker.expr(&arm.body)
                    })?;
                }
                if is_integer_type(ty) {
                    let bodies = arms.iter().map(|arm| &arm.body).collect::<Vec<_>>();
                    if untyped_placeholder_join(ty, &bodies) {
                        return Ok(());
                    }
                    let derived = derive_arms_int_type(&bodies, ty).1;
                    integer_claim_agrees(ty, &derived, || expr_label(expr))
                } else {
                    composite_holds(ty, arms.iter().map(|arm| &arm.body), "match")
                }
            }
            TrustVcExpr::Let {
                name,
                ty,
                value,
                body,
            } => {
                self.expr(value)?;
                binding_holds(value, ty, name)?;
                self.with_binders([(name.clone(), Some(ty.clone()))], |walker| {
                    walker.expr(body)
                })
            }
            TrustVcExpr::Cast {
                expr: inner,
                from_ty,
                ..
            } => {
                self.expr(inner)?;
                cast_operand_agrees(inner, from_ty)
            }
            TrustVcExpr::CollectionOp {
                op,
                receiver,
                args,
                ty,
                ..
            } => {
                self.expr(receiver)?;
                for arg in args {
                    self.expr(arg)?;
                }
                collection_op_agrees(*op, receiver, args, ty)
            }
            TrustVcExpr::Index {
                receiver,
                index,
                elem_ty,
                ..
            } => {
                self.expr(receiver)?;
                self.expr(index)?;
                element_read_agrees(receiver, index, elem_ty)
            }
            TrustVcExpr::WrappingArith {
                left, right, ty, ..
            } => {
                self.expr(left)?;
                self.expr(right)?;
                for operand in [left.as_ref(), right.as_ref()] {
                    if let IntBinding::Mismatch(found) = wrapping_operand(operand, ty) {
                        return Err(format!(
                            "a `wrapping`/`saturating` operand of type `{}` at type `{}`: \
                             the method takes a value of its own type",
                            found.to_type_string(),
                            ty.to_type_string()
                        ));
                    }
                }
                Ok(())
            }
            TrustVcExpr::Quantifier {
                bound_vars, body, ..
            } => {
                let binders = bound_vars
                    .iter()
                    .map(|(name, ty)| (name.clone(), Some(ty.clone())));
                self.with_binders(binders, |walker| walker.expr(body))
            }
            TrustVcExpr::FnCall {
                name,
                args,
                return_ty,
            } => {
                for arg in args {
                    self.expr(arg)?;
                }
                self.call_arguments(name, args)?;
                self.call_result(name, return_ty)
            }
            TrustVcExpr::SpecClosure { params, body, ty } => {
                let binders = params
                    .iter()
                    .map(|(name, ty)| (name.clone(), Some(ty.clone())));
                self.with_binders(binders, |walker| walker.expr(body))?;
                spec_closure_agrees(params, body, ty)
            }
            TrustVcExpr::Choose {
                var_name,
                var_ty,
                condition,
                also_assert,
                ..
            } => self.with_binders([(var_name.clone(), Some(var_ty.clone()))], |walker| {
                walker.expr(condition)?;
                match also_assert {
                    Some(extra) => walker.expr(extra),
                    None => Ok(()),
                }
            }),
            TrustVcExpr::ProphecyResolve { value, .. } => self.expr(value),
        }
    }

    /// Every call argument is a value its parameter's DECLARED type holds
    /// (`bind_call_argument`, §5b rule 11) — at the root, before an inline
    /// body is substituted for the call. Only the non-inline dispatch bound
    /// arguments: an INLINE `fid(q: u8) -> u8 { q }` applied to `y: i8 ==
    /// -56` substituted `y` for `q` unbound, so `fid(y) < 0` was `Verified`
    /// (and so was the non-inline call in the exec lane, whose demand-inline
    /// retry re-encodes the call inline).
    fn call_arguments(&self, name: &str, args: &[TrustVcExpr]) -> Result<(), String> {
        let Some(params) = self
            .scope
            .parameters
            .and_then(|parameters| parameters.get(name))
        else {
            return Ok(());
        };
        if params.len() != args.len() {
            return Ok(());
        }
        for (index, (arg, param)) in args.iter().zip(params).enumerate() {
            if mentions_type_parameter(param) {
                continue;
            }
            if let Err(found) = bind_call_argument(arg, param) {
                return Err(format!(
                    "a call of `{name}` passes a value of type `{}` for parameter {index} of \
                     type `{}`, which cannot hold it",
                    found.to_type_string(),
                    param.to_type_string()
                ));
            }
        }
        Ok(())
    }

    /// A call's result is a value of the function's DECLARED result type (a
    /// generic one is instantiated at the call and not compared here).
    fn call_result(&self, name: &str, return_ty: &TrustVcType) -> Result<(), String> {
        let Some(declared) = self
            .scope
            .functions
            .and_then(|functions| functions.get(name))
        else {
            return Ok(());
        };
        if declared == return_ty || mentions_type_parameter(declared) {
            return Ok(());
        }
        let disagree = if is_integer_type(declared) || is_integer_type(return_ty) {
            is_integer_type(declared) && is_integer_type(return_ty)
        } else {
            !(integer_positions_agree(declared, return_ty)
                && integer_positions_agree(return_ty, declared))
        };
        if disagree {
            return Err(format!(
                "a call of `{name}` (declared to return `{}`) read at type `{}`",
                declared.to_type_string(),
                return_ty.to_type_string()
            ));
        }
        Ok(())
    }

    /// A variable is a value of its binder's type. The context may declare an
    /// `int`/`nat` for a variable the IR reads at a fixed width inside an
    /// integer-mode quantifier body (`encode_var`'s promotion), which is not a
    /// disagreement here; every other difference is.
    fn var(&self, name: &str, ty: &TrustVcType) -> Result<(), String> {
        let Some(Some(declared)) = self.binder_type(name) else {
            return Ok(());
        };
        let promoted =
            matches!(declared, TrustVcType::MathInt | TrustVcType::Nat) && ty.is_integer();
        if declared == ty || promoted || !type_holds_an_integer(declared) {
            return Ok(());
        }
        Err(format!(
            "the variable `{name}` of type `{}` read at type `{}`",
            declared.to_type_string(),
            ty.to_type_string()
        ))
    }
}
