// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

/// Maximum number of *inline body expansions* permitted along any single path
/// of the expression tree before substitution stops and leaves the residual
/// call uninterpreted.
///
/// This is a HARD ROBUSTNESS BOUND, not a tuning knob. Inlining a recursive
/// spec function's body is non-terminating: each expansion of `f`'s body
/// re-introduces a call to `f` (directly, or through a mutual partner), so an
/// unbounded `substitute_inline_calls` recurses until the stack guard page is
/// hit (SIGBUS / stack overflow). The proc-macro inline path rejects recursive
/// inline functions at compile time (`spec_expand.rs`), but the demand-inline
/// retry (#2655) *promotes* an ordinary recursive body axiom to inline at
/// runtime, bypassing that gate — `build_body_catalog` filters direct recursion,
/// while termination-proven mutual recursion may be expanded for a fully ground
/// branch. This bound is the belt-and-braces backstop so
/// the encoder can NEVER crash even if a recursive body reaches this function
/// (e.g. a symbolic mutual `a -> b -> a` inline cycle).
///
/// The counter only increments on an actual body expansion, never on structural
/// descent into sub-expressions, so legitimate non-recursive inline chains
/// (bounded by the call-graph depth, which is far below this limit) are never
/// truncated. Leaving the residual `FnCall` uninterpreted is sound: an
/// uninterpreted symbol drops the body equation for that one term, which can
/// only make a goal HARDER to prove — never produce a false `Verified`.
const MAX_INLINE_EXPANSION_DEPTH: usize = 64;

/// Recursively substitutes inline spec function calls with their body expression.
///
/// For each `FnCall { name }` where `inline_bodies` contains `name`, replaces
/// the call with the body expression after substituting formal parameters with
/// actual arguments. Non-inline calls and non-FnCall nodes pass through unchanged.
///
/// Part of #2488.
/// Inline-body catalog value: `(formal param names, formal param TYPES, body)`.
/// The param types (positionally aligned with the names) carry the TEMPLATE
/// types so a generic inline body is monomorphized to the call-site
/// instantiation (#2777, `inline_poly`).
pub(in crate::encoder) type InlineBodyMap = std::collections::HashMap<
    String,
    (
        Vec<String>,
        Vec<crate::ir::TrustVcType>,
        crate::ir::TrustVcExpr,
    ),
>;

pub(in crate::encoder) fn substitute_inline_calls(
    expr: &crate::ir::TrustVcExpr,
    inline_bodies: &InlineBodyMap,
) -> crate::ir::TrustVcExpr {
    substitute_inline_calls_bounded(expr, inline_bodies, 0, &[])
}

/// Recursion-bounded core of [`substitute_inline_calls`]. `expansion_depth` counts
/// the inline body expansions performed on the path from the original call down
/// to `expr`; it is incremented ONLY when a body is expanded (never on
/// structural descent), and capped by [`MAX_INLINE_EXPANSION_DEPTH`] to
/// guarantee termination on (mutually) recursive inline bodies. `active_calls`
/// also stops an exact repeated `(function, arguments)` state immediately; this
/// avoids constructing a deep conditional spine for `a(x) -> b(x) -> a(x)`
/// while preserving finite ground recursion whose arguments genuinely change.
fn substitute_inline_calls_bounded(
    expr: &crate::ir::TrustVcExpr,
    inline_bodies: &InlineBodyMap,
    expansion_depth: usize,
    active_calls: &[(String, Vec<crate::ir::TrustVcExpr>)],
) -> crate::ir::TrustVcExpr {
    use crate::ir::TrustVcExpr;

    // Structural descent preserves the expansion depth — only an actual body
    // expansion (below) increments it.
    let rec_vec = |exprs: &[TrustVcExpr]| -> Vec<TrustVcExpr> {
        exprs
            .iter()
            .map(|e| {
                substitute_inline_calls_bounded(e, inline_bodies, expansion_depth, active_calls)
            })
            .collect()
    };
    let rec = |e: &TrustVcExpr| {
        substitute_inline_calls_bounded(e, inline_bodies, expansion_depth, active_calls)
    };

    match expr {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            let expanded_args = rec_vec(args);
            if let Some((param_names, param_types, body)) = inline_bodies.get(name) {
                // Every argument is BOUND at its parameter's type, exactly as
                // a non-inline call binds it (`ir_lowering::bind_call_argument`,
                // §5b rule 11): the body reads the parameter at its declared
                // type, so a `u8` argument of an `int` parameter lands as the
                // integer it denotes. An argument the parameter's type cannot
                // hold leaves the call unexpanded — the dispatch refuses it
                // (`fid(q: u8) -> u8 { q }` applied to `y: i8 == -56`
                // substituted `y` bare: `fid(y) < 0` was `Verified`).
                let bound_args = if param_types.len() == expanded_args.len() {
                    param_types
                        .iter()
                        .zip(&expanded_args)
                        .map(|(param_ty, arg)| {
                            crate::ir_lowering::bind_call_argument(arg, param_ty).ok()
                        })
                        .collect::<Option<Vec<_>>>()
                } else {
                    None
                };
                // Stop before exceeding the expansion bound: leave the residual
                // call uninterpreted rather than recurse into a non-terminating
                // (recursive) inline body and overflow the stack.
                if let Some(bound_args) = bound_args.filter(|_| {
                    expansion_depth < MAX_INLINE_EXPANSION_DEPTH
                        && param_names.len() == expanded_args.len()
                        && !active_calls.iter().any(|(active_name, active_args)| {
                            active_name == name && active_args == &expanded_args
                        })
                }) {
                    // Monomorphize the (possibly generic) inline body to the
                    // concrete instantiation implied by the call-site argument
                    // types (#2777, upstream inline.rs `inline_poly`). Unify each
                    // TEMPLATE param type (e.g. `Set(TypeParam("A"))`) against the
                    // actual argument type (`Set(int)`) to collect the
                    // `TypeParam`->concrete bindings, then substitute those into
                    // every sort embedded in the body (quantifier binder types,
                    // Set/Seq/Map element sorts, return types, ...). Without this
                    // the forall binder `|a: A|` keeps its `TypeParam` sort while
                    // the receiver becomes concrete, so the encoder hits a
                    // select/contains index-sort mismatch (`Poly` vs `int`) and
                    // returns Unknown. EXACT & SOUND: it only makes sorts concrete
                    // from the ACTUAL arguments (never proves more than Verus's
                    // inline-then-typecheck); any `TypeParam` left unbound (a
                    // return-only param, or a mismatched arity) stays generic ->
                    // encodes to the `Poly` sort -> fail-closed sort mismatch,
                    // never a false `Verified`.
                    let mut bindings: Vec<(String, crate::ir::TrustVcType)> = Vec::new();
                    for (param_ty, arg) in param_types.iter().zip(expanded_args.iter()) {
                        param_ty.collect_type_param_bindings(
                            &crate::ir_lowering::infer_expr_type(arg),
                            &mut bindings,
                        );
                    }
                    let monomorphized_body: TrustVcExpr;
                    let body: &TrustVcExpr = if bindings.is_empty() {
                        body
                    } else {
                        monomorphized_body = monomorphize_inline_body_types(body, &bindings);
                        &monomorphized_body
                    };

                    let subst: std::collections::HashMap<&str, &TrustVcExpr> = param_names
                        .iter()
                        .zip(bound_args.iter())
                        .map(|(p, a)| (p.as_str(), a))
                        .collect();
                    let substituted = super::vars::substitute_vars_in_expr(body, &subst);
                    let mut nested_calls = active_calls.to_vec();
                    nested_calls.push((name.clone(), expanded_args.clone()));
                    return substitute_inline_calls_bounded(
                        &substituted,
                        inline_bodies,
                        expansion_depth + 1,
                        &nested_calls,
                    );
                }
            }
            // A tuple constructor from an inlined generic body (`(b, a)` in
            // `swap<A, B>`) is lowered ONCE at catalog time under the TEMPLATE
            // field types (`(B, A)`), so its constructor name / return sort are
            // stale after the formal params are substituted with the concrete
            // call-site arguments (`(true, 10u8)`). Recompute the tuple carrier
            // structurally from the now-concrete argument types so the
            // substituted value's sort matches the concrete `(bool, u8)` carrier
            // the call-site field-access selectors were lowered against. This is
            // exact — a tuple literal's type IS its element types — so it can
            // never prove more than Verus. Non-tuple constructors (named
            // struct/enum variants) keep their declared name and sort.
            let (name, return_ty) = renormalize_tuple_constructor(name, &expanded_args, return_ty);
            TrustVcExpr::FnCall {
                name,
                args: expanded_args,
                return_ty,
            }
        }
        TrustVcExpr::BoolLit(_)
        | TrustVcExpr::UnitLit
        | TrustVcExpr::StringLit(_)
        | TrustVcExpr::IntLit { .. }
        | TrustVcExpr::IntConst { .. }
        | TrustVcExpr::Var { .. } => expr.clone(),
        TrustVcExpr::SpecClosure { params, body, ty } => TrustVcExpr::SpecClosure {
            params: params.clone(),
            body: Box::new(rec(body)),
            ty: ty.clone(),
        },
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
        } => {
            let expanded_cond = rec(cond);
            // Inline recursive definitions lazily across a statically decided
            // branch.  Expanding BOTH arms of `if 0 == 0 { 0 } else { f(..) }`
            // follows an unreachable recursive call until the robustness cap,
            // leaving a residual UF even though the selected expression is the
            // exact ground value `0`.  Choosing an arm is exact only when the
            // condition is decided structurally below; symbolic conditions keep
            // the old eager, bounded behavior and therefore remain fail-closed.
            if let Some(value) = statically_decided_inline_condition(&expanded_cond) {
                return if value {
                    rec(then_branch)
                } else {
                    rec(else_branch)
                };
            }
            TrustVcExpr::Ite {
                cond: Box::new(expanded_cond),
                then_branch: Box::new(rec(then_branch)),
                else_branch: Box::new(rec(else_branch)),
                ty: ty.clone(),
            }
        }
        TrustVcExpr::Let {
            name,
            ty,
            value,
            body,
        } => TrustVcExpr::Let {
            name: name.clone(),
            ty: ty.clone(),
            value: Box::new(rec(value)),
            body: Box::new(rec(body)),
        },
        TrustVcExpr::Cast {
            expr: inner,
            from_ty,
            to_ty,
        } => TrustVcExpr::Cast {
            expr: Box::new(rec(inner)),
            from_ty: from_ty.clone(),
            to_ty: to_ty.clone(),
        },
        TrustVcExpr::CollectionOp {
            op,
            receiver,
            receiver_name,
            args,
            ty,
        } => TrustVcExpr::CollectionOp {
            op: *op,
            receiver: Box::new(rec(receiver)),
            receiver_name: receiver_name.clone(),
            args: rec_vec(args),
            ty: ty.clone(),
        },
        TrustVcExpr::Index {
            receiver,
            index,
            receiver_name,
            elem_ty,
        } => TrustVcExpr::Index {
            receiver: Box::new(rec(receiver)),
            index: Box::new(rec(index)),
            receiver_name: receiver_name.clone(),
            elem_ty: elem_ty.clone(),
        },
        TrustVcExpr::Quantifier {
            kind,
            bound_vars,
            body,
            triggers,
            trigger_inference_mode,
        } => TrustVcExpr::Quantifier {
            kind: *kind,
            bound_vars: bound_vars.clone(),
            body: Box::new(rec(body)),
            triggers: triggers
                .as_ref()
                .map(|ts| ts.iter().map(|g| rec_vec(g)).collect()),
            trigger_inference_mode: *trigger_inference_mode,
        },
        TrustVcExpr::Match {
            scrutinee,
            arms,
            ty,
        } => TrustVcExpr::Match {
            scrutinee: Box::new(rec(scrutinee)),
            arms: arms
                .iter()
                .map(|arm| crate::ir::MatchArm {
                    pattern: arm.pattern.clone(),
                    body: rec(&arm.body),
                    // Substitute inside the guard too — an inlined guarded match whose
                    // guard was dropped would become unconditional (false-verify).
                    guard: arm.guard.as_ref().map(rec),
                })
                .collect(),
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
        TrustVcExpr::Choose {
            var_name,
            var_ty,
            condition,
            key,
            also_assert,
        } => TrustVcExpr::Choose {
            var_name: var_name.clone(),
            var_ty: var_ty.clone(),
            condition: Box::new(rec(condition)),
            key: key.clone(),
            also_assert: also_assert.as_ref().map(|e| Box::new(rec(e))),
        },
        TrustVcExpr::ReadPlace { place, ty } => TrustVcExpr::ReadPlace {
            place: place.map_indices(&rec),
            ty: ty.clone(),
        },
        TrustVcExpr::PlaceDisjoint { left, right } => TrustVcExpr::PlaceDisjoint {
            left: left.map_indices(&rec),
            right: right.map_indices(&rec),
        },
        TrustVcExpr::ProphecyNew { name, ty } => TrustVcExpr::ProphecyNew {
            name: name.clone(),
            ty: ty.clone(),
        },
        TrustVcExpr::ProphecyResolve { name, value } => TrustVcExpr::ProphecyResolve {
            name: name.clone(),
            value: Box::new(rec(value)),
        },
    }
}

/// Returns a Boolean only when the IR itself proves the condition's value.
///
/// This deliberately is not a general arithmetic simplifier.  In particular,
/// two syntactically different integer literals may still carry context-sized
/// default types, so comparing their host values here could choose the wrong
/// fixed-width branch. Reflexive equality/disequality is used only for the
/// explicitly classified non-floating scalar sorts below: IEEE NaN makes
/// `x == x` false, so Float must never take this shortcut. Boolean
/// literals/negation preserve exactness.
fn statically_decided_inline_condition(expr: &crate::ir::TrustVcExpr) -> Option<bool> {
    use crate::ir::{CompareOp, TrustVcExpr};

    match expr {
        TrustVcExpr::BoolLit(value) => Some(*value),
        TrustVcExpr::Not(inner) => statically_decided_inline_condition(inner).map(|v| !v),
        TrustVcExpr::Compare { op, left, right }
            if left == right
                && matches!(
                    crate::ir_lowering::infer_expr_type(left),
                    crate::ir::TrustVcType::Unit
                        | crate::ir::TrustVcType::Bool
                        | crate::ir::TrustVcType::Int { .. }
                        | crate::ir::TrustVcType::Uint { .. }
                        | crate::ir::TrustVcType::MathInt
                        | crate::ir::TrustVcType::Nat
                        | crate::ir::TrustVcType::Char
                ) =>
        {
            match op {
                CompareOp::Eq => Some(true),
                CompareOp::Ne => Some(false),
                CompareOp::Lt | CompareOp::Le | CompareOp::Gt | CompareOp::Ge => None,
            }
        }
        _ => None,
    }
}

/// Recompute a tuple constructor's carrier name and return sort from its
/// (already inline-substituted) concrete argument types.
///
/// A tuple is lowered as `FnCall { name: variant_symbol_name(tuple_name,
/// "Tuple"), return_ty: Datatype { name: tuple_name, variants: [Tuple{..}] } }`.
/// When such a constructor comes from an inlined generic body it was lowered
/// under TEMPLATE field types (e.g. `(B, A)`); after the formal params are
/// replaced with the concrete call-site arguments the tuple's true sort is that
/// of its elements (`(bool, u8)`). Recomputing structurally from the argument
/// types keeps the substituted value's sort consistent with the concrete tuple
/// carrier the call-site field-access selectors were lowered against. Exact
/// (a tuple literal's type is its element types), so never proves more than
/// Verus.
///
/// Only anonymous tuple carriers (the sole variant named `TUPLE_VARIANT_NAME`,
/// with the constructor name matching that carrier) are recomputed; any other
/// `FnCall` (named struct/enum constructor, spec helper, selector) is returned
/// unchanged.
fn renormalize_tuple_constructor(
    name: &str,
    args: &[crate::ir::TrustVcExpr],
    return_ty: &crate::ir::TrustVcType,
) -> (String, crate::ir::TrustVcType) {
    use crate::ir::TrustVcType;
    use crate::ir_expr::{tuple_datatype_type, TUPLE_VARIANT_NAME};

    let TrustVcType::Datatype {
        name: dt_name,
        variants,
    } = return_ty
    else {
        return (name.to_string(), return_ty.clone());
    };
    // Must be a single anonymous tuple variant whose constructor symbol matches,
    // with a tuple-shaped carrier name (`(` prefix — the only shape
    // `tuple_datatype_name` emits). The name guard keeps a hypothetical user enum
    // `enum Foo { Tuple(..) }` (whose sole variant is coincidentally named
    // `Tuple`) from being renamed. A miss leaves the constructor unchanged.
    let [variant] = variants.as_slice() else {
        return (name.to_string(), return_ty.clone());
    };
    if variant.name != TUPLE_VARIANT_NAME
        || !dt_name.starts_with('(')
        || name != crate::encoder::datatype::variant_symbol_name(dt_name, TUPLE_VARIANT_NAME)
        || variant.fields.len() != args.len()
    {
        return (name.to_string(), return_ty.clone());
    }
    let element_tys = args
        .iter()
        .map(crate::ir_lowering::infer_expr_type)
        .collect::<Vec<_>>();
    let recomputed = tuple_datatype_type(element_tys);
    let TrustVcType::Datatype { name: new_name, .. } = &recomputed else {
        return (name.to_string(), return_ty.clone());
    };
    (
        crate::encoder::datatype::variant_symbol_name(new_name, TUPLE_VARIANT_NAME),
        recomputed,
    )
}

/// Substitutes concrete type bindings for `TypeParam`s in EVERY sort embedded in
/// an expression tree — quantifier binder types, `Set`/`Seq`/`Map` element
/// sorts, `FnCall` return types, `Var`/`Let`/`Cast` types, etc. Used to
/// monomorphize a generic inline spec-fn body to the concrete instantiation
/// implied by the call-site argument types (#2777, `inline_poly`), so the
/// substituted body's sorts line up with the concrete arguments.
///
/// SOUNDNESS: `substitute_type_params` only replaces a `TypeParam(name)` with
/// its bound concrete type (structural recursion, tuple-carrier renormalization,
/// NO arbitrary datatype-carrier renaming). It makes sorts concrete strictly
/// from the actual argument types — it can never make a false property provable.
/// An unbound `TypeParam` is left as-is (encodes to the `Poly` sort -> fail-
/// closed sort mismatch), so incompleteness here is safe: never a false Verified.
fn monomorphize_inline_body_types(
    body: &crate::ir::TrustVcExpr,
    bindings: &[(String, crate::ir::TrustVcType)],
) -> crate::ir::TrustVcExpr {
    use crate::ir_expr_traversal::TrustVcExprFolder;
    if bindings.is_empty() {
        return body.clone();
    }
    let mut monomorphizer = InlineBodyTypeMonomorphizer { bindings };
    monomorphizer.fold_expr(body.clone())
}

/// [`TrustVcExprFolder`] that rewrites every embedded sort through
/// [`crate::ir_lowering::substitute_type_params`] using the call-site bindings,
/// then delegates child-expression recursion to `fold_expr_children`.
struct InlineBodyTypeMonomorphizer<'a> {
    bindings: &'a [(String, crate::ir::TrustVcType)],
}

/// True iff `ty` is an anonymous tuple carrier (a single `Tuple` variant with a
/// `(`-prefixed carrier name — the only shape `tuple_datatype_name` emits). Such
/// return types are recomputed by `renormalize_tuple_constructor` from the
/// concrete arguments, so the type monomorphizer must not touch them.
fn is_tuple_carrier(ty: &crate::ir::TrustVcType) -> bool {
    matches!(
        ty,
        crate::ir::TrustVcType::Datatype { name, variants }
            if name.starts_with('(')
                && matches!(
                    variants.as_slice(),
                    [only] if only.name == crate::ir_expr::TUPLE_VARIANT_NAME
                )
    )
}

impl InlineBodyTypeMonomorphizer<'_> {
    fn subst(&self, ty: &crate::ir::TrustVcType) -> crate::ir::TrustVcType {
        crate::ir_lowering::substitute_type_params(ty, self.bindings)
    }

    /// Rewrites ONLY this node's own embedded type fields (child expressions are
    /// left untouched here — `fold_expr_children` folds them next). The match is
    /// exhaustive with NO catch-all, so a newly added `TrustVcExpr` variant
    /// forces a compile error until it is classified (mirrors `fold_expr_children`).
    fn rewrite_own_types(&self, expr: crate::ir::TrustVcExpr) -> crate::ir::TrustVcExpr {
        use crate::ir::TrustVcExpr as E;
        match expr {
            // Type-carrying nodes: monomorphize the embedded sort(s).
            E::IntLit { value, ty } => E::IntLit {
                value,
                ty: self.subst(&ty),
            },
            E::Var { name, ty } => E::Var {
                name,
                ty: self.subst(&ty),
            },
            E::Arith {
                op,
                left,
                right,
                ty,
            } => E::Arith {
                op,
                left,
                right,
                ty: self.subst(&ty),
            },
            E::Ite {
                cond,
                then_branch,
                else_branch,
                ty,
            } => E::Ite {
                cond,
                then_branch,
                else_branch,
                ty: self.subst(&ty),
            },
            E::Match {
                scrutinee,
                arms,
                ty,
            } => E::Match {
                scrutinee,
                arms,
                ty: self.subst(&ty),
            },
            E::Let {
                name,
                ty,
                value,
                body,
            } => E::Let {
                name,
                ty: self.subst(&ty),
                value,
                body,
            },
            E::Cast {
                expr,
                from_ty,
                to_ty,
            } => E::Cast {
                expr,
                from_ty: self.subst(&from_ty),
                to_ty: self.subst(&to_ty),
            },
            E::CollectionOp {
                op,
                receiver,
                receiver_name,
                args,
                ty,
            } => E::CollectionOp {
                op,
                receiver,
                receiver_name,
                args,
                ty: self.subst(&ty),
            },
            E::Index {
                receiver,
                index,
                receiver_name,
                elem_ty,
            } => E::Index {
                receiver,
                index,
                receiver_name,
                elem_ty: self.subst(&elem_ty),
            },
            E::Quantifier {
                kind,
                bound_vars,
                body,
                triggers,
                trigger_inference_mode,
            } => E::Quantifier {
                kind,
                bound_vars: bound_vars
                    .into_iter()
                    .map(|(n, t)| (n, self.subst(&t)))
                    .collect(),
                body,
                triggers,
                trigger_inference_mode,
            },
            E::FnCall {
                name,
                args,
                return_ty,
            } => {
                // Leave a TUPLE-constructor return type to
                // `renormalize_tuple_constructor`, which recomputes BOTH the
                // carrier name and the return sort from the concrete
                // post-substitution argument types. Monomorphizing the return
                // sort here would desync it from the still-template constructor
                // NAME (which this pass does not rewrite) -> the exact sort
                // mismatch `renormalize` exists to prevent. Non-tuple returns are
                // monomorphized normally. (Un-monomorphized => fail-closed, so
                // even a non-constructor tuple return is at worst incomplete.)
                let return_ty = if is_tuple_carrier(&return_ty) {
                    return_ty
                } else {
                    self.subst(&return_ty)
                };
                E::FnCall {
                    name,
                    args,
                    return_ty,
                }
            }
            E::SpecClosure { params, body, ty } => E::SpecClosure {
                params: params
                    .into_iter()
                    .map(|(n, t)| (n, self.subst(&t)))
                    .collect(),
                body,
                ty: self.subst(&ty),
            },
            E::IntConst { ty, kind } => E::IntConst {
                ty: self.subst(&ty),
                kind,
            },
            E::SpecialArith {
                op,
                left,
                right,
                ty,
            } => E::SpecialArith {
                op,
                left,
                right,
                ty: self.subst(&ty),
            },
            E::WrappingArith {
                mode,
                op,
                left,
                right,
                ty,
            } => E::WrappingArith {
                mode,
                op,
                left,
                right,
                ty: self.subst(&ty),
            },
            E::Choose {
                var_name,
                var_ty,
                condition,
                key,
                also_assert,
            } => E::Choose {
                var_name,
                var_ty: self.subst(&var_ty),
                condition,
                key,
                also_assert,
            },
            // `place` projections may carry their own sorts; those are left as-is
            // (an un-substituted `TypeParam` fails closed, never a false verify).
            E::ReadPlace { place, ty } => E::ReadPlace {
                place,
                ty: self.subst(&ty),
            },
            E::ProphecyNew { name, ty } => E::ProphecyNew {
                name,
                ty: self.subst(&ty),
            },
            // Nodes with no embedded sorts: pass through unchanged.
            E::UnitLit
            | E::BoolLit(_)
            | E::StringLit(_)
            | E::Neg(_)
            | E::Compare { .. }
            | E::Logic { .. }
            | E::Not(_)
            | E::Implies { .. }
            | E::PlaceDisjoint { .. }
            | E::ProphecyResolve { .. } => expr,
        }
    }
}

impl crate::ir_expr_traversal::TrustVcExprFolder for InlineBodyTypeMonomorphizer<'_> {
    fn fold_expr(&mut self, expr: crate::ir::TrustVcExpr) -> crate::ir::TrustVcExpr {
        // Rewrite this node's own types first, then recurse into children.
        let expr = self.rewrite_own_types(expr);
        crate::ir_expr_traversal::fold_expr_children(self, expr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{ArithOp, CompareOp, TrustVcExpr, TrustVcType};
    use std::collections::HashMap;

    fn int_ty() -> TrustVcType {
        TrustVcType::Int { width: 64 }
    }

    fn var(name: &str) -> TrustVcExpr {
        TrustVcExpr::Var {
            name: name.to_string(),
            ty: int_ty(),
        }
    }

    fn int_lit(value: i128) -> TrustVcExpr {
        TrustVcExpr::IntLit {
            value,
            ty: int_ty(),
        }
    }

    fn call(name: &str, args: Vec<TrustVcExpr>) -> TrustVcExpr {
        TrustVcExpr::FnCall {
            name: name.to_string(),
            args,
            return_ty: int_ty(),
        }
    }

    fn add(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
        TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(left),
            right: Box::new(right),
            ty: int_ty(),
        }
    }

    fn zero_guarded_recursive_call(partner: &str) -> TrustVcExpr {
        TrustVcExpr::Ite {
            cond: Box::new(TrustVcExpr::Compare {
                op: CompareOp::Eq,
                left: Box::new(var("x")),
                right: Box::new(int_lit(0)),
            }),
            then_branch: Box::new(int_lit(0)),
            else_branch: Box::new(add(int_lit(1), call(partner, vec![var("x")]))),
            ty: int_ty(),
        }
    }

    /// Counts how many `FnCall` nodes naming `name` survive in `expr`.
    fn count_calls(expr: &TrustVcExpr, name: &str) -> usize {
        match expr {
            TrustVcExpr::FnCall { name: n, args, .. } => {
                (if n == name { 1 } else { 0 })
                    + args.iter().map(|a| count_calls(a, name)).sum::<usize>()
            }
            TrustVcExpr::Arith { left, right, .. } => {
                count_calls(left, name) + count_calls(right, name)
            }
            _ => 0,
        }
    }

    fn count_all_calls(expr: &TrustVcExpr, names: &[&str]) -> usize {
        use crate::ir_expr_traversal::{walk_expr, TrustVcExprVisitor};

        struct Counter<'a> {
            names: &'a [&'a str],
            count: usize,
        }
        impl TrustVcExprVisitor for Counter<'_> {
            fn visit_expr(&mut self, expr: &TrustVcExpr) {
                if let TrustVcExpr::FnCall { name, .. } = expr {
                    self.count += usize::from(self.names.contains(&name.as_str()));
                }
                walk_expr(self, expr);
            }
        }

        let mut counter = Counter { names, count: 0 };
        counter.visit_expr(expr);
        counter.count
    }

    /// A SELF-recursive inline body `f(x) == f(x) + 1` must not drive
    /// `substitute_inline_calls` into unbounded recursion. The expansion is
    /// capped and a single residual `f(...)` call is left uninterpreted. Before
    /// the depth backstop this stack-overflowed (SIGBUS). Part of #54.
    #[test]
    fn self_recursive_inline_body_terminates_with_residual_call() {
        let mut bodies: InlineBodyMap = HashMap::new();
        bodies.insert(
            "f".to_string(),
            (
                vec!["x".to_string()],
                vec![int_ty()],
                add(call("f", vec![var("x")]), int_lit(1)),
            ),
        );

        let result = substitute_inline_calls(&call("f", vec![int_lit(0)]), &bodies);

        // Terminated (no stack overflow) and stopped at the bound, leaving
        // exactly one residual `f` call rather than inlining forever.
        assert_eq!(
            count_calls(&result, "f"),
            1,
            "expected a single residual self-call after the expansion bound, got: {result:?}"
        );
    }

    /// A MUTUALLY-recursive inline cycle `a(x) == b(x) + 1`, `b(x) == a(x) + 1`
    /// (the open finding in `eval_audit_p584.rs`) is likewise bounded by the
    /// depth backstop rather than overflowing the stack. Part of #54.
    #[test]
    fn mutually_recursive_inline_bodies_terminate() {
        let mut bodies: InlineBodyMap = HashMap::new();
        bodies.insert(
            "a".to_string(),
            (
                vec!["x".to_string()],
                vec![int_ty()],
                add(call("b", vec![var("x")]), int_lit(1)),
            ),
        );
        bodies.insert(
            "b".to_string(),
            (
                vec!["x".to_string()],
                vec![int_ty()],
                add(call("a", vec![var("x")]), int_lit(1)),
            ),
        );

        let result = substitute_inline_calls(&call("a", vec![int_lit(0)]), &bodies);

        // Exactly one residual call remains (to whichever partner the bound
        // halted on); the key property is that we got here at all.
        let residual = count_calls(&result, "a") + count_calls(&result, "b");
        assert_eq!(
            residual, 1,
            "expected a single residual mutual-call after the expansion bound, got: {result:?}"
        );
    }

    /// A ground base-case call through a mutually-recursive body is an exact
    /// finite expansion: the false recursive arm is unreachable and must not be
    /// traversed merely because substitution walks the expression tree.
    #[test]
    fn mutually_recursive_ground_base_case_prunes_unreachable_arm() {
        let mut bodies: InlineBodyMap = HashMap::new();
        bodies.insert(
            "a".to_string(),
            (
                vec!["x".to_string()],
                vec![int_ty()],
                zero_guarded_recursive_call("b"),
            ),
        );
        bodies.insert(
            "b".to_string(),
            (
                vec!["x".to_string()],
                vec![int_ty()],
                zero_guarded_recursive_call("a"),
            ),
        );

        let result = substitute_inline_calls(&call("b", vec![int_lit(0)]), &bodies);

        assert_eq!(result, int_lit(0));
    }

    /// A symbolic guard is not guessed. Both branches retain their meaning and
    /// recursive expansion remains capped with a residual call (fail-closed).
    #[test]
    fn mutually_recursive_symbolic_guard_is_not_pruned() {
        let mut bodies: InlineBodyMap = HashMap::new();
        bodies.insert(
            "a".to_string(),
            (
                vec!["x".to_string()],
                vec![int_ty()],
                zero_guarded_recursive_call("b"),
            ),
        );
        bodies.insert(
            "b".to_string(),
            (
                vec!["x".to_string()],
                vec![int_ty()],
                zero_guarded_recursive_call("a"),
            ),
        );

        let result = substitute_inline_calls(&call("b", vec![var("n")]), &bodies);
        let residual = count_all_calls(&result, &["a", "b"]);

        assert!(residual > 0, "symbolic recursion must remain fail-closed");
    }

    /// IEEE equality is not reflexive at NaN, so syntactic identity alone must
    /// never decide a floating-point branch.
    #[test]
    fn identical_float_operands_do_not_prune_branch() {
        let float = TrustVcExpr::Var {
            name: "f".to_string(),
            ty: TrustVcType::Float { width: 64 },
        };
        let condition = TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(float.clone()),
            right: Box::new(float),
        };

        assert_eq!(statically_decided_inline_condition(&condition), None);
    }

    /// An inline call's argument is BOUND at its parameter's type before the
    /// body lands (§5b rule 11): a `u8` argument of an `int` parameter is the
    /// integer it denotes, and an `i8` argument of a `u8` parameter leaves the
    /// call unexpanded, for the dispatch to refuse (substituted bare, `fid(q:
    /// u8) -> u8 { q }` at `y: i8 == -56` made `fid(y) < 0` `Verified`).
    #[test]
    fn an_inline_argument_is_bound_at_its_parameter_type() {
        let u8_ty = TrustVcType::Uint { width: 8 };
        let i8_ty = TrustVcType::Int { width: 8 };
        let typed_var = |name: &str, ty: &TrustVcType| TrustVcExpr::Var {
            name: name.to_string(),
            ty: ty.clone(),
        };
        let mut bodies: InlineBodyMap = HashMap::new();
        bodies.insert(
            "fid".to_string(),
            (
                vec!["q".to_string()],
                vec![u8_ty.clone()],
                typed_var("q", &u8_ty),
            ),
        );
        bodies.insert(
            "fint".to_string(),
            (
                vec!["q".to_string()],
                vec![TrustVcType::MathInt],
                typed_var("q", &TrustVcType::MathInt),
            ),
        );
        let refused = substitute_inline_calls(&call("fid", vec![typed_var("y", &i8_ty)]), &bodies);
        assert_eq!(
            count_calls(&refused, "fid"),
            1,
            "an i8 argument of a u8 parameter: {refused:?}"
        );
        let lifted = substitute_inline_calls(&call("fint", vec![typed_var("x", &u8_ty)]), &bodies);
        assert!(
            matches!(
                &lifted,
                TrustVcExpr::Cast { from_ty, to_ty: TrustVcType::MathInt, .. } if *from_ty == u8_ty
            ),
            "a u8 argument of an int parameter is lifted: {lifted:?}"
        );
    }

    /// A non-recursive inline chain shorter than the bound is fully expanded:
    /// the depth counter only advances on body expansion, so legitimate inlining
    /// is never truncated.
    #[test]
    fn nonrecursive_chain_fully_expands() {
        let mut bodies: InlineBodyMap = HashMap::new();
        // g(x) == x + 1 ; h(x) == g(x) + 1  -> h(0) == (0 + 1) + 1, no residual.
        bodies.insert(
            "g".to_string(),
            (
                vec!["x".to_string()],
                vec![int_ty()],
                add(var("x"), int_lit(1)),
            ),
        );
        bodies.insert(
            "h".to_string(),
            (
                vec!["x".to_string()],
                vec![int_ty()],
                add(call("g", vec![var("x")]), int_lit(1)),
            ),
        );

        let result = substitute_inline_calls(&call("h", vec![int_lit(0)]), &bodies);

        assert_eq!(count_calls(&result, "g"), 0, "g should be fully inlined");
        assert_eq!(count_calls(&result, "h"), 0, "h should be fully inlined");
    }
}
