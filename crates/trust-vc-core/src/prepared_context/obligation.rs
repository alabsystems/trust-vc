//! Prepared-obligation conversion for typed verification contexts.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::borrow::Cow;

use super::expr_repair::fix_fn_call_return_types;

use crate::encoder::datatype::variant_symbol_name;
use crate::error::TrustVcError;
use crate::expr_depth::validate_expr_depth;
use crate::ir::{CompareOp, MatchPattern, TrustVcExpr, TrustVcType};
use crate::ir_expr_traversal::{fold_expr_children, free_root_names, TrustVcExprFolder};
use crate::ir_lowering::{lower_syn_expr, IntBinding, TypeEnv};
use crate::vc::{ConditionOrigin, ObligationKind, ProofObligation, ProofStepMeta, SolverMode};

struct GroundConstructorMatchSimplifier;

impl TrustVcExprFolder for GroundConstructorMatchSimplifier {
    fn fold_expr(&mut self, expr: TrustVcExpr) -> TrustVcExpr {
        let folded = fold_expr_children(self, expr);
        let (scrutinee, arms, ty) = match folded {
            TrustVcExpr::Match {
                scrutinee,
                arms,
                ty,
            } => (scrutinee, arms, ty),
            other => return other,
        };

        if let Some(variant_name) = ground_constructor_variant_name(&scrutinee) {
            for arm in &arms {
                let Some(bindings) = pattern_bindings_for_constructor(&arm.pattern, &variant_name)
                else {
                    continue;
                };
                // A GUARDED arm does not unconditionally reduce to its body — its guard
                // may be false, so the ground constructor can still fall through to a
                // later arm. Leave the match symbolic rather than fold to this body
                // (folding it would be an unconditional-default false-verify).
                if arm.guard.is_some() {
                    break;
                }
                let free_names = free_root_names(&arm.body);
                if bindings.iter().all(|binding| !free_names.contains(binding)) {
                    return arm.body.clone();
                }
                break;
            }
        }

        TrustVcExpr::Match {
            scrutinee,
            arms,
            ty,
        }
    }
}

fn simplify_ground_constructor_matches(expr: TrustVcExpr) -> TrustVcExpr {
    let mut simplifier = GroundConstructorMatchSimplifier;
    simplifier.fold_expr(expr)
}

fn ground_constructor_variant_name(expr: &TrustVcExpr) -> Option<String> {
    let TrustVcExpr::FnCall {
        name, return_ty, ..
    } = expr
    else {
        return None;
    };
    let TrustVcType::Datatype {
        name: datatype_name,
        variants,
    } = return_ty
    else {
        return None;
    };

    variants
        .iter()
        .find(|variant| variant_symbol_name(datatype_name, &variant.name) == *name)
        .map(|variant| variant.name.clone())
}

fn pattern_bindings_for_constructor(
    pattern: &MatchPattern,
    constructor_variant: &str,
) -> Option<Vec<String>> {
    match pattern {
        MatchPattern::Constructor {
            variant_name,
            bindings,
            ..
        } if variant_name == constructor_variant => Some(bindings.clone()),
        MatchPattern::Struct {
            variant_name,
            fields,
            ..
        } if variant_name == constructor_variant => Some(
            fields
                .iter()
                .filter_map(|field| field.binding.clone())
                .collect(),
        ),
        MatchPattern::Wildcard => Some(Vec::new()),
        MatchPattern::Ident(name) => Some(vec![name.clone()]),
        MatchPattern::Or(patterns) => patterns
            .iter()
            .find_map(|pattern| pattern_bindings_for_constructor(pattern, constructor_variant)),
        _ => None,
    }
}

/// A trigger expression that has been parsed and lowered to typed IR once,
/// at the prepared-context boundary. Consumers read precomputed metadata
/// instead of reparsing trigger strings on every verification pass.
#[derive(Debug, Clone)]
pub(crate) struct PreparedTrigger {
    /// Original trigger source text, preserved for diagnostics.
    pub(crate) source: String,
    /// Lowered typed expression for direct solver encoding.
    pub(crate) expr: TrustVcExpr,
    /// Head function symbol extracted from `expr`, if it is a `FnCall`.
    pub(crate) head_symbol: Option<String>,
}

#[derive(Debug, Clone)]
pub(crate) struct PreparedObligation {
    pub name: String,
    pub kind: ObligationKind,
    pub location: Option<String>,
    pub condition_origin: ConditionOrigin,
    pub bound_vars: Option<Vec<String>>,
    pub trigger_patterns: Option<Vec<Vec<String>>>,
    /// Typed trigger metadata, populated once by `from_legacy()`. Consumers
    /// should prefer this over reparsing `trigger_patterns` strings.
    pub(crate) prepared_triggers: Option<Vec<Vec<PreparedTrigger>>>,
    pub solver_mode: Option<SolverMode>,
    pub is_opaque: bool,
    pub is_inline: bool,
    pub broadcast_group: Option<String>,
    pub condition: String,
    pub expr: TrustVcExpr,
    /// Invariant namespace for InvariantOpen/InvariantClose obligations.
    /// When present, the mask system checks that this namespace is allowed
    /// by the function's `opens_invariants` attribute. Part of #2427 Slice 4.
    pub invariant_namespace: Option<i64>,
    /// Trigger inference mode set by #[auto_trigger] or #[all_triggers].
    /// None means default (conservative). Part of #2461 Slice 3.
    pub trigger_inference_mode: Option<crate::trigger_inference::TriggerInferenceMode>,
    /// Typed guard from broadcast `requires!` clauses. When present, the
    /// encoder publishes `guard ==> body` instead of bare `body`. Part of #2575.
    pub(crate) broadcast_guard: Option<TrustVcExpr>,
    /// Number of raw broadcast guard clauses observed before lowering.
    /// Used by validation to reject lossy guard lowering. Part of #2606.
    pub(crate) raw_broadcast_guard_count: usize,
    /// Proof-step metadata: separates internal scope key from display label.
    /// When present, `display_name()` returns `step_meta.label` instead of `name`.
    /// Part of #2652.
    pub step_meta: Option<ProofStepMeta>,
}

/// Lower trigger pattern strings to typed `PreparedTrigger` groups.
/// Invalid trigger terms are skipped here and rejected at the validation
/// boundary by comparing raw and prepared group arity.
fn lower_trigger_patterns(patterns: &[Vec<String>], env: &TypeEnv) -> Vec<Vec<PreparedTrigger>> {
    patterns
        .iter()
        .map(|group| {
            group
                .iter()
                .filter_map(|source| {
                    let syn_expr =
                        crate::chained_comparisons::parse_expr_str_with_chains(source).ok()?;
                    let expr = lower_syn_expr(&syn_expr, env).ok()?;
                    let head_symbol = head_symbol_from_expr(&expr);
                    Some(PreparedTrigger {
                        source: source.clone(),
                        expr,
                        head_symbol,
                    })
                })
                .collect()
        })
        .collect()
}

fn head_symbol_from_expr(expr: &TrustVcExpr) -> Option<String> {
    match expr {
        TrustVcExpr::FnCall { name, .. } => Some(name.clone()),
        _ => None,
    }
}

fn head_symbol_from_legacy_trigger(trigger: &str) -> Option<String> {
    let expr = syn::parse_str::<syn::Expr>(trigger).ok()?;
    let syn::Expr::Call(call) = expr else {
        return None;
    };
    let syn::Expr::Path(path) = &*call.func else {
        return None;
    };

    Some(
        path.path
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect::<Vec<_>>()
            .join("::"),
    )
}

impl PreparedObligation {
    /// Returns the user-facing display name for this obligation.
    ///
    /// Prefers `step_meta.label` when present, falling back to `name`.
    /// Used in counterexample diagnostics and split localization. Part of #2652.
    pub fn display_name(&self) -> &str {
        self.step_meta.as_ref().map_or(&self.name, |m| &m.label)
    }

    /// All head function symbols from all trigger expressions.
    /// Used by reveal/helper-detection code that needs name discovery.
    pub(crate) fn trigger_head_symbols(&self) -> Vec<Cow<'_, str>> {
        if let Some(ref groups) = self.prepared_triggers {
            return groups
                .iter()
                .flat_map(|group| group.iter())
                .filter_map(|t| t.head_symbol.as_deref().map(Cow::Borrowed))
                .collect();
        }

        self.trigger_patterns
            .as_ref()
            .into_iter()
            .flatten()
            .flatten()
            .filter_map(|trigger| head_symbol_from_legacy_trigger(trigger).map(Cow::Owned))
            .collect()
    }

    /// Symbols from singleton trigger groups eligible for eager ground seeding.
    /// Only groups with exactly one trigger that has a head_symbol qualify.
    #[allow(clippy::indexing_slicing)] // group[0] is only read after filtering singleton trigger groups
    pub(crate) fn eager_seed_symbols(&self) -> Vec<Cow<'_, str>> {
        if let Some(ref groups) = self.prepared_triggers {
            return groups
                .iter()
                .filter(|group| group.len() == 1)
                .filter_map(|group| group[0].head_symbol.as_deref().map(Cow::Borrowed))
                .collect();
        }

        self.trigger_patterns
            .as_ref()
            .into_iter()
            .flatten()
            .filter(|group| group.len() == 1)
            .filter_map(|group| head_symbol_from_legacy_trigger(&group[0]).map(Cow::Owned))
            .collect()
    }

    /// Singleton function-call trigger patterns eligible for eager ground
    /// seeding, including their argument shape. This lets the ground pool
    /// instantiate triggers such as `f(a + b)` from a concrete `f(2 + 3)` call.
    pub(crate) fn eager_seed_trigger_patterns(&self) -> Vec<(String, Vec<TrustVcExpr>)> {
        self.prepared_triggers
            .as_ref()
            .into_iter()
            .flatten()
            .filter(|group| group.len() == 1)
            .filter_map(|group| match &group[0].expr {
                TrustVcExpr::FnCall { name, args, .. } => Some((name.clone(), args.clone())),
                _ => None,
            })
            .collect()
    }

    pub(super) fn from_legacy(
        obligation: &ProofObligation,
        env: &TypeEnv,
    ) -> Result<Self, TrustVcError> {
        // Reveal obligations are metadata — no condition to parse.
        // InvariantOpen/InvariantClose use marker condition strings
        // (__trust_vc_invariant_open/close) that are not parseable Rust
        // expressions. In the encoder test path, these carry their predicate
        // via direct PreparedObligation construction. In the macro path,
        // the predicate is carried by separate assume/assert obligations
        // within the invariant scope body.
        if matches!(
            obligation.kind,
            ObligationKind::Reveal
                | ObligationKind::Hide
                | ObligationKind::BroadcastUse
                | ObligationKind::InvariantOpen
                | ObligationKind::InvariantClose
        ) {
            return Ok(Self {
                name: obligation.name.clone(),
                kind: obligation.kind,
                location: obligation.location.clone(),
                condition_origin: obligation.condition_origin,
                bound_vars: None,
                trigger_patterns: None,
                prepared_triggers: None,
                solver_mode: None,
                is_opaque: false,
                is_inline: false,
                // Preserved for the `BroadcastUse` marker: the activated group
                // name is read here by the position-aware broadcast gate.
                broadcast_group: obligation.broadcast_group.clone(),
                condition: obligation.condition.clone(),
                expr: TrustVcExpr::BoolLit(true),
                invariant_namespace: obligation.invariant_namespace,
                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: obligation.step_meta.clone(),
            });
        }

        let loc = obligation
            .location
            .as_deref()
            .map(|location| format!(" at {location}"))
            .unwrap_or_default();

        let expr = if let Some(typed_expr) = obligation.typed_expr.as_ref() {
            validate_expr_depth(typed_expr, "prepared-context typed expression").map_err(
                |err| TrustVcError::Encoding {
                    context: "prepare obligation",
                    detail: format!(
                        "Failed to validate typed obligation '{}'{}: {}",
                        obligation.name, loc, err
                    ),
                },
            )?;
            fix_fn_call_return_types(typed_expr.clone(), env)
        } else {
            // Fast path: check thread-local cache for pre-built TrustVcExpr
            // (from proc macro codegen, Phase 5 Step 3b). Skip string parse+lower.
            let pre_built = crate::obligation_collection::take_pre_built_expr(
                &obligation.name,
                &obligation.condition,
            );
            if let Some(pre_built) = pre_built {
                validate_expr_depth(&pre_built, "prepared-context cached expression repair")
                    .map_err(|err| TrustVcError::Encoding {
                        context: "prepare obligation",
                        detail: format!(
                            "Failed to validate cached obligation '{}'{}: {}",
                            obligation.name, loc, err
                        ),
                    })?;
                // Fix FnCall return types: expr_codegen.rs hardcodes a default
                // return type for function calls because proc macros lack type info.
                // Correct them using the TypeEnv which has helper function return
                // types registered. Fixes #2222.
                fix_fn_call_return_types(pre_built, env)
            } else {
                let syn_expr: syn::Expr =
                    crate::chained_comparisons::parse_expr_str_with_chains(&obligation.condition)
                        .map_err(|err| TrustVcError::Encoding {
                        context: "prepare obligation",
                        detail: format!(
                            "Failed to parse obligation '{}'{}: {}",
                            obligation.name, loc, err
                        ),
                    })?;

                // The expected-result marker is a synthetic source-catalog
                // implementation detail, not a user-callable builtin. Grant it
                // only on a scoped clone when the originating obligation carries
                // the crate-private provenance bit.
                let scoped_env = obligation
                    .source_catalog_math_int_context
                    .then(|| env.clone().with_source_catalog_math_int_marker());
                let lowering_env = scoped_env.as_ref().unwrap_or(env);

                lower_syn_expr(&syn_expr, lowering_env).map_err(|err| TrustVcError::Encoding {
                    context: "prepare obligation",
                    detail: format!(
                        "Failed to lower obligation '{}'{}: {}",
                        obligation.name, loc, err
                    ),
                })?
            }
        };
        let expr = simplify_ground_constructor_matches(expr);
        // SPEC ARITHMETIC IS MATHEMATICAL (see `crate::spec_arith`). A
        // `requires` clause is spec code in Verus, so its `+`/`-`/`*` are the
        // operations on integers — and it has to read that way for BOTH roles
        // of one call, the caller's `__call_requires_*` discharge and the
        // callee's `precondition` assumption. This is the single boundary where
        // both are built, which is why the rewrite lives here rather than at
        // either encode site.
        let expr = if crate::spec_arith::is_requires_channel(obligation.kind, &obligation.name) {
            crate::spec_arith::to_math_int_spec_arith(&expr)
        } else {
            expr
        };
        if obligation.kind == ObligationKind::BroadcastAssume
            && obligation.name.starts_with("__body_axiom_")
        {
            check_body_axiom_result_type(&expr).map_err(|detail| TrustVcError::Encoding {
                context: "prepare obligation",
                detail: format!(
                    "Failed to admit definition '{}'{}: {}",
                    obligation.name, loc, detail
                ),
            })?;
        }
        if obligation.name == "return_value"
            && matches!(
                obligation.kind,
                ObligationKind::Assume | ObligationKind::PostLoopAssume
            )
        {
            check_return_value_binding(&expr).map_err(|detail| TrustVcError::Encoding {
                context: "prepare obligation",
                detail: format!("Failed to bind the return value{}: {}", loc, detail),
            })?;
        }
        let expr = if states_lane_identity(obligation.kind, &obligation.name) {
            crate::float_identity::read_equations_as_identity(expr)
        } else {
            expr
        };

        let prepared_triggers = obligation
            .trigger_patterns
            .as_ref()
            .map(|patterns| lower_trigger_patterns(patterns, env));

        let raw_broadcast_guard_count = obligation.broadcast_guard.as_ref().map_or(0, Vec::len);
        // Lower broadcast guard clauses (#2575): parse + lower each clause,
        // then conjoin into a single typed guard expression. Fail closed on
        // any clause loss so validation can reject the dropped-guard case.
        let broadcast_guard = obligation.broadcast_guard.as_ref().and_then(|clauses| {
            let exprs: Option<Vec<TrustVcExpr>> = clauses
                .iter()
                .map(|clause| {
                    let syn_expr =
                        crate::chained_comparisons::parse_expr_str_with_chains(&clause.condition)
                            .ok()?;
                    lower_syn_expr(&syn_expr, env).ok()
                })
                .collect();
            let exprs = exprs?;
            match exprs.len() {
                0 => None,
                1 => exprs.into_iter().next(),
                _ => {
                    // Right-fold into nested And nodes: a && (b && c)
                    let mut iter = exprs.into_iter().rev();
                    let mut acc = iter.next()?;
                    for expr in iter {
                        acc = TrustVcExpr::Logic {
                            op: crate::ir_expr::LogicOp::And,
                            left: Box::new(expr),
                            right: Box::new(acc),
                        };
                    }
                    Some(acc)
                }
            }
        });

        Ok(Self {
            name: obligation.name.clone(),
            kind: obligation.kind,
            location: obligation.location.clone(),
            condition_origin: obligation.condition_origin,
            bound_vars: obligation.bound_vars.clone(),
            trigger_patterns: obligation.trigger_patterns.clone(),
            prepared_triggers,
            solver_mode: obligation.solver_mode,
            is_opaque: obligation.is_opaque,
            is_inline: obligation.is_inline,
            broadcast_group: obligation.broadcast_group.clone(),
            condition: obligation.condition.clone(),
            expr,
            invariant_namespace: obligation.invariant_namespace,
            trigger_inference_mode: obligation.trigger_inference_mode,
            broadcast_guard,
            raw_broadcast_guard_count,
            step_meta: obligation.step_meta.clone(),
        })
    }
}

/// A function's defining axiom `f(params) == body` (under an optional
/// precondition guard) is admitted only when `body` is a value of `f`'s
/// declared result type — for a fixed-width result `T`, a value of type `T`
/// (or an untyped literal that fits it; `ir_lowering::int_binding`).
///
/// The axiom is universally quantified, so a body of another integer type
/// makes it INCONSISTENT wherever that value leaves `T`: `fn mixsum(x: u8, y:
/// i16) -> u8 { x + y }` (the integer -1 at `(0, -1)`) or `fn m() -> u8 { -1 }`
/// equate a bit-vector with a value it cannot hold, and every VC mentioning
/// the function came back `Verified` (`mixsum(0, -1) == 65535`, `> 1000`).
/// Rust and Verus reject such a function; so does this. A `nat` result holds
/// only non-negative values and is checked the same way (an unsigned or `nat`
/// body, or a literal it holds): `spec fn gneg() -> nat { -1 }` verified
/// `gneg() == -1` and refuted `gneg() >= 0`. An `int` result holds every
/// integer the body denotes and is not checked here.
fn check_body_axiom_result_type(expr: &TrustVcExpr) -> Result<(), String> {
    let equation = match expr {
        TrustVcExpr::Implies { conclusion, .. } => conclusion.as_ref(),
        other => other,
    };
    let TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left,
        right,
    } = equation
    else {
        return Ok(());
    };
    let (name, return_ty, body) = match (left.as_ref(), right.as_ref()) {
        (
            TrustVcExpr::FnCall {
                name, return_ty, ..
            },
            body,
        ) => (name, return_ty, body),
        (
            body,
            TrustVcExpr::FnCall {
                name, return_ty, ..
            },
        ) => (name, return_ty, body),
        _ => return Ok(()),
    };
    if !crate::ir_lowering::is_integer_type(return_ty)
        && crate::ir_lowering::type_holds_an_integer(return_ty)
    {
        // A COMPOSITE result holds the body's value at every integer position
        // (`spec fn as_i8(s: Seq<u8>) -> Seq<i8> { s }` equated a `Seq<i8>`
        // with the `Seq<u8>`'s bits, so `as_i8(s)[0] == -56` for `s[0] ==
        // 200` was `Verified`).
        let body_ty = crate::ir_lowering::infer_expr_type(body);
        if !crate::ir_lowering::integer_positions_agree(&body_ty, return_ty) {
            return Err(format!(
                "`{name}` is declared to return `{}`, but its body is a value of type `{}`",
                return_ty.to_type_string(),
                body_ty.to_type_string()
            ));
        }
        return Ok(());
    }
    if !crate::ir_lowering::is_fixed_width_int(return_ty) && *return_ty != TrustVcType::Nat {
        return Ok(());
    }
    match crate::ir_lowering::int_binding(body, return_ty) {
        IntBinding::Mismatch(body_ty) => Err(format!(
            "`{name}` is declared to return `{}`, but its body is a value of type `{}`: the \
             definition would equate a `{}` with values it cannot hold",
            return_ty.to_type_string(),
            body_ty.to_type_string(),
            return_ty.to_type_string()
        )),
        IntBinding::Same
        | IntBinding::Literal(_)
        | IntBinding::LiftToInt
        | IntBinding::NotInteger => Ok(()),
    }
}

/// An exec function's return binding `result == value` (one per return path,
/// or-ed) is admitted only when each `value` is a value of `result`'s declared
/// type (`ir_lowering::int_binding`). It is ASSUMED, so a value the type cannot
/// hold constrains the inputs instead of binding `result`: with `-> u8` and a
/// body `if c { -1 } else { 0 }`, `result == -1` is unsatisfiable, the
/// assumption forces `!c`, and `ensures c ==> result == 7` came back
/// `Verified`; `x + y` (`y: i16`) did the same for `y == -1`. Rust rejects
/// such a function; so does this.
/// Whether the obligation is an equation the lane writes to say two terms are
/// one value, which must not be read as IEEE equality over floats (see
/// [`crate::float_identity`]): the binding of the return value, of a
/// `closure!()` result to the closure body, and of a loop-modified local to its
/// value at loop entry (`{invariant}__entry_{var}`), the definition of a
/// function by its body, and of a spec function alias by the function it names.
fn states_lane_identity(kind: ObligationKind, name: &str) -> bool {
    match kind {
        ObligationKind::Assume => {
            name == "return_value" || name == "closure_def_side_result" || name.contains("__entry_")
        }
        ObligationKind::PostLoopAssume => name == "return_value",
        ObligationKind::BroadcastAssume => {
            name.starts_with("__body_axiom_") || name.starts_with("__alias_axiom_")
        }
        _ => false,
    }
}

fn check_return_value_binding(expr: &TrustVcExpr) -> Result<(), String> {
    match expr {
        TrustVcExpr::Logic {
            op: crate::ir_expr::LogicOp::Or,
            left,
            right,
        } => {
            check_return_value_binding(left)?;
            check_return_value_binding(right)
        }
        TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left,
            right,
        } => {
            let TrustVcExpr::Var { name, ty } = left.as_ref() else {
                return Ok(());
            };
            match crate::ir_lowering::int_binding(right, ty) {
                IntBinding::Mismatch(value_ty) => Err(format!(
                    "`{name}` has type `{}`, but the function returns a value of type `{}`",
                    ty.to_type_string(),
                    value_ty.to_type_string()
                )),
                IntBinding::Same
                | IntBinding::Literal(_)
                | IntBinding::LiftToInt
                | IntBinding::NotInteger => Ok(()),
            }
        }
        _ => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::MatchArm;
    use crate::ir_lowering::TypeEnv;
    use crate::vc::ObligationKind;

    fn result_i32_ty() -> TrustVcType {
        TrustVcType::parse_or_opaque("Result<i32, i32>")
    }

    fn result_constructor(variant: &str, value: i128) -> TrustVcExpr {
        let return_ty = result_i32_ty();
        let TrustVcType::Datatype {
            name: datatype_name,
            ..
        } = &return_ty
        else {
            unreachable!("Result should parse as a datatype")
        };
        TrustVcExpr::FnCall {
            name: variant_symbol_name(datatype_name, variant),
            args: vec![TrustVcExpr::IntLit {
                value,
                ty: TrustVcType::Int { width: 32 },
            }],
            return_ty,
        }
    }

    #[test]
    fn simplifies_ground_constructor_match_when_binding_is_unused() {
        let expr = TrustVcExpr::Match {
            scrutinee: Box::new(result_constructor("Ok", 1)),
            arms: vec![
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "Ok".to_string(),
                        bindings: vec!["_value".to_string()],
                        has_rest: false,
                    },
                    TrustVcExpr::BoolLit(false),
                ),
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "Err".to_string(),
                        bindings: vec!["_error".to_string()],
                        has_rest: false,
                    },
                    TrustVcExpr::BoolLit(true),
                ),
            ],
            ty: TrustVcType::Bool,
        };

        assert_eq!(
            simplify_ground_constructor_matches(expr),
            TrustVcExpr::BoolLit(false)
        );
    }

    #[test]
    fn keeps_ground_constructor_match_when_selected_arm_uses_binding() {
        let expr = TrustVcExpr::Match {
            scrutinee: Box::new(result_constructor("Ok", 1)),
            arms: vec![
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "Ok".to_string(),
                        bindings: vec!["value".to_string()],
                        has_rest: false,
                    },
                    TrustVcExpr::Compare {
                        op: CompareOp::Eq,
                        left: Box::new(TrustVcExpr::Var {
                            name: "value".to_string(),
                            ty: TrustVcType::Int { width: 32 },
                        }),
                        right: Box::new(TrustVcExpr::IntLit {
                            value: 1,
                            ty: TrustVcType::Int { width: 32 },
                        }),
                    },
                ),
                MatchArm::new(
                    MatchPattern::Constructor {
                        variant_name: "Err".to_string(),
                        bindings: vec!["_error".to_string()],
                        has_rest: false,
                    },
                    TrustVcExpr::BoolLit(false),
                ),
            ],
            ty: TrustVcType::Bool,
        };

        assert!(matches!(
            simplify_ground_constructor_matches(expr),
            TrustVcExpr::Match { .. }
        ));
    }

    #[test]
    fn prepares_result_wrong_variant_assertion_to_plain_false() -> Result<(), TrustVcError> {
        let obligation = ProofObligation::new(
            "assertion_0",
            "match Result::<i32, i32>::Ok(1i32) { \
                Ok(_value) => false, \
                Err(_error_code) => true, \
            }",
            ObligationKind::Assert,
        );
        let prepared = PreparedObligation::from_legacy(&obligation, &TypeEnv::new())?;

        assert_eq!(prepared.expr, TrustVcExpr::BoolLit(false));
        Ok(())
    }
}
