//! Typed broadcast encoding for the verification pipeline.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::Term;

use crate::encoder::ground_pool::{GroundAxiom, GroundTrigger};
use crate::encoder::AYEncoder;
use crate::error::TrustVcResult;
use crate::ir::TrustVcExpr;
#[cfg(feature = "native-seq")]
use crate::ir::{CollectionOp, TrustVcType};
#[cfg(feature = "native-seq")]
use crate::ir_expr_traversal::{fold_expr_children, TrustVcExprFolder};
use crate::prepared_context::PreparedObligation;

use super::encoding_error;

#[cfg(feature = "native-seq")]
const NATIVE_SEQ_SMALL_INDEX_GROUND_LIMIT: i64 = 4;

/// Maximum goal-side IR-level trigger-match instantiations asserted per
/// dead-trigger broadcast lemma (on top of the fixed type-boundary battery).
const INTERPRETED_TRIGGER_GOAL_MATCH_CAP: usize = 16;

/// True when a trigger expression is HEADED by an interpreted arithmetic/BV
/// operation. ay's E-matcher indexes only uninterpreted function applications,
/// so such a trigger can never fire inside ay — the quantifier's trigger is
/// structurally DEAD regardless of which ground terms the goal contains
/// (cross-sort dead trigger; e.g. `x * x` lowers to `bvmul`, an interpreted
/// op the matcher never indexes).
fn interpreted_arith_headed(expr: &TrustVcExpr) -> bool {
    matches!(
        expr,
        TrustVcExpr::Arith { .. }
            | TrustVcExpr::Neg(_)
            | TrustVcExpr::SpecialArith { .. }
            | TrustVcExpr::WrappingArith { .. }
    )
}

/// Classifies a broadcast obligation as an interpreted-op DEAD-TRIGGER lemma.
///
/// Returns `Some(all trigger pattern exprs)` iff the lemma has bound variables,
/// explicit prepared triggers, and EVERY trigger group contains at least one
/// interpreted-arith-headed term — an E-matching group only fires when ALL its
/// terms match, so one unmatchable term kills the group, and when every group
/// is dead the live `forall` can never be instantiated by ay. Any live
/// (fully-uninterpreted) group keeps the lemma on the live-forall path.
///
/// Conservative fallbacks (return `None`, keeping the existing live-forall
/// path): missing/empty prepared triggers, an empty group, or a prepared view
/// that lost terms relative to the raw trigger strings during lowering.
pub(in crate::encoder) fn interpreted_dead_trigger_patterns(
    obligation: &PreparedObligation,
) -> Option<Vec<TrustVcExpr>> {
    let bound_names = obligation.bound_vars.as_ref()?;
    if bound_names.is_empty() {
        return None;
    }
    let groups = obligation.prepared_triggers.as_ref()?;
    if groups.is_empty() || groups.iter().any(|group| group.is_empty()) {
        return None;
    }
    if let Some(raw_groups) = obligation.trigger_patterns.as_ref() {
        let arity_matches = raw_groups.len() == groups.len()
            && raw_groups
                .iter()
                .zip(groups)
                .all(|(raw_group, group)| raw_group.len() == group.len());
        if !arity_matches {
            return None;
        }
    }
    if !groups.iter().all(|group| {
        group
            .iter()
            .any(|trigger| interpreted_arith_headed(&trigger.expr))
    }) {
        return None;
    }
    Some(
        groups
            .iter()
            .flatten()
            .map(|trigger| trigger.expr.clone())
            .collect(),
    )
}

/// Collects deduplicated bound-variable binding tuples by matching each dead
/// trigger pattern against every subexpression of the candidate source
/// expressions (IR-level stand-in for the E-matching ay cannot do). A tuple is
/// kept only when every binding's free root names are declared encoder
/// variables — i.e. the instance is ground in the current scope (a goal
/// quantifier's binder is not, so its occurrences are skipped).
///
/// Groundness is NOT sortedness. A tuple that passes the scope check can still
/// bind a `u8` bound variable to a `u64` expression, because `match_trigger_expr`
/// compares operators and names but never types. The caller must therefore pass
/// every tuple through `witness_sort::instantiate_bound_vars_in_sort` before
/// substituting; see `replay_interpreted_trigger_broadcast_ground`.
fn collect_interpreted_trigger_binding_tuples(
    sources: &[TrustVcExpr],
    patterns: &[TrustVcExpr],
    bound_vars: &[String],
    variables: &std::collections::HashMap<String, Term>,
    cap: usize,
) -> Vec<Vec<TrustVcExpr>> {
    struct TriggerMatchCollector<'a> {
        patterns: &'a [TrustVcExpr],
        bound_vars: &'a [String],
        variables: &'a std::collections::HashMap<String, Term>,
        tuples: Vec<Vec<TrustVcExpr>>,
        cap: usize,
    }

    impl crate::ir_expr_traversal::TrustVcExprVisitor for TriggerMatchCollector<'_> {
        fn visit_expr(&mut self, expr: &TrustVcExpr) {
            if self.tuples.len() >= self.cap {
                return;
            }
            for pattern in self.patterns {
                let Some(bound_exprs) = crate::encoder::ground_pool::match_trigger_args(
                    std::slice::from_ref(pattern),
                    std::slice::from_ref(expr),
                    self.bound_vars,
                ) else {
                    continue;
                };
                let all_in_scope = bound_exprs.iter().all(|binding| {
                    crate::ir_expr_traversal::free_root_names(binding)
                        .iter()
                        .all(|name| self.variables.contains_key(name))
                });
                if all_in_scope && !self.tuples.contains(&bound_exprs) {
                    self.tuples.push(bound_exprs);
                }
            }
            crate::ir_expr_traversal::walk_expr(self, expr);
        }
    }

    let mut collector = TriggerMatchCollector {
        patterns,
        bound_vars,
        variables,
        tuples: Vec::new(),
        cap,
    };
    for source in sources {
        crate::ir_expr_traversal::TrustVcExprVisitor::visit_expr(&mut collector, source);
    }
    collector.tuples
}

fn expr_contains_type_param(expr: &crate::ir::TrustVcExpr) -> bool {
    if matches!(
        crate::ir_lowering::infer_expr_type(expr),
        crate::ir::TrustVcType::TypeParam(_)
    ) {
        return true;
    }

    struct Visitor {
        found: bool,
    }

    impl crate::ir_expr_traversal::TrustVcExprVisitor for Visitor {
        fn visit_expr(&mut self, expr: &crate::ir::TrustVcExpr) {
            if self.found {
                return;
            }
            if matches!(
                crate::ir_lowering::infer_expr_type(expr),
                crate::ir::TrustVcType::TypeParam(_)
            ) {
                self.found = true;
                return;
            }
            crate::ir_expr_traversal::walk_expr(self, expr);
        }
    }

    let mut visitor = Visitor { found: false };
    crate::ir_expr_traversal::TrustVcExprVisitor::visit_expr(&mut visitor, expr);
    visitor.found
}

#[cfg(feature = "native-seq")]
fn is_native_seq_singleton_index_trigger(
    obligation: &PreparedObligation,
    bound_name: &str,
) -> bool {
    obligation
        .prepared_triggers
        .as_ref()
        .into_iter()
        .flatten()
        .filter(|group| group.len() == 1)
        .any(|group| match &group[0].expr {
            TrustVcExpr::CollectionOp {
                op: CollectionOp::Get,
                receiver,
                args,
                ..
            } => {
                matches!(
                    crate::ir_lowering::infer_expr_type(receiver),
                    TrustVcType::Seq(_) | TrustVcType::Array(_, _)
                ) && matches!(
                    args.as_slice(),
                    [TrustVcExpr::Var { name, .. }] if name == bound_name
                )
            }
            TrustVcExpr::Index {
                receiver, index, ..
            } => {
                matches!(
                    crate::ir_lowering::infer_expr_type(receiver),
                    TrustVcType::Seq(_) | TrustVcType::Array(_, _)
                ) && matches!(
                    index.as_ref(),
                    TrustVcExpr::Var { name, .. } if name == bound_name
                )
            }
            _ => false,
        })
}

#[cfg(feature = "native-seq")]
fn grounded_int_literal_fits(value: i128, ty: &TrustVcType) -> bool {
    match ty {
        TrustVcType::Int { width } => crate::encoder::types::fits_in_signed_bv(value, *width),
        TrustVcType::Uint { width } => {
            if value < 0 {
                return false;
            }
            if *width >= 128 {
                return true;
            }
            (value as u128) < (1u128 << width)
        }
        TrustVcType::MathInt => true,
        TrustVcType::Nat => value >= 0,
        _ => false,
    }
}

#[cfg(feature = "native-seq")]
fn fold_grounded_concrete_ints(expr: TrustVcExpr) -> TrustVcExpr {
    struct GroundedIntFolder;

    impl TrustVcExprFolder for GroundedIntFolder {
        fn fold_expr(&mut self, expr: TrustVcExpr) -> TrustVcExpr {
            let folded = fold_expr_children(self, expr);
            let ty = crate::ir_lowering::infer_expr_type(&folded);
            if let Some(value) = crate::encoder::AYEncoder::try_reduce_to_int(&folded) {
                if grounded_int_literal_fits(value, &ty) {
                    return TrustVcExpr::IntLit { value, ty };
                }
            }
            folded
        }
    }

    GroundedIntFolder.fold_expr(expr)
}

impl AYEncoder {
    fn encode_broadcast_trigger_groups(
        &mut self,
        obligation: &PreparedObligation,
    ) -> TrustVcResult<Vec<Vec<Term>>> {
        let mut parsed_groups: Vec<Vec<Term>> = Vec::new();

        if let Some(ref raw_groups) = obligation.trigger_patterns {
            for (group_index, raw_group) in raw_groups.iter().enumerate() {
                let prepared_group = obligation
                    .prepared_triggers
                    .as_ref()
                    .and_then(|groups| groups.get(group_index));
                let use_prepared_group =
                    prepared_group.is_some_and(|group| group.len() == raw_group.len());

                let mut group_terms: Vec<Term> = Vec::new();
                if let (true, Some(prepared_group)) = (use_prepared_group, prepared_group) {
                    for trigger in prepared_group {
                        group_terms.push(self.encode_trigger_expr_typed(&trigger.expr).map_err(
                            |e| {
                                encoding_error(
                                    "encode typed broadcast",
                                    format!(
                                    "Failed to encode prepared trigger '{}' for broadcast '{}': {}",
                                    trigger.source, obligation.name, e
                                ),
                                )
                            },
                        )?);
                    }
                } else {
                    for expr in raw_group {
                        group_terms.push(self.encode_trigger_typed(expr).map_err(|e| {
                            encoding_error(
                                "encode typed broadcast",
                                format!(
                                    "Failed to encode trigger '{}' for broadcast '{}': {}",
                                    expr, obligation.name, e
                                ),
                            )
                        })?);
                    }
                }

                if !group_terms.is_empty() {
                    parsed_groups.push(group_terms);
                }
            }

            return Ok(parsed_groups);
        }

        if let Some(ref prepared_groups) = obligation.prepared_triggers {
            for group in prepared_groups {
                let mut group_terms: Vec<Term> = Vec::new();
                for trigger in group {
                    group_terms.push(self.encode_trigger_expr_typed(&trigger.expr).map_err(
                        |e| {
                            encoding_error(
                                "encode typed broadcast",
                                format!(
                                    "Failed to encode prepared trigger '{}' for broadcast '{}': {}",
                                    trigger.source, obligation.name, e
                                ),
                            )
                        },
                    )?);
                }
                if !group_terms.is_empty() {
                    parsed_groups.push(group_terms);
                }
            }
        }

        Ok(parsed_groups)
    }

    #[cfg(feature = "native-seq")]
    fn instantiate_small_native_seq_index_cases(
        &mut self,
        obligation: &PreparedObligation,
    ) -> TrustVcResult<()> {
        let Some([bound_name]) = obligation.bound_vars.as_deref() else {
            return Ok(());
        };
        if !is_native_seq_singleton_index_trigger(obligation, bound_name) {
            return Ok(());
        }

        // ay-dpll currently returns QuantifierUnhandled for seq.nth triggers in
        // otherwise-simple singleton-index broadcasts. Seed a few concrete
        // instances directly so native-seq inherits the same small-index
        // coverage that the array path already relies on. Part of #2697.
        let grounded_expr = if let Some(ref guard_expr) = obligation.broadcast_guard {
            TrustVcExpr::Implies {
                premise: Box::new(guard_expr.clone()),
                conclusion: Box::new(obligation.expr.clone()),
            }
        } else {
            obligation.expr.clone()
        };

        for i in 0..NATIVE_SEQ_SMALL_INDEX_GROUND_LIMIT {
            let concrete_idx_ty = self
                .var_types
                .get(bound_name.as_str())
                .cloned()
                .unwrap_or(TrustVcType::MathInt);
            let concrete_idx = TrustVcExpr::IntLit {
                value: i128::from(i),
                ty: concrete_idx_ty,
            };
            // Same shared sort gate as every other witness source: an index
            // literal outside the bound variable's sort is not an instantiation.
            // (In practice `concrete_idx` is built AT the bound variable's own
            // type and is small, so this passes — the point is that no
            // substitution site is exempt from the check.)
            let Some(substituted) = crate::encoder::witness_sort::instantiate_bound_vars_in_sort(
                &grounded_expr,
                std::slice::from_ref(bound_name),
                std::slice::from_ref(&concrete_idx),
                &self.var_types,
            ) else {
                continue;
            };
            let grounded_instance = fold_grounded_concrete_ints(substituted);
            let instance =
                crate::encoder::with_flag_unwind_safe!(self.state.in_assumption_context, true, {
                    self.resolve_condition_typed(&grounded_instance)
                })
                .map_err(|e| {
                    encoding_error(
                        "encode typed broadcast",
                        format!(
                            "Failed to encode native-seq ground instance {} for broadcast '{}': {}",
                            i, obligation.name, e
                        ),
                    )
                })?;
            self.solver.try_assert_term(instance).map_err(|e| {
                encoding_error(
                    "encode typed broadcast",
                    format!(
                        "Failed to assert native-seq ground instance {} for broadcast '{}': {}",
                        i, obligation.name, e
                    ),
                )
            })?;
        }

        Ok(())
    }

    /// Ground-only replay for an interpreted-op DEAD-TRIGGER broadcast lemma.
    ///
    /// Asserts ground instances of `guard ==> body` at:
    /// 1. the fixed type-boundary battery for the bound variables (reusing
    ///    `build_premise_ground_instances` with no model witnesses — e.g.
    ///    `-1, 0, 1, MIN, MAX` for a signed bound var, plus literal constants
    ///    from the lemma itself). This keeps the broadcast-vacuity guard's
    ///    teeth: a lemma contradictory at a boundary point (`x*x < 0` at 0,
    ///    `x+1 == x` anywhere) still poisons the context, so the vacuous-truth
    ///    precheck / probe still classifies it — as pure GROUND facts, robust
    ///    to any ay quantifier-handling regime.
    /// 2. IR-level matches of the trigger patterns against the goal/assumption
    ///    expressions (`broadcast_ground_replay_sources`), the trust-vc-side
    ///    stand-in for the E-matching ay cannot perform on interpreted heads.
    ///
    /// Finally records the lemma as a `BroadcastForallPremise` so (a) the
    /// broadcast-vacuity probe machinery stays active and (b) candidate SAT
    /// models are re-validated against the lemma instantiated at the model's
    /// own witnesses (`revalidate_broadcast_premises_against_model`) —
    /// recovering, at exactly the witness a model chooses, the proof power the
    /// un-asserted `forall` would have provided.
    ///
    /// SOUNDNESS: every asserted term is a universal instantiation of a
    /// conformance-checked lemma; omitting the `forall` itself can only lose
    /// completeness (fail-closed).
    ///
    /// That first clause used to read "— always sound to assert", and that was
    /// FALSE. An instantiation is only sound when the substituted witness is a
    /// value of the bound variable's sort, and source (2) supplies arbitrary
    /// goal subexpressions of arbitrary type. A `u8`-bound lemma matched against
    /// a `u64` product asserted `w <= 255` for an arbitrary `u64` — consistent,
    /// unjustified, and a cardinal false verify (regression:
    /// `broadcast_goal_witness_sort_soundness`). Both sources now pass through
    /// `witness_sort::instantiate_bound_vars_in_sort`, which declines any
    /// out-of-sort tuple.
    fn replay_interpreted_trigger_broadcast_ground(
        &mut self,
        obligation: &PreparedObligation,
        trigger_patterns: &[TrustVcExpr],
    ) -> TrustVcResult<()> {
        let bound_names = obligation.bound_vars.clone().unwrap_or_default();
        let premise = crate::encoder::encoder_state::BroadcastForallPremise {
            bound_vars: bound_names.clone(),
            body: obligation.expr.clone(),
            guard: obligation.broadcast_guard.clone(),
        };

        // (1) Fixed type-boundary battery (no model witnesses yet).
        let mut instances = self.build_premise_ground_instances(&premise, &[], &[true, false]);

        // (2) Goal-side IR-level trigger matches.
        let binding_tuples = collect_interpreted_trigger_binding_tuples(
            &self.state.broadcast_ground_replay_sources,
            trigger_patterns,
            &bound_names,
            &self.variables,
            INTERPRETED_TRIGGER_GOAL_MATCH_CAP,
        );
        let full = if let Some(ref guard_expr) = obligation.broadcast_guard {
            TrustVcExpr::Implies {
                premise: Box::new(guard_expr.clone()),
                conclusion: Box::new(obligation.expr.clone()),
            }
        } else {
            obligation.expr.clone()
        };
        for tuple in binding_tuples {
            // SOUNDNESS (cardinal, sibling of the model-witness defect). A
            // trigger match against the goal binds a bound variable to an
            // arbitrary goal SUBEXPRESSION, whose type need not be the bound
            // variable's. Substituting a wider-typed expression does not produce
            // a visibly false fact — it produces a consistent, unjustified one:
            // `forall|x: u8| x <= 255u8` matched against `w * w` for a `u64 w`
            // asserted `w <= 255`, so `fn f(w: u64) -> u64 { w }` verified
            // `ensures result <= 255u64`. The vacuity guard cannot see it
            // (nothing is contradictory). Route every tuple through the shared
            // sort gate; an out-of-sort tuple is DECLINED, not substituted.
            if let Some(instance) = crate::encoder::witness_sort::instantiate_bound_vars_in_sort(
                &full,
                &bound_names,
                &tuple,
                &self.var_types,
            ) {
                instances.push(instance);
            }
        }

        for instance in instances {
            let normalized = crate::encoder::ir_encoder::normalize::normalize_int_expr(&instance);
            let term =
                crate::encoder::with_flag_unwind_safe!(self.state.in_assumption_context, true, {
                    self.resolve_condition_typed(&normalized)
                })
                .map_err(|e| {
                    encoding_error(
                        "encode typed broadcast",
                        format!(
                            "Failed to encode interpreted-trigger ground instance for \
                             broadcast '{}': {}",
                            obligation.name, e
                        ),
                    )
                })?;
            self.solver.try_assert_term(term).map_err(|e| {
                encoding_error(
                    "encode typed broadcast",
                    format!(
                        "Failed to assert interpreted-trigger ground instance for \
                         broadcast '{}': {}",
                        obligation.name, e
                    ),
                )
            })?;
        }

        // Premise recording: keeps the vacuity probe + model revalidation
        // active for this lemma even though no live `forall` was asserted.
        if !bound_names.is_empty() {
            self.state.broadcast_premises.push(premise);
        }
        self.state.interpreted_trigger_ground_replays += 1;
        Ok(())
    }

    /// Adds a broadcast assumption from a PreparedObligation.
    ///
    /// Encodes the broadcast body in assumption context (forall preserved, not
    /// Skolemized), then wraps in a quantifier with optional triggers.
    /// Validates that all `bound_vars` exist in scope - missing variables
    /// produce a hard error (not a silent filter).
    pub(in crate::encoder) fn add_typed_broadcast(
        &mut self,
        obligation: &PreparedObligation,
        all_var_terms: &[Term],
    ) -> TrustVcResult<()> {
        // BINDER CAPTURE (CARDINAL). This function encodes the axiom body FIRST,
        // with every bound variable resolved as an ordinary top-level term out of
        // `self.variables`, and only closes the `forall` over those terms further
        // down. During the encode there is therefore no live binder for the
        // encoder to see (`real_quantifier_depth` is 0), yet a binder IS coming.
        // Any encoder helper that hoists a derived fact to the solver top level
        // with `try_assert_term` would have that fact's variables captured by the
        // `forall` built below — the fact stays at the top level while the
        // occurrence inside the axiom becomes bound, so the axiom silently loses
        // its dependence on the bound variable. Measured instance: the spec-fn
        // defining axiom for `tests/data/datatype_ne_refutation.rs::dbl` came out
        // as `(forall ((n Nat)) (= (dbl n) __trust_vc_match_dt_4))` — "dbl is a
        // CONSTANT function" — because `bind_datatype_match_result` hoisted the
        // datatype match's ITE binding. Announce the pending closure so those
        // helpers can decline; see `bind_datatype_match_result`.
        //
        // That flag is a per-site OPT-IN and only two sites take it. 47 helpers
        // on `AstExpressionParser` have the same shape, so the CLASS is closed
        // below instead, at this closure boundary, by the assertion watermark:
        // see `crate::encoder::binder_capture`.
        let var_terms: Vec<Term> = if let Some(ref bound_names) = obligation.bound_vars {
            let filtered: Vec<Term> = bound_names
                .iter()
                .filter_map(|name| self.variables.get(name).copied())
                .collect();
            if filtered.len() < bound_names.len() {
                let missing: Vec<&String> = bound_names
                    .iter()
                    .filter(|name| !self.variables.contains_key(name.as_str()))
                    .collect();
                return Err(encoding_error(
                    "encode typed broadcast",
                    format!(
                        "Broadcast '{}': {}/{} bound variables not found in scope: {:?}",
                        obligation.name,
                        missing.len(),
                        bound_names.len(),
                        missing,
                    ),
                ));
            }
            filtered
        } else {
            all_var_terms.to_vec()
        };

        let will_universally_close = match obligation.bound_vars.as_deref() {
            Some(names) => !names.is_empty(),
            None => !all_var_terms.is_empty(),
        };
        // GENERAL BACKSTOP for the same defect class. `pending_universal_closure`
        // lets the handful of helpers we have inlined decline their hoist; this
        // watermark catches every helper we have NOT — including ones added
        // later — by asking, at the closure boundary itself, whether anything
        // hoisted during the encode mentions a term the `forall` is about to
        // bind. See `crate::encoder::binder_capture`.
        let capture_watermark = self.assertion_watermark();
        let body = self.with_ground_template_scope(&var_terms, |encoder| {
            crate::encoder::with_flag_unwind_safe!(
                encoder.state.pending_universal_closure,
                will_universally_close,
                {
                    crate::encoder::with_flag_unwind_safe!(
                        encoder.state.in_assumption_context,
                        true,
                        { encoder.resolve_condition_typed(&obligation.expr) }
                    )
                }
            )
        });
        let body = body.map_err(|e| {
            encoding_error(
                "encode typed broadcast",
                format!(
                    "Failed to encode broadcast assumption '{}': {}",
                    obligation.name, e
                ),
            )
        })?;

        // Build `guard ==> body` when broadcast has requires clauses (#2575).
        // The guard is resolved in assumption context so nested foralls are not
        // Skolemized. The guarded body is used for both the quantified axiom
        // and the ground-pool replay path.
        let body = if let Some(ref guard_expr) = obligation.broadcast_guard {
            let guard = self.with_ground_template_scope(&var_terms, |encoder| {
                crate::encoder::with_flag_unwind_safe!(
                    encoder.state.pending_universal_closure,
                    will_universally_close,
                    {
                        crate::encoder::with_flag_unwind_safe!(
                            encoder.state.in_assumption_context,
                            true,
                            { encoder.resolve_condition_typed(guard_expr) }
                        )
                    }
                )
            });
            let guard = guard.map_err(|e| {
                encoding_error(
                    "encode typed broadcast",
                    format!(
                        "Failed to encode broadcast guard for '{}': {}",
                        obligation.name, e
                    ),
                )
            })?;
            self.solver.try_implies(guard, body).map_err(|e| {
                encoding_error(
                    "encode typed broadcast",
                    format!(
                        "Failed to create guard implication for broadcast '{}': {}",
                        obligation.name, e
                    ),
                )
            })?
        } else {
            body
        };

        let has_type_param_bound = expr_contains_type_param(&obligation.expr)
            || obligation.bound_vars.as_ref().is_some_and(|bound_names| {
                bound_names.iter().any(|name| {
                    matches!(
                        self.var_types.get(name.as_str()),
                        Some(crate::ir::TrustVcType::TypeParam(_))
                    )
                })
            });

        if var_terms.is_empty() {
            self.solver.try_assert_term(body).map_err(|e| {
                encoding_error(
                    "encode typed broadcast",
                    format!(
                        "Failed to assert broadcast body '{}': {}",
                        obligation.name, e
                    ),
                )
            })?;
        } else if has_type_param_bound {
            // Type-param axioms are replayed through the ground-instantiation
            // path below. Keeping a live forall here can turn otherwise
            // definitive SAT negatives into QuantifierUnhandled, especially for
            // Poly generic calls. Ground-only replay is fail-closed: it may miss
            // a proof, but it cannot prove a false assertion.
        } else if let Some(dead_trigger_patterns) = interpreted_dead_trigger_patterns(obligation) {
            // Interpreted-op DEAD TRIGGER — ground-only replay (same route as
            // the type-param branch above). ay's E-matcher indexes only
            // uninterpreted function applications, so a trigger term headed by
            // an interpreted arithmetic/BV op (e.g. `x * x` -> `bvmul`) can
            // never fire: the live `forall` could never be instantiated by
            // matching, and — after ay's wrong-SAT closures (39ea40bc /
            // 0bd4fda9) stopped trusting ground models under an
            // un-instantiatable live forall — its mere presence turns
            // definitive ground SAT/counterexample verdicts into Unknown.
            // Instantiate the lemma trust-vc-side instead and assert only
            // ground instances; see `replay_interpreted_trigger_broadcast_ground`
            // for the witness sets and the soundness argument.
            self.replay_interpreted_trigger_broadcast_ground(obligation, &dead_trigger_patterns)?;
        } else {
            let mut parsed_groups = self.with_ground_template_scope(&var_terms, |encoder| {
                encoder.encode_broadcast_trigger_groups(obligation)
            })?;

            // Automatic trigger inference (#2461): if no explicit triggers
            // exist, infer them from the obligation body. Uses the names-only
            // variant since PreparedObligation carries String names without types.
            // Mode comes from #[auto_trigger] (conservative) or #[all_triggers]
            // (aggressive); defaults to conservative. Part of #2461 Slice 3.
            if parsed_groups.is_empty() {
                if let Some(ref bound_names) = obligation.bound_vars {
                    let names: Vec<&str> = bound_names.iter().map(|s| s.as_str()).collect();
                    let mode = obligation.trigger_inference_mode.unwrap_or_default();
                    let inferred = crate::trigger_inference::infer_triggers_from_names_with_mode(
                        &names,
                        &obligation.expr,
                        mode,
                    );
                    if !inferred.is_empty() {
                        for group in &inferred {
                            let mut group_terms = Vec::new();
                            for trigger_expr in group {
                                match self.with_ground_template_scope(&var_terms, |encoder| {
                                    encoder.resolve_condition_typed(trigger_expr)
                                }) {
                                    Ok(term) => group_terms.push(term),
                                    Err(_) => break,
                                }
                            }
                            if group_terms.len() == group.len() {
                                parsed_groups.push(group_terms);
                            }
                        }
                    }
                }
            }

            // A fact hoisted to the solver TOP LEVEL during this encode that
            // mentions a variable this `forall` would bind means the axiom
            // would be CAPTURED and collapse the lemma (measured:
            // `forall c. next(c) == __trust_vc_match_dt_4`). Decline the axiom
            // — the symbol stays uninterpreted, which is strictly weaker.
            // The broadcast PREMISE is withheld along with the axiom: the
            // model-revalidation lane (solve.rs) instantiates premises at a
            // candidate SAT model's witnesses and promotes an UNSAT re-check
            // to Verified, which is sound ONLY because those instances are
            // consequences of an ASSERTED forall. With the forall declined
            // they would be fresh assumptions on the one path that upgrades a
            // counterexample to Verified — the exact inversion this backstop
            // exists to prevent. Ground-pool replay (re-encoded per concrete
            // instance, never captured) is unaffected.
            match self.binder_capture_since(capture_watermark, &var_terms) {
                Some(capture) => {
                    let site = format!("broadcast:{}", obligation.name);
                    self.record_binder_capture(&site, &capture);
                }
                None => {
                    let quantified = if parsed_groups.is_empty() {
                        self.solver.try_forall(&var_terms, body)
                    } else {
                        let trigger_refs: Vec<&[Term]> =
                            parsed_groups.iter().map(|g| g.as_slice()).collect();
                        self.solver
                            .try_forall_with_triggers(&var_terms, body, &trigger_refs)
                    }
                    .map_err(|e| {
                        encoding_error(
                            "encode typed broadcast",
                            format!(
                                "Failed to create forall for broadcast '{}': {}",
                                obligation.name, e
                            ),
                        )
                    })?;
                    self.solver.try_assert_term(quantified).map_err(|e| {
                        encoding_error(
                            "encode typed broadcast",
                            format!(
                                "Failed to assert broadcast forall '{}': {}",
                                obligation.name, e
                            ),
                        )
                    })?;

                    // Record this live `forall` premise so a candidate SAT
                    // counterexample can be re-validated against it. ay's model
                    // validation skips quantified assertions (it trusts
                    // E-matching/CEGQI), so an un-instantiated broadcast
                    // `forall` can be silently violated by a SAT model that is
                    // still reported as `sat_model_validated`. Only the
                    // quantified branch needs this — the ground/cap/type-param
                    // branches assert their body directly and are validated by
                    // ay. Soundness fix #1.
                    //
                    // The push lives INSIDE this arm on purpose: the
                    // revalidation promotion (solve.rs) is sound only for
                    // premises whose `forall` is actually IN the solver. A
                    // premise recorded for a declined axiom would let the
                    // model-revalidation lane assert fresh, never-asserted
                    // instances on the one path that upgrades a SAT
                    // counterexample to Verified.
                    if let Some(ref bound_names) = obligation.bound_vars {
                        if !bound_names.is_empty() {
                            self.state.broadcast_premises.push(
                                crate::encoder::encoder_state::BroadcastForallPremise {
                                    bound_vars: bound_names.clone(),
                                    body: obligation.expr.clone(),
                                    guard: obligation.broadcast_guard.clone(),
                                },
                            );
                        }
                    }
                }
            }
        }

        #[cfg(feature = "native-seq")]
        self.instantiate_small_native_seq_index_cases(obligation)?;

        let seed_symbols: Vec<String> = obligation
            .eager_seed_symbols()
            .into_iter()
            .map(|symbol| symbol.into_owned())
            .collect();
        let seed_triggers: Vec<GroundTrigger> = if has_type_param_bound {
            Vec::new()
        } else {
            obligation
                .eager_seed_trigger_patterns()
                .into_iter()
                .flat_map(|(symbol, arg_patterns)| {
                    let mut triggers = vec![GroundTrigger {
                        symbol: symbol.clone(),
                        arg_patterns: arg_patterns.clone(),
                        bound_exprs: None,
                    }];

                    if let Some(bound_vars) = obligation.bound_vars.as_ref() {
                        let bound_exprs: Option<Vec<TrustVcExpr>> = bound_vars
                            .iter()
                            .map(|name| self.state.equality_assumptions.get(name).cloned())
                            .collect();
                        if let Some(bound_exprs) = bound_exprs {
                            let normalized_patterns = arg_patterns
                                .iter()
                                .map(|arg| {
                                    let substituted =
                                        crate::encoder::ir_encoder::normalize::substitute_vars(
                                            arg,
                                            &self.state.equality_assumptions,
                                        );
                                    crate::encoder::ir_encoder::normalize::normalize_int_expr(
                                        &substituted,
                                    )
                                })
                                .collect();
                            triggers.push(GroundTrigger {
                                symbol,
                                arg_patterns: normalized_patterns,
                                bound_exprs: Some(bound_exprs),
                            });
                        }
                    }

                    triggers
                })
                .collect()
        };
        if let Some(bound_vars) = obligation
            .bound_vars
            .as_ref()
            .filter(|_| !seed_symbols.is_empty() || !seed_triggers.is_empty())
        {
            // Use the guarded expression for ground-pool replay (#2575).
            // Without this, ground instantiation would re-assert unguarded
            // postconditions even after the initial forall is repaired.
            let pool_expr = if let Some(ref guard_expr) = obligation.broadcast_guard {
                crate::ir::TrustVcExpr::Implies {
                    premise: Box::new(guard_expr.clone()),
                    conclusion: Box::new(obligation.expr.clone()),
                }
            } else {
                obligation.expr.clone()
            };
            self.state.ground_pool.register_axiom(GroundAxiom {
                name: obligation.name.clone(),
                seed_symbols,
                seed_triggers,
                bound_vars: bound_vars.clone(),
                expr: pool_expr,
            });
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encoder::verification::panic::is_sort_mismatch_error;
    use crate::error::TrustVcError;
    use crate::ir::TrustVcType;
    use crate::prepared_context::prepare_context;
    use crate::vc::{ProofObligation, VerificationContext};

    /// Route A (#2779) makes every spec-collection `.len()` an unbounded
    /// `Int`, so the broadcast body `exists(|v: i32| s.push(v).len() == 3)`
    /// on `Seq<i32>` no longer builds the BV-vs-Int sort mismatch this case
    /// was constructed to surface — `len(s) + 1` and `3` are both Int. This
    /// test pins the NEW correct behaviour: the typed broadcast encodes
    /// cleanly. The accompanying check that a sort-mismatched broadcast still
    /// surfaces as a typed error lives in
    /// `test_add_typed_broadcast_genuine_sort_mismatch_surfaces_as_typed_error`.
    #[test]
    fn test_add_typed_broadcast_push_len_encodes_without_sort_mismatch() {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
        ctx.obligations.push(ProofObligation::broadcast_assume(
            "broadcast_push",
            "exists(|v: i32| s.push(v).len() == 3)",
        ));

        let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
        let obligation = prepared
            .obligations
            .first()
            .expect("prepared context should contain the broadcast obligation");

        let mut encoder = AYEncoder::new();
        for variable in &prepared.variables {
            encoder
                .declare_variable(variable)
                .expect("variable declaration should succeed");
        }
        let all_var_terms: Vec<_> = encoder.variables.values().copied().collect();

        let result = encoder.add_typed_broadcast(obligation, &all_var_terms);
        assert!(
            result.is_ok(),
            "Route A uniform-Int length must let the push-length broadcast body \
             encode cleanly (no BV-vs-Int sort mismatch), got: {:?}",
            result
        );
    }

    /// Discriminating companion: a broadcast whose body genuinely crosses sorts
    /// (a `Seq<i32>` element compared against a `Bool`) must STILL surface as a
    /// typed `Encoding` error — Route A only removed the *spurious* length
    /// mismatch, not the typed-error reporting path itself.
    #[test]
    fn test_add_typed_broadcast_genuine_sort_mismatch_surfaces_as_typed_error() {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
        ctx.declare_var_typed("b", crate::ir::TrustVcType::Bool);
        ctx.obligations.push(ProofObligation::broadcast_assume(
            "broadcast_bad",
            "forall(|i: i32| s.index(i) == b)",
        ));

        let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
        let obligation = prepared
            .obligations
            .first()
            .expect("prepared context should contain the broadcast obligation");

        let mut encoder = AYEncoder::new();
        for variable in &prepared.variables {
            encoder
                .declare_variable(variable)
                .expect("variable declaration should succeed");
        }
        let all_var_terms: Vec<_> = encoder.variables.values().copied().collect();

        let result = encoder.add_typed_broadcast(obligation, &all_var_terms);
        match result {
            Err(TrustVcError::Encoding { detail, .. }) => assert!(
                is_sort_mismatch_error(&detail),
                "typed broadcast helper should preserve sort-mismatch detail, got: {}",
                detail
            ),
            other => panic!(
                "a genuine Seq<i32>-vs-Bool broadcast mismatch must surface as \
                 TrustVcError::Encoding, got: {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_add_typed_broadcast_registers_all_alternative_singleton_seed_symbols() {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_helper_function_typed(
            "f",
            TrustVcType::Bool,
            vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        );
        ctx.declare_helper_function_typed(
            "g",
            TrustVcType::Bool,
            vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        );
        ctx.obligations.push(
            ProofObligation::broadcast_assume("broadcast_fg", "x == x")
                .with_bound_vars(vec!["x".to_string()])
                .with_trigger_patterns(vec![vec!["f(x)".to_string()], vec!["g(x)".to_string()]]),
        );

        let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
        let obligation = prepared
            .obligations
            .first()
            .expect("prepared context should contain the broadcast obligation");

        let mut encoder = AYEncoder::new();
        for variable in &prepared.variables {
            encoder
                .declare_variable(variable)
                .expect("variable declaration should succeed");
        }
        for helper in &prepared.helper_function_contexts {
            encoder
                .register_function_context(helper)
                .expect("helper registration should succeed");
        }
        let all_var_terms: Vec<_> = encoder.variables.values().copied().collect();

        encoder
            .add_typed_broadcast(obligation, &all_var_terms)
            .expect("typed broadcast should encode");
        assert_eq!(
            encoder.state.ground_pool.ground_term_count(),
            0,
            "bound-template triggers must not become free caller demand"
        );
        assert_eq!(
            encoder
                .state
                .ground_pool
                .pending_instantiation_count_for_tests(),
            0
        );
        for (name, value) in [("f", 5), ("g", 7)] {
            encoder
                .encode_condition_typed(&TrustVcExpr::FnCall {
                    name: name.into(),
                    args: vec![TrustVcExpr::IntLit {
                        value,
                        ty: TrustVcType::Int { width: 32 },
                    }],
                    return_ty: TrustVcType::Bool,
                })
                .expect("genuine caller");
        }
        assert_eq!(encoder.state.ground_pool.ground_term_count(), 2);
        assert_eq!(
            encoder
                .state
                .ground_pool
                .pending_instantiation_count_for_tests(),
            2,
            "both alternative singleton seed symbols must accept genuine caller bindings"
        );
    }

    #[test]
    fn test_add_typed_broadcast_keeps_multi_trigger_groups_solver_only_for_seeding() {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_helper_function_typed(
            "f",
            TrustVcType::Bool,
            vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        );
        ctx.declare_helper_function_typed(
            "g",
            TrustVcType::Bool,
            vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        );
        ctx.obligations.push(
            ProofObligation::broadcast_assume("broadcast_multi", "x == x")
                .with_bound_vars(vec!["x".to_string()])
                .with_trigger_patterns(vec![vec!["f(x)".to_string(), "g(x)".to_string()]]),
        );

        let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
        let obligation = prepared
            .obligations
            .first()
            .expect("prepared context should contain the broadcast obligation");

        let mut encoder = AYEncoder::new();
        for variable in &prepared.variables {
            encoder
                .declare_variable(variable)
                .expect("variable declaration should succeed");
        }
        for helper in &prepared.helper_function_contexts {
            encoder
                .register_function_context(helper)
                .expect("helper registration should succeed");
        }
        let all_var_terms: Vec<_> = encoder.variables.values().copied().collect();

        encoder
            .add_typed_broadcast(obligation, &all_var_terms)
            .expect("typed broadcast should encode");
        assert_eq!(
            encoder.state.ground_pool.ground_term_count(),
            0,
            "multi-trigger templates must not become free caller demand"
        );
        for name in ["f", "g"] {
            encoder
                .encode_condition_typed(&TrustVcExpr::FnCall {
                    name: name.into(),
                    args: vec![TrustVcExpr::IntLit {
                        value: 5,
                        ty: TrustVcType::Int { width: 32 },
                    }],
                    return_ty: TrustVcType::Bool,
                })
                .expect("genuine caller");
        }
        assert_eq!(encoder.state.ground_pool.ground_term_count(), 2);
        assert_eq!(
            encoder.state.ground_pool.pending_instantiation_count_for_tests(),
            0,
            "multi-trigger groups must stay solver-only instead of fabricating eager-seed registrations"
        );
    }

    /// An interpreted-op-headed trigger (`x * x` -> `bvmul`) can never be
    /// E-matched by ay, so the lemma must take the ground-replay route: no
    /// live `forall` asserted, ground instances only, premise recorded for
    /// the vacuity probe + model revalidation.
    #[test]
    fn test_interpreted_trigger_broadcast_routes_to_ground_replay() {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.obligations.push(
            ProofObligation::broadcast_assume("broadcast_sq_nonneg", "x * x >= 0")
                .with_bound_vars(vec!["x".to_string()])
                .with_trigger_patterns(vec![vec!["x * x".to_string()]]),
        );

        let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
        let obligation = prepared
            .obligations
            .first()
            .expect("prepared context should contain the broadcast obligation");
        assert!(
            interpreted_dead_trigger_patterns(obligation).is_some(),
            "an `x * x` trigger must classify as an interpreted-op dead trigger"
        );

        let mut encoder = AYEncoder::new();
        for variable in &prepared.variables {
            encoder
                .declare_variable(variable)
                .expect("variable declaration should succeed");
        }
        let all_var_terms: Vec<_> = encoder.variables.values().copied().collect();
        encoder
            .add_typed_broadcast(obligation, &all_var_terms)
            .expect("typed broadcast should encode");

        assert_eq!(
            encoder.state.interpreted_trigger_ground_replays, 1,
            "interpreted-op trigger must take the ground-replay route"
        );
        assert_eq!(
            encoder.state.broadcast_premises.len(),
            1,
            "ground-replay route must record the lemma premise for the \
             vacuity probe and model revalidation"
        );
    }

    /// Discriminating companion: a matchable uninterpreted-head trigger
    /// (`f(x)`) must STAY on the live-forall path (ay's E-matcher handles it),
    /// with the premise recorded by that branch as before.
    #[test]
    fn test_uninterpreted_trigger_broadcast_keeps_live_forall_path() {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_helper_function_typed(
            "f",
            TrustVcType::Bool,
            vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        );
        ctx.obligations.push(
            ProofObligation::broadcast_assume("broadcast_f_holds", "f(x)")
                .with_bound_vars(vec!["x".to_string()])
                .with_trigger_patterns(vec![vec!["f(x)".to_string()]]),
        );

        let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
        let obligation = prepared
            .obligations
            .first()
            .expect("prepared context should contain the broadcast obligation");
        assert!(
            interpreted_dead_trigger_patterns(obligation).is_none(),
            "an `f(x)` trigger must NOT classify as an interpreted-op dead trigger"
        );

        let mut encoder = AYEncoder::new();
        for variable in &prepared.variables {
            encoder
                .declare_variable(variable)
                .expect("variable declaration should succeed");
        }
        for helper in &prepared.helper_function_contexts {
            encoder
                .register_function_context(helper)
                .expect("helper registration should succeed");
        }
        let all_var_terms: Vec<_> = encoder.variables.values().copied().collect();
        encoder
            .add_typed_broadcast(obligation, &all_var_terms)
            .expect("typed broadcast should encode");

        assert_eq!(
            encoder.state.interpreted_trigger_ground_replays, 0,
            "uninterpreted-head trigger must keep the live-forall path"
        );
        assert_eq!(
            encoder.state.broadcast_premises.len(),
            1,
            "live-forall path must record the lemma premise as before"
        );
    }

    /// A MIXED trigger group (`[f(x), x * x]`) is dead as a whole — E-matching
    /// fires a group only when ALL its terms match, so one interpreted-headed
    /// term kills the group. With every group dead, the lemma ground-replays.
    /// A lemma with at least one fully-uninterpreted ALTERNATIVE group stays
    /// live (ay can match through that group).
    #[test]
    fn test_mixed_and_alternative_trigger_group_classification() {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_helper_function_typed(
            "f",
            TrustVcType::Bool,
            vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        );
        ctx.obligations.push(
            ProofObligation::broadcast_assume("broadcast_mixed_group", "x == x")
                .with_bound_vars(vec!["x".to_string()])
                .with_trigger_patterns(vec![vec!["f(x)".to_string(), "x * x".to_string()]]),
        );
        ctx.obligations.push(
            ProofObligation::broadcast_assume("broadcast_live_alternative", "x == x")
                .with_bound_vars(vec!["x".to_string()])
                .with_trigger_patterns(vec![vec!["x * x".to_string()], vec!["f(x)".to_string()]]),
        );

        let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
        let mixed = prepared
            .obligations
            .iter()
            .find(|o| o.name == "broadcast_mixed_group")
            .expect("mixed-group obligation should be prepared");
        let alternative = prepared
            .obligations
            .iter()
            .find(|o| o.name == "broadcast_live_alternative")
            .expect("alternative-group obligation should be prepared");

        assert!(
            interpreted_dead_trigger_patterns(mixed).is_some(),
            "a single mixed group containing an interpreted-headed term is dead"
        );
        assert!(
            interpreted_dead_trigger_patterns(alternative).is_none(),
            "an alternative fully-uninterpreted group keeps the lemma live"
        );
    }

    #[cfg(feature = "native-seq")]
    #[test]
    fn test_fold_grounded_concrete_ints_reduces_index_arithmetic_to_literal() {
        let seq_ty = crate::ir::TrustVcType::parse_or_opaque("Seq<i64>");
        let expr = TrustVcExpr::Index {
            receiver: Box::new(TrustVcExpr::Var {
                name: "s".to_string(),
                ty: seq_ty,
            }),
            index: Box::new(TrustVcExpr::Arith {
                op: crate::ir::ArithOp::Add,
                left: Box::new(TrustVcExpr::IntLit {
                    value: 0,
                    ty: TrustVcType::Uint { width: 64 },
                }),
                right: Box::new(TrustVcExpr::IntLit {
                    value: 1,
                    ty: TrustVcType::Uint { width: 64 },
                }),
                ty: TrustVcType::Uint { width: 64 },
            }),
            receiver_name: Some("s".to_string()),
            elem_ty: TrustVcType::Int { width: 64 },
        };

        let folded = fold_grounded_concrete_ints(expr);
        match folded {
            TrustVcExpr::Index { index, .. } => assert!(
                matches!(
                    index.as_ref(),
                    TrustVcExpr::IntLit {
                        value: 1,
                        ty: TrustVcType::Uint { width: 64 },
                    }
                ),
                "grounded index arithmetic should fold to a concrete Uint literal, got {:?}",
                index
            ),
            other => panic!("expected folded Index expr, got {:?}", other),
        }
    }
}
