// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Typed assumption encoding and equality reconciliation helpers.

use crate::encoder::AYEncoder;
use crate::error::TrustVcResult;
use crate::ir::{CollectionOp, CompareOp, QuantifierKind, TrustVcExpr};
use ay_dpll::api::{SolverScope, Term};

use super::encoding_error;

impl AYEncoder {
    /// Adds a TrustVcExpr as an assumption (in assumption context).
    ///
    /// Also extracts equality bindings (`var == expr`) for TrustVcExpr-level
    /// substitution into later assertion encodings. Part of #2187.
    ///
    /// When `eq_queue` is provided, equality expressions are pushed for later
    /// reconciliation with the final binding map. Part of #2386.
    pub(in crate::encoder) fn add_typed_assumption(
        &mut self,
        name: &str,
        expr: &crate::ir::TrustVcExpr,
        mut eq_queue: Option<&mut Vec<crate::ir::TrustVcExpr>>,
    ) -> TrustVcResult<()> {
        self.add_typed_assumption_inner(name, expr, &mut eq_queue, false, None)
    }

    /// Adds an assumption while preserving the obligation's original solver
    /// mode during encoding. Used when replaying proven assert_by facts.
    /// Part of #2862.
    pub(in crate::encoder) fn add_typed_assumption_with_solver_mode(
        &mut self,
        name: &str,
        expr: &crate::ir::TrustVcExpr,
        mut eq_queue: Option<&mut Vec<crate::ir::TrustVcExpr>>,
        solver_mode: Option<crate::vc::SolverMode>,
    ) -> TrustVcResult<()> {
        self.add_typed_assumption_inner(name, expr, &mut eq_queue, false, solver_mode)
    }

    /// Adds an assumption while preserving concrete bound-variable sorts for
    /// any nested quantifiers. Used for `assert_forall_by` facts that mention
    /// helper UFs over concrete integer sorts. Part of #2551.
    #[cfg(test)]
    pub(in crate::encoder) fn add_typed_assumption_with_concrete_quantifier_sorts(
        &mut self,
        name: &str,
        expr: &crate::ir::TrustVcExpr,
        mut eq_queue: Option<&mut Vec<crate::ir::TrustVcExpr>>,
    ) -> TrustVcResult<()> {
        self.add_typed_assumption_inner(name, expr, &mut eq_queue, true, None)
    }

    /// Adds an assumption while preserving both concrete quantifier sorts and
    /// the original solver mode. Used for replayed forall-by/assert_by facts.
    /// Part of #2862.
    pub(in crate::encoder) fn add_typed_assumption_with_concrete_quantifier_sorts_and_solver_mode(
        &mut self,
        name: &str,
        expr: &crate::ir::TrustVcExpr,
        mut eq_queue: Option<&mut Vec<crate::ir::TrustVcExpr>>,
        solver_mode: Option<crate::vc::SolverMode>,
    ) -> TrustVcResult<()> {
        self.add_typed_assumption_inner(name, expr, &mut eq_queue, true, solver_mode)
    }

    /// Assert a fact that was established under the OTHER arithmetic reading,
    /// GUARDED by its own no-overflow predicates.
    ///
    /// The two universes evaluate fixed-width `+`, `-`, `*` and a wrapping
    /// unary `-` identically EXACTLY when the operation does not overflow, so
    /// `no_overflow(F) ==> F` is true under both readings whatever the other
    /// one meant. In models where the arithmetic really does overflow it says
    /// nothing at all, which is precisely the case the unguarded assert got
    /// wrong.
    ///
    /// This is what lets an ordinary `assume!(m == n - 1)` reach the
    /// `decreases` lane (`test_multi_arg_decreases::
    /// test_collected_vs_direct_measure_decreases_parity`): with `n > 0` the
    /// guard discharges and the fact is available, while at `n == i32::MIN` —
    /// where the readings part company — it is not.
    ///
    /// Deliberately does NOT run the equality-binding extraction that
    /// [`Self::add_typed_assumption_with_solver_mode`] does: a CONDITIONAL fact
    /// must never be recorded as an unconditional rewrite of `m`.
    ///
    /// Fail-closed at every step. If the expression does not encode, or the
    /// encoder emits no predicate to guard with, NOTHING is asserted — the
    /// fact is dropped exactly as an unguardable one would be.
    pub(in crate::encoder) fn add_cross_reading_guarded_assumption(
        &mut self,
        name: &str,
        expr: &crate::ir::TrustVcExpr,
        solver_mode: Option<crate::vc::SolverMode>,
        int_lane: bool,
    ) -> TrustVcResult<()> {
        // Into the `Int` universe the guard is a RANGE test on the fact's own
        // arithmetic, built as IR: that lane emits no no-overflow predicates of
        // its own, and a range test is exactly the right statement there.
        if int_lane {
            let Some(guarded_expr) = super::arith_reading::int_lane_range_guarded(expr) else {
                return Ok(());
            };
            let mut no_queue: Option<&mut Vec<crate::ir::TrustVcExpr>> = None;
            // The doc comment above promises that a fact which does not encode
            // is DROPPED exactly as an unguardable one would be. That was true
            // only of the fixed-width branch: this one PROPAGATED the encode
            // failure, so a legitimate `forall`-shaped hypothesis turned an
            // ordinary `by(nonlinear_arith)` or measure obligation into a hard
            // `VerifyResult::Error` carrying an internal encoder message that
            // blamed the user's source. Dropping is the fail-closed answer —
            // a hypothesis fewer can only make the goal harder.
            if let Err(error) = self.add_typed_assumption_inner(
                name,
                &guarded_expr,
                &mut no_queue,
                false,
                solver_mode,
            ) {
                tracing::debug!(
                    assumption = %name,
                    error = %format!("{error:?}"),
                    "cross-reading fact dropped: its range-guarded form did not encode in the int lane"
                );
            }
            return Ok(());
        }
        let encoded =
            crate::encoder::with_flag_unwind_safe!(self.state.active_solver_mode, solver_mode, {
                crate::encoder::with_flag_unwind_safe!(self.state.in_assumption_context, true, {
                    self.resolve_condition_with_overflow_typed(expr, true)
                })
            });
        let (term, overflow_preds) = match encoded {
            Ok(encoded) => encoded,
            Err(error) => {
                tracing::debug!(
                    assumption = %name,
                    error = %format!("{error:?}"),
                    "cross-reading fact dropped: it did not encode in the target reading"
                );
                return Ok(());
            }
        };
        if overflow_preds.is_empty() {
            tracing::debug!(
                assumption = %name,
                "cross-reading fact dropped: the target reading emitted no no-overflow \
                 predicate to guard it with"
            );
            return Ok(());
        }
        let mut guard: Option<Term> = None;
        for (_, pred) in &overflow_preds {
            guard = Some(match guard {
                None => *pred,
                Some(acc) => match self.solver.try_and(acc, *pred) {
                    Ok(term) => term,
                    Err(error) => {
                        tracing::debug!(
                            assumption = %name,
                            error = %format!("{error:?}"),
                            "cross-reading fact dropped: could not conjoin its guard"
                        );
                        return Ok(());
                    }
                },
            });
        }
        let Some(guard) = guard else {
            return Ok(());
        };
        let guarded = match self.solver.try_implies(guard, term) {
            Ok(term) => term,
            Err(error) => {
                tracing::debug!(
                    assumption = %name,
                    error = %format!("{error:?}"),
                    "cross-reading fact dropped: could not build its guarded form"
                );
                return Ok(());
            }
        };
        let solver_name = format!("__trust_vc_cross_reading_{}", self.state.assumption_count);
        if let Err(error) = self.solver.try_assert_named(guarded, &solver_name) {
            return Err(encoding_error(
                "encode guarded cross-reading assumption",
                format!("Failed to assert guarded assumption '{name}': {error}"),
            ));
        }
        self.state.assumption_count += 1;
        Ok(())
    }

    fn add_typed_assumption_inner(
        &mut self,
        name: &str,
        expr: &crate::ir::TrustVcExpr,
        eq_queue: &mut Option<&mut Vec<crate::ir::TrustVcExpr>>,
        preserve_quantifier_sorts: bool,
        solver_mode: Option<crate::vc::SolverMode>,
    ) -> TrustVcResult<()> {
        // Extract equality binding for pre-encoding substitution.
        // Substitute existing bindings into the new binding's RHS so
        // chained equalities work: if y→d*q2 exists and x==q*y+r arrives,
        // store x→q*(d*q2)+r (not x→q*y+r).
        //
        // The binding is extracted and resolved BEFORE encoding, but
        // inserted AFTER encoding. This ensures the assumption itself
        // is encoded with only PRIOR bindings (not its own), preventing
        // self-substitution that would make `n == 0` become `0 == 0`.
        // Part of #2187, #2400.
        //
        // Extract the binding from the INLINE-SUBSTITUTED form of the
        // assumption: every later `encode_condition_typed` inlines spec-fn
        // calls FIRST and applies the binding map SECOND, so a binding whose
        // RHS still carries a raw call to an inlined function (`out ==
        // successor(i)` under a demand-inline override of `successor`) would
        // re-introduce that call after inlining ran — and the override never
        // declares the function's UF, so the goal (`out == 5` → `successor(i)
        // == 5`) failed to encode ("Undefined function") and the retry was
        // silently abandoned, leaving the proof_in_spec.rs wrong-result
        // postcondition a fail-closed Unknown instead of the Counterexample the
        // ground retry decides. The substitution is the one every encode
        // applies anyway, so the asserted facts are unchanged; only the binding
        // is recorded in its already-inlined shape.
        let inlined_expr = if self.state.inline_bodies.is_empty() {
            std::borrow::Cow::Borrowed(expr)
        } else {
            std::borrow::Cow::Owned(super::super::eval::substitute_inline_calls(
                expr,
                &self.state.inline_bodies,
            ))
        };
        let pending_binding = super::super::ir_encoder::normalize::extract_equality_binding(
            &inlined_expr,
        )
        .map(|(var_name, rhs_expr)| {
            let resolved_rhs = if self.state.equality_assumptions.is_empty() {
                rhs_expr
            } else {
                super::super::ir_encoder::normalize::substitute_vars(
                    &rhs_expr,
                    &self.state.equality_assumptions,
                )
            };
            (var_name, resolved_rhs)
        });
        let pending_collection_len = concrete_collection_len_binding(expr);
        let pending_collection_len_var = variable_collection_len_binding(expr);

        // CONSERVATIVE TOP-LEVEL-ONLY gate for eager Skolemization of an assumed
        // existential (resolution B). Fire ONLY when the assumption is a LITERAL
        // top-level `Exists` node — unambiguously positive, so no polarity
        // analysis is needed. Any existential nested under `Not`/`Implies`/
        // `Compare`/`Ite`/etc. keeps the unchanged real `try_exists` path: those
        // can carry negative polarity (`(exists .. ) == false` is `forall ..
        // !..`), and eager-Skolemizing a negatively-polarized existential would
        // wrongly refute a valid program (false-CE). We deliberately do NOT
        // descend or analyze polarity here.
        let skolemize_top_level_exists = matches!(
            expr,
            TrustVcExpr::Quantifier {
                kind: QuantifierKind::Exists,
                ..
            }
        );

        // Encode the assumption using only PRIOR bindings for substitution.
        let encoded =
            crate::encoder::with_flag_unwind_safe!(self.state.active_solver_mode, solver_mode, {
                crate::encoder::with_flag_unwind_safe!(self.state.in_assumption_context, true, {
                    crate::encoder::with_flag_unwind_safe!(
                        self.state.skolemize_top_level_assumption_exists,
                        skolemize_top_level_exists,
                        {
                            crate::encoder::with_flag_unwind_safe!(
                                self.state.preserve_assumption_quantifier_sorts,
                                preserve_quantifier_sorts,
                                { self.resolve_condition_with_overflow_typed(expr, false) }
                            )
                        }
                    )
                })
            });

        let (term, side_conditions) = encoded.map_err(|e| {
            encoding_error(
                "encode typed assumption",
                format!("Failed to encode assumption '{}': {}", name, e),
            )
        })?;
        self.check_assumption_side_conditions(name, &side_conditions)?;

        // Now insert the binding and back-propagate.
        if let Some((var_name, resolved_rhs)) = pending_binding {
            if let Some(queue) = eq_queue.as_deref_mut() {
                queue.push(expr.clone());
            }

            // Use shared insert+back-propagate helper. On duplicate,
            // derive cross-equality for reconciliation. Part of #2386, #2454.
            if !super::super::ir_encoder::normalize::insert_and_back_propagate(
                &mut self.state.equality_assumptions,
                var_name.clone(),
                resolved_rhs.clone(),
            ) {
                // Duplicate binding: variable has two equality assumptions.
                // Derive the cross-equality: existing_rhs == new_rhs.
                if let Some(queue) = eq_queue.as_deref_mut() {
                    if let Some(existing_rhs) = self.state.equality_assumptions.get(&var_name) {
                        let derived_eq = crate::ir::TrustVcExpr::Compare {
                            op: crate::ir::CompareOp::Eq,
                            left: Box::new(existing_rhs.clone()),
                            right: Box::new(resolved_rhs),
                        };
                        queue.push(derived_eq);
                    }
                }
            }
        }
        #[cfg(feature = "named-assertions")]
        let assert_result = {
            let solver_name = self.state.register_assumption_core_name(name);
            self.solver.try_assert_named(term, &solver_name)
        };
        #[cfg(not(feature = "named-assertions"))]
        let assert_result = {
            // ay records all native API assertions under the same parsed
            // placeholder when try_assert_term() is used. Unique internal names
            // keep assumption frames distinct without enabling user-facing cores.
            let solver_name = format!("__trust_vc_assumption_{}", self.state.assumption_count);
            self.solver.try_assert_named(term, &solver_name)
        };

        assert_result.map_err(|e| {
            encoding_error(
                "encode typed assumption",
                format!("Failed to assert assumption '{}': {}", name, e),
            )
        })?;
        self.state.assumption_count += 1;
        if let Some((collection_name, len_value)) = pending_collection_len {
            self.record_concrete_collection_len_assumption(&collection_name, len_value)?;
        } else if let Some((collection_name, var_name)) = pending_collection_len_var {
            self.record_variable_collection_len_assumption(&collection_name, &var_name)?;
        }
        Ok(())
    }

    /// Pin a spec-collection length to an unsigned bitvector variable's value
    /// when an assumption states `coll.len() == var` (and `var` is a declared
    /// fixed-width unsigned variable). Under Route A (#2779) the length is an
    /// unbounded `Int`; this stores it as `bv2int(var)` (= `bv2nat(var)`).
    ///
    /// Why this is the right companion: a length pinned to a width-`w` BV value
    /// cannot exceed `2^w`, so `bv2nat(var)` is the exact (non-wrapping) length.
    /// Crucially, ay constant-folds `int2bv(w, bv2nat(var)) == var`, so the
    /// later `len_as_index_bv`/`coerce_to_len_width` bridge used by index-bounds
    /// checks resolves to `var` itself with no residual `int2bv` subterm — the
    /// bound `idx <u var` then discharges in pure BV, exactly as it did before
    /// Route A made the length `Int`. Only applied for UNSIGNED `var` (signed
    /// `bv2int_signed` does not fold and could be negative).
    fn record_variable_collection_len_assumption(
        &mut self,
        collection_name: &str,
        var_name: &str,
    ) -> TrustVcResult<()> {
        let Some(existing_len) = self.collection_lengths.get(collection_name).copied() else {
            return Ok(());
        };
        // Only meaningful when the length is the Route A unbounded `Int` model.
        if !matches!(self.solver.term_sort(existing_len), ay_dpll::api::Sort::Int) {
            return Ok(());
        }
        // The peer must be a declared, fixed-width *unsigned* integer variable.
        let Some(ty) = self.var_types.get(var_name) else {
            return Ok(());
        };
        if !matches!(ty, crate::ir::TrustVcType::Uint { .. }) {
            return Ok(());
        }
        let Some(var_term) = self.variables.get(var_name).copied() else {
            return Ok(());
        };
        if !matches!(
            self.solver.term_sort(var_term),
            ay_dpll::api::Sort::BitVec(_)
        ) {
            return Ok(());
        }
        let len_as_bv2int = self.solver.try_bv2int(var_term).map_err(|e| {
            encoding_error(
                "encode typed assumption",
                format!(
                    "Failed to pin length of '{}' to variable '{}': {}",
                    collection_name, var_name, e
                ),
            )
        })?;
        self.collection_lengths
            .insert(collection_name.to_string(), len_as_bv2int);
        Ok(())
    }

    fn record_concrete_collection_len_assumption(
        &mut self,
        collection_name: &str,
        len_value: i128,
    ) -> TrustVcResult<()> {
        if len_value < 0 || len_value > i64::MAX as i128 {
            return Ok(());
        }
        let Some(existing_len) = self.collection_lengths.get(collection_name).copied() else {
            return Ok(());
        };
        let len_term = if matches!(self.solver.term_sort(existing_len), ay_dpll::api::Sort::Int) {
            self.solver.int_const(len_value as i64)
        } else {
            self.solver
                .try_bv_const(len_value as i64, crate::ir::pointer_width())
                .map_err(|e| {
                    encoding_error(
                        "encode typed assumption",
                        format!(
                            "Failed to record concrete length for collection '{}': {}",
                            collection_name, e
                        ),
                    )
                })?
        };
        self.collection_lengths
            .insert(collection_name.to_string(), len_term);
        Ok(())
    }

    fn check_assumption_side_conditions(
        &mut self,
        name: &str,
        side_conditions: &[(std::borrow::Cow<'static, str>, Term)],
    ) -> TrustVcResult<()> {
        for (index, (check_name, predicate)) in side_conditions.iter().enumerate() {
            let mut scope = SolverScope::new(&mut self.solver).map_err(|e| {
                encoding_error(
                    "check typed assumption side condition",
                    format!(
                        "Failed to create solver scope for side condition '{}' in assumption '{}': {}",
                        check_name, name, e
                    ),
                )
            })?;
            let negated = scope.try_not(*predicate).map_err(|e| {
                encoding_error(
                    "check typed assumption side condition",
                    format!(
                        "Failed to negate side condition '{}' in assumption '{}': {}",
                        check_name, name, e
                    ),
                )
            })?;
            let probe_name = format!(
                "__trust_vc_assumption_{}_side_condition_{}",
                self.state.assumption_count, index
            );
            scope.try_assert_named(negated, &probe_name).map_err(|e| {
                encoding_error(
                    "check typed assumption side condition",
                    format!(
                        "Failed to assert side condition '{}' in assumption '{}': {}",
                        check_name, name, e
                    ),
                )
            })?;
            if let Some(first) = self.state.solver_panic.as_deref() {
                return Err(encoding_error(
                    "check typed assumption side condition",
                    format!(
                        "ay error while checking side condition '{}' in assumption '{}': {}",
                        check_name,
                        name,
                        super::solve::poisoned_solver_error(first)
                    ),
                ));
            }
            let result = scope.try_check_sat();
            super::solve::note_solver_panic(&result, &mut self.state.solver_panic);
            let result = result.map_err(|e| {
                encoding_error(
                    "check typed assumption side condition",
                    format!(
                        "ay error while checking side condition '{}' in assumption '{}': {}",
                        check_name, name, e
                    ),
                )
            })?;
            let solve_result = result.result();
            if solve_result.is_unsat() {
                continue;
            }
            return Err(encoding_error(
                "check typed assumption side condition",
                format!(
                    "Assumption '{}' requires side condition '{}', but it is not established by prior assumptions",
                    name, check_name
                ),
            ));
        }
        Ok(())
    }

    /// Re-encode equality assumptions with the final binding map.
    ///
    /// After all assumptions are processed, late-arriving bindings may have
    /// updated the binding map via back-propagation. Assumptions encoded
    /// earlier missed these updates. Re-encoding produces ordering-independent
    /// derived equalities that ay can use directly.
    ///
    /// For assumptions already encoded with complete bindings, the
    /// re-encoding is a tautology (zero solver cost). Part of #2386.
    pub(in crate::encoder) fn reconcile_equality_assumptions(
        &mut self,
        exprs: &[crate::ir::TrustVcExpr],
    ) -> TrustVcResult<()> {
        if exprs.is_empty() {
            return Ok(());
        }
        let result: TrustVcResult<()> =
            crate::encoder::with_flag_unwind_safe!(self.state.in_assumption_context, true, {
                (|| {
                    for expr in exprs {
                        let term = self.encode_condition_typed(expr)?;
                        self.solver.try_assert_term(term).map_err(|e| {
                            encoding_error(
                                "reconcile equality assumption",
                                format!("Failed to assert reconciled equality: {}", e),
                            )
                        })?;
                    }
                    Ok(())
                })()
            });
        result?;
        Ok(())
    }
}

/// F3 point-interval pin recognizer (declaration-time pinning, see
/// `setup.rs::collect_finite_len_pins`): extract `(seq_var_name, literal_len)`
/// from a TOP-LEVEL positive assumption expression that ENTAILS a concrete
/// length for a declared Seq variable. Two shapes:
///
/// 1. `var == <chain>` / `<chain> == var`, where `<chain>` is a Seq
///    constructor chain whose length is statically known
///    (`AstExpressionParser::finite_seq_literal_len` — empty/push/concat over
///    literal chains, or a fixed `[T; N]` array operand): extensional
///    equality forces `var.len() == n`. A Seq-typed peer VAR yields `None`
///    (only the ARRAY arm of `finite_seq_literal_len` resolves plain vars).
/// 2. `var.len() == N` / `N == var.len()` with a non-negative integer
///    literal `N` (the requires-derived pin).
///
/// POLARITY: callers must only apply this to a LITERAL top-level assumption
/// node — unambiguously positive (mirrors the eager-Skolemization gate in
/// `add_typed_assumption_inner`). An equality nested under
/// `Not`/`Implies`/`Ite` can carry negative polarity, where the length
/// equality would NOT be entailed, and is never inspected.
pub(in crate::encoder) fn finite_len_pin_binding(expr: &TrustVcExpr) -> Option<(String, i64)> {
    let TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left,
        right,
    } = expr
    else {
        return None;
    };
    // Shape 1: ext-eq against a statically-finite constructor chain.
    if let TrustVcExpr::Var { name, .. } = left.as_ref() {
        if let Some(n) = crate::encoder::AstExpressionParser::finite_seq_literal_len(right) {
            return i64::try_from(n).ok().map(|n| (name.clone(), n));
        }
    }
    if let TrustVcExpr::Var { name, .. } = right.as_ref() {
        if let Some(n) = crate::encoder::AstExpressionParser::finite_seq_literal_len(left) {
            return i64::try_from(n).ok().map(|n| (name.clone(), n));
        }
    }
    // Shape 2: `var.len() == N` (requires-derived literal pin).
    let (name, value) = concrete_collection_len_binding(expr)?;
    if value < 0 {
        return None;
    }
    i64::try_from(value).ok().map(|n| (name, n))
}

fn concrete_collection_len_binding(expr: &TrustVcExpr) -> Option<(String, i128)> {
    let TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left,
        right,
    } = expr
    else {
        return None;
    };
    collection_len_name(left)
        .and_then(|name| int_literal_value(right).map(|value| (name, value)))
        .or_else(|| {
            collection_len_name(right)
                .and_then(|name| int_literal_value(left).map(|value| (name, value)))
        })
}

/// Extract `(collection_name, var_name)` from an assumption of the shape
/// `coll.len() == var` or `var == coll.len()`, where `var` is a plain
/// variable reference. The caller verifies `var`'s declared type and sort.
fn variable_collection_len_binding(expr: &TrustVcExpr) -> Option<(String, String)> {
    let TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left,
        right,
    } = expr
    else {
        return None;
    };
    collection_len_name(left)
        .and_then(|name| var_ref_name(right).map(|var| (name, var)))
        .or_else(|| {
            collection_len_name(right).and_then(|name| var_ref_name(left).map(|var| (name, var)))
        })
}

fn var_ref_name(expr: &TrustVcExpr) -> Option<String> {
    if let TrustVcExpr::Var { name, .. } = expr {
        Some(name.clone())
    } else {
        None
    }
}

/// The collection whose length a `len()` node reads, when that collection is
/// a NAMED variable — the key every length pin (`collection_lengths`,
/// `pinned_seq_lens`) is recorded under.
///
/// SOUNDNESS-CRITICAL: the pin REPLACES the named
/// collection's length term, so the `len()` must be taken of that collection
/// ITSELF — a bare variable, or its identity `view()` when the variable is a
/// `Seq` (a `Vec<T>` is modelled as one). The node's `receiver_name` is not
/// that: lowering threads the ROOT name of a whole method chain through it
/// (`s.push(x).len()` carries `receiver_name == "s"`), and every `vec![..]` /
/// `seq![..]` literal carries its EMPTY constructor's name. Keyed on it,
/// `requires(s.push(1).len() == 3)` pinned `len(s) := 3` (a satisfiable
/// precondition then read as contradictory — `VacuousTruth` on a true claim),
/// and a loop invariant `v.view().len() == 3` over `let v = vec![3, 4, 6]`
/// pinned the EMPTY sequence's length to 3, so the invariant's second encoding
/// in the same query folded to `false` and every obligation of the loop body —
/// `assert!(false)` included — verified. A chain, a literal, a field
/// projection or any other receiver now yields `None`: the equality is still
/// asserted as a term, only the (optional) pin is skipped.
fn collection_len_name(expr: &TrustVcExpr) -> Option<String> {
    let TrustVcExpr::CollectionOp {
        op: CollectionOp::Len,
        receiver,
        ..
    } = expr
    else {
        return None;
    };
    let mut current = receiver.as_ref();
    loop {
        match current {
            TrustVcExpr::Var { name, .. } => return Some(name.clone()),
            TrustVcExpr::CollectionOp {
                op: CollectionOp::View,
                receiver,
                args,
                ..
            } if args.is_empty()
                && matches!(
                    crate::ir_lowering::infer_expr_type(receiver),
                    crate::ir::TrustVcType::Seq(_)
                ) =>
            {
                current = receiver.as_ref();
            }
            _ => return None,
        }
    }
}

fn int_literal_value(expr: &TrustVcExpr) -> Option<i128> {
    if let TrustVcExpr::IntLit { value, .. } = expr {
        Some(*value)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::TrustVcError;
    use crate::prepared_context::prepare_context;
    use crate::vc::VerificationContext;

    /// A cross-reading fact that DOES yield a guard but CANNOT encode: its
    /// variable is never declared in the solve.
    ///
    /// `int_lane_range_guarded` builds `MIN <= x + 1 <= MAX ==> x + 1 > x`
    /// happily (the arithmetic is width-bearing and binder-free), and the
    /// encoder then fails on the undefined variable. That is exactly the split
    /// the doc comment on [`AYEncoder::add_cross_reading_guarded_assumption`]
    /// promises both branches handle the same way.
    fn undeclared_wrapping_fact() -> crate::ir::TrustVcExpr {
        let ty = crate::ir::TrustVcType::Uint { width: 32 };
        let var = crate::ir::TrustVcExpr::Var {
            name: "never_declared_in_this_solve".to_string(),
            ty: ty.clone(),
        };
        crate::ir::TrustVcExpr::Compare {
            op: crate::ir::CompareOp::Gt,
            left: Box::new(crate::ir::TrustVcExpr::Arith {
                op: crate::ir::ArithOp::Add,
                left: Box::new(var.clone()),
                right: Box::new(crate::ir::TrustVcExpr::IntLit {
                    value: 1,
                    ty: ty.clone(),
                }),
                ty,
            }),
            right: Box::new(var),
        }
    }

    /// PIN (int lane): "a fact which does not encode is DROPPED exactly as an
    /// unguardable one would be" is a PROMISE OF BOTH BRANCHES, not of one.
    ///
    /// The int-lane branch used to `return` the encode error, so a legitimate
    /// hypothesis turned an ordinary `by(nonlinear_arith)` or `decreases`
    /// obligation into a hard `VerifyResult::Error` carrying an internal
    /// encoder message that blamed the user's source. With the scope-aware
    /// guard builder in place no fixture in the tree reaches the swallow any
    /// more, so the promise is pinned HERE, directly, rather than left true by
    /// inspection.
    #[test]
    fn an_int_lane_fact_that_does_not_encode_is_dropped_not_propagated() {
        let expr = undeclared_wrapping_fact();
        // NON-VACUITY: the guard really is built, so the test exercises the
        // swallow rather than the `None` early return above it.
        assert!(
            super::super::arith_reading::int_lane_range_guarded(&expr).is_some(),
            "the fact must yield a range guard, or this pins nothing"
        );

        let mut encoder = AYEncoder::new();
        let before = encoder.state.assumption_count;
        let result = encoder.add_cross_reading_guarded_assumption("undeclared", &expr, None, true);

        assert!(
            result.is_ok(),
            "an int-lane cross-reading fact that does not encode must be DROPPED,              not propagated as an error: {result:?}"
        );
        assert_eq!(
            encoder.state.assumption_count, before,
            "a dropped fact must leave no assumption behind"
        );
    }

    /// TWIN (fixed-width lane): the same expression, the same promise, the
    /// branch that always kept it. Pinning both is what makes the doc comment
    /// a property of the FUNCTION rather than of one of its two arms.
    #[test]
    fn a_fixed_width_fact_that_does_not_encode_is_dropped_not_propagated() {
        let expr = undeclared_wrapping_fact();
        let mut encoder = AYEncoder::new();
        let before = encoder.state.assumption_count;
        let result = encoder.add_cross_reading_guarded_assumption("undeclared", &expr, None, false);

        assert!(
            result.is_ok(),
            "a fixed-width cross-reading fact that does not encode must be DROPPED,              not propagated as an error: {result:?}"
        );
        assert_eq!(
            encoder.state.assumption_count, before,
            "a dropped fact must leave no assumption behind"
        );
    }

    /// Route A (#2779) makes every spec-collection `.len()` an unbounded
    /// `Int`, so a length comparison inside a quantifier body — here
    /// `exists(|v: i32| s.push(v).len() == 3)` on `Seq<i32>` — no longer
    /// constructs the BV-vs-Int sort mismatch this case was built to surface.
    /// The push-length is `len(s) + 1` (Int) and the peer `3` is Int, so the
    /// body encodes cleanly. This test now pins the NEW correct behaviour: the
    /// assumption encodes without error, and the obligation is still encoded
    /// with real semantics (verified by the discriminating check below, not a
    /// vacuous pass).
    #[test]
    fn test_add_typed_assumption_push_len_encodes_without_sort_mismatch() {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
        ctx.push_obligation(crate::vc::ProofObligation::assert(
            "exists_push",
            "exists(|v: i32| s.push(v).len() == 3)",
        ));

        let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
        let obligation = prepared
            .obligations
            .first()
            .expect("prepared context should contain the assertion");

        let mut encoder = AYEncoder::new();
        for variable in &prepared.variables {
            encoder
                .declare_variable(variable)
                .expect("variable declaration should succeed");
        }

        // Under Route A the uniform-Int length removes the spurious sort
        // mismatch, so encoding the assumption now succeeds.
        let result = encoder.add_typed_assumption("exists_push_assume", &obligation.expr, None);
        assert!(
            result.is_ok(),
            "Route A uniform-Int length must encode the push-length comparison \
             cleanly (no BV-vs-Int sort mismatch), got: {:?}",
            result
        );

        // Discriminating guard against a vacuous pass: with `s.len() == 2`,
        // `s.push(x).len() == 3` must verify (push adds exactly one element),
        // while `== 4` must NOT. This confirms the cleanly-encoded length is
        // real `len(s) + 1` arithmetic, not a degenerate/unconstrained term.
        let mut ok_ctx = VerificationContext::new();
        ok_ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
        ok_ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ok_ctx.push_obligation(crate::vc::ProofObligation::assume("len2", "s.len() == 2"));
        ok_ctx.push_obligation(crate::vc::ProofObligation::assert(
            "push_len_ok",
            "s.push(x).len() == 3",
        ));
        let ok_result = AYEncoder::verify(&ok_ctx);
        assert!(
            ok_result.is_verified(),
            "push-length (len 2 -> 3) must verify under uniform-Int length, got: {:?}",
            ok_result
        );

        let mut bad_ctx = VerificationContext::new();
        bad_ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
        bad_ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
        bad_ctx.push_obligation(crate::vc::ProofObligation::assume("len2", "s.len() == 2"));
        bad_ctx.push_obligation(crate::vc::ProofObligation::assert(
            "push_len_wrong",
            "s.push(x).len() == 4",
        ));
        let bad_result = AYEncoder::verify(&bad_ctx);
        assert!(
            !bad_result.is_verified(),
            "wrong push-length (len 2 -> 4) must NOT verify (guards against a \
             vacuous clean-encode), got: {:?}",
            bad_result
        );
    }

    #[test]
    fn test_add_typed_assumption_does_not_keep_binding_after_encode_error() {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
        ctx.push_obligation(crate::vc::ProofObligation::assume(
            "bad_eq",
            "x == s.push(1)",
        ));

        let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
        let assumption = prepared
            .obligations
            .first()
            .expect("prepared context should contain the assumption");

        let mut encoder = AYEncoder::new();
        for variable in &prepared.variables {
            encoder
                .declare_variable(variable)
                .expect("variable declaration should succeed");
        }

        let result = encoder.add_typed_assumption("bad_eq", &assumption.expr, None);
        assert!(
            matches!(result, Err(TrustVcError::Encoding { .. })),
            "sort mismatch equality should fail during encoding, got: {:?}",
            result
        );
        assert!(
            encoder.state.equality_assumptions.is_empty(),
            "failed equality assumptions must not leave a phantom binding behind"
        );
    }
}
