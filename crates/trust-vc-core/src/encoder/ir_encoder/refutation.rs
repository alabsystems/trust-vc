//! Structural assertion refutation encoding.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! TrustVc verifies assertions by solving assumptions plus the negated
//! assertion. For quantified assertions, building that negation with a backend
//! `not` can manufacture an existential quantifier and route ay through its
//! incomplete exists E-matching path. This module pushes the negation through
//! common boolean forms and refutes `forall` with fresh witness constants.

use ay_dpll::api::Term;
use num_bigint::BigInt;
use std::collections::HashSet;

use crate::encoder::diagnostics::EncodingApproximation;
use crate::encoder::quantifiers::integer_range_bounds;
use crate::encoder::types::{quantifier_sort_for_type, sort_for_type};
use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{CompareOp, IntConstKind, LogicOp, QuantifierKind, TrustVcExpr, TrustVcType};

/// Maximum finite-domain size for ground-expanding a bounded `forall`
/// refutation. Bounded `forall`s over a wider concrete domain fall through to
/// the symbolic-witness refutation.
const MAX_FINITE_FORALL_EXPAND: u128 = 64;

impl<'a> AstExpressionParser<'a> {
    pub(in crate::encoder) fn encode_refutation_expr(
        &mut self,
        expr: &TrustVcExpr,
    ) -> TrustVcResult<Term> {
        match expr {
            TrustVcExpr::BoolLit(value) => Ok(self.solver.bool_const(!*value)),
            // Refuting a Multiset `==` (e.g. an `ensures a.add(b) == a.add(a)`
            // postcondition, which lowers to `Compare::Eq`) through the default
            // `encode_compare(Ne, …)` builds `not(forall v. count==count)`, which
            // ay handles via its incomplete negated-`forall` path and bails to
            // `QuantifierUnhandled`. Instead build the extensional-equality
            // `forall` and refute it via `encode_forall_refutation`, which
            // introduces a ground Skolem witness `w` and the quantifier-free
            // body `count(lhs, w) != count(rhs, w)`. With compositional `count`
            // (no MBQI-unsafe pointwise axioms in scope) a genuinely false `==`
            // then yields a concrete differing-count Counterexample. Scoped to
            // Multiset so Set/Map/Seq equality refutation is unchanged. #2779.
            TrustVcExpr::Compare {
                op: CompareOp::Eq,
                left,
                right,
            } if self.operands_are_multiset(left, right) => {
                let ext_eq =
                    crate::extensional_eq::build_ext_eq_expr((**left).clone(), (**right).clone());
                if crate::extensional_eq::is_collection_extensional_eq(&ext_eq) {
                    self.encode_refutation_expr(&ext_eq)
                } else {
                    self.encode_compare(CompareOp::Ne, left, right)
                }
            }
            // An equality between two ALPHA-EQUIVALENT quantifiers (same kind,
            // same bound-var types, body identical up to bound-var renaming) is
            // valid by reflexivity — `(forall|i| P(i)) == (forall|j| P(j))` is
            // always true. Its refutation `L != R` is therefore unsatisfiable, so
            // emit `false` directly. This is the body↔spec discharge for the
            // `verify_all_constraints` verdict gate: the body's `seq.all(|c| p(c))`
            // and the contract's `forall|i| i < seq.len() ==> p(&seq[i])` lower to
            // alpha-equivalent `usize`-indexed quantifiers, which ay's (incomplete)
            // BV-quantifier-equality path would otherwise leave `Unknown`. Sound:
            // alpha-equivalent terms are equal in every model; a structural
            // mismatch (e.g. `forall` vs `exists`, or a different predicate) is
            // not alpha-equal, so the guard fails and the query falls through to
            // the solver unchanged (never a false `Verified`).
            TrustVcExpr::Compare {
                op: CompareOp::Eq,
                left,
                right,
            } if quantifiers_alpha_equal(left, right) => Ok(self.solver.bool_const(false)),
            TrustVcExpr::Compare { op, left, right } => {
                self.encode_compare(invert_compare_op(*op), left, right)
            }
            TrustVcExpr::Not(inner) => {
                let inner_term = self.encode_subexpr(inner)?;
                // The refutation of `!P` is `P` itself, which is asserted
                // directly — gate it through the same Bool-sort check as the
                // fallback arms (an ill-typed `assert!(!<non-bool>)` must be a
                // deterministic Error, not a downstream backend failure).
                self.ensure_bool_assert_operand(inner_term)
            }
            TrustVcExpr::Logic { op, left, right } => {
                let left_refuted = self.encode_refutation_expr(left)?;
                let right_refuted = self.encode_refutation_expr(right)?;
                match op {
                    LogicOp::And => self
                        .solver
                        .try_or(left_refuted, right_refuted)
                        .map_err(|e| e.to_string().into()),
                    LogicOp::Or => self
                        .solver
                        .try_and(left_refuted, right_refuted)
                        .map_err(|e| e.to_string().into()),
                }
            }
            TrustVcExpr::Implies {
                premise,
                conclusion,
            } => {
                let premise_term = self.encode_subexpr(premise)?;
                let conclusion_refuted = self.encode_refutation_expr(conclusion)?;
                self.solver
                    .try_and(premise_term, conclusion_refuted)
                    .map_err(|e| e.to_string().into())
            }
            TrustVcExpr::Quantifier {
                kind: QuantifierKind::Forall,
                bound_vars,
                body,
                triggers,
                ..
            } => {
                // Prefer sound finite-domain ground expansion for a bounded,
                // unsigned, collection-indexing `forall`. The symbolic-witness
                // refutation builds `select(s, i)` over a fresh witness `i`,
                // which ay's array+BV solver fails to refute (returning a false
                // SAT with an invalid model) once the Route-A Int length atom
                // poisons the query (#1888/#1932 soundness regression). Expanding
                // `∀i∈[0,hi). body(i)` into `⋁ₖ refute(body[i:=k])` over the
                // concrete domain reads each element at a *literal* index, which
                // is congruent to the ground element assumptions, so the
                // refutation is decided in the sound ground BV+array fragment.
                if let Some(expanded) =
                    self.try_finite_expand_forall_refutation(bound_vars, body, triggers.as_deref())?
                {
                    Ok(expanded)
                } else {
                    self.encode_forall_refutation(bound_vars, body, triggers.as_deref())
                }
            }
            TrustVcExpr::Quantifier {
                kind: QuantifierKind::Exists,
                bound_vars,
                body,
                triggers: Some(trigger_groups),
                ..
            } if !trigger_groups.is_empty() => {
                self.encode_exists_refutation_with_triggers(bound_vars, body, trigger_groups)
            }
            expr if statically_refutes_finite_exists(expr) => Ok(self.solver.bool_const(true)),
            TrustVcExpr::Quantifier {
                kind: QuantifierKind::Exists,
                bound_vars,
                body,
                triggers,
                ..
            } if triggers.as_ref().is_none_or(|groups| groups.is_empty()) => {
                // Triggerless existential (e.g. upstream `exists |n: nat|
                // nat_to_real(n) >= x` with no explicit `#[trigger]`). Infer a
                // trigger from the body so the exact-negation universal
                // `forall n. ¬body(n)` carries an E-matching pattern and the
                // existential is discharged by a ground instance from the proof
                // body — instead of routing through ay's incomplete negated-
                // `exists` CEGQI path.
                //
                // Soundness: inferred triggers only steer E-matching; the emitted
                // refutation is the same real universal regardless of the pattern,
                // so an inferred trigger can never make a false existential appear
                // proven. If inference yields no valid group, fall through to the
                // structural default.
                if let Some(group) = self.infer_exists_refutation_trigger(bound_vars, body) {
                    self.encode_exists_refutation_with_triggers(bound_vars, body, &[group])
                } else if body.contains_forall_quantifier() {
                    // Nested universal inside the existential body. The structural
                    // default below (`not(encode(exists v. BODY))`) hands ay the
                    // alternating negation `forall v. exists … ¬…`, which its
                    // incomplete CEGQI decides UNSOUNDLY — a genuinely-false
                    // `exists i. forall j. P` returns a spurious UNSAT and is
                    // reported Verified (round8 finding 17). Emit the EXACT
                    // structural negation instead (sound; Unknown rather than
                    // Verified when ay cannot instantiate it).
                    self.encode_exists_nested_forall_refutation(bound_vars, body)
                } else {
                    let condition = self.encode_subexpr(expr)?;
                    let condition = self.ensure_bool_assert_operand(condition)?;
                    self.solver
                        .try_not(condition)
                        .map_err(|e| e.to_string().into())
                }
            }
            _ => {
                let condition = self.encode_subexpr(expr)?;
                let condition = self.ensure_bool_assert_operand(condition)?;
                self.solver
                    .try_not(condition)
                    .map_err(|e| e.to_string().into())
            }
        }
    }

    /// Fail-closed Bool-sort gate for top-level assertion refutation operands.
    ///
    /// The structural arms of `encode_refutation_expr` (compare / logic /
    /// implies / quantifier) produce `Bool` by construction, but the fallback
    /// arms encode the raw operand and negate it with a backend `not`. A
    /// non-boolean operand — an ill-typed assert such as `assert!(vec![1, 2,
    /// 3])`, which encodes to an Array term — used to surface as the backend's
    /// `not` sort-mismatch error, which the solve layer classifies as
    /// `Unknown { category: SolverPanic }` (an incompleteness-style verdict).
    /// An ill-typed assert operand is a deterministic spec error, not solver
    /// incompleteness — Verus rejects it at type-check — so reject it here
    /// with a stable fail-closed `Error` instead. The message deliberately
    /// avoids the backend "sort mismatch" phrasing so the solve layer's
    /// `is_sort_mismatch_error` Unknown-mapping does not reclassify it.
    fn ensure_bool_assert_operand(&self, term: Term) -> TrustVcResult<Term> {
        let sort = self.solver.term_sort(term);
        if matches!(sort, ay_core::Sort::Bool) {
            Ok(term)
        } else {
            Err(format!(
                "assertion operand must encode to a Bool term, got {sort}; \
                 non-boolean assert operands are rejected fail-closed"
            )
            .into())
        }
    }

    /// True when both comparison operands are `Multiset<_>` — the gate for
    /// routing a `Compare::Eq` refutation through the extensional-equality
    /// Skolem-witness path (#2779).
    fn operands_are_multiset(&self, left: &TrustVcExpr, right: &TrustVcExpr) -> bool {
        matches!(
            self.infer_effective_expr_type(left, None),
            TrustVcType::Multiset(_)
        ) && matches!(
            self.infer_effective_expr_type(right, None),
            TrustVcType::Multiset(_)
        )
    }

    fn encode_forall_refutation(
        &mut self,
        bound_vars: &[(String, TrustVcType)],
        body: &TrustVcExpr,
        triggers: Option<&[Vec<TrustVcExpr>]>,
    ) -> TrustVcResult<Term> {
        if bound_vars.is_empty() {
            return Err("quantifier requires at least one bound variable"
                .to_string()
                .into());
        }

        let triggerless = triggers.is_none_or(|groups| groups.is_empty());
        let all_finite_width_bound_vars = bound_vars.iter().all(|(_, ty)| ty.bit_width().is_some());
        let collection_concrete_refutation =
            triggerless && body.references_collection() && all_finite_width_bound_vars;
        let bitvector_finite_quantifier = self.solver_mode
            == Some(crate::vc::SolverMode::BitVector)
            && all_finite_width_bound_vars;
        let use_concrete_sorts = collection_concrete_refutation || bitvector_finite_quantifier;
        let finite_concrete_quantifier = use_concrete_sorts && all_finite_width_bound_vars;

        // Quantifier-order soundness (P1-D, refutation path). Refuting `forall i. P`
        // introduces the existential witness `exists i. ¬P`. Modeling that witness
        // as a FREE Skolem constant is sound only when the existential is outermost
        // (the solver's SAT search existentially-closes free vars at the top). When
        // this forall-refutation is itself nested inside a real enclosing quantifier
        // — e.g. the `forall j` emitted while refuting `exists j. forall i. P` — a
        // free witness `i` would leak outside that `forall j` and be closed at the
        // top, silently swapping `∀j.∃i` into `∃i.∀j`. So when nested under a real
        // quantifier, emit a genuine `try_exists` instead of a free witness.
        let emit_real_exists_witness = self.real_quantifier_depth > 0;

        let old_depth = self.quantifier_depth;
        let old_bv_depth = self.bv_quantifier_depth;
        let old_real_depth = self.real_quantifier_depth;
        if emit_real_exists_witness {
            // The witness becomes a real `exists` binder; nested foralls in its
            // body must likewise stay real.
            self.real_quantifier_depth += 1;
        }
        if finite_concrete_quantifier {
            self.quantifier_depth += 1;
            self.bv_quantifier_depth += 1;
        } else if !use_concrete_sorts {
            self.quantifier_depth += 1;
        }
        self.push_quantifier_scope(bound_vars);

        let mut saved_locals = Vec::new();
        let encode_result = (|| -> TrustVcResult<Term> {
            let mut bound_terms = Vec::new();
            for (name, ty) in bound_vars {
                if let TrustVcType::Opaque(type_name) = ty {
                    return Err(format!(
                        "Unsupported type '{}' in forall refutation bound variable '{}'",
                        type_name, name
                    )
                    .into());
                }

                let sort = if use_concrete_sorts {
                    sort_for_type(ty)
                } else {
                    quantifier_sort_for_type(ty)
                };
                let witness_name = format!("__trust_vc_refute_forall_{name}");
                let witness = self.solver.fresh_var(&witness_name, sort);

                if use_concrete_sorts {
                    if let Some(width) = ty.bit_width() {
                        if width > 0 {
                            let signed = matches!(ty, TrustVcType::Int { .. });
                            self.term_widths.insert(witness, (width, signed));
                        }
                    }
                }

                if let Some(scope) = self.quantifier_scopes.last_mut() {
                    scope.add_bound_term(witness);
                }
                saved_locals.push(self.save_local_binding(name.clone(), witness, ty.clone()));
                bound_terms.push(witness);
            }

            let range_guards = if finite_concrete_quantifier {
                Vec::new()
            } else {
                self.build_range_guards(bound_vars, &bound_terms)?
            };
            let guard = conjoin_terms(self, &range_guards)?;

            let before_body = self.overflow_checks.len();
            let body_refuted = self.encode_refutation_expr(body)?;
            let witness_body = if let Some(guard) = guard {
                let not_in_range = self.solver.try_not(guard).map_err(|e| e.to_string())?;
                self.guard_overflow_checks_since(before_body, not_in_range)?;
                self.solver
                    .try_and(guard, body_refuted)
                    .map_err(|e| e.to_string())?
            } else {
                body_refuted
            };
            // When nested under a real quantifier, bind the witness as a genuine
            // existential so quantifier order is preserved (P1-D). Otherwise leave
            // the witness free — it is the outermost existential, soundly closed by
            // the refutation SAT search.
            if emit_real_exists_witness {
                self.solver
                    .try_exists(&bound_terms, witness_body)
                    .map_err(|e| e.to_string().into())
            } else {
                Ok(witness_body)
            }
        })();

        self.restore_locals(saved_locals);
        self.quantifier_depth = old_depth;
        self.bv_quantifier_depth = old_bv_depth;
        self.real_quantifier_depth = old_real_depth;
        self.pop_quantifier_scope();

        if !emit_real_exists_witness {
            // A free-witness refutation Skolemizes the universal; record the
            // approximation. The real-`exists` form is an exact encoding.
            self.diagnostics
                .record(EncodingApproximation::ForallSkolemization);
        }
        encode_result
    }

    /// Sound ground-expansion refutation for a concrete-bounded, unsigned,
    /// collection-indexing `forall`.
    ///
    /// Refuting `∀i. (i < hi) ⇒ P(i)` (or the equivalent `!(i < hi) || P(i)`)
    /// over an *unsigned* `i` means finding a witness `i` with `0 ≤ i < hi` and
    /// `¬P(i)`. When `hi` is a small concrete constant we expand this directly:
    ///
    /// ```text
    /// refute(∀i. guard(i) ⇒ P(i))  ≡  ⋁_{k=0}^{hi-1} refute(P(k))
    /// ```
    ///
    /// This is *exact* (sound and complete): the guard plus unsigned-ness forces
    /// every witness into `[0, hi)`, so OR-ing the per-index refutations equals
    /// the existential. Crucially, each `refute(P(k))` reads the sequence at a
    /// *literal* index `k`, producing `select(s, k_lit)` — congruent with the
    /// ground element assumptions — instead of `select(s, i)` over a symbolic
    /// witness, which ay's array+BV solver mishandles when the Route-A Int
    /// length atom is in scope (the #1888/#1932 false-counterexample).
    ///
    /// Returns `None` (fall through to the symbolic-witness refutation) unless
    /// every guard condition holds: triggerless, exactly one unsigned
    /// finite-width bound variable, the body references a collection, and a
    /// concrete exclusive upper bound `hi ≤ MAX_FINITE_FORALL_EXPAND` is
    /// derivable from the body's guard.
    fn try_finite_expand_forall_refutation(
        &mut self,
        bound_vars: &[(String, TrustVcType)],
        body: &TrustVcExpr,
        triggers: Option<&[Vec<TrustVcExpr>]>,
    ) -> TrustVcResult<Option<Term>> {
        if triggers.is_some_and(|groups| !groups.is_empty()) {
            return Ok(None);
        }
        let [(name, ty)] = bound_vars else {
            return Ok(None);
        };
        // Unsigned finite-width only: unsigned-ness guarantees the witness lower
        // bound is 0 without an explicit guard, so the domain is exactly
        // `[0, hi)`. Signed bound vars could admit negative witnesses outside
        // `[0, hi)`, so they fall through (would be unsound to expand).
        if ty.bit_width().is_none() || !ty.is_unsigned() {
            return Ok(None);
        }
        // Scope to collection bodies — the targeted fix is for symbolic Seq/array
        // index reads; arithmetic-only bounded `forall`s keep their existing
        // refutation behavior to avoid perturbing unrelated proofs.
        if !body.references_collection() {
            return Ok(None);
        }
        let Some(hi) = forall_refute_upper_bound_exclusive(body, name) else {
            return Ok(None);
        };
        if hi > MAX_FINITE_FORALL_EXPAND {
            return Ok(None);
        }

        // `hi == 0`: the guard `i < 0` is unsatisfiable for unsigned `i`, so the
        // `forall` is vacuously true and its refutation is `false`.
        let mut disjuncts: Vec<Term> = Vec::with_capacity(hi as usize);
        for k in 0..hi {
            let substituted = substitute_var_with_int_lit(body, name, k as i128, ty);
            disjuncts.push(self.encode_refutation_expr(&substituted)?);
        }
        let result = match disjuncts.split_first() {
            None => self.solver.bool_const(false),
            Some((&first, rest)) => {
                let mut acc = first;
                for &d in rest {
                    acc = self.solver.try_or(acc, d).map_err(|e| e.to_string())?;
                }
                acc
            }
        };
        // Ground expansion of the negated universal is the same approximation
        // class as Skolemization for diagnostics/demotion purposes.
        self.diagnostics
            .record(EncodingApproximation::ForallSkolemization);
        Ok(Some(result))
    }

    /// Infer a single trigger group for a triggerless existential refutation.
    ///
    /// Uses conservative trigger inference (Verus's default policy) over the
    /// existential body and returns the first group whose union covers every
    /// bound variable. Returns `None` when no admissible trigger exists, in
    /// which case the caller keeps the structural default encoding.
    ///
    /// Only function-application / cast-shaped candidates make usable E-matching
    /// patterns; arithmetic-only bodies produce no candidate and fall through.
    fn infer_exists_refutation_trigger(
        &self,
        bound_vars: &[(String, TrustVcType)],
        body: &TrustVcExpr,
    ) -> Option<Vec<TrustVcExpr>> {
        let groups = crate::trigger_inference::infer_triggers(bound_vars, body);
        groups.into_iter().next().filter(|group| !group.is_empty())
    }

    /// Refute `exists |n: T| #[trigger] g(n) ▷ body(n)` via trigger-driven
    /// witness instantiation rather than the incomplete negated-`exists` CEGQI
    /// path.
    ///
    /// The logical negation of `exists n. body(n)` is the *universal*
    /// `forall n. ¬body(n)`. We emit that universal as a real quantifier whose
    /// E-matching pattern is the user-supplied `#[trigger]` term `g(n)`. This is
    /// the exact negation (sound for proving the existential), but instead of
    /// asking ay to invent a witness it lets ay's E-matching instantiate the
    /// trigger against ground instances of `g` already present in the assumption
    /// set (e.g. a `nat_to_real(a + 1)` introduced by an `assert` in the proof
    /// body). When a ground instance `g(w)` makes `¬body(w)` contradict the
    /// assumptions, the refutation is UNSAT and the existential is discharged
    /// with `n := w` — exactly Verus's archimedean_nat mechanism, without a
    /// general MBQI engine.
    ///
    /// Soundness: the emitted term is implied by the true refutation
    /// `forall n. ¬body(n)` (it *is* that term), so UNSAT of
    /// `assumptions ∧ refutation` implies the original `exists` holds. If the
    /// refutation is satisfiable the model is a genuine universal witness that no
    /// `n` satisfies `body`, so the existential genuinely fails; the SAT branch's
    /// `has_non_skolemized_quantifier` empty-model guard still demotes models the
    /// solver cannot exhibit concretely.
    fn encode_exists_refutation_with_triggers(
        &mut self,
        bound_vars: &[(String, TrustVcType)],
        body: &TrustVcExpr,
        trigger_groups: &[Vec<TrustVcExpr>],
    ) -> TrustVcResult<Term> {
        if bound_vars.is_empty() {
            return Err("quantifier requires at least one bound variable"
                .to_string()
                .into());
        }

        // The bound variables become genuine universally-quantified variables of
        // the refutation `forall n. ¬body(n)`, so they must use the quantifier
        // (Int-style) sorts that the trigger terms are encoded against.
        let old_depth = self.quantifier_depth;
        self.quantifier_depth += 1;
        // The exists refutation emits the real universal `forall n. ¬body(n)`, so
        // its binder is genuinely symbolic (#2779).
        let old_symbolic_depth = self.symbolic_quantifier_depth;
        self.symbolic_quantifier_depth += 1;
        // It is also a real (non-Skolemized) solver quantifier, so any `forall`
        // refuted inside `¬body(n)` must stay a real `exists` rather than leaking a
        // free witness out of this universal's scope (P1-D quantifier-order fix).
        let old_real_depth = self.real_quantifier_depth;
        self.real_quantifier_depth += 1;
        self.push_quantifier_scope(bound_vars);

        let mut saved_locals = Vec::new();
        let encode_result = (|| -> TrustVcResult<Term> {
            let mut bound_terms = Vec::new();
            for (name, ty) in bound_vars {
                if let TrustVcType::Opaque(type_name) = ty {
                    return Err(format!(
                        "Unsupported type '{}' in exists refutation bound variable '{}'",
                        type_name, name
                    )
                    .into());
                }
                let sort = quantifier_sort_for_type(ty);
                let var_term = self.solver.fresh_var(name, sort);
                if let Some(scope) = self.quantifier_scopes.last_mut() {
                    scope.add_bound_term(var_term);
                }
                saved_locals.push(self.save_local_binding(name.clone(), var_term, ty.clone()));
                bound_terms.push(var_term);
            }

            // Range guards constrain the universal to the bound variable's
            // domain. For `exists`, the negation is `forall n. range(n) =>
            // ¬body(n)`, matching the `range(n) && body(n)` shape the positive
            // encoder builds for existential bodies (quantifiers.rs).
            let range_guards = self.build_range_guards(bound_vars, &bound_terms)?;
            let guard = conjoin_terms(self, &range_guards)?;

            // Negate the body directly so a body that is itself quantified or a
            // boolean combination is refuted structurally, then re-apply the
            // domain guard as an implication antecedent.
            let before_body = self.overflow_checks.len();
            let body_refuted = self.encode_refutation_expr(body)?;
            // Any overflow predicates emitted while encoding the body reference
            // the universal bound vars; guard them with `¬range` so they only
            // fire inside the bound-variable domain (mirrors the forall path).
            if let Some(guard) = guard {
                let not_in_range = self.solver.try_not(guard).map_err(|e| e.to_string())?;
                self.guard_overflow_checks_since(before_body, not_in_range)?;
            }
            let guarded_body = if let Some(guard) = guard {
                self.solver
                    .try_implies(guard, body_refuted)
                    .map_err(|e| e.to_string())?
            } else {
                body_refuted
            };

            // Encode the user trigger terms within the quantifier scope so the
            // bound variables resolve to the fresh universal vars. Non-`App`
            // triggers are dropped by `try_forall_with_triggers`; an `App`
            // trigger that fails to reference a bound var is reported as an
            // error there.
            let mut encoded_groups: Vec<Vec<Term>> = Vec::new();
            for group in trigger_groups {
                let mut group_terms = Vec::new();
                for trigger_expr in group {
                    group_terms.push(self.encode_subexpr(trigger_expr)?);
                }
                encoded_groups.push(group_terms);
            }
            let trigger_refs: Vec<&[Term]> = encoded_groups.iter().map(|g| g.as_slice()).collect();

            self.solver
                .try_forall_with_triggers(&bound_terms, guarded_body, &trigger_refs)
                .map_err(|e| {
                    format!("exists refutation: failed to create triggered forall: {e}").into()
                })
        })();

        self.restore_locals(saved_locals);
        self.quantifier_depth = old_depth;
        self.symbolic_quantifier_depth = old_symbolic_depth;
        self.real_quantifier_depth = old_real_depth;
        self.pop_quantifier_scope();

        encode_result
    }

    /// Sound refutation of a triggerless `exists |v..| BODY` whose BODY contains a
    /// nested `forall` (round8 finding 17).
    ///
    /// The structural default `try_not(encode(exists v. BODY))` builds the
    /// alternating negation `¬∃v.(…∀…)` ≡ `∀v.(…∃…)` as a single top-level `not`
    /// over a nested-quantifier term, which ay's incomplete negated-quantifier
    /// normalization decides UNSOUNDLY (spurious UNSAT -> false `Verified`).
    /// We instead build the *exact* structural negation directly:
    ///
    /// * If BODY does not reference any bound `v`, then `∃v:T. C ≡ C` for an
    ///   inhabited integer/char/bool domain `T`; we refute `C` directly, so an
    ///   i-independent inner universal is discharged by the ordinary
    ///   (free-witness) `forall` refutation — keeping a TRUE
    ///   `exists i. forall j. body(j)` Verified.
    /// * Otherwise we emit `∀v. range(v) ⇒ refute(BODY)` as a REAL solver
    ///   `forall` (not a `not(...)`), incrementing `real_quantifier_depth` so the
    ///   nested `forall` refutes to a real `exists` (P1-D). ay then sees a genuine
    ///   `∀∃` formula whose existential it Skolemizes SOUNDLY; if it cannot
    ///   instantiate the goal it returns `Unknown` (sound incompleteness), never a
    ///   spurious `Verified`.
    fn encode_exists_nested_forall_refutation(
        &mut self,
        bound_vars: &[(String, TrustVcType)],
        body: &TrustVcExpr,
    ) -> TrustVcResult<Term> {
        if bound_vars.is_empty() {
            return Err("quantifier requires at least one bound variable"
                .to_string()
                .into());
        }

        // Drop a witness binder whose whole body is independent of it (sound for an
        // inhabited integer/char/bool/nat domain), reducing `∃v. C` to `C`.
        let names: std::collections::HashSet<&str> =
            bound_vars.iter().map(|(n, _)| n.as_str()).collect();
        if bound_vars
            .iter()
            .all(|(_, ty)| type_is_inhabited_scalar(ty))
            && !crate::ir_expr_traversal::expr_references_any_name(body, &names)
        {
            return self.encode_refutation_expr(body);
        }

        // Witness-dependent `∃v.(…∀…)`: the structural negation is a real
        // alternating `∀∃` over a witness depending on `v`, which ay decides
        // UNRELIABLY (a spurious UNSAT would report a false existential as
        // Verified). Record the demoting approximation so an UNSAT/`Verified` on
        // this query is downgraded to `Unknown` (sound; the i-INDEPENDENT case is
        // discharged soundly above and never reaches here).
        self.diagnostics
            .record(EncodingApproximation::NestedExistentialAlternation);

        // Exact structural negation `∀v. range(v) ⇒ refute(BODY)` as a real forall.
        let old_depth = self.quantifier_depth;
        self.quantifier_depth += 1;
        let old_symbolic_depth = self.symbolic_quantifier_depth;
        self.symbolic_quantifier_depth += 1;
        // Real (non-Skolemized) solver quantifier: any `forall` refuted inside
        // `¬BODY` must stay a real `exists` so quantifier order is preserved
        // (P1-D), rather than leaking a free witness out of this universal.
        let old_real_depth = self.real_quantifier_depth;
        self.real_quantifier_depth += 1;
        self.push_quantifier_scope(bound_vars);

        let mut saved_locals = Vec::new();
        let encode_result = (|| -> TrustVcResult<Term> {
            let mut bound_terms = Vec::new();
            for (name, ty) in bound_vars {
                if let TrustVcType::Opaque(type_name) = ty {
                    return Err(format!(
                        "Unsupported type '{}' in exists refutation bound variable '{}'",
                        type_name, name
                    )
                    .into());
                }
                let sort = quantifier_sort_for_type(ty);
                let var_term = self.solver.fresh_var(name, sort);
                if let Some(scope) = self.quantifier_scopes.last_mut() {
                    scope.add_bound_term(var_term);
                }
                saved_locals.push(self.save_local_binding(name.clone(), var_term, ty.clone()));
                bound_terms.push(var_term);
            }

            let range_guards = self.build_range_guards(bound_vars, &bound_terms)?;
            let guard = conjoin_terms(self, &range_guards)?;

            let before_body = self.overflow_checks.len();
            let body_refuted = self.encode_refutation_expr(body)?;
            if let Some(guard) = guard {
                let not_in_range = self.solver.try_not(guard).map_err(|e| e.to_string())?;
                self.guard_overflow_checks_since(before_body, not_in_range)?;
            }
            let guarded_body = if let Some(guard) = guard {
                self.solver
                    .try_implies(guard, body_refuted)
                    .map_err(|e| e.to_string())?
            } else {
                body_refuted
            };

            self.solver
                .try_forall(&bound_terms, guarded_body)
                .map_err(|e| {
                    format!("exists nested-forall refutation: failed to create forall: {e}").into()
                })
        })();

        self.restore_locals(saved_locals);
        self.quantifier_depth = old_depth;
        self.symbolic_quantifier_depth = old_symbolic_depth;
        self.real_quantifier_depth = old_real_depth;
        self.pop_quantifier_scope();

        encode_result
    }
}

/// True for scalar quantifier-bound types whose domain is provably non-empty, so
/// `∃v:T. C ≡ C` (for a body `C` independent of `v`) is a sound rewrite. Used by
/// the nested-forall existential refutation to drop a non-referenced witness.
/// Conservative: only types that are definitely inhabited return `true`.
fn type_is_inhabited_scalar(ty: &TrustVcType) -> bool {
    matches!(
        ty,
        TrustVcType::Int { .. }
            | TrustVcType::Uint { .. }
            | TrustVcType::Char
            | TrustVcType::Bool
            | TrustVcType::Nat
            | TrustVcType::MathInt
            | TrustVcType::Real
    )
}

/// Derive the exclusive upper bound `hi` such that refuting `body` necessarily
/// forces the bound variable `name` into `[0, hi)`.
///
/// Sound only when the returned bound is *necessary* for refutation:
/// - `premise ⇒ concl`: `refute = premise ∧ refute(concl)`, so every conjunct of
///   `premise` holds in any witness — an upper-bound conjunct `name < N` is
///   guaranteed.
/// - `A || B`: `refute = refute(A) ∧ refute(B)`, so if a disjunct is a negated
///   guard `!(name < N)` then `refute` of that disjunct yields `name < N`.
///
/// Returns `None` for any other shape (caller falls through to the symbolic
/// refutation).
fn forall_refute_upper_bound_exclusive(body: &TrustVcExpr, name: &str) -> Option<u128> {
    match body {
        TrustVcExpr::Implies { premise, .. } => upper_bound_from_guard_conjunction(premise, name),
        TrustVcExpr::Logic {
            op: LogicOp::Or,
            left,
            right,
        } => upper_bound_from_negated_guard(left, name)
            .or_else(|| upper_bound_from_negated_guard(right, name)),
        _ => None,
    }
}

/// Upper bound contributed by a (possibly conjunctive) implication premise.
/// Any conjunct that upper-bounds `name` is valid; the tightest is preferred.
fn upper_bound_from_guard_conjunction(premise: &TrustVcExpr, name: &str) -> Option<u128> {
    match premise {
        TrustVcExpr::Logic {
            op: LogicOp::And,
            left,
            right,
        } => {
            let l = upper_bound_from_guard_conjunction(left, name);
            let r = upper_bound_from_guard_conjunction(right, name);
            match (l, r) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (a, b) => a.or(b),
            }
        }
        _ => upper_bound_from_comparison(premise, name),
    }
}

/// Upper bound from a `!(guard)` disjunct, where `guard` upper-bounds `name`.
fn upper_bound_from_negated_guard(expr: &TrustVcExpr, name: &str) -> Option<u128> {
    let TrustVcExpr::Not(inner) = expr else {
        return None;
    };
    upper_bound_from_comparison(inner, name)
}

/// Exclusive upper bound for `name` from a single concrete comparison, or
/// `None` if the comparison does not upper-bound `name` by a non-negative
/// integer literal.
fn upper_bound_from_comparison(cmp: &TrustVcExpr, name: &str) -> Option<u128> {
    let TrustVcExpr::Compare { op, left, right } = cmp else {
        return None;
    };
    let is_var = |e: &TrustVcExpr| matches!(e, TrustVcExpr::Var { name: n, .. } if n == name);
    let nonneg_lit = |e: &TrustVcExpr| match e {
        TrustVcExpr::IntLit { value, .. } if *value >= 0 => Some(*value as u128),
        _ => None,
    };
    match op {
        // i < N  -> [0, N)
        CompareOp::Lt if is_var(left) => nonneg_lit(right),
        // i <= N -> [0, N+1)
        CompareOp::Le if is_var(left) => nonneg_lit(right).map(|n| n + 1),
        // N > i  -> [0, N)
        CompareOp::Gt if is_var(right) => nonneg_lit(left),
        // N >= i -> [0, N+1)
        CompareOp::Ge if is_var(right) => nonneg_lit(left).map(|n| n + 1),
        _ => None,
    }
}

/// Substitute every free occurrence of the variable `name` with an integer
/// literal of type `ty`. Shadowing inner binders that rebind `name` are left
/// untouched (scope-aware fold).
fn substitute_var_with_int_lit(
    expr: &TrustVcExpr,
    name: &str,
    value: i128,
    ty: &TrustVcType,
) -> TrustVcExpr {
    use crate::ir_expr_traversal::{fold_expr_scoped_children, ScopeAwareTrustVcExprFolder};

    struct Subst<'a> {
        target: &'a str,
        value: i128,
        ty: TrustVcType,
    }
    impl ScopeAwareTrustVcExprFolder for Subst<'_> {
        fn fold_expr_scoped(&mut self, expr: TrustVcExpr, bound: &HashSet<&str>) -> TrustVcExpr {
            match expr {
                TrustVcExpr::Var { ref name, .. }
                    if name.as_str() == self.target && !bound.contains(self.target) =>
                {
                    TrustVcExpr::IntLit {
                        value: self.value,
                        ty: self.ty.clone(),
                    }
                }
                other => fold_expr_scoped_children(self, other, bound),
            }
        }
    }

    let mut subst = Subst {
        target: name,
        value,
        ty: ty.clone(),
    };
    subst.fold_expr_scoped(expr.clone(), &HashSet::new())
}

pub(in crate::encoder) fn statically_refutes_finite_exists(expr: &TrustVcExpr) -> bool {
    let TrustVcExpr::Quantifier {
        kind: QuantifierKind::Exists,
        bound_vars,
        body,
        triggers,
        ..
    } = expr
    else {
        return false;
    };
    if triggers.as_ref().is_some_and(|groups| !groups.is_empty()) {
        return false;
    }
    let [(var_name, var_ty)] = bound_vars.as_slice() else {
        return false;
    };
    let Some((lower, upper)) = integer_range_bounds(var_ty) else {
        return false;
    };
    let Some((op, value)) = normalize_bound_var_comparison(var_name, body) else {
        return false;
    };
    comparison_has_no_finite_witness(op, &value, &lower, &upper)
}

fn normalize_bound_var_comparison(
    var_name: &str,
    expr: &TrustVcExpr,
) -> Option<(CompareOp, BigInt)> {
    let TrustVcExpr::Compare { op, left, right } = expr else {
        return None;
    };
    if is_bound_var(var_name, left) {
        let value = integer_constant_value(right)?;
        return Some((*op, value));
    }
    if is_bound_var(var_name, right) {
        let value = integer_constant_value(left)?;
        return Some((flip_compare_op(*op), value));
    }
    None
}

fn is_bound_var(var_name: &str, expr: &TrustVcExpr) -> bool {
    matches!(expr, TrustVcExpr::Var { name, .. } if name == var_name)
}

fn integer_constant_value(expr: &TrustVcExpr) -> Option<BigInt> {
    match expr {
        TrustVcExpr::IntLit { value, .. } => Some(BigInt::from(*value)),
        TrustVcExpr::IntConst { ty, kind } => {
            let (lower, upper) = integer_range_bounds(ty)?;
            match kind {
                IntConstKind::Min => Some(lower),
                IntConstKind::Max => Some(upper - BigInt::from(1)),
            }
        }
        _ => None,
    }
}

fn flip_compare_op(op: CompareOp) -> CompareOp {
    match op {
        CompareOp::Eq => CompareOp::Eq,
        CompareOp::Ne => CompareOp::Ne,
        CompareOp::Lt => CompareOp::Gt,
        CompareOp::Le => CompareOp::Ge,
        CompareOp::Gt => CompareOp::Lt,
        CompareOp::Ge => CompareOp::Le,
    }
}

fn comparison_has_no_finite_witness(
    op: CompareOp,
    value: &BigInt,
    lower: &BigInt,
    upper: &BigInt,
) -> bool {
    match op {
        CompareOp::Eq => value < lower || value >= upper,
        CompareOp::Ne => {
            let only_value = lower + BigInt::from(1);
            &only_value == upper && value == lower
        }
        CompareOp::Lt => value <= lower,
        CompareOp::Le => value < lower,
        CompareOp::Gt => value >= &(upper - BigInt::from(1)),
        CompareOp::Ge => value >= upper,
    }
}

fn invert_compare_op(op: CompareOp) -> CompareOp {
    match op {
        CompareOp::Eq => CompareOp::Ne,
        CompareOp::Ne => CompareOp::Eq,
        CompareOp::Lt => CompareOp::Ge,
        CompareOp::Le => CompareOp::Gt,
        CompareOp::Gt => CompareOp::Le,
        CompareOp::Ge => CompareOp::Lt,
    }
}

fn conjoin_terms(
    parser: &mut AstExpressionParser<'_>,
    terms: &[Term],
) -> TrustVcResult<Option<Term>> {
    let Some((&first, rest)) = terms.split_first() else {
        return Ok(None);
    };
    let term = rest.iter().try_fold(first, |acc, &term| {
        parser.solver.try_and(acc, term).map_err(|e| e.to_string())
    })?;
    Ok(Some(term))
}

/// True iff `left` and `right` are alpha-equivalent quantifiers: same kind, the
/// same number of bound variables with pairwise-equal types, and bodies that are
/// structurally identical after renaming `left`'s bound-variable names to
/// `right`'s. Triggers are intentionally ignored — they steer e-matching but do
/// not change a quantifier's truth value, so two quantifiers that differ only in
/// triggers are still semantically equal.
///
/// Conservative: any structural difference the renaming does not reconcile
/// (notably a nested quantifier that rebinds a differently-named variable) yields
/// `false`, so the caller falls through to the ordinary solver path. It is only
/// ever used to recognize a TRUE equality (returning `false` here can never make
/// a false equality look proven).
fn quantifiers_alpha_equal(left: &TrustVcExpr, right: &TrustVcExpr) -> bool {
    let (
        TrustVcExpr::Quantifier {
            kind: lk,
            bound_vars: lbv,
            body: lbody,
            ..
        },
        TrustVcExpr::Quantifier {
            kind: rk,
            bound_vars: rbv,
            body: rbody,
            ..
        },
    ) = (left, right)
    else {
        return false;
    };
    if lk != rk || lbv.len() != rbv.len() {
        return false;
    }
    let mut rename = std::collections::HashMap::new();
    for ((ln, lt), (rn, rt)) in lbv.iter().zip(rbv.iter()) {
        if lt != rt {
            return false;
        }
        if ln != rn {
            rename.insert(ln.clone(), rn.clone());
        }
    }
    let renamed = if rename.is_empty() {
        (**lbody).clone()
    } else {
        let mut renamer = BoundVarRenamer { rename: &rename };
        crate::ir_expr_traversal::TrustVcExprFolder::fold_expr(&mut renamer, (**lbody).clone())
    };
    &renamed == &**rbody
}

/// Owned-tree folder that renames free `Var` references (and nested quantifier
/// bound-variable declarations) according to a name map. Used to alpha-rename one
/// quantifier body onto another's bound-variable names for the equality check.
struct BoundVarRenamer<'a> {
    rename: &'a std::collections::HashMap<String, String>,
}

impl crate::ir_expr_traversal::TrustVcExprFolder for BoundVarRenamer<'_> {
    fn fold_expr(&mut self, expr: TrustVcExpr) -> TrustVcExpr {
        match expr {
            TrustVcExpr::Var { name, ty } => {
                let name = self.rename.get(&name).cloned().unwrap_or(name);
                TrustVcExpr::Var { name, ty }
            }
            other => crate::ir_expr_traversal::fold_expr_children(self, other),
        }
    }
}
