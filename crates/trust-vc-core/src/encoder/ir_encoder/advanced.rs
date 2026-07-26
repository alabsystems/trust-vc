//! Quantifier encoding for TrustVcExpr IR — Skolemization, triggers, range guards.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Quantifier encoding involves:
//! - Skolemization for trigger-less forall over collections (#2187)
//! - BV vs Int sort selection for bound variables
//! - Trigger validation (#2138) and E-matching trigger encoding
//! - Range guard construction for Int-sorted quantifiers
//! - Tautology short-circuits for trivial bodies (#2062)
//!
//! Choose (Skolem) encoding is in choose.rs. Free-variable collection is
//! in free_vars.rs. Cast, function call, and match encoding live in
//! cast.rs, fn_call.rs, and match_encode.rs.

use ay_dpll::api::Term;

use std::collections::HashSet;

use crate::encoder::types::{quantifier_sort_for_type, sort_for_type};
use crate::error::TrustVcResult;
use crate::ir::{QuantifierKind, TrustVcExpr, TrustVcType};
use crate::ir_expr_traversal::expr_references_any_name;

use crate::encoder::AstExpressionParser;

#[cfg(test)]
#[path = "advanced_tests.rs"]
mod tests;

impl<'a> AstExpressionParser<'a> {
    // =================================================================
    // Quantifiers
    // =================================================================

    /// Encode a universal or existential quantifier.
    pub(super) fn encode_quantifier(
        &mut self,
        kind: QuantifierKind,
        bound_vars: &[(String, TrustVcType)],
        body: &TrustVcExpr,
        triggers: Option<&[Vec<TrustVcExpr>]>,
        trigger_inference_mode: Option<crate::trigger_inference::TriggerInferenceMode>,
    ) -> TrustVcResult<Term> {
        // Defense-in-depth: reject empty bound variables at encoder level (#2083).
        if bound_vars.is_empty() {
            return Err("quantifier requires at least one bound variable"
                .to_string()
                .into());
        }

        // Validate trigger patterns BEFORE entering the quantifier scope or
        // checking for tautology short-circuits (#2138). Invalid triggers (those
        // that don't reference any bound variable) must be rejected regardless
        // of whether the body simplifies to a constant. Without this check, the
        // tautology short-circuit at line ~206 returns Ok(true) for
        // `forall(|x| x == x, triggers=[f(y)])` without ever validating the
        // trigger, masking the invalid `f(y)` reference. Regression from #2034.
        if let Some(trigger_groups) = triggers {
            let bound_names: HashSet<&str> =
                bound_vars.iter().map(|(name, _)| name.as_str()).collect();
            for (gi, group) in trigger_groups.iter().enumerate() {
                for (ti, trigger_expr) in group.iter().enumerate() {
                    if !expr_references_any_name(trigger_expr, &bound_names) {
                        return Err(format!(
                            "trigger[{}][{}] does not reference any bound variable ({:?})",
                            gi,
                            ti,
                            bound_names.iter().collect::<Vec<_>>()
                        )
                        .into());
                    }
                }
            }
        }

        let triggerless_forall =
            kind == QuantifierKind::Forall && triggers.is_none_or(|t| t.is_empty());
        let all_finite_width_bound_vars = bound_vars.iter().all(|(_, ty)| ty.bit_width().is_some());
        let all_native_collection_bound_vars = bound_vars.iter().all(|(_, ty)| {
            ty.bit_width().is_some()
                || matches!(
                    ty,
                    TrustVcType::Bool
                        | TrustVcType::MathInt
                        | TrustVcType::Nat
                        | TrustVcType::TypeParam(_)
                        | TrustVcType::Poly
                )
        });
        let bitvector_finite_quantifier = self.solver_mode
            == Some(crate::vc::SolverMode::BitVector)
            && all_finite_width_bound_vars;

        // Collection quantifiers must bypass trigger inference so they stay on
        // the native collection-sort path even when auto-trigger inference
        // would otherwise invent patterns (#2461). This includes finite-width
        // BV element domains and erased generic domains (`TypeParam`/`Poly`).
        let preserve_collection_bv_path =
            triggerless_forall && body.references_collection() && all_native_collection_bound_vars;

        // Automatic trigger inference (#2461): collection quantifiers skip this
        // step so they stay on the established native collection path. Other
        // trigger-less quantifiers still try inference first; if no trigger is
        // found and the assertion stays ground, we can still switch to concrete
        // sorts below.
        let infer_collection_assumption_triggers =
            self.in_assumption_context && !all_finite_width_bound_vars;
        let inferred_triggers;
        let triggers = if preserve_collection_bv_path && !infer_collection_assumption_triggers {
            triggers
        } else {
            match triggers {
                Some(t) if !t.is_empty() => Some(t),
                _ => {
                    inferred_triggers = crate::trigger_inference::infer_triggers_with_mode(
                        bound_vars,
                        body,
                        trigger_inference_mode.unwrap_or_default(),
                    );
                    if inferred_triggers.is_empty() {
                        None
                    } else {
                        Some(inferred_triggers.as_slice())
                    }
                }
            }
        };

        // Collection quantifiers with trigger-less forall and native collection
        // bound vars are Skolemized to ground formulas with concrete sorts.
        // General arithmetic quantifiers are NOT Skolemized because their bodies
        // may reference outer Int-sorted variables, causing sort mismatches
        // (#2679). Only collection quantifiers are self-contained in their
        // native collection sorts.
        let will_skolemize = preserve_collection_bv_path;
        let preserve_concrete_sorts =
            self.in_assumption_context && self.preserve_assumption_quantifier_sorts;
        let use_concrete_sorts =
            will_skolemize || preserve_concrete_sorts || bitvector_finite_quantifier;
        let finite_concrete_quantifier = use_concrete_sorts && all_finite_width_bound_vars;

        // Quantifier-order soundness (P1-D): a trigger-less assertion-position
        // `forall` is normally Skolemized to a ground guarded body, which is sound
        // only when its bound vars are universally closed at the OUTERMOST scope by
        // verification-by-refutation. If this `forall` is nested inside the scope of
        // a real (already-emitted) solver quantifier — e.g. `exists j. forall i. P`
        // — Skolemizing it would let `i` leak outside the enclosing `exists` and be
        // closed at the top, silently swapping the strong `∃j.∀i.P` into the weak
        // `∀i.∃j.P`. So force such a nested `forall` to stay a real `try_forall`.
        // (Collection-Skolemized foralls keep their established concrete-sort path.)
        let has_real_triggers = triggers.is_some_and(|t| !t.is_empty());
        let nested_under_real = self.real_quantifier_depth > 0;
        let force_forall_real =
            kind == QuantifierKind::Forall && nested_under_real && !will_skolemize;
        // Whether this quantifier is emitted as a real `ay` quantifier (vs a
        // Skolemized ground body). Tracked via `real_quantifier_depth` so any
        // quantifier nested in this body sees whether it is under a real binder.
        let skolemized_forall = kind == QuantifierKind::Forall
            && !has_real_triggers
            && !self.in_assumption_context
            && !force_forall_real;
        let emits_real_quantifier = !skolemized_forall;

        // Enter quantifier scope with explicit bound-variable metadata (#2046).
        let old_depth = self.quantifier_depth;
        let old_bv_depth = self.bv_quantifier_depth;
        // A positive `forall`/`exists` binder is genuinely symbolic (ranges over
        // its whole domain), unlike the ground Skolem witnesses produced by
        // `encode_forall_refutation`. Track it so multiset count reasoning emits
        // the pointwise `forall` axioms here (sound for symbolic binders) and
        // suppresses them in the depth-0 refutation context where they would
        // block a concrete differing-count counterexample (#2779).
        let old_symbolic_depth = self.symbolic_quantifier_depth;
        self.symbolic_quantifier_depth += 1;
        // Track real-quantifier nesting so nested trigger-less foralls are not
        // unsoundly Skolemized out of an enclosing quantifier's scope (P1-D).
        let old_real_depth = self.real_quantifier_depth;
        if emits_real_quantifier {
            self.real_quantifier_depth += 1;
        }
        if finite_concrete_quantifier {
            // Keep arithmetic in BV mode while still marking the body as
            // quantified so overflow/shift side-channel checks stay scoped.
            self.quantifier_depth += 1;
            self.bv_quantifier_depth += 1;
        } else if !use_concrete_sorts {
            // Int-sorted quantifiers use arithmetic mode for their bodies.
            // Concrete-sorted quantifiers stay in the normal BV/array mode.
            self.quantifier_depth += 1;
        }
        self.push_quantifier_scope(bound_vars);

        // Declare bound variables with appropriate sort
        let mut saved_locals = Vec::new();
        let mut bound_collection_terms = Vec::new();
        let encode_result = (|| -> TrustVcResult<Term> {
            let mut bound_terms = Vec::new();
            let mut user_bound_terms = Vec::new();
            for (name, ty) in bound_vars {
                if let TrustVcType::Opaque(type_name) = ty {
                    let quantifier_name = match kind {
                        QuantifierKind::Forall => "forall",
                        QuantifierKind::Exists => "exists",
                    };
                    return Err(format!(
                        "Unsupported type '{}' in {} bound variable '{}'",
                        type_name, quantifier_name, name
                    )
                    .into());
                }
                let sort = if use_concrete_sorts {
                    // Preserve concrete sorts for Skolemized quantifiers and for
                    // scoped forall-by facts reintroduced as assumptions.
                    sort_for_type(ty)
                } else {
                    quantifier_sort_for_type(ty)
                };
                let var_term = self.solver.fresh_var(name, sort);

                // Register BV width info for concrete-sorted bound vars so that
                // coerce_seq_index uses zero-extend instead of int2bv (#2187, #2551).
                if use_concrete_sorts {
                    if let Some(width) = ty.bit_width() {
                        if width > 0 {
                            let signed = matches!(ty, TrustVcType::Int { .. });
                            self.term_widths.insert(var_term, (width, signed));
                        }
                    }
                }

                // Register bound term in quantifier scope for targeted bounds
                // check skipping (#2231 Finding 1).
                if let Some(scope) = self.quantifier_scopes.last_mut() {
                    scope.add_bound_term(var_term);
                }

                saved_locals.push(self.save_local_binding(name.clone(), var_term, ty.clone()));
                user_bound_terms.push(var_term);
                bound_terms.push(var_term);
                if ty.is_collection() {
                    let extra_terms = self.register_bound_collection_meta(name, ty, var_term)?;
                    bound_collection_terms.push(var_term);
                    bound_terms.extend(extra_terms);
                }
            }

            // Range guards: skip for Skolemized forall — BV width already
            // constrains the domain exactly (u64 = 0..2^64-1, i32 = -2^31..2^31-1
            // via signed BV interpretation). Int-sorted quantifiers still need
            // explicit range guards because Sort::Int is unbounded.
            let range_guards = if finite_concrete_quantifier {
                Vec::new()
            } else if preserve_concrete_sorts {
                let guarded_vars: Vec<(String, TrustVcType)> = bound_vars
                    .iter()
                    .filter(|(_, ty)| ty.bit_width().is_none())
                    .cloned()
                    .collect();
                let guarded_terms: Vec<Term> = bound_vars
                    .iter()
                    .zip(user_bound_terms.iter())
                    .filter(|((_, ty), _)| ty.bit_width().is_none())
                    .map(|(_, term)| *term)
                    .collect();
                self.build_range_guards(&guarded_vars, &guarded_terms)?
            } else {
                self.build_range_guards(bound_vars, &user_bound_terms)?
            };

            // Encode the body in quantifier scope.
            let before_body = self.overflow_checks.len();
            let body_term = self.encode_subexpr(body)?;

            // Short-circuit: if the body is a constant that makes the quantifier
            // trivially true/false, skip quantifier creation entirely. This avoids
            // ay-dpll CEGQI returning Unknown on quantifiers with trivial bodies
            // like `forall(|j: u32| j + 1 >= 0)` where the comparison was already
            // simplified to `true` by `simplify_unsigned_zero_compare` (#2062).
            let true_const = self.solver.bool_const(true);
            let false_const = self.solver.bool_const(false);
            match kind {
                QuantifierKind::Forall if body_term == true_const => return Ok(true_const),
                QuantifierKind::Exists if body_term == false_const => return Ok(false_const),
                _ => {}
            }

            // Compute range guard conjunction (reusable for overflow checks + body).
            let guard_conjunction = if let Some((&first, rest)) = range_guards.split_first() {
                Some(rest.iter().try_fold(first, |a, &b| {
                    self.solver.try_and(a, b).map_err(|e| e.to_string())
                })?)
            } else {
                None
            };

            // Guard overflow checks from body with range constraints (#1849).
            // Without this, overflow predicates reference unbounded Int-sorted
            // variables and check_overflow_predicates rejects with spurious
            // counterexamples (e.g., x = -1000 for a u8 bound variable).
            if let Some(guard) = guard_conjunction {
                let not_in_range = self.solver.try_not(guard).map_err(|e| e.to_string())?;
                self.guard_overflow_checks_since(before_body, not_in_range)?;
            }

            // Combine range guards with body.
            let guarded_body = if let Some(guard) = guard_conjunction {
                match kind {
                    QuantifierKind::Forall => self
                        .solver
                        .try_implies(guard, body_term)
                        .map_err(|e| e.to_string())?,
                    QuantifierKind::Exists => self
                        .solver
                        .try_and(guard, body_term)
                        .map_err(|e| e.to_string())?,
                }
            } else {
                body_term
            };

            // Encode trigger patterns for E-matching (broadcast lemmas).
            // Each trigger group is a Vec<TrustVcExpr>; we encode each
            // expression to a ay Term within the quantifier scope.
            let encoded_triggers = if let Some(trigger_groups) = triggers {
                let mut groups: Vec<Vec<Term>> = Vec::new();
                for group in trigger_groups {
                    let mut group_terms = Vec::new();
                    for trigger_expr in group {
                        group_terms.push(self.encode_subexpr(trigger_expr)?);
                    }
                    groups.push(group_terms);
                }
                Some(groups)
            } else {
                None
            };

            // Resolution B: eager-Skolemize a TOP-LEVEL positive assumption
            // existential. `skolemize_top_level_assumption_exists` is set ONLY by
            // `add_typed_assumption_inner` for a literal top-level `Exists`
            // assumption (never on the goal/refutation path), and `old_real_depth
            // == 0` confines firing to the OUTERMOST binder (a nested existential
            // sits at depth >= 1, since this `exists` bumped `real_quantifier_depth`
            // before its body was encoded), so Skolem CONSTANTS — not functions —
            // are correct. Asserting `guarded_body` directly encodes `∃v. guard(v)
            // & body(v)` as `guard(c) & body(c)` over the fresh consts `c` already
            // minted PRE-watermark by `fresh_var`, so a `no_mbqi` axiom can
            // E-match the assumed witness. Equisatisfiable rewrite of an
            // assumption ⇒ cannot strengthen it ⇒ cannot introduce a false-verify.
            let skolemize_assumed_exists = kind == QuantifierKind::Exists
                && self.skolemize_top_level_assumption_exists
                && old_real_depth == 0;
            if skolemize_assumed_exists {
                return Ok(guarded_body);
            }

            // Create the quantifier term, with triggers when available.
            let quantifier = match (kind, &encoded_triggers) {
                (QuantifierKind::Forall, Some(groups)) if !groups.is_empty() => {
                    let trigger_refs: Vec<&[Term]> = groups.iter().map(|g| g.as_slice()).collect();
                    self.solver
                        .try_forall_with_triggers(&bound_terms, guarded_body, &trigger_refs)
                        .map_err(|e| format!("Failed to create forall with triggers: {}", e))?
                }
                (QuantifierKind::Exists, Some(groups)) if !groups.is_empty() => {
                    let trigger_refs: Vec<&[Term]> = groups.iter().map(|g| g.as_slice()).collect();
                    self.solver
                        .try_exists_with_triggers(&bound_terms, guarded_body, &trigger_refs)
                        .map_err(|e| format!("Failed to create exists with triggers: {}", e))?
                }
                (QuantifierKind::Forall, _) if self.in_assumption_context || force_forall_real => {
                    // A forall must stay a real quantifier when:
                    //  - in assumption context, to preserve universal strength
                    //    (Skolemization is only correct for assertions negated by
                    //    refutation, #2187); or
                    //  - it is nested inside the scope of a real quantifier
                    //    (`force_forall_real`), where Skolemizing it would leak its
                    //    bound vars out of that scope and swap quantifier order
                    //    (P1-D: `exists j. forall i. P` must not collapse into the
                    //    weaker `forall i. exists j. P`).
                    self.solver
                        .try_forall(&bound_terms, guarded_body)
                        .map_err(|e| e.to_string())?
                }
                (QuantifierKind::Forall, _) => {
                    // Skolemize: bound variables are already fresh unconstrained
                    // vars from solver.fresh_var(). Return guarded body as ground
                    // formula — no ay quantifier wrapper needed. The verification-
                    // by-refutation framework negates this and checks UNSAT, which
                    // is equivalent to checking the universal. Part of #2187.
                    self.diagnostics.record(
                        super::super::diagnostics::EncodingApproximation::ForallSkolemization,
                    );
                    guarded_body
                }
                (QuantifierKind::Exists, _) => self
                    .solver
                    .try_exists(&bound_terms, guarded_body)
                    .map_err(|e| e.to_string())?,
            };
            Ok(quantifier)
        })();

        // Always restore locals + quantifier scope, including error paths.
        self.restore_locals(saved_locals);
        for term in bound_collection_terms {
            self.collection_meta_by_term.remove(&term);
        }
        self.quantifier_depth = old_depth;
        self.bv_quantifier_depth = old_bv_depth;
        self.symbolic_quantifier_depth = old_symbolic_depth;
        self.real_quantifier_depth = old_real_depth;
        self.pop_quantifier_scope();

        encode_result
    }

    /// Build range guard terms for quantifier-bound integer variables.
    ///
    /// Delegates to `integer_range_bounds` (quantifiers.rs) for the canonical
    /// bounds computation. Uses exclusive upper bound with `lt` to match the
    /// convention in `add_integer_range_guards`. Consolidation: #2231 Finding 3.
    pub(super) fn build_range_guards(
        &mut self,
        bound_vars: &[(String, TrustVcType)],
        bound_terms: &[Term],
    ) -> TrustVcResult<Vec<Term>> {
        use crate::encoder::quantifiers::{integer_range_bounds, lower_bound_only};

        let mut guards = Vec::new();
        for ((_, ty), term) in bound_vars.iter().zip(bound_terms.iter()) {
            if matches!(ty, TrustVcType::Unit) {
                guards.push(super::super::unit::unit_eq(self.solver, *term)?);
            } else if matches!(ty, TrustVcType::Char) {
                // `char` is a Unicode scalar value: exclude the UTF-16 surrogate
                // band U+D800..=U+DFFF and cap at U+10FFFF rather than using the
                // bare [0, 2^32) bounds (round8 findings 20/21). Single conjoined
                // predicate; the caller conjoins all guards.
                guards.push(self.char_domain_guard(*term)?);
            } else if let Some((lower_val, upper_val)) = integer_range_bounds(ty) {
                let lower_term = self.solver.int_const_bigint(&lower_val);
                let upper_term = self.solver.int_const_bigint(&upper_val);
                guards.push(
                    self.solver
                        .try_ge(*term, lower_term)
                        .map_err(|e| e.to_string())?,
                );
                guards.push(
                    self.solver
                        .try_lt(*term, upper_term)
                        .map_err(|e| e.to_string())?,
                );
            } else if let Some(lower_val) = lower_bound_only(ty) {
                // Lower-only bound (e.g., Nat >= 0). Part of #2418/#2423.
                let lower_term = self.solver.int_const_bigint(&lower_val);
                guards.push(
                    self.solver
                        .try_ge(*term, lower_term)
                        .map_err(|e| e.to_string())?,
                );
            }
        }
        Ok(guards)
    }
}
