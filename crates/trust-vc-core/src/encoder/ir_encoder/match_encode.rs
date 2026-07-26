//! Match-expression encoding for TrustVcExpr IR.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::{Sort, Term, TermKind};

use super::match_datatype::*;
use crate::encoder::binding_scope::SavedLocalBinding;
use crate::encoder::datatype::{
    datatype_sort_for, field_sort_for, selector_symbol_name, variant_symbol_name,
};
use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{MatchPattern, TrustVcExpr, TrustVcType};
use crate::ir_expr::MatchArm;
use crate::ir_lowering::infer_expr_type;

impl<'a> AstExpressionParser<'a> {
    /// Encode a match expression as chained if-then-else.
    ///
    /// Overflow checks from arm bodies are guarded behind their arm conditions
    /// so they only fire when the arm is actually taken. Fixes #2114.
    /// Parity: encode_ite overflow guard pattern (mod.rs:327-344).
    #[allow(clippy::indexing_slicing)] // all_arm_conditions[0]/[1..] guarded by is_empty; overflow_checks[start..end] guarded by start < end
    pub(super) fn encode_match(
        &mut self,
        scrutinee: &TrustVcExpr,
        arms: &[MatchArm],
        ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        let scrutinee_term = self.encode_subexpr(scrutinee)?;
        let scrutinee_ty = infer_expr_type(scrutinee);
        if let TrustVcType::Datatype { name, variants } = &scrutinee_ty {
            self.solver
                .try_declare_datatype(&datatype_sort_for(name, variants))
                .map_err(|e| e.to_string())?;
        }
        let constructor_patterns_are_exhaustive =
            constructor_patterns_cover_datatype(&scrutinee_ty, arms);

        crate::encoder::with_flag_unwind_safe!(self.use_int_arithmetic, {
            if ty.bit_width().is_some_and(|width| width > 0) {
                // Datatype carriers are Sort::Int, but a match returning a Rust
                // integer type must encode its arm bodies with BV semantics so the
                // default arm and selector-backed arms stay sort-aligned.
                self.use_int_arithmetic = false;
            }

            let mut result: Option<Term> = None;
            // Track the actual BV width after coercion. When arms have mixed
            // widths (e.g. u8 vs u32), coerce_bv_widths widens to the max.
            // We must register this actual width, not ty's declared width,
            // so downstream coerce_bv_widths comparisons use the right size.
            // Fixes: #2131 term_widths mismatch causing outer == sort panic.
            let mut actual_width: Option<(u32, bool)> = None;

            // Track wildcard overflow check range and all conditional arm
            // conditions for post-loop guarding. The wildcard arm's overflow
            // checks must be guarded by "no conditional arm matched" - without
            // this, wildcard overflow checks fire unconditionally even when a
            // different arm was taken, causing false counterexamples. #2563.
            let mut wildcard_overflow_range: Option<(usize, usize)> = None;
            let mut all_arm_conditions: Vec<Term> = Vec::new();

            // Process arms in reverse to build nested ITEs
            for arm in arms.iter().rev() {
                let saved =
                    self.bind_match_pattern_locals(&arm.pattern, scrutinee_term, &scrutinee_ty)?;

                let overflow_before = self.overflow_checks.len();
                let body_result = self.encode_subexpr(&arm.body);
                // The match guard references the arm's pattern bindings, so it must be
                // encoded WHILE they are still in scope (before restore_locals). Its
                // own partiality checks are tracked in a separate range so they can be
                // guarded by the pattern condition rather than the full arm condition.
                let guard_overflow_before = self.overflow_checks.len();
                let guard_result = arm.guard.as_ref().map(|g| self.encode_subexpr(g));
                self.restore_locals(saved);
                let body_term = body_result?;
                let guard_term = guard_result.transpose()?;

                // Track body width for actual_width computation
                if let Some(&(bw, bs)) = self.term_widths.get(&body_term) {
                    actual_width = Some(match actual_width {
                        Some((aw, asig)) if aw >= bw => (aw, asig),
                        _ => (bw, bs),
                    });
                }

                let pattern_cond =
                    self.encode_match_pattern(&arm.pattern, scrutinee_term, &scrutinee_ty)?;

                // A match guard's own partiality checks (a div/index/shift inside the
                // guard) are evaluated whenever the PATTERN matches (before the guard's
                // value is known), so guard them by `!pattern_cond` — NOT `!arm_cond`.
                // Guarding them by `!arm_cond` would drop them on the `pattern ∧ ¬guard`
                // path where the guard was still evaluated: the false-verify direction.
                if guard_term.is_some() {
                    if let Some(pc) = pattern_cond {
                        let not_pc = self.solver.try_not(pc).map_err(|e| e.to_string())?;
                        self.guard_overflow_checks_since(guard_overflow_before, not_pc)?;
                    }
                }

                // The arm is taken when the pattern matches AND the guard holds. A
                // guarded IRREFUTABLE pattern (pattern_cond == None) is promoted to the
                // guard condition so it becomes a CONDITIONAL arm, never the
                // unconditional default (TRAP #1 — otherwise `_ if g => v` would
                // overwrite the real default even when the guard is false).
                let arm_cond = match (pattern_cond, guard_term) {
                    (None, None) => None,
                    (Some(p), None) => Some(p),
                    (None, Some(g)) => Some(g),
                    (Some(p), Some(g)) => {
                        Some(self.solver.try_and(p, g).map_err(|e| e.to_string())?)
                    }
                };

                if let Some(cond) = arm_cond {
                    all_arm_conditions.push(cond);

                    // Guard THIS arm body's overflow checks (only the body range — the
                    // guard's own checks above are guarded separately by !pattern_cond):
                    // they apply only when the arm is actually taken. #2114, #2236.
                    let not_cond = self.solver.try_not(cond).map_err(|e| e.to_string())?;
                    self.guard_overflow_checks_range(
                        overflow_before,
                        guard_overflow_before,
                        not_cond,
                    )?;

                    match result {
                        Some(else_term) => {
                            // Coerce branch widths before ITE to prevent ay sort
                            // mismatch panics on mixed-width arms (e.g. u8 vs u32).
                            // Parity: encode_ite (mod.rs:357). #2131.
                            let (body_coerced, else_coerced) =
                                self.coerce_bv_widths(body_term, else_term)?;
                            result = Some(
                                self.solver
                                    .try_ite(cond, body_coerced, else_coerced)
                                    .map_err(|e| e.to_string())?,
                            );
                        }
                        None => {
                            // A GUARDED arm can never seed the default: its guard may be
                            // false, so it does not cover its pattern (TRAP #2). Only an
                            // unguarded arm over a constructor-exhaustive datatype may
                            // seed. (constructor_patterns_are_exhaustive is already
                            // false when any arm is guarded — see match_datatype.rs — so
                            // this is defense-in-depth.)
                            if constructor_patterns_are_exhaustive && arm.guard.is_none() {
                                // Constructor patterns over a datatype can safely
                                // seed the default branch when the arm set covers
                                // every variant. Earlier arms still shadow later
                                // ones through the surrounding ITE chain.
                                result = Some(body_term);
                            } else {
                                // #2035: A non-wildcard arm with no else branch
                                // means the match is non-exhaustive. Dropping the
                                // condition would make this arm's body the
                                // unconditional default, which is unsound.
                                return Err(
                                    "Non-exhaustive match: last arm has a condition but no \
                                         wildcard/default arm follows. Every non-wildcard arm \
                                         must have an else branch."
                                        .to_string()
                                        .into(),
                                );
                            }
                        }
                    }
                } else {
                    // Wildcard or irrefutable pattern (unguarded) - track overflow
                    // range for post-loop guarding. The wildcard body only executes
                    // when no conditional arm matched, so its overflow checks must be
                    // guarded accordingly. #2563.
                    wildcard_overflow_range = Some((overflow_before, self.overflow_checks.len()));
                    result = Some(body_term);
                }
            }

            // Guard wildcard arm overflow checks: only fire when no conditional
            // arm matched. Without this, wildcard overflow checks are
            // unconditional, causing false counterexamples. #2563.
            if let Some((start, end)) = wildcard_overflow_range {
                if start < end && !all_arm_conditions.is_empty() {
                    let mut any_cond_matched = all_arm_conditions[0];
                    for &cond in &all_arm_conditions[1..] {
                        any_cond_matched = self
                            .solver
                            .try_or(any_cond_matched, cond)
                            .map_err(|e| e.to_string())?;
                    }
                    for check in &mut self.overflow_checks[start..end] {
                        check.1 = self
                            .solver
                            .try_or(any_cond_matched, check.1)
                            .map_err(|e| e.to_string())?;
                    }
                }
            }

            let mut match_term = result.ok_or_else(|| "Empty match expression".to_string())?;

            // Datatype-valued match results: ay's native datatype theory resolves
            // a selector/tester only on a *syntactic* constructor argument (e.g.
            // `Some_0(Some(z)) == z`) or on a datatype-sorted *variable* via the
            // reconstruction lemma — but NOT on an `ite(...)` tree of constructor
            // leaves, and NOT across an equality that is only *conditionally*
            // propagated during boolean search. A symbolic `match` therefore leaves
            // `Some_0(match_term)` under-constrained: the verifier can pick a field
            // value inconsistent with the taken arm's constructor body (the
            // `option_and_then` symbolic-branch regression: CEX `opt = Some(510)`).
            //
            // Re-establish the lost link soundly and *unconditionally*: bind the
            // result to a fresh datatype const `m == match_term`, then for every
            // tester / selector `f` of the result datatype assert `f(m) == f`
            // distributed to the constructor leaves of the `ite` tree. `f` over a
            // syntactic constructor leaf is evaluated natively, and
            // `f(ite(c,a,b)) == ite(c, f(a), f(b))` is a tautology — so every
            // assertion is a sound consequence of the match's own semantics. These
            // ground equalities live at the top level, where the native theory
            // *does* fire, so downstream `Some_0(m)` resolves per branch.
            if let TrustVcType::Datatype { name, variants } = ty {
                match_term = self.bind_datatype_match_result(match_term, name, variants)?;
            }

            // Register term_widths for the match result using the actual coerced
            // width (max of all arm body widths), not the declared IR type.
            // When arms have mixed widths (e.g. u8 vs u32), coerce_bv_widths
            // widens to u32, but ty remains Uint{8} from IR lowering. Using ty
            // would make downstream coerce_bv_widths see width=8 for a 32-bit
            // term, causing double-extension and sort mismatches. #2131.
            // Signedness: use ty's signedness (not arm-derived) to avoid
            // order-dependent results when arms have mixed signedness. #2565.
            let ty_signed = ty.bit_width().map(|_| !ty.is_unsigned());
            let (reg_width, reg_signed) = actual_width
                .map(|(w, arm_signed)| (w, ty_signed.unwrap_or(arm_signed)))
                .or_else(|| {
                    ty.bit_width()
                        .filter(|&w| w > 0)
                        .map(|w| (w, !ty.is_unsigned()))
                })
                .unwrap_or((0, false));
            if reg_width > 0 {
                self.term_widths.insert(match_term, (reg_width, reg_signed));
            }

            Ok::<_, crate::error::TrustVcError>(match_term)
        })
    }

    /// Re-bind a datatype-valued match result so its testers/selectors resolve.
    ///
    /// Returns a fresh datatype-sorted const `m` constrained `m == match_term`,
    /// plus, for every variant tester `is-V` and every selector `sel` of the
    /// result datatype, the unconditional ground equation `f(m) == f⟂match_term`,
    /// where `f⟂match_term` pushes `f` to the constructor leaves of the `ite`
    /// tree (`f(ite(c,a,b)) == ite(c, f(a), f(b))`). The native datatype theory
    /// evaluates `f` on a syntactic constructor leaf directly, so downstream
    /// `sel(m)` / `is-V(m)` are fully determined per branch.
    ///
    /// Soundness: every emitted fact is a logical consequence of `match_term`'s
    /// own meaning (ITE pushing is a tautology; constructor-leaf evaluation is the
    /// native datatype axiom). It only *adds* sound equalities — it can never make
    /// a wrong obligation verify.
    fn bind_datatype_match_result(
        &mut self,
        match_term: Term,
        datatype_name: &str,
        variants: &[crate::ir::DatatypeVariant],
    ) -> TrustVcResult<Term> {
        let carrier = self.solver.term_sort(match_term);
        self.solver
            .try_declare_datatype(&datatype_sort_for(datatype_name, variants))
            .map_err(|e| e.to_string())?;

        // Only datatype-sorted ITE trees benefit: a bare leaf (single-arm /
        // constant-folded result that is itself a constructor application or a
        // datatype variable) already resolves natively, so skip the extra const.
        if !matches!(self.solver.term_kind(match_term), TermKind::Ite) {
            return Ok(match_term);
        }

        let m = self
            .solver
            .fresh_var("__trust_vc_match_dt", carrier.clone());
        let m_eq = self
            .solver
            .try_eq(m, match_term)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(m_eq)
            .map_err(|e| e.to_string())?;

        for variant in variants {
            // Tester: is-V(m) == is-V distributed over the ite leaves.
            let constructor_name = variant_symbol_name(datatype_name, &variant.name);
            let tester_on_m = self
                .solver
                .try_datatype_tester(&constructor_name, m)
                .map_err(|e| e.to_string())?;
            let tester_dist =
                self.distribute_datatype_tester_over_ite(&constructor_name, match_term)?;
            let tester_link = self
                .solver
                .try_eq(tester_on_m, tester_dist)
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(tester_link)
                .map_err(|e| e.to_string())?;

            // Selectors: sel(m) == sel distributed over the ite leaves.
            for (index, (field_name, field_ty)) in variant.fields.iter().enumerate() {
                let selector_name =
                    selector_symbol_name(datatype_name, &variant.name, field_name, index);
                let selector_sort = field_sort_for(datatype_name, field_ty);
                let sel_on_m = self
                    .solver
                    .try_datatype_selector(&selector_name, m, selector_sort.clone())
                    .map_err(|e| e.to_string())?;
                let sel_dist = self.distribute_datatype_selector_over_ite(
                    &selector_name,
                    &selector_sort,
                    match_term,
                )?;
                let sel_link = self
                    .solver
                    .try_eq(sel_on_m, sel_dist)
                    .map_err(|e| e.to_string())?;
                self.solver
                    .try_assert_term(sel_link)
                    .map_err(|e| e.to_string())?;
                // Selector results over BV fields need width tracking so the
                // distributed field value coerces consistently downstream.
                if let Some(width) = field_ty.bit_width() {
                    if width > 0 {
                        let signed = !field_ty.is_unsigned();
                        self.term_widths.insert(sel_on_m, (width, signed));
                        self.term_widths.insert(sel_dist, (width, signed));
                    }
                }
            }
        }

        Ok(m)
    }

    /// Push a native datatype tester through an `ite` tree to its leaves.
    fn distribute_datatype_tester_over_ite(
        &mut self,
        constructor: &str,
        term: Term,
    ) -> TrustVcResult<Term> {
        if matches!(self.solver.term_kind(term), TermKind::Ite) {
            let children = self.solver.term_children(term);
            if let [cond, then_branch, else_branch] = children.as_slice() {
                let then_dist =
                    self.distribute_datatype_tester_over_ite(constructor, *then_branch)?;
                let else_dist =
                    self.distribute_datatype_tester_over_ite(constructor, *else_branch)?;
                return self
                    .solver
                    .try_ite(*cond, then_dist, else_dist)
                    .map_err(|e| e.to_string().into());
            }
        }
        self.solver
            .try_datatype_tester(constructor, term)
            .map_err(|e| e.to_string().into())
    }

    /// Push a native datatype selector through an `ite` tree to its leaves:
    /// `f(ite(c,a,b)) == ite(c, f(a), f(b))`, recursing on datatype-sorted then/
    /// else branches. Non-ite (leaf constructor / const / var) arguments get `f`
    /// applied directly — exactly the form ay's native datatype theory evaluates.
    fn distribute_datatype_selector_over_ite(
        &mut self,
        selector: &str,
        result_sort: &Sort,
        term: Term,
    ) -> TrustVcResult<Term> {
        if matches!(self.solver.term_kind(term), TermKind::Ite) {
            let children = self.solver.term_children(term);
            if let [cond, then_branch, else_branch] = children.as_slice() {
                let cond = *cond;
                let then_branch = *then_branch;
                let else_branch = *else_branch;
                let then_dist =
                    self.distribute_datatype_selector_over_ite(selector, result_sort, then_branch)?;
                let else_dist =
                    self.distribute_datatype_selector_over_ite(selector, result_sort, else_branch)?;
                return self
                    .solver
                    .try_ite(cond, then_dist, else_dist)
                    .map_err(|e| e.to_string().into());
            }
        }
        self.solver
            .try_datatype_selector(selector, term, result_sort.clone())
            .map_err(|e| e.to_string().into())
    }

    /// Encode a match pattern into a boolean condition, or None for wildcard.
    fn encode_match_pattern(
        &mut self,
        pattern: &MatchPattern,
        scrutinee: Term,
        scrutinee_ty: &TrustVcType,
    ) -> TrustVcResult<Option<Term>> {
        match pattern {
            MatchPattern::Wildcard => Ok(None),
            MatchPattern::Ident(_) => Ok(None),
            MatchPattern::Constructor { variant_name, .. } => {
                let (datatype_name, _) = datatype_variant(scrutinee_ty, variant_name)?;
                let constructor_name = variant_symbol_name(datatype_name, variant_name);
                let cond = self
                    .solver
                    .try_datatype_tester(&constructor_name, scrutinee)
                    .map_err(|e| e.to_string())?;
                Ok(Some(cond))
            }
            MatchPattern::Struct { variant_name, .. } => {
                let (datatype_name, _) = datatype_variant(scrutinee_ty, variant_name)?;
                let constructor_name = variant_symbol_name(datatype_name, variant_name);
                let cond = self
                    .solver
                    .try_datatype_tester(&constructor_name, scrutinee)
                    .map_err(|e| e.to_string())?;
                Ok(Some(cond))
            }
            MatchPattern::Lit(expr) => {
                let lit_term = self.encode_subexpr(expr)?;
                let eq = self
                    .solver
                    .try_eq(scrutinee, lit_term)
                    .map_err(|e| e.to_string())?;
                Ok(Some(eq))
            }
            MatchPattern::Or(patterns) => {
                let mut conds = Vec::new();
                for p in patterns {
                    if let Some(c) = self.encode_match_pattern(p, scrutinee, scrutinee_ty)? {
                        conds.push(c);
                    } else {
                        return Ok(None);
                    }
                }
                if conds.is_empty() {
                    Ok(None)
                } else {
                    let mut cond_terms = conds.into_iter();
                    let first_cond = cond_terms.next().ok_or_else(|| {
                        "internal encoder error: expected non-empty match OR conditions".to_string()
                    })?;
                    let combined = cond_terms.try_fold(first_cond, |a, b| {
                        self.solver.try_or(a, b).map_err(|e| e.to_string())
                    })?;
                    Ok(Some(combined))
                }
            }
        }
    }

    #[allow(clippy::indexing_slicing)] // per_alt[0] guarded by per_alt.is_empty() continue; per_alt[..n] uses saturating_sub
    fn bind_match_pattern_locals(
        &mut self,
        pattern: &MatchPattern,
        scrutinee: Term,
        scrutinee_ty: &TrustVcType,
    ) -> TrustVcResult<Vec<SavedLocalBinding>> {
        match pattern {
            MatchPattern::Ident(name) => Ok(vec![self.save_local_binding(
                name.clone(),
                scrutinee,
                scrutinee_ty.clone(),
            )]),
            MatchPattern::Constructor {
                variant_name,
                bindings,
                has_rest,
            } => {
                let (datatype_name, variant) = datatype_variant(scrutinee_ty, variant_name)?;
                // With a trailing `..` rest, the LEADING bindings project to the
                // first N field selectors and the remaining fields are ignored
                // (mirror `Struct::has_rest`, which binds only named fields). The
                // `.zip` below truncates to `bindings.len()`, so each leading
                // binding still binds to its EXACT field selector `selector(scrut)`
                // — no havoc, no invented value. The exact-arity equality relaxes
                // to `bindings <= fields` only when `has_rest`.
                let arity_ok = if *has_rest {
                    bindings.len() <= variant.fields.len()
                } else {
                    variant.fields.len() == bindings.len()
                };
                if !arity_ok {
                    return Err(format!(
                        "Constructor pattern '{}' expected {} binding(s), got {}",
                        variant_name,
                        variant.fields.len(),
                        bindings.len()
                    )
                    .into());
                }
                crate::encoder::with_flag_unwind_safe!(self.use_int_arithmetic, {
                    let mut saved = Vec::with_capacity(bindings.len());
                    for (index, (binding_name, (field_name, field_ty))) in
                        bindings.iter().zip(variant.fields.iter()).enumerate()
                    {
                        if crate::match_pattern_scope::is_ignored_match_binding(binding_name) {
                            continue;
                        }
                        let selector_name =
                            selector_symbol_name(datatype_name, variant_name, field_name, index);
                        let field_term = self
                            .solver
                            .try_datatype_selector(
                                &selector_name,
                                scrutinee,
                                field_sort_for(datatype_name, field_ty),
                            )
                            .map_err(|e| e.to_string())?;
                        if let Some(width) = field_ty.bit_width() {
                            if width > 0 {
                                let signed = !field_ty.is_unsigned();
                                self.term_widths.insert(field_term, (width, signed));
                                // Datatype carriers use Sort::Int, but selector
                                // results can reintroduce BV arithmetic into a
                                // parser that started in pure-Int mode.
                                self.use_int_arithmetic = false;
                            }
                        }
                        saved.push(self.save_local_binding(
                            binding_name.clone(),
                            field_term,
                            field_ty.clone(),
                        ));
                    }
                    Ok::<_, crate::error::TrustVcError>(saved)
                })
            }
            MatchPattern::Struct {
                variant_name,
                fields,
                ..
            } => {
                let (datatype_name, variant) = datatype_variant(scrutinee_ty, variant_name)?;
                crate::encoder::with_flag_unwind_safe!(self.use_int_arithmetic, {
                    let mut saved = Vec::new();
                    for field in fields {
                        let Some(binding_name) = &field.binding else {
                            continue;
                        };
                        let (index, field_ty) =
                            datatype_field(variant_name, variant, field.field_name.as_str())?;
                        let selector_name = selector_symbol_name(
                            datatype_name,
                            variant_name,
                            field.field_name.as_str(),
                            index,
                        );
                        let field_term = self
                            .solver
                            .try_datatype_selector(
                                &selector_name,
                                scrutinee,
                                field_sort_for(datatype_name, field_ty),
                            )
                            .map_err(|e| e.to_string())?;
                        if let Some(width) = field_ty.bit_width() {
                            if width > 0 {
                                let signed = !field_ty.is_unsigned();
                                self.term_widths.insert(field_term, (width, signed));
                                self.use_int_arithmetic = false;
                            }
                        }
                        saved.push(self.save_local_binding(
                            binding_name.clone(),
                            field_term,
                            field_ty.clone(),
                        ));
                    }
                    Ok::<_, crate::error::TrustVcError>(saved)
                })
            }
            MatchPattern::Lit(_) | MatchPattern::Wildcard => Ok(vec![]),
            MatchPattern::Or(patterns) => {
                use crate::match_pattern_scope::pattern_bound_names;

                let all_names = pattern_bound_names(pattern);
                if all_names.is_empty() {
                    return Ok(vec![]);
                }
                // De-duplicate: Or unions all alternatives but Rust guarantees
                // each alternative binds the same names.
                let mut canonical: Vec<String> = Vec::new();
                for name in all_names {
                    if !canonical.contains(&name) {
                        canonical.push(name);
                    }
                }

                // Collect per-alternative condition + binding terms.
                let mut alt_info = Vec::new();

                for sub_pat in patterns {
                    let cond = self.encode_match_pattern(sub_pat, scrutinee, scrutinee_ty)?;
                    let sub_saved =
                        self.bind_match_pattern_locals(sub_pat, scrutinee, scrutinee_ty)?;

                    let mut bindings = Vec::new();
                    for name in &canonical {
                        if let (Some(&term), Some(ty)) =
                            (self.local_vars.get(name), self.local_var_types.get(name))
                        {
                            bindings.push((name.clone(), term, ty.clone()));
                        }
                    }

                    self.restore_locals(sub_saved);
                    alt_info.push((cond, bindings));
                }

                // Build ITE-merged term per canonical name.
                // Last alternative is the default; earlier alternatives get
                // ITE conditions so the first matching alt wins.
                let mut saved = Vec::with_capacity(canonical.len());
                for name in &canonical {
                    let per_alt: Vec<(Option<Term>, Term, TrustVcType)> = alt_info
                        .iter()
                        .filter_map(|(cond, bindings)| {
                            bindings
                                .iter()
                                .find(|(n, _, _)| n == name)
                                .map(|(_, term, ty)| (*cond, *term, ty.clone()))
                        })
                        .collect();

                    if per_alt.is_empty() {
                        continue;
                    }

                    let binding_ty = per_alt[0].2.clone();
                    let Some((_, last_term, _)) = per_alt.last() else {
                        continue;
                    };
                    let mut merged = *last_term;

                    // Chain ITEs from second-to-last backwards so that
                    // earlier alternatives take precedence.
                    for entry in per_alt[..per_alt.len().saturating_sub(1)].iter().rev() {
                        if let Some(c) = entry.0 {
                            let (left, right) = self.coerce_bv_widths(entry.1, merged)?;
                            merged = self
                                .solver
                                .try_ite(c, left, right)
                                .map_err(|e| e.to_string())?;
                        } else {
                            // Irrefutable sub-pattern - takes unconditionally.
                            merged = entry.1;
                        }
                    }

                    // Propagate BV width to the final merged ITE term.
                    if let Some(&w) = self.term_widths.get(&per_alt[0].1) {
                        self.term_widths.insert(merged, w);
                    }

                    saved.push(self.save_local_binding(name.clone(), merged, binding_ty));
                }

                Ok(saved)
            }
        }
    }
}
