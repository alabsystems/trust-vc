//! Choose (Hilbert choice / witness extraction) encoding — Part of #2143.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Encodes `choose!(|x: T| cond(x))` as a Skolem uninterpreted function plus
//! a guarded axiom: any established witness for the predicate implies the
//! chosen value satisfies the predicate.
//!
//! Extracted from advanced.rs as part of #2433.

use ay_dpll::api::Term;

use crate::encoder::types::sort_for_type;
use crate::error::TrustVcResult;
use crate::ir::{CompareOp, TrustVcExpr, TrustVcType};

use crate::encoder::AstExpressionParser;

impl<'a> AstExpressionParser<'a> {
    /// Encode `choose!(|x: T| cond(x))` as a Skolem function + axiom.
    ///
    /// 1. Collect free variables in `condition` other than `var_name` (captures).
    /// 2. Look up or create a Skolem UF keyed by `key`.
    /// 3. Declare UF: `__trust_vc_choose_<hash>(captures...) -> T`
    /// 4. Assert: `forall x. cond(x) ==> cond[x := skolem(captures)]`
    /// 5. Return `skolem(captures...)`.
    pub(super) fn encode_choose(
        &mut self,
        var_name: &str,
        var_ty: &TrustVcType,
        condition: &TrustVcExpr,
        key: &str,
        also_assert: Option<&TrustVcExpr>,
    ) -> TrustVcResult<Term> {
        // Collect free variable names referenced in the condition (excluding the bound var).
        let free_vars = super::free_vars::collect_free_vars(condition, var_name);

        // Resolve capture terms and sorts from the current variable context.
        let mut capture_terms = Vec::new();
        let mut capture_sorts = Vec::new();
        for cap_name in &free_vars {
            let term = self
                .local_vars
                .get(cap_name.as_str())
                .or_else(|| self.variables.get(cap_name.as_str()))
                .copied()
                .ok_or_else(|| format!("choose: undefined capture variable '{}'", cap_name))?;
            let ty = self
                .local_var_types
                .get(cap_name.as_str())
                .or_else(|| self.var_types.get(cap_name.as_str()))
                .ok_or_else(|| format!("choose: no type for capture variable '{}'", cap_name))?;
            capture_terms.push(term);
            capture_sorts.push(sort_for_type(ty));
        }

        let return_sort = sort_for_type(var_ty);

        // Look up or create the Skolem function for this key.
        let registry = self
            .choose_registry
            .as_mut()
            .ok_or_else(|| "choose: no choose_registry available (internal error)".to_string())?;

        let (skolem_decl, should_assert_axiom) = if let Some(existing) = registry.get(key) {
            (existing.clone(), false)
        } else {
            // Generate a unique name using registry size as counter.
            let skolem_name = format!("__trust_vc_choose_{}", registry.len());
            let decl = self
                .solver
                .try_declare_fun(&skolem_name, &capture_sorts, return_sort.clone())
                .map_err(|e| format!("choose: failed to declare Skolem: {}", e))?;
            registry.insert(key.to_string(), decl.clone());
            (decl, true)
        };

        // Return the Skolem function applied to captures.
        let result = self
            .solver
            .try_apply(&skolem_decl, &capture_terms)
            .map_err(|e| format!("choose: failed to apply Skolem: {}", e))?;

        if should_assert_axiom {
            // Definitional-equality-choose recognition: when the predicate is
            // `var == g` / `g == var` with `g` free of `var`, the Hilbert choice is
            // DEFINITIONALLY `g` (the unique witness of `{i : i == g}`). Assert the
            // ground fact `result == g` and SKIP the guarded Skolem axiom, which
            // `result == g` strictly subsumes (it makes the conclusion `g == result`
            // valid, so `∀x. (g==x) => (g==result)` holds trivially). This makes the
            // choose value deterministic — instead of relying on the guarded axiom
            // being E-matched at `x := g` (equality is not an E-match trigger, so it
            // otherwise fires only when an incidental reflexive ground term exists:
            // the context-dependent `quantifier-unhandled` Unknown) — AND, for the
            // BV/i32 case, avoids leaving an unhandled guarded quantifier that would
            // itself escalate to `quantifier-unhandled` even once the ground CE is
            // available. SOUND: `result == g` is exactly the guarded axiom
            // instantiated at its own unique witness (`(g==g) => (g==result)` ≡
            // `result==g`) — a valid universal instantiation, model-set-preserving and
            // monotone, so it can never turn SAT into UNSAT (no false-verify); it
            // proves no more than Verus, which resolves `choose|i| i==g` to `g`.
            if let Some(g) = definitional_equality_witness(condition, var_name, var_ty) {
                let g_term = self.encode_trust_vc_expr(g)?;
                let witness_eq = self
                    .solver
                    .try_eq(result, g_term)
                    .map_err(|e| format!("choose: failed to build definitional witness eq: {e}"))?;
                self.solver
                    .try_assert_term(witness_eq)
                    .map_err(|e| format!("choose: failed to assert definitional witness: {e}"))?;
            } else {
                let cond_with_skolem = self
                    .with_local_bindings([(var_name.to_string(), result, var_ty.clone())], |s| {
                        s.encode_trust_vc_expr(condition)
                    })?;

                // BINDER-CAPTURE backstop (see `encoder::binder_capture`):
                // `condition` is re-encoded below with `witness_var` standing
                // in as an ORDINARY TOP-LEVEL term and is then closed under
                // `forall witness_var` — the encode-then-close shape. Watermark
                // the assertion stack so a helper hoist that mentions the
                // witness cannot be silently captured by that binder.
                let capture_watermark = crate::encoder::binder_capture::watermark(self.solver);

                let witness_var = self.solver.fresh_var(var_name, return_sort);
                if let Some(width) = var_ty.bit_width() {
                    if width > 0 {
                        let signed = matches!(var_ty, TrustVcType::Int { .. });
                        self.term_widths.insert(witness_var, (width, signed));
                    }
                }
                // The condition is destined for the body of `forall
                // witness_var`: let the capture-aware helpers (`match_encode.rs`,
                // `arith/int_arith.rs`) INLINE their result rather than hoist a
                // fresh const, as every other wired closure boundary does.
                let witness_condition = crate::encoder::with_flag_unwind_safe!(
                    self.pending_universal_closure,
                    true,
                    {
                        self.with_local_bindings(
                            [(var_name.to_string(), witness_var, var_ty.clone())],
                            |s| s.encode_trust_vc_expr(condition),
                        )
                    }
                )?;
                let witness_antecedent = if var_ty.bit_width().is_none() {
                    let guards = self.build_range_guards(
                        &[(var_name.to_string(), var_ty.clone())],
                        &[witness_var],
                    )?;
                    if let Some((&first, rest)) = guards.split_first() {
                        let guard = rest.iter().try_fold(first, |acc, &term| {
                            self.solver.try_and(acc, term).map_err(|e| e.to_string())
                        })?;
                        self.solver.try_and(guard, witness_condition).map_err(|e| {
                            format!("choose: failed to guard witness antecedent: {e}")
                        })?
                    } else {
                        witness_condition
                    }
                } else {
                    witness_condition
                };
                match crate::encoder::binder_capture::capture_since(
                    self.solver,
                    capture_watermark,
                    &[witness_var],
                ) {
                    Some(capture) => {
                        // Decline the Skolem-witness axiom outright: `result`
                        // stays an unconstrained const of the right sort, so a
                        // goal that needs the chosen value's defining property
                        // gets a counterexample or Unknown — never a false
                        // `Verified` through a captured hoist.
                        crate::encoder::binder_capture::record_capture(
                            &mut self.diagnostics,
                            "choose:skolem_witness",
                            &capture,
                        );
                    }
                    None => {
                        let guarded_axiom = self
                            .solver
                            .try_implies(witness_antecedent, cond_with_skolem)
                            .map_err(|e| {
                                format!("choose: failed to build guarded Skolem axiom: {}", e)
                            })?;
                        let guarded_axiom = self
                            .solver
                            .try_forall(&[witness_var], guarded_axiom)
                            .map_err(|e| {
                                format!("choose: failed to quantify guarded Skolem axiom: {}", e)
                            })?;
                        self.solver
                            .try_assert_term(guarded_axiom)
                            .map_err(|e| {
                                format!("choose: failed to assert guarded Skolem axiom: {}", e)
                            })?;
                    }
                }
            }

            // Emit any attached extra axiom (the multi-binder combined Hilbert
            // axiom) once, alongside the standard Skolem-witness axiom. It is a
            // closed, self-contained predicate over already-declared skolems, so
            // it encodes directly in the current scope.
            if let Some(extra) = also_assert {
                let extra_term = self.encode_trust_vc_expr(extra)?;
                // Trigger-gate: a combined axiom over a spec-fn / opaque predicate
                // (mentions a `FnCall`) is marked `no_mbqi` so it fires ONLY on a
                // genuine ground witness (an asserted witness or a pre-`choose`
                // assumed `exists` Skolemized to fresh consts) and MBQI cannot
                // FABRICATE a witness (that would be a false-verify). A decidable
                // arithmetic combined axiom mentions no fn call and stays
                // unmarked so it verifies via normal instantiation. This mirrors
                // exactly the `trigger_gated` split in `lower_multi_binder_choose_closure`.
                if crate::ir_expr_traversal::expr_mentions_fncall(extra) {
                    self.solver.mark_no_mbqi(extra_term);
                }
                self.solver
                    .try_assert_term(extra_term)
                    .map_err(|e| format!("choose: failed to assert combined choose axiom: {e}"))?;
            }
        }

        // Track width metadata for downstream coercion.
        if let Some(width) = var_ty.bit_width() {
            if width > 0 {
                let signed = matches!(var_ty, TrustVcType::Int { .. });
                self.term_widths.insert(result, (width, signed));
            }
        }

        if matches!(var_ty, TrustVcType::Unit) {
            super::super::unit::assert_unit_term(self.solver, result, "encode choose", var_name)?;
        }
        if matches!(var_ty, TrustVcType::Nat) {
            let zero = self.solver.int_const(0);
            let nonnegative = self
                .solver
                .try_ge(result, zero)
                .map_err(|e| format!("choose: failed to build nat invariant: {}", e))?;
            self.solver
                .try_assert_term(nonnegative)
                .map_err(|e| format!("choose: failed to assert nat invariant: {}", e))?;
        }

        Ok(result)
    }
}

/// If `condition` is a definitional equality `var == g` or `g == var` where `g`
/// is free of `var`, return `g` — the unique witness the Hilbert choice
/// `choose|var| (var == g)` is definitionally forced to. Returns `None` for any
/// other predicate, and (crucially for soundness) when `g` itself mentions `var`
/// (e.g. `i == i + 1`), which is not a singleton definitional witness.
fn definitional_equality_witness<'e>(
    condition: &'e TrustVcExpr,
    var_name: &str,
    var_ty: &TrustVcType,
) -> Option<&'e TrustVcExpr> {
    // SOUNDNESS: only for binder types whose `==` is reflexive-total (`g == g`
    // always holds), so `{i : i == g}` is the singleton `{g}` and `result == g` is
    // forced. Excludes IEEE `Float` (NaN != NaN, so the set can be EMPTY and the
    // choose is arbitrary — asserting `result == g` there is a false-verify) and,
    // conservatively, every non-scalar / potentially-float-bearing type
    // (containers, datatypes, spec-fns, poly): those just fall back to the guarded
    // axiom, which is sound.
    if !is_reflexive_total_eq_type(var_ty) {
        return None;
    }
    let TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left,
        right,
    } = condition
    else {
        return None;
    };
    let left: &TrustVcExpr = left;
    let right: &TrustVcExpr = right;
    let is_binder =
        |e: &TrustVcExpr| matches!(e, TrustVcExpr::Var { name, .. } if name == var_name);
    let g = if is_binder(left) {
        right
    } else if is_binder(right) {
        left
    } else {
        return None;
    };
    // `g` must not itself mention the binder, else `{i : i == g}` is not a
    // singleton (or is empty) and asserting `result == g` would be unsound.
    if super::free_vars::collect_free_vars(g, "")
        .iter()
        .any(|n| n == var_name)
    {
        return None;
    }
    Some(g)
}

/// Types whose `==` is reflexive-total (`x == x` holds for every value), so a
/// predicate `i == g` has the unique solution `i = g`. Deliberately conservative:
/// scalar integer/bool/char/unit/real/string only. EXCLUDES `Float` (IEEE NaN is
/// not equal to itself) and all container / datatype / spec-fn / poly / opaque
/// types (which may transitively contain floats), for which `definitional_
/// equality_witness` must not fire — they fall back to the sound guarded axiom.
fn is_reflexive_total_eq_type(ty: &TrustVcType) -> bool {
    matches!(
        ty,
        TrustVcType::Int { .. }
            | TrustVcType::Uint { .. }
            | TrustVcType::MathInt
            | TrustVcType::Nat
            | TrustVcType::Bool
            | TrustVcType::Char
            | TrustVcType::Unit
            | TrustVcType::Real
            | TrustVcType::StrSlice
            | TrustVcType::String
    )
}
