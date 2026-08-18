//! Seq map/filter encoders.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::{ArraySort, Sort, Term};

use super::super::AstExpressionParser;
use crate::encoder::types::sort_for_type;
use crate::error::TrustVcResult;
use crate::ir::{TrustVcExpr, TrustVcType};

const FILTER_BOUNDED_MEMBERSHIP_UNROLL_LIMIT: i64 = 2;

/// Number of concrete `0..n` index instances ground-seeded for the `Seq::map`
/// pointwise axiom (see the seeding block in `encode_seq_map`). Matches the
/// native-seq map seed window (`GROUND_SEED_COUNT`) and the `Seq::from_fn` base
/// (`SEQ_FROM_FN_GROUND_SEED_BASE`); each instance is independently guarded by
/// `k < len`, so seeding past the real length is inert (sound), and a concrete
/// index beyond the window stays fail-closed (honest incompleteness).
const SEQ_MAP_GROUND_SEED_COUNT: i64 = 4;

/// Number of ground index instances seeded for `Seq::from_fn` / `Seq::new`
/// when the element sort is a mathematical integer (see `encode_seq_from_fn`).
/// A small base covers symbolic lengths; a literal length seeds up to its
/// concrete value, capped to bound the assertion count.
#[cfg(not(feature = "native-seq"))]
const SEQ_FROM_FN_GROUND_SEED_BASE: i64 = 4;
#[cfg(not(feature = "native-seq"))]
const SEQ_FROM_FN_GROUND_SEED_LIMIT: i64 = 16;

/// Decide how many concrete `0..n` index instances to seed for the
/// `Seq::from_fn` pointwise axiom. A literal length seeds `min(len, LIMIT)`
/// (so a 5-element `Seq::new(5, ..)` covers every in-range index); a symbolic
/// length falls back to the small base count, each instance still guarded by
/// `i < len` so over-seeding past the real length is inert.
#[cfg(not(feature = "native-seq"))]
fn seq_from_fn_ground_seed_count(len_expr: &TrustVcExpr) -> i64 {
    match len_expr {
        TrustVcExpr::IntLit { value, .. } => i64::try_from(*value)
            .ok()
            .filter(|len| *len > SEQ_FROM_FN_GROUND_SEED_BASE)
            .map(|len| len.min(SEQ_FROM_FN_GROUND_SEED_LIMIT))
            .unwrap_or(SEQ_FROM_FN_GROUND_SEED_BASE),
        _ => SEQ_FROM_FN_GROUND_SEED_BASE,
    }
}

/// Whether the `Seq::from_fn` ground seeds already cover EVERY in-range index,
/// which makes the quantified pointwise axiom logically redundant.
///
/// The seeding loop emits, for `k in 0..seed_count`, the instance
/// `bvult(k, len_bv) => result[k] == f(k)`, and the quantified axiom is
/// `forall idx. bvult(idx, len_bv) => result[idx] == f(idx)` — the SAME body
/// over the SAME `len_bv` guard term. So when the set of indices admitted by
/// `bvult(idx, len_bv)` is a subset of the seeded literals `{0..seed_count-1}`,
/// the conjunction of seeds ENTAILS the quantified axiom (every non-vacuous
/// instance is literally one of the seeds; every other instance has a false
/// guard and holds vacuously). Asserting it as well adds no content while
/// forcing the SAT direction — which is what a REFUTATION is — to construct a
/// model satisfying a quantifier over the whole `2^pointer_width` index domain.
///
/// A literal length `n` gives `val(len_bv) == n` (the coercions in
/// `coerce_to_len_width` are value-preserving for `0 <= n <= LIMIT`, far inside
/// every supported pointer width), so `bvult(idx, len_bv)` admits exactly
/// `{0..n-1}`, and the seeds cover it iff `n <= seed_count`. A symbolic length
/// admits an unknown index set and keeps the quantified axiom.
#[cfg(not(feature = "native-seq"))]
fn seq_from_fn_seeds_cover_all_indices(len_expr: &TrustVcExpr) -> bool {
    let TrustVcExpr::IntLit { value, .. } = len_expr else {
        return false;
    };
    // A negative literal would coerce to a huge unsigned `len_bv`, admitting
    // indices no seed covers — keep the axiom.
    let Ok(len) = i64::try_from(*value) else {
        return false;
    };
    (0..=seq_from_fn_ground_seed_count(len_expr)).contains(&len)
}

struct SeqFilterBoundedPack<'a> {
    source: Term,
    source_name: Option<&'a str>,
    source_len: Term,
    result: Term,
    result_len: Term,
    param_name: &'a str,
    param_ty: &'a TrustVcType,
    pred_body_expr: &'a TrustVcExpr,
}

impl<'a> AstExpressionParser<'a> {
    /// Encode `Seq::from_fn(len, f)` as a fresh sequence with a guarded
    /// pointwise axiom:
    ///   result.len() == len
    ///   forall i. i < len => result[i] == f(i)
    #[cfg(not(feature = "native-seq"))]
    pub(in crate::encoder) fn encode_seq_from_fn(
        &mut self,
        args: &[TrustVcExpr],
        return_ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        let [len_expr, TrustVcExpr::SpecClosure { params, body, ty }] = args else {
            return Err("Seq::from_fn expects a length plus SpecFn::new(...)"
                .to_string()
                .into());
        };
        let [(idx_param_name, idx_param_ty)] = params.as_slice() else {
            return Err("Seq::from_fn requires a unary SpecFn<usize, T>"
                .to_string()
                .into());
        };
        let TrustVcType::Seq(elem_ty) = return_ty else {
            return Err("Seq::from_fn builtin must return Seq<T>".to_string().into());
        };
        if idx_param_ty
            != &(TrustVcType::Uint {
                width: crate::ir::pointer_width(),
            })
        {
            return Err(format!(
                "Seq::from_fn requires SpecFn<usize, T>, got SpecFn<{}, _>",
                idx_param_ty.to_type_string()
            )
            .into());
        }
        let TrustVcType::SpecFn(_, ret_ty) = ty else {
            return Err("Seq::from_fn requires a SpecFn argument".to_string().into());
        };
        if ret_ty.as_ref() != elem_ty.as_ref() {
            return Err(format!(
                "Seq::from_fn closure returns '{}', but result element type is '{}'",
                ret_ty.to_type_string(),
                elem_ty.to_type_string()
            )
            .into());
        }

        let pw = crate::ir::pointer_width();
        let len_bv = self.encode_subexpr(len_expr)?;
        let len_bv = self.coerce_to_len_width(len_bv)?;
        // Route A (#2779): store the spec length as Int; keep a BV view of the
        // user-supplied length for the BV-indexed range guard.
        let len_int = self
            .solver
            .try_bv2int(len_bv)
            .map_err(|e| format!("Seq::from_fn length to Int: {e}"))?;
        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(pw),
            element_sort: sort_for_type(elem_ty),
        }));
        let result = self.solver.fresh_var("__seq_from_fn", result_sort);
        self.register_collection_meta(
            result,
            super::super::parser_state::CollectionMeta {
                kind: super::super::parser_state::CollectionKind::Seq,
                len_term: Some(len_int),
                len_guard: None,
                elem_ty: Some(elem_ty.as_ref().clone()),
                key_ty: None,
                dom_term: None,
            },
        );

        let bound_idx = self.solver.fresh_var("__seq_from_fn_idx", Sort::bitvec(pw));
        self.term_widths.insert(bound_idx, (pw, false));
        let mapped_body = {
            let old_depth = self.quantifier_depth;
            let old_bv_depth = self.bv_quantifier_depth;
            self.quantifier_depth += 1;
            self.bv_quantifier_depth += 1;
            let result = self.with_local_bindings(
                [(idx_param_name.clone(), bound_idx, idx_param_ty.clone())],
                |s| s.encode_trust_vc_expr(body),
            );
            self.quantifier_depth = old_depth;
            self.bv_quantifier_depth = old_bv_depth;
            result?
        };
        let mapped_body = self.coerce_value_for_seq_elem_ty(mapped_body, elem_ty)?;
        let result_elem = self
            .solver
            .try_select(result, bound_idx)
            .map_err(|e| format!("Seq::from_fn result select: {e}"))?;
        let elem_eq = self
            .solver
            .try_eq(result_elem, mapped_body)
            .map_err(|e| format!("Seq::from_fn element equality: {e}"))?;
        let idx_in_range = self
            .solver
            .try_bvult(bound_idx, len_bv)
            .map_err(|e| format!("Seq::from_fn index guard: {e}"))?;
        let guarded_body = self
            .solver
            .try_implies(idx_in_range, elem_eq)
            .map_err(|e| format!("Seq::from_fn guarded body: {e}"))?;
        let axiom = self
            .solver
            .try_forall_with_triggers(&[bound_idx], guarded_body, &[&[result_elem]])
            .map_err(|e| format!("Seq::from_fn forall: {e}"))?;
        // Assert the quantified pointwise axiom ONLY when the ground seeds below
        // do not already cover every in-range index. When they do
        // (`seq_from_fn_seeds_cover_all_indices`), the seed conjunction entails
        // this axiom verbatim, so asserting it adds ZERO logical content — but it
        // does force a refutation (a SAT query) to build a model satisfying a
        // quantifier ranging over the entire `2^pointer_width` index domain, which
        // is what made `Seq::new` refutations time out. Dropping an entailed
        // assumption cannot change the assumption set's models, so the encoder
        // refutes exactly the same programs; and in general dropping an assumption
        // can only SHRINK the `Verified` set and GROW the refuted set, never the
        // reverse — a false `Verified` cannot be introduced this way.
        if !seq_from_fn_seeds_cover_all_indices(len_expr) {
            self.solver
                .try_assert_term(axiom)
                .map_err(|e| format!("Seq::from_fn assert axiom: {e}"))?;
        }

        // Ground-instance seeding for the pointwise index axiom.
        //
        // When the element type is a mathematical integer (`int`/`nat`, which
        // map to `Sort::Int`), the closure body crosses the BV->Int boundary by
        // applying `bv2int` to the BV-sorted bound index (e.g. `i as int`). ay's
        // quantifier instantiation does not fire e-matching across that boundary:
        // the guarded pointwise axiom
        //   forall i. i < len ==> result[i] == f(i)
        // — itself a TRUE fact — then cannot discharge a concrete-index goal such
        // as `s.index(3) == 30`, and ay returns a spurious counterexample model in
        // which the in-range element is left unconstrained.
        //
        // Fixed-width (BV) element types DO e-match the quantified axiom for a
        // DIRECT literal select `result[k]` (the goal term is itself the
        // trigger), but NOT through a subrange/shift view: `subrange(result, a,
        // b)` is encoded as a fresh `__seq_shifted` array whose ground instances
        // pin `shifted[i] == result[bvadd(i, a)]`. The from_fn trigger
        // `result[idx]` is not reliably instantiated at that *compound* `bvadd`
        // source index, so `result[a + i]` is left under-constrained and an
        // ext-eq unroll over the subrange (`subrange(Seq::new(i32), a, b) =~=
        // ...`) fabricates a model in which a VALID equality is refuted (a false
        // counterexample).
        //
        // We therefore — for ALL element sorts, BV included — additionally emit
        // *ground* instances of the SAME axiom at concrete indices `0..n`, each
        // guarded by `i < len`. For BV elements the literal seed `result[k] ==
        // f(k)` connects to the shifted view by BV congruence (`bvadd(i, a)`
        // equals the literal `a + i`, so `result[bvadd(i, a)]` is congruent to
        // the seeded `result[a + i]`), resolving the subrange element at a
        // concrete index. Soundness in BOTH directions is preserved because every
        // seeded instance is a theorem implied by the constructor's spec (the
        // value at index `i` is exactly `f(i)`, coerced to the declared element
        // width/sign by `coerce_value_for_seq_elem_ty`):
        //   * a TRUE in-range goal now discharges (the value is pinned to f(i));
        //   * a FALSE in-range goal still fails — the seeded equality contradicts
        //     the wrong claim, yielding a counterexample, never a false Verified;
        //   * out-of-range indices stay unconstrained (the `i < len` guard is
        //     false), so the Seq::index precondition behavior is unchanged.
        {
            let seed_count = seq_from_fn_ground_seed_count(len_expr);
            for k in 0..seed_count {
                let k_bv = self
                    .solver
                    .try_bv_const(k, pw)
                    .map_err(|e| format!("Seq::from_fn ground index: {e}"))?;
                self.term_widths.insert(k_bv, (pw, false));
                let mapped_k = {
                    // Encode the body with the index bound to the concrete
                    // constant. Bump the quantifier depth like the quantified
                    // path so closure-body arithmetic does not leak overflow
                    // obligations into the enclosing scope.
                    let old_depth = self.quantifier_depth;
                    let old_bv_depth = self.bv_quantifier_depth;
                    self.quantifier_depth += 1;
                    self.bv_quantifier_depth += 1;
                    let r = self.with_local_bindings(
                        [(idx_param_name.clone(), k_bv, idx_param_ty.clone())],
                        |s| s.encode_trust_vc_expr(body),
                    );
                    self.quantifier_depth = old_depth;
                    self.bv_quantifier_depth = old_bv_depth;
                    r?
                };
                let mapped_k = self.coerce_value_for_seq_elem_ty(mapped_k, elem_ty)?;
                let result_elem_k = self
                    .solver
                    .try_select(result, k_bv)
                    .map_err(|e| format!("Seq::from_fn ground select: {e}"))?;
                let elem_eq_k = self
                    .solver
                    .try_eq(result_elem_k, mapped_k)
                    .map_err(|e| format!("Seq::from_fn ground equality: {e}"))?;
                let k_in_range = self
                    .solver
                    .try_bvult(k_bv, len_bv)
                    .map_err(|e| format!("Seq::from_fn ground index guard: {e}"))?;
                let guarded_k = self
                    .solver
                    .try_implies(k_in_range, elem_eq_k)
                    .map_err(|e| format!("Seq::from_fn ground guarded body: {e}"))?;
                self.solver
                    .try_assert_term(guarded_k)
                    .map_err(|e| format!("Seq::from_fn ground assert: {e}"))?;
            }
        }

        Ok(result)
    }

    /// Encode `Seq::map_values(f)` as a fresh sequence with pointwise equality.
    ///
    /// Encoding:
    ///   result.len() == source.len()
    ///   forall i. result[i] == f(source[i])
    pub(in crate::encoder) fn encode_seq_map_values(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let rname = receiver_name.unwrap_or("<anonymous>");
        let [TrustVcExpr::SpecClosure { params, body, ty }] = args else {
            return Err(
                "Seq::map_values expects exactly one SpecFn::new(...) argument"
                    .to_string()
                    .into(),
            );
        };
        let [(param_name, param_ty)] = params.as_slice() else {
            return Err(
                "Seq::map_values currently supports unary SpecFn closures only"
                    .to_string()
                    .into(),
            );
        };
        let TrustVcType::SpecFn(_, ret_ty) = ty else {
            return Err("Seq::map_values requires a SpecFn argument"
                .to_string()
                .into());
        };

        let len = self
            .lookup_collection_len(receiver, receiver_name)
            .ok_or_else(|| format!("No length tracked for Seq '{}' in map_values()", rname))?;
        // BV view of the (Int) length for the BV-indexed range guard (#2779).
        //
        // The SOURCE length can itself be the result of a length-DECREASING view
        // (`skip(n)` with `n > len`, `subrange(i, j)` with `i > j`,
        // `drop_first`/`drop_last` on empty) whose length goes NEGATIVE exactly
        // when that op's Verus precondition is violated. The unconditional
        // `len_index_companion` would assert `bv2int(companion) == len`, which is
        // UNSAT for a negative `len` and POISONS the whole solver context into a
        // vacuous proof — silently discharging BOTH the violated source
        // precondition AND a false downstream goal (e.g. `.len() == 99`). Use the
        // precondition-guarded companion so a negative source length leaves the
        // bridge inert (-> Counterexample/Unknown) instead of poisoning
        // (#soundness skip/subrange/drop — map_values consumer site).
        let len_bv = self.len_index_companion_maybe_negative(len)?;
        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(crate::ir::pointer_width()),
            element_sort: sort_for_type(ret_ty),
        }));
        let result = self.solver.fresh_var("__seq_map_values", result_sort);
        self.register_collection_meta(
            result,
            super::super::parser_state::CollectionMeta {
                kind: super::super::parser_state::CollectionKind::Seq,
                len_term: Some(len),
                len_guard: None,
                elem_ty: Some(ret_ty.as_ref().clone()),
                key_ty: None,
                dom_term: None,
            },
        );

        let bound_idx = self
            .solver
            .fresh_var("__seq_map_idx", Sort::bitvec(crate::ir::pointer_width()));
        let source_elem = self
            .solver
            .try_select(receiver, bound_idx)
            .map_err(|e| e.to_string())?;
        if let Some(info) = self.element_width_info(receiver, receiver_name) {
            self.term_widths.insert(source_elem, info);
        }
        let bound_value = self.coerce_element_for_int_mode(source_elem, receiver, receiver_name)?;

        let mapped_body = self.with_closure_body_bindings(
            [(param_name.clone(), bound_value, param_ty.clone())],
            |s| s.encode_trust_vc_expr(body),
        )?;
        let mapped_body = self.coerce_value_for_store_in_int_mode(mapped_body, result, None)?;
        let result_elem = self
            .solver
            .try_select(result, bound_idx)
            .map_err(|e| e.to_string())?;
        let body = self
            .solver
            .try_eq(result_elem, mapped_body)
            .map_err(|e| e.to_string())?;
        // Range guard: only constrain in-bounds indices (#2572).
        // Without this, the closure is applied to the "junk" region of
        // the SMT array (indices >= len), which can produce unsatisfiable
        // constraints and cause false verification failures.
        let idx_in_range = self
            .solver
            .try_bvult(bound_idx, len_bv)
            .map_err(|e| e.to_string())?;
        let guarded_body = self
            .solver
            .try_implies(idx_in_range, body)
            .map_err(|e| e.to_string())?;
        let axiom = self
            .solver
            .try_forall_with_triggers(&[bound_idx], guarded_body, &[&[result_elem]])
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| e.to_string())?;

        Ok(result)
    }

    /// Encode `Seq::map(f)` as a fresh sequence with indexed pointwise equality.
    ///
    /// Encoding:
    ///   result.len() == source.len()
    ///   forall i. result[i] == f(i, source[i])
    pub(in crate::encoder) fn encode_seq_map(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let rname = receiver_name.unwrap_or("<anonymous>");
        let [TrustVcExpr::SpecClosure { params, body, ty }] = args else {
            return Err("Seq::map expects exactly one SpecFn::new(...) argument"
                .to_string()
                .into());
        };
        let [(idx_param_name, _), (val_param_name, val_param_ty)] = params.as_slice() else {
            return Err("Seq::map requires a 2-parameter SpecFn (index, element)"
                .to_string()
                .into());
        };
        let TrustVcType::SpecFn(_, ret_ty) = ty else {
            return Err("Seq::map requires a SpecFn argument".to_string().into());
        };

        let len = self
            .lookup_collection_len(receiver, receiver_name)
            .ok_or_else(|| format!("No length tracked for Seq '{}' in map()", rname))?;
        // BV view of the (Int) length for the BV-indexed range guard (#2779).
        // Precondition-guarded so a length-DECREASING source view whose
        // precondition is violated (negative length) leaves the bridge inert
        // instead of UNSAT-poisoning the context (#soundness skip/subrange/drop —
        // map consumer site; see `encode_seq_map_values`).
        let len_bv = self.len_index_companion_maybe_negative(len)?;
        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(crate::ir::pointer_width()),
            element_sort: sort_for_type(ret_ty),
        }));
        let result = self.solver.fresh_var("__seq_map", result_sort);
        self.register_collection_meta(
            result,
            super::super::parser_state::CollectionMeta {
                kind: super::super::parser_state::CollectionKind::Seq,
                len_term: Some(len),
                len_guard: None,
                elem_ty: Some(ret_ty.as_ref().clone()),
                key_ty: None,
                dom_term: None,
            },
        );

        let bound_idx = self
            .solver
            .fresh_var("__seq_map_idx", Sort::bitvec(crate::ir::pointer_width()));
        let source_elem = self
            .solver
            .try_select(receiver, bound_idx)
            .map_err(|e| e.to_string())?;
        if let Some(info) = self.element_width_info(receiver, receiver_name) {
            self.term_widths.insert(source_elem, info);
        }
        let bound_value = self.coerce_element_for_int_mode(source_elem, receiver, receiver_name)?;

        // Declare `bound_idx` as quantifier-bound WHILE encoding the closure body.
        // `bound_idx` is the variable of the pointwise `forall i. result[i] ==
        // f(i, source[i])` we build below, but because the map assembles that
        // quantifier manually (not via `encode_quantifier`) it was never
        // registered in a quantifier scope. That mattered for a SAME-WIDTH index
        // cast inside the body (`i as i32` when `pointer_width() == 32`, so a
        // 32-bit `usize` index reinterprets to a 32-bit `i32`): with `bound_idx`
        // seen as a FREE bitvector, `reinterpret_bv_signedness` mints a fresh
        // `sc == bound_idx` var for the cast result. The ground-seed below
        // discharges concrete-index goals (`s.map(f).index(2) == 34`) by
        // `substitute(body_eq, [bound_idx], [k])` — which rewrites `bound_idx` but
        // NOT the disconnected `sc`, so `f(k, ..)` never folded and `result[k]`
        // stayed unconstrained -> Unknown ONLY on the 32-bit leg (on 64-bit the
        // same cast is a NARROWING `bvextract` that folds under substitution).
        // Marking `bound_idx` quantifier-bound routes the cast through the in-place
        // signedness-reinterpret path (the result stays `bound_idx`, so the seed's
        // substitution reaches it). Sound: over `0..len` a `usize` index is
        // non-negative and small, so the signed/unsigned reading agree; the scope
        // is popped immediately after the body so no later encoding is affected.
        self.push_quantifier_scope(&[(
            idx_param_name.clone(),
            TrustVcType::Uint {
                width: crate::ir::pointer_width(),
            },
        )]);
        if let Some(scope) = self.quantifier_scopes.last_mut() {
            scope.add_bound_term(bound_idx);
        }
        let mapped_body = self.with_closure_body_bindings(
            [
                (
                    idx_param_name.clone(),
                    bound_idx,
                    TrustVcType::Uint {
                        width: crate::ir::pointer_width(),
                    },
                ),
                (val_param_name.clone(), bound_value, val_param_ty.clone()),
            ],
            |s| s.encode_trust_vc_expr(body),
        );
        self.pop_quantifier_scope();
        let mapped_body = mapped_body?;

        let mapped_body = self.coerce_value_for_store_in_int_mode(mapped_body, result, None)?;
        let result_elem = self
            .solver
            .try_select(result, bound_idx)
            .map_err(|e| e.to_string())?;
        let body_eq = self
            .solver
            .try_eq(result_elem, mapped_body)
            .map_err(|e| e.to_string())?;
        // Range guard: only constrain in-bounds indices (#2572).
        let idx_in_range = self
            .solver
            .try_bvult(bound_idx, len_bv)
            .map_err(|e| e.to_string())?;
        let guarded_body = self
            .solver
            .try_implies(idx_in_range, body_eq)
            .map_err(|e| e.to_string())?;
        let axiom = self
            .solver
            .try_forall_with_triggers(&[bound_idx], guarded_body, &[&[result_elem]])
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| e.to_string())?;

        // Ground-instance seeding for the pointwise map axiom.
        //
        // The quantified axiom
        //   forall i. i < len ==> result[i] == f(i, source[i])
        // — itself a TRUE fact — does not reliably e-match a CONCRETE-index goal
        // such as `s.map(f).index(2) == 34`: the closure body crosses the BV->Int
        // boundary (`i as int`, `bv2int(source[i])`), so ay's quantifier
        // instantiation does not fire at the literal read and leaves `result[2]`
        // unconstrained — yielding a spurious counterexample (model:
        // empty/under-constrained source).
        //
        // We seed the SAME equation at concrete indices `0..n` by SUBSTITUTING the
        // quantifier's bound index with the concrete index constant inside the
        // already-built body equation `body_eq` (`result[i] == f(i, source[i])`),
        // via `solver.substitute`. Substitution rebuilds + eagerly folds, so the
        // index-dependent operations collapse to constants exactly as a fired
        // instantiation would — e.g. `(k as i32)` becomes a literal and
        // `select(store_chain, k)` resolves to the stored element — WITHOUT
        // re-encoding the closure body.
        //
        // Why substitution rather than re-encoding the body at a constant index:
        // re-encoding would bind the closure's index parameter to the concrete
        // index constant `try_bv_const(k, pw)`. On the 32-bit-pointer arch leg
        // `pw == 32`, that constant interns to the SAME bit-vector term as an
        // element-typed body literal of equal value (e.g. `2i32`, `BitVec{2,32}`)
        // — ay interns BV constants by `(value, width)` only, with signedness
        // tracked separately in `term_widths`. The `i32` literal stamps that term
        // `(32, signed)` while the `usize` index demands `(32, unsigned)`, and
        // `encode_var` then rejects the index with a "sort metadata mismatch"
        // internal Error. Substitution sidesteps this entirely: `body_eq` was
        // built once with a FRESH bound variable (alias-free), and substitution is
        // a pure term operation that never calls `encode_var` or touches
        // `term_widths`.
        //
        // Each instance is guarded by `k < len` in the LENGTH (Int) domain via
        // `len_lt` — NOT the `bvult(k, len_bv)` BV form the `Seq::from_fn` seed
        // uses. `len_bv` is a fresh bit-vector bridged to the Int length only by
        // `bv2int(len_bv) == len`, and ay does not reliably invert that bridge to
        // a concrete `len_bv`, so a BV guard's antecedent stays undecided and the
        // instance never fires. The Int guard `int(k) < len` is decided directly
        // by linear arithmetic.
        //
        // Soundness (both directions): each instance is exactly `map`'s spec at
        // index `k`, guarded by `k < len`. A TRUE in-range goal discharges; a
        // FALSE in-range goal still refutes (the seeded value contradicts the
        // wrong claim — counterexample, never a false Verified); an out-of-range
        // index (`k >= len`) leaves `result[k]` unconstrained (guard false), so
        // the `Seq::index` precondition behavior is unchanged.
        {
            let pw = crate::ir::pointer_width();
            for k in 0..SEQ_MAP_GROUND_SEED_COUNT {
                let k_bv = self
                    .solver
                    .try_bv_const(k, pw)
                    .map_err(|e| format!("Seq::map ground index: {e}"))?;
                let ground_eq = self.solver.substitute(body_eq, &[bound_idx], &[k_bv]);
                let k_len = self.len_const_like(len, k)?;
                let k_in_range = self.len_lt(k_len, len)?;
                let guarded_k = self
                    .solver
                    .try_implies(k_in_range, ground_eq)
                    .map_err(|e| format!("Seq::map ground guarded body: {e}"))?;
                self.solver
                    .try_assert_term(guarded_k)
                    .map_err(|e| format!("Seq::map ground assert: {e}"))?;
            }
        }

        Ok(result)
    }

    /// Encode `Seq::filter(pred)` as a fresh subsequence.
    ///
    /// Encoding:
    ///   result_len <= source_len
    ///   forall j. {select(result, j)} bvult(j, result_len) ==> pred(result[j])
    ///   forall i. {select(source, i)}
    ///     bvult(i, source_len) && pred(source[i]) ==>
    ///     bvult(witness[i], result_len) && select(result, witness[i]) == source[i]
    ///
    /// The existential in axiom 2 is Skolemized via a BV-sorted witness array.
    pub(in crate::encoder) fn encode_seq_filter(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let rname = receiver_name.unwrap_or("<anonymous>");
        let [TrustVcExpr::SpecClosure { params, body, .. }] = args else {
            return Err("Seq::filter expects exactly one SpecFn::new(...) argument"
                .to_string()
                .into());
        };
        let [(param_name, param_ty)] = params.as_slice() else {
            return Err("Seq::filter requires a unary SpecFn predicate"
                .to_string()
                .into());
        };
        let pw = crate::ir::pointer_width();

        let source_len = self
            .lookup_collection_len(receiver, receiver_name)
            .ok_or_else(|| format!("No length tracked for Seq '{}' in filter()", rname))?;
        let elem_sort = self.seq_element_sort(receiver, receiver_name)?;

        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(pw),
            element_sort: elem_sort,
        }));
        let result = self.solver.fresh_var("__seq_filter", result_sort);
        // Route A (#2779): result length is an unbounded Int witness. A BV view
        // (`result_len_bv`) is derived for the BV-indexed range/witness guards;
        // a BV view of the source length is used where they are compared as
        // array indices. The detection of this witness via its name
        // (`__seq_filter_len`, used by `should_bounded_unroll_filter_contains`)
        // is preserved.
        let result_len = self.solver.fresh_var("__seq_filter_len", Sort::Int);
        let result_len_zero = self.solver.int_const(0);
        let result_len_nonneg = self
            .solver
            .try_ge(result_len, result_len_zero)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(result_len_nonneg)
            .map_err(|e| e.to_string())?;
        // Companions for the two pointwise FORALLs — pure BV so ay-dpll can
        // model-validate them (Route A #2779). `result_len` is a fresh witness
        // asserted `>= 0` above, so its bridge is always SAT; the SOURCE length,
        // however, can be a NEGATIVE length-decreasing view result (e.g.
        // `skip(n>len).filter(..)`), so route it through the precondition-guarded
        // companion to avoid UNSAT-poisoning the context (#soundness
        // skip/subrange/drop — filter consumer site).
        let result_len_bv = self.len_index_companion(result_len)?;
        let source_len_bv = self.len_index_companion_maybe_negative(source_len)?;

        let elem_ty = self.resolve_source_elem_ty(receiver, receiver_name);
        self.register_collection_meta(
            result,
            super::super::parser_state::CollectionMeta {
                kind: super::super::parser_state::CollectionKind::Seq,
                len_term: Some(result_len),
                len_guard: None,
                elem_ty,
                key_ty: None,
                dom_term: None,
            },
        );

        // result_len <= source_len, in the Int length domain. Guard by
        // `source_len >= 0`: `result_len` is asserted `>= 0`, so an
        // UNCONDITIONAL `result_len <= source_len` is itself UNSAT whenever the
        // source is a precondition-violating NEGATIVE length-decreasing view
        // (e.g. `skip(n>len).filter(..)`), which would UNSAT-poison the context
        // and vacuously discharge both the violated source precondition and a
        // false downstream goal — the same hole the guarded companion closes. For
        // a valid (non-negative) source the antecedent holds and the bound is
        // delivered unchanged (#soundness skip/subrange/drop — filter len bound).
        let len_bound = self.len_le(result_len, source_len)?;
        let len_bound = self.guard_len_fact_nonneg(source_len, len_bound)?;
        self.solver
            .try_assert_term(len_bound)
            .map_err(|e| e.to_string())?;

        {
            let bound_j = self.solver.fresh_var("__seq_filter_j", Sort::bitvec(pw));
            let result_elem = self
                .solver
                .try_select(result, bound_j)
                .map_err(|e| e.to_string())?;
            if let Some(info) = self.element_width_info(receiver, receiver_name) {
                self.term_widths.insert(result_elem, info);
            }
            let bound_value =
                self.coerce_element_for_int_mode(result_elem, receiver, receiver_name)?;

            let pred_body = self.with_closure_body_bindings(
                [(param_name.clone(), bound_value, param_ty.clone())],
                |s| s.encode_trust_vc_expr(body),
            )?;

            // Range guard: only assert predicate for in-bounds indices.
            // Without this, the predicate applies to the "junk" region of
            // the SMT array (indices >= result_len), which can make the
            // axiom unsatisfiable and cause false verification. Fixes #2528.
            let j_in_range = self
                .solver
                .try_bvult(bound_j, result_len_bv)
                .map_err(|e| e.to_string())?;
            let guarded_body = self
                .solver
                .try_implies(j_in_range, pred_body)
                .map_err(|e| e.to_string())?;

            let axiom1 = self
                .solver
                .try_forall_with_triggers(&[bound_j], guarded_body, &[&[result_elem]])
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(axiom1)
                .map_err(|e| e.to_string())?;
        }

        let witness_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(pw),
            element_sort: Sort::bitvec(pw),
        }));
        let witness = self.solver.fresh_var("__seq_filter_witness", witness_sort);
        {
            let bound_i = self.solver.fresh_var("__seq_filter_i", Sort::bitvec(pw));
            let source_elem = self
                .solver
                .try_select(receiver, bound_i)
                .map_err(|e| e.to_string())?;
            if let Some(info) = self.element_width_info(receiver, receiver_name) {
                self.term_widths.insert(source_elem, info);
            }
            let bound_value =
                self.coerce_element_for_int_mode(source_elem, receiver, receiver_name)?;

            let pred_body = self.with_closure_body_bindings(
                [(param_name.clone(), bound_value, param_ty.clone())],
                |s| s.encode_trust_vc_expr(body),
            )?;

            let i_in_range = self
                .solver
                .try_bvult(bound_i, source_len_bv)
                .map_err(|e| e.to_string())?;
            let antecedent = self
                .solver
                .try_and(i_in_range, pred_body)
                .map_err(|e| e.to_string())?;

            let witness_idx = self
                .solver
                .try_select(witness, bound_i)
                .map_err(|e| e.to_string())?;
            let witness_in_range = self
                .solver
                .try_bvult(witness_idx, result_len_bv)
                .map_err(|e| e.to_string())?;
            let result_at_witness = self
                .solver
                .try_select(result, witness_idx)
                .map_err(|e| e.to_string())?;
            let (result_at_witness, source_elem_coerced) =
                self.coerce_bv_widths(result_at_witness, source_elem)?;
            let elem_match = self
                .solver
                .try_eq(result_at_witness, source_elem_coerced)
                .map_err(|e| e.to_string())?;
            let consequent = self
                .solver
                .try_and(witness_in_range, elem_match)
                .map_err(|e| e.to_string())?;

            let implication = self
                .solver
                .try_implies(antecedent, consequent)
                .map_err(|e| e.to_string())?;
            let axiom2 = self
                .solver
                .try_forall_with_triggers(&[bound_i], implication, &[&[source_elem]])
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(axiom2)
                .map_err(|e| e.to_string())?;
        }

        if self
            .solver
            .format_term(source_len)
            .contains("__seq_len_push")
        {
            self.assert_seq_filter_bounded_pack_instances(SeqFilterBoundedPack {
                source: receiver,
                source_name: receiver_name,
                source_len,
                result,
                result_len,
                param_name,
                param_ty,
                pred_body_expr: body,
            })?;
        }

        Ok(result)
    }

    fn assert_seq_filter_bounded_pack_instances(
        &mut self,
        pack: SeqFilterBoundedPack<'_>,
    ) -> TrustVcResult<()> {
        let SeqFilterBoundedPack {
            source,
            source_name,
            source_len,
            result,
            result_len,
            param_name,
            param_ty,
            pred_body_expr,
        } = pack;
        let pw = crate::ir::pointer_width();
        // `source_len <= limit` is a length comparison (Int under Route A #2779);
        // BV views are used for the per-index range guards on the carrier.
        let limit = self.len_const_like(source_len, FILTER_BOUNDED_MEMBERSHIP_UNROLL_LIMIT)?;
        let source_len_within_limit = self.len_le(source_len, limit)?;
        let source_len_bv = self.len_as_index_bv(source_len)?;
        let result_len_bv = self.len_as_index_bv(result_len)?;
        let zero = self.solver.try_bv_const(0, pw).map_err(|e| e.to_string())?;
        let one = self.solver.try_bv_const(1, pw).map_err(|e| e.to_string())?;
        self.term_widths.insert(zero, (pw, false));
        self.term_widths.insert(one, (pw, false));
        let mut write_idx = zero;

        for source_idx_value in 0..FILTER_BOUNDED_MEMBERSHIP_UNROLL_LIMIT {
            let source_idx = self
                .solver
                .try_bv_const(source_idx_value, pw)
                .map_err(|e| e.to_string())?;
            self.term_widths.insert(source_idx, (pw, false));
            let source_idx_in_range = self
                .solver
                .try_bvult(source_idx, source_len_bv)
                .map_err(|e| e.to_string())?;
            let source_elem = self
                .solver
                .try_select(source, source_idx)
                .map_err(|e| e.to_string())?;
            if let Some(info) = self.element_width_info(source, source_name) {
                self.term_widths.insert(source_elem, info);
            }
            let bound_value = self.coerce_element_for_int_mode(source_elem, source, source_name)?;
            let pred_body = self.with_closure_body_bindings(
                [(param_name.to_string(), bound_value, param_ty.clone())],
                |s| s.encode_trust_vc_expr(pred_body_expr),
            )?;
            let keep_source_elem = self
                .solver
                .try_and(source_idx_in_range, pred_body)
                .map_err(|e| e.to_string())?;
            let antecedent = self
                .solver
                .try_and(source_len_within_limit, keep_source_elem)
                .map_err(|e| e.to_string())?;

            let result_elem = self
                .solver
                .try_select(result, write_idx)
                .map_err(|e| e.to_string())?;
            if let Some(info) = self.element_width_info(source, source_name) {
                self.term_widths.insert(result_elem, info);
            }
            let (result_elem, source_elem_for_eq) =
                self.coerce_bv_widths(result_elem, source_elem)?;
            let elem_match = self
                .solver
                .try_eq(result_elem, source_elem_for_eq)
                .map_err(|e| e.to_string())?;
            let write_idx_in_result = self
                .solver
                .try_bvult(write_idx, result_len_bv)
                .map_err(|e| e.to_string())?;
            let retained_at_write_idx = self
                .solver
                .try_and(write_idx_in_result, elem_match)
                .map_err(|e| e.to_string())?;

            let implication = self
                .solver
                .try_implies(antecedent, retained_at_write_idx)
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(implication)
                .map_err(|e| e.to_string())?;

            let incremented = self
                .solver
                .try_bvadd(write_idx, one)
                .map_err(|e| e.to_string())?;
            write_idx = self
                .solver
                .try_ite(keep_source_elem, incremented, write_idx)
                .map_err(|e| e.to_string())?;
            self.term_widths.insert(write_idx, (pw, false));
        }

        // result_len (Int) == final write_idx (BV count) — lift to the length sort.
        let write_idx_len = self.len_match_sort(result_len, write_idx)?;
        let bounded_len_eq = self
            .solver
            .try_eq(result_len, write_idx_len)
            .map_err(|e| e.to_string())?;
        let bounded_len_implication = self
            .solver
            .try_implies(source_len_within_limit, bounded_len_eq)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(bounded_len_implication)
            .map_err(|e| e.to_string())?;

        Ok(())
    }
}
