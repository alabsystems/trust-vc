//! Seq-specific comparison encoding (extensional equality, view extraction).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from `compare.rs` for the 500-line limit (#2621).

#[cfg(not(feature = "native-seq"))]
use ay_dpll::api::{Sort, Term};

#[cfg(not(feature = "native-seq"))]
use crate::encoder::AstExpressionParser;
#[cfg(not(feature = "native-seq"))]
use crate::error::TrustVcResult;
#[cfg(not(feature = "native-seq"))]
use crate::ir::{CollectionOp, TrustVcExpr};

#[cfg(not(feature = "native-seq"))]
use super::super::is_trust_vc_literal_zero;

#[cfg(not(feature = "native-seq"))]
impl<'a> AstExpressionParser<'a> {
    pub(super) fn seq_expr_receiver_name(expr: &TrustVcExpr) -> Option<&str> {
        match expr {
            TrustVcExpr::Var { name, .. } => Some(name.as_str()),
            TrustVcExpr::FnCall { name, args, .. } if args.is_empty() => Some(name.as_str()),
            TrustVcExpr::CollectionOp {
                receiver_name,
                receiver,
                ..
            }
            | TrustVcExpr::Index {
                receiver_name,
                receiver,
                ..
            } => receiver_name
                .as_deref()
                .or_else(|| Self::seq_expr_receiver_name(receiver)),
            TrustVcExpr::Cast { expr, .. } => Self::seq_expr_receiver_name(expr),
            _ => None,
        }
    }

    /// Returns `(source, offset, len)` where `offset = None` means zero.
    ///
    /// Using `Option<Term>` instead of a BV constant `0` avoids creating
    /// `bvadd(idx, 0)` / `bvsub(end, 0)` terms that the BV solver cannot
    /// eagerly simplify, causing term-matching failures after ay bumps (#2494).
    #[cfg(not(feature = "native-seq"))]
    #[allow(clippy::indexing_slicing)] // args[0]/args[1] are only used after the args.len() != 2 guard in the subrange branch
    pub(super) fn encode_seq_view(
        &mut self,
        expr: &TrustVcExpr,
    ) -> TrustVcResult<(Term, Option<Term>, Term)> {
        if let TrustVcExpr::CollectionOp {
            op: CollectionOp::Subrange,
            receiver,
            args,
            ..
        } = expr
        {
            if args.len() != 2 {
                return Err(format!("subrange() expects 2 arguments, got {}", args.len()).into());
            }
            let (source, base_offset, base_len) = self.encode_seq_view(receiver)?;
            let start = self.encode_subexpr(&args[0])?;
            let end = self.encode_subexpr(&args[1])?;
            let start_pw = self.coerce_to_len_width(start)?;
            let end_pw = self.coerce_to_len_width(end)?;
            // `start <= end` across possibly-mixed BV/Int sorts: a
            // length-derived bound (`(v).len()`, `(v).len() - 1`) stays
            // Sort::Int under Route A (#2779) and `coerce_to_len_width`
            // passes it through outside quantifier bodies, so a raw `bvule`
            // here was ill-sorted (BV64 vs Int). `index_bound_le` compares in
            // Int with an EXACT `bv2int` lift of any BV side — never a
            // wrapping `int2bv` in an obligation.
            let start_le_end = self
                .index_bound_le(start_pw, end_pw)
                .map_err(|e| format!("Failed to create subrange bounds check: {}", e))?;
            self.overflow_checks.push((
                "Seq::subrange(start, end) requires start <= end".into(),
                start_le_end,
            ));
            // An Int-sorted `start` is not `>= 0` by sort (the unsigned BV
            // path was); keep `0 <= start` genuinely enforced.
            self.push_int_bound_nonneg_check(
                start_pw,
                "Seq::subrange(start, end) requires 0 <= start",
            )?;
            // `end <= len` is a length comparison (Int under Route A #2779);
            // lift the BV end index to the length sort.
            let end_len = self.len_match_sort(base_len, end_pw)?;
            let end_le_len = self.len_le(end_len, base_len)?;
            self.overflow_checks.push((
                "Seq::subrange(start, end) requires end <= len".into(),
                end_le_len,
            ));
            // Zero-offset optimization (#2494): skip bvadd/bvsub with 0 to
            // avoid creating wrapped terms that block BV solver E-matching.
            let start_is_zero = is_trust_vc_literal_zero(&args[0]);
            let offset = if start_is_zero {
                // Identity: base + 0 = base
                base_offset
            } else {
                // The carrier offset must be a BitVec(pw) index; bridge an
                // Int start (length-derived, e.g. the Vec::append model's
                // `subrange(len, len)`) via the total `len_as_index_bv` —
                // exact within the carrier once the pushed
                // `0 <= start <= end <= len` obligations hold.
                let start_idx = if self.len_is_int(start_pw) {
                    self.len_as_index_bv(start_pw)?
                } else {
                    start_pw
                };
                let composed = match base_offset {
                    Some(base) => self
                        .solver
                        .try_bvadd(base, start_idx)
                        .map_err(|e| e.to_string())?,
                    None => start_idx,
                };
                Some(composed)
            };
            // The view LENGTH `end - start` is Int (no wrap).
            let len = if start_is_zero {
                end_len // end - 0 = end
            } else {
                let start_len = self.len_match_sort(base_len, start_pw)?;
                self.len_sub(end_len, start_len)?
            };
            return Ok((source, offset, len));
        }

        let term = self.encode_subexpr(expr)?;
        let name = Self::seq_expr_receiver_name(expr);
        let len = self
            .lookup_collection_len(term, name)
            .ok_or_else(|| "No length tracked for Seq equality operand".to_string())?;
        Ok((term, None, len))
    }

    #[cfg(not(feature = "native-seq"))]
    pub(super) fn encode_seq_extensional_eq(
        &mut self,
        left: &TrustVcExpr,
        right: &TrustVcExpr,
    ) -> TrustVcResult<Term> {
        let (left_source, left_offset, left_len) = self.encode_seq_view(left)?;
        let (right_source, right_offset, right_len) = self.encode_seq_view(right)?;
        // Syntactically-reflexive collection equality: the SAME source
        // expression compared to itself (e.g. the discarded-`.set` bounds pin
        // `(x.update(i,v)) == (x.update(i,v))` emitted by
        // `emit_seq_set_bounds_obligation`). Such an equality is trivially `true`
        // by reflexivity, so emitting the pointwise FORALL + `bv2nat`
        // length-companion bridges is not only redundant but actively harmful:
        // the vacuous `forall i. true` quantifier and the Int<->BV length bridges
        // accumulate (as assumptions) into the scope of any LATER obligation and
        // derail ay's SAT model generation — the standalone Int length variable
        // is left unmaterialized, model validation rejects the `(= len k)`
        // assumption, and the solve fails closed with an `internal-error`.
        //
        // SCOPED to *structurally identical* operand expressions. This is
        // deliberately NOT widened to "operands that merely encode to the same
        // backing term": the loop-invariant inductive step frames an unmodified
        // sequence as `s == s__trust_vc_pre` (two DISTINCT expressions aliased to
        // the same array term), and that equality's extensional `len`/element
        // facts are load-bearing for the inductive proof — short-circuiting it
        // regresses the step to `Unknown`. The operand side-effects (e.g. the
        // `idx < len` bounds overflow-check raised while encoding
        // `x.update(i,v)`) were already recorded by `encode_seq_view` above, so
        // short-circuiting only drops the redundant equality witness.
        if left == right
            && left_source == right_source
            && left_offset == right_offset
            && left_len == right_len
        {
            return Ok(self.solver.bool_const(true));
        }
        // Length equality is over the (Int) length sort; ensure both operands
        // share a sort before comparing (Route A #2779).
        let right_len_matched = self.len_match_sort(left_len, right_len)?;
        let len_eq = self
            .solver
            .try_eq(left_len, right_len_matched)
            .map_err(|e| e.to_string())?;
        // Fully-grounded array alias (#array-alias completeness). When at least
        // one operand is a fixed array `[T; N]` whose static length `N` is
        // within the GROUND_SEED_INDICES window, the per-index ground seeds
        // emitted below (`k in 0..GROUND_SEED_INDICES`, each guarded `k < len`)
        // already cover EVERY in-bounds index of BOTH operands — the length
        // equality conjunct (`len(left) == len(right)`) plus the fixed-array pin
        // force both lengths to exactly `N <= GROUND_SEED_INDICES`, so indices
        // `>= N` are out of bounds for both sides and carry no element fact.
        //
        // In that case the pointwise FORALL and the symbolic-tail seed are
        // logically REDUNDANT with the ground seeds, but each introduces a
        // subterm that ay-dpll cannot model-validate for a SAT/counterexample
        // query: the unbounded `forall` over the BV index domain, and the
        // `int2bv(len)` tail index (an Int length lowered to a BV index — see
        // `len_as_index_bv`, whose surviving `int2bv` view forces the whole
        // query `Unknown`). Their presence left a GENUINE wrong-length
        // counterexample (e.g. `sl == ar` with `ar: [u8; 3]`, asserting
        // `sl.len() == 4`) stuck at `Unknown` instead of refuting.
        //
        // SOUNDNESS: skipping them removes no constraint. Length equality is
        // preserved verbatim (`len_eq`), and each ground seed below is exactly
        // the pointwise-forall body instantiated at a concrete in-bounds index,
        // so a wrong element value still refutes and a non-aliased operand still
        // emits no seed. The remaining terms are all ground and Int/array-native,
        // so ay-dpll can construct and validate the model. Scoped to short fixed
        // arrays only; the unbounded symbolic `Seq == Seq` path keeps the FORALL
        // + tail seed unchanged (its element congruence beyond the seed window is
        // load-bearing).
        const GROUND_SEED_INDICES: i64 = 8;
        let fixed_static_len = match crate::ir_lowering::infer_expr_type(left) {
            crate::ir::TrustVcType::Array(_, n) => Some(n),
            _ => match crate::ir_lowering::infer_expr_type(right) {
                crate::ir::TrustVcType::Array(_, n) => Some(n),
                _ => None,
            },
        };
        let grounded_alias = fixed_static_len
            .is_some_and(|n| i64::try_from(n).is_ok_and(|n| n <= GROUND_SEED_INDICES));
        let mut combined = if grounded_alias {
            len_eq
        } else {
            // BV companions for the pointwise FORALL — pure BV so ay-dpll can
            // model-validate the quantifier (Route A #2779). Operand seqs are
            // representable in the BV-indexed carrier, so `bv2int(companion)==len`
            // adds no assumption. The symbolic-tail GROUND seed (below) uses the
            // total `int2bv` view.
            //
            // The operand length can be the result of a length-DECREASING op
            // (`subrange(start,end)` -> `end-start`, `skip(n)` -> `len-n`,
            // `drop_first`/`drop_last` -> `len-1`) that goes NEGATIVE exactly when
            // that op's Verus precondition is violated (`start>end`, `n>len`, empty
            // receiver). The UNCONDITIONAL `len_index_companion` asserts
            // `bv2int(companion) == left_len` and, because `bv2int >= 0` always,
            // that bridge is UNSAT for a negative `left_len` — poisoning the whole
            // obligation context and vacuously discharging BOTH the pushed
            // precondition guard AND the equality goal (a catastrophic
            // FALSE-VERIFIED: `X == [99]` and `X != [99]` both "verify"). Use the
            // precondition-guarded companion, which conditions the carrier-range
            // bridge on `left_len >= 0`: for a satisfied precondition (incl. every
            // concrete in-range view, where `end-start`/`len-n`/`len-1` folds to a
            // non-negative constant) the antecedent holds and the bridge is
            // delivered byte-for-byte as before; for a VIOLATED precondition the
            // negative length leaves the bridge inert (no poison) so the
            // precondition guard refutes (#soundness skip/subrange/drop — operand
            // ext-eq companion site, dual of the seq_transforms.rs fix).
            let left_len_bv = self.len_index_companion_maybe_negative(left_len)?;
            // SYMMETRIC companion for the RIGHT operand length. `len_as_index_bv`
            // below pushes the NC4 carrier-representability side condition
            // `0 <= len <= 2^pw - 1` for BOTH lengths, but only the guarded
            // companion bridge (`len >= 0 ==> bv2int(companion) == len`, with
            // `bv2int(companion) <= 2^pw - 1` by construction) makes that side
            // condition PROVABLE for a symbolic length. Without a right-operand
            // companion the right length's side condition is genuinely
            // unprovable (SAT — see docs/probes/2026-07-18-ay-lane/dump-css/
            // side1_probe.smt2) and `check_assumption_side_conditions` fails the
            // whole file closed with "index/length not representable in the
            // BitVec(64) carrier". The companion's BV value is not needed here
            // (the pointwise bound is taken on the LEFT length, tied to the
            // right by `len_eq`); only its bridge assertion is load-bearing.
            // Soundness: identical to the left companion — operand seqs are
            // representable in the BV-indexed carrier, so the guarded bridge
            // adds no assumption the carrier did not already make.
            let _right_len_bv = self.len_index_companion_maybe_negative(right_len)?;
            let left_len_ground_bv = self.len_as_index_bv(left_len)?;
            let right_len_ground_bv = self.len_as_index_bv(right_len)?;
            let bound_idx = self.solver.fresh_var(
                "__trust_vc_seq_eq_idx",
                Sort::bitvec(crate::ir::pointer_width()),
            );
            let in_bounds = self
                .solver
                .try_bvult(bound_idx, left_len_bv)
                .map_err(|e| e.to_string())?;
            // When offset is None (zero), use bound_idx directly — avoids
            // bvadd(idx, 0) which prevents BV solver term matching (#2494).
            let left_idx = match left_offset {
                Some(off) => self
                    .solver
                    .try_bvadd(bound_idx, off)
                    .map_err(|e| e.to_string())?,
                None => bound_idx,
            };
            let right_idx = match right_offset {
                Some(off) => self
                    .solver
                    .try_bvadd(bound_idx, off)
                    .map_err(|e| e.to_string())?,
                None => bound_idx,
            };
            let left_elem = self
                .solver
                .try_select(left_source, left_idx)
                .map_err(|e| e.to_string())?;
            let right_elem = self
                .solver
                .try_select(right_source, right_idx)
                .map_err(|e| e.to_string())?;
            let elem_eq = self
                .solver
                .try_eq(left_elem, right_elem)
                .map_err(|e| e.to_string())?;
            let body = self
                .solver
                .try_implies(in_bounds, elem_eq)
                .map_err(|e| e.to_string())?;
            let pointwise = self
                .solver
                .try_forall_with_triggers(&[bound_idx], body, &[&[left_elem], &[right_elem]])
                .map_err(|e| e.to_string())?;

            let one = self
                .solver
                .try_bv_const(1, crate::ir::pointer_width())
                .map_err(|e| e.to_string())?;
            // `len > 0` and the tail-index seed are GROUND (non-quantified), so the
            // total `int2bv` view is fine for the tail INDEX below.
            //
            // The non-emptiness GUARD, however, is taken in the LENGTH's own domain
            // (`left_len > 0`), NOT as the BV `bvugt(left_len_ground_bv, 0)`. When the
            // length is pinned to an unsigned BV companion (`left_len == bv2nat(k)`
            // from `s.len() == k`), that `bv2nat(k)` bridge sits on the assertion
            // stack, and ay-dpll then leaves a BV guard whose consequent reads a
            // `bvsub(k, 1)` index (the symbolic tail `s[k-1]`) UNDISCHARGED — the
            // implication stays vacuous and the seed never fires (the symbolic-tail
            // subrange goal is left `Unknown`). The Int guard `bv2nat(k) > 0`
            // discharges directly from the same `k > 4` premise, so the seed fires
            // and the tail equality propagates. Soundness is unchanged: `left_len`
            // and `left_len_ground_bv` denote the same non-negative length, so the
            // guard is the identical `len > 0` non-emptiness condition (it still
            // blocks the empty-sequence case where the tail index would wrap). For a
            // BV length (fixed array) `len_gt` keeps the prior `bvugt` form, a
            // trivially-decidable constant comparison.
            let len_zero = self.len_const_like(left_len, 0)?;
            let len_pos = self.len_gt(left_len, len_zero)?;
            // Compute end = offset + len for tail seed (a BV array index). When
            // offset is None (zero), end = len_bv — avoids bvadd(0, len) wrapper
            // (#2494).
            let left_end = match left_offset {
                Some(off) => self
                    .solver
                    .try_bvadd(off, left_len_ground_bv)
                    .map_err(|e| e.to_string())?,
                None => left_len_ground_bv,
            };
            let right_end = match right_offset {
                Some(off) => self
                    .solver
                    .try_bvadd(off, right_len_ground_bv)
                    .map_err(|e| e.to_string())?,
                None => right_len_ground_bv,
            };
            let left_tail_idx = self
                .solver
                .try_bvsub(left_end, one)
                .map_err(|e| e.to_string())?;
            let right_tail_idx = self
                .solver
                .try_bvsub(right_end, one)
                .map_err(|e| e.to_string())?;
            let left_tail = self
                .solver
                .try_select(left_source, left_tail_idx)
                .map_err(|e| e.to_string())?;
            let right_tail = self
                .solver
                .try_select(right_source, right_tail_idx)
                .map_err(|e| e.to_string())?;
            let tail_eq = self
                .solver
                .try_eq(left_tail, right_tail)
                .map_err(|e| e.to_string())?;
            let tail_seed = self
                .solver
                .try_implies(len_pos, tail_eq)
                .map_err(|e| e.to_string())?;

            let len_and_pointwise = self
                .solver
                .try_and(len_eq, pointwise)
                .map_err(|e| e.to_string())?;
            self.solver
                .try_and(len_and_pointwise, tail_seed)
                .map_err(|e| e.to_string())?
        };

        // Low-index GROUND seeds for the pointwise agreement (#completeness gap).
        //
        // The pointwise FORALL above carries the full element congruence
        // `forall i. i < len => left[off+i] == right[off+i]`, but ay does not
        // reliably E-match/instantiate it at a concrete *interior* index from a
        // ground `select(side, k)` read elsewhere in the query, so a goal like
        // `sl@.index(1) == ar[1]` (given `sl == ar`) is left Unknown. The
        // symbolic-tail seed only pins the LAST index, so middle indices fall
        // through.
        //
        // Each seed below is EXACTLY the forall body instantiated at a concrete
        // `k`, guarded by the same in-bounds condition `k < len`. It is therefore
        // a sound logical consequence of the extensional equality (never an
        // unconditional element equality): the guard means a WRONG element value
        // still refutes, an index past `len` adds nothing, and the seed only
        // exists because `left == right` was asserted (it does not fire for a
        // non-aliased sequence). Ground form keeps ay's model validator able to
        // evaluate it (see `len_as_index_bv`), matching the tail-seed treatment.
        //
        // SCOPED to array-alias equalities — at least one operand has a
        // statically-known fixed length (`[T; N]`). This is exactly the
        // array<->slice / array<->array alias case the seeds target (the goal's
        // ground element index is concrete). For a pure symbolic `Seq == Seq`
        // with no fixed-length operand the extra ground `select` terms only
        // perturb ay's quantifier/array search (they match the pointwise
        // forall's `select` triggers) without closing any concrete-index gap, so
        // they are withheld there to avoid regressing symbolic-length proofs
        // (e.g. `s[0..k] == t[0..k]` reaching the symbolic tail `s[k-1]`).
        let left_fixed_array = matches!(
            crate::ir_lowering::infer_expr_type(left),
            crate::ir::TrustVcType::Array(_, _)
        );
        let right_fixed_array = matches!(
            crate::ir_lowering::infer_expr_type(right),
            crate::ir::TrustVcType::Array(_, _)
        );
        let emit_ground_seeds = left_fixed_array || right_fixed_array;
        for k in 0i64..GROUND_SEED_INDICES {
            if !emit_ground_seeds {
                break;
            }
            let idx_k = self
                .solver
                .try_bv_const(k, crate::ir::pointer_width())
                .map_err(|e| e.to_string())?;
            // In-bounds guard `k < len`, evaluated in the LENGTH's own sort
            // (Int under Route A #2779). This is deliberately NOT a BV guard:
            // the length facts (`len(left) == len(right)`, fixed-array pins)
            // live in the Int theory, and ay does not reliably cross the
            // `int2bv`/`bv2int` boundary, so a BV guard (`k <u int2bv(len)` or a
            // `bv2int(companion)==len` companion) leaves the guard undecided and
            // the implication vacuous. A pure-Int guard discharges directly from
            // the same facts that make `len(left) == k_lit` provable.
            let k_len = self.len_const_like(left_len, k)?;
            let guard = self.len_lt(k_len, left_len)?;
            // Offset-relative element indices: `off + k`, or just `k` when the
            // view has zero offset (avoids a bvadd(_, 0) wrapper — see #2494).
            let left_idx_k = match left_offset {
                Some(off) => self
                    .solver
                    .try_bvadd(idx_k, off)
                    .map_err(|e| e.to_string())?,
                None => idx_k,
            };
            let right_idx_k = match right_offset {
                Some(off) => self
                    .solver
                    .try_bvadd(idx_k, off)
                    .map_err(|e| e.to_string())?,
                None => idx_k,
            };
            let left_elem_k = self
                .solver
                .try_select(left_source, left_idx_k)
                .map_err(|e| e.to_string())?;
            let right_elem_k = self
                .solver
                .try_select(right_source, right_idx_k)
                .map_err(|e| e.to_string())?;
            let elem_eq_k = self
                .solver
                .try_eq(left_elem_k, right_elem_k)
                .map_err(|e| e.to_string())?;
            let seed_k = self
                .solver
                .try_implies(guard, elem_eq_k)
                .map_err(|e| e.to_string())?;
            combined = self
                .solver
                .try_and(combined, seed_k)
                .map_err(|e| e.to_string())?;
        }
        Ok(combined)
    }
}
