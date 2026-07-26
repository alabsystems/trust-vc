//! Extracted Seq collection dispatch helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::Term;

use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{CollectionOp, TrustVcExpr, TrustVcType};

impl<'a> AstExpressionParser<'a> {
    pub(in crate::encoder::ir_encoder) fn try_encode_seq_concat_index(
        &mut self,
        receiver: &TrustVcExpr,
        index: &TrustVcExpr,
    ) -> TrustVcResult<Option<Term>> {
        let TrustVcExpr::CollectionOp {
            op: CollectionOp::Concat | CollectionOp::Add,
            receiver: lhs_expr,
            receiver_name,
            args,
            ty,
        } = receiver
        else {
            return Ok(None);
        };
        if !matches!(ty, TrustVcType::Seq(_)) {
            return Ok(None);
        }
        let [rhs_expr] = args.as_slice() else {
            return Err(format!("concat() expects 1 argument, got {}", args.len()).into());
        };

        let lhs = self.encode_subexpr(lhs_expr)?;
        let rhs = self.encode_subexpr(rhs_expr)?;
        let lhs_name = receiver_name.as_deref().or(match lhs_expr.as_ref() {
            TrustVcExpr::Var { name, .. } => Some(name.as_str()),
            _ => None,
        });
        let rhs_name = match rhs_expr {
            TrustVcExpr::Var { name, .. } => Some(name.as_str()),
            _ => None,
        };
        let lhs_len = self.lookup_collection_len(lhs, lhs_name).ok_or_else(|| {
            format!(
                "No length tracking for Seq '{}' in concat index",
                lhs_name.unwrap_or("<anonymous>")
            )
        })?;
        let rhs_len = self.lookup_collection_len(rhs, rhs_name).ok_or_else(|| {
            format!(
                "Seq::concat() requires length tracking for rhs '{}'",
                rhs_name.unwrap_or("<anonymous>")
            )
        })?;

        let idx = self.encode_subexpr(index)?;
        let idx = self.coerce_seq_index(lhs, lhs_name, idx)?;
        // Route A (#2779): concat result length is Int addition — monotone, no
        // wraparound. The old BV "concat length no overflow" obligation was an
        // artifact of the bounded-width length model and is GONE here (Verus
        // models Seq::len() as unbounded nat). Per-operand `len >= 0` is already
        // asserted at declaration; Int `+` preserves it, so the explicit
        // non-negativity obligation is likewise unnecessary on the Int path.
        let new_len = self.len_add(lhs_len, rhs_len)?;
        self.add_seq_index_bounds_check_for_len(idx, new_len, "index")?;
        if !self.len_is_int(new_len) {
            // Legacy/feature BV-length path retains the bounded-width guards.
            let zero = self
                .solver
                .try_bv_const(0, crate::ir::pointer_width())
                .map_err(|e| e.to_string())?;
            let nonneg = self
                .solver
                .try_bvuge(new_len, zero)
                .map_err(|e| format!("concat length non-negativity: {}", e))?;
            self.overflow_checks
                .push(("concat length non-negative".into(), nonneg));
            let no_overflow = self
                .solver
                .try_bvuge(new_len, lhs_len)
                .map_err(|e| format!("concat length overflow: {}", e))?;
            self.overflow_checks
                .push(("concat length no overflow".into(), no_overflow));
        }

        // The Array(BV,T) carrier is BV-indexed; bridge the (Int) lhs length to
        // a BV index for the rhs offset and the in-lhs boundary comparison.
        let lhs_len_bv = self.len_as_index_bv(lhs_len)?;
        let lhs_elem = self
            .solver
            .try_select(lhs, idx)
            .map_err(|e| e.to_string())?;
        let rhs_offset = self
            .solver
            .try_bvsub(idx, lhs_len_bv)
            .map_err(|e| e.to_string())?;
        let rhs_elem = self
            .solver
            .try_select(rhs, rhs_offset)
            .map_err(|e| e.to_string())?;
        let in_lhs = self
            .solver
            .try_bvult(idx, lhs_len_bv)
            .map_err(|e| e.to_string())?;
        let result = self
            .solver
            .try_ite(in_lhs, lhs_elem, rhs_elem)
            .map_err(|e| e.to_string())?;

        if let Some(info) = self.element_width_info(lhs, lhs_name) {
            self.term_widths.insert(result, info);
        }
        let result = self.coerce_element_for_int_mode(result, lhs, lhs_name)?;
        Ok(Some(result))
    }

    fn add_seq_index_bounds_check_for_len(
        &mut self,
        idx: Term,
        len: Term,
        method: &str,
    ) -> TrustVcResult<()> {
        if self.quantifier_depth > 0 && self.is_quantifier_bound_term(idx) {
            self.diagnostics
                .record(crate::encoder::diagnostics::EncodingApproximation::BoundsCheckSkipped);
            return Ok(());
        }
        // `len` is Int under Route A (#2779); compare `0 <= idx < len` in the
        // Int domain (idx is a BV array index, lifted via bv2int). On the
        // legacy BV-length path (or pure-BV mode) keep the bvult form.
        let in_bounds = if self.len_is_int(len) || self.int_mode() {
            let len_int = if self.len_is_int(len) {
                len
            } else {
                self.solver
                    .try_bv2int(len)
                    .map_err(|e| format!("Failed bv2int for Seq::{} bounds check: {}", method, e))?
            };
            let idx_int = self.solver.try_bv2int(idx).unwrap_or(idx);
            let zero = self.solver.int_const(0);
            let idx_nonneg = self
                .solver
                .try_ge(idx_int, zero)
                .map_err(|e| e.to_string())?;
            let idx_lt_len = self
                .solver
                .try_lt(idx_int, len_int)
                .map_err(|e| e.to_string())?;
            self.solver
                .try_and(idx_nonneg, idx_lt_len)
                .map_err(|e| e.to_string())?
        } else {
            self.solver
                .try_bvult(idx, len)
                .map_err(|e| format!("Failed to create Seq::{} bounds check: {}", method, e))?
        };
        self.overflow_checks.push((
            format!("Seq::{}(<derived>, i) requires i < len", method).into(),
            in_bounds,
        ));
        Ok(())
    }

    pub(in crate::encoder::ir_encoder) fn encode_seq_len(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        rname: &str,
    ) -> TrustVcResult<Term> {
        if let Some(len_term) = self.lookup_collection_len(receiver_term, receiver_name) {
            self.emit_collection_len_guard(receiver_term);
            Ok(len_term)
        } else {
            Err(format!(
                "collection `{rname}` has no tracked length — ensure the Seq/Set/Map \
                 variable is declared as a function parameter or let-binding before use"
            )
            .into())
        }
    }

    pub(in crate::encoder::ir_encoder) fn encode_seq_is_empty(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        rname: &str,
    ) -> TrustVcResult<Term> {
        if let Some(len_term) = self.lookup_collection_len(receiver_term, receiver_name) {
            self.emit_collection_len_guard(receiver_term);
            // `len_term` is Int under Route A (#2779); match its sort for `== 0`.
            let zero = self.len_const_like(len_term, 0)?;
            self.solver
                .try_eq(len_term, zero)
                .map_err(|e| e.to_string().into())
        } else {
            Err(format!(
                "collection `{rname}` has no tracked length — ensure the Seq/Set/Map \
                 variable is declared as a function parameter or let-binding before use"
            )
            .into())
        }
    }

    #[allow(clippy::indexing_slicing)] // args[0] guarded by args.len() == 1 above
    pub(in crate::encoder::ir_encoder) fn encode_seq_get(
        &mut self,
        receiver_term: Term,
        rname: &str,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 1 {
            return Err(format!("get() expects 1 argument, got {}", args.len()).into());
        }
        let key = self.encode_subexpr(&args[0])?;
        let is_map = self.receiver_is_map(receiver_term, Some(rname));
        // Same-index `Seq::push` read-back: `db.push(v); db.index(db.len() - 1)`
        // reads back the just-appended cell, TRUE regardless of int2bv carrier
        // representability (store and select alias the identical wrapped cell).
        // Fires only under the strict index-identity gate; otherwise falls
        // through to the normal path (representability obligation preserved).
        if !is_map {
            if let Some(result) =
                self.try_encode_push_same_index_readback(receiver_term, key, Some(rname))?
            {
                return Ok(result);
            }
        }
        let key = if is_map {
            self.coerce_key_for_store_in_int_mode(key, receiver_term, Some(rname))?
        } else {
            // Coerce Seq index to BV64 (parity: methods.rs:31) before
            // int_mode key coercion. Without this, BV32 literals cause
            // sort mismatch on Seq arrays indexed by BV64 (#1979).
            let key = self.coerce_seq_index(receiver_term, Some(rname), key)?;
            self.coerce_key_for_store_in_int_mode(key, receiver_term, Some(rname))?
        };
        if is_map {
            self.add_map_index_domain_check(receiver_term, Some(rname), key, "get")?;
        } else {
            self.add_seq_index_bounds_check(receiver_term, Some(rname), key, "index")?;
        }
        let result = self
            .solver
            .try_select(receiver_term, key)
            .map_err(|e| e.to_string())?;
        // Register element width for downstream coercion (parity: methods.rs:42-47)
        if let Some(info) = self.element_width_info(receiver_term, Some(rname)) {
            self.term_widths.insert(result, info);
        }
        // In int_mode, convert BV element to Int (parity: methods.rs:47)
        self.coerce_element_for_int_mode(result, receiver_term, Some(rname))
    }

    #[allow(clippy::indexing_slicing)] // args[0]/args[1] guarded by args.len() == 2 above
    pub(in crate::encoder::ir_encoder) fn encode_seq_update(
        &mut self,
        receiver_term: Term,
        rname: &str,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 2 {
            return Err(format!("update() expects 2 arguments, got {}", args.len()).into());
        }
        let idx = self.encode_subexpr(&args[0])?;
        let idx = self.coerce_seq_index(receiver_term, Some(rname), idx)?;
        let idx = self.coerce_key_for_store_in_int_mode(idx, receiver_term, Some(rname))?;
        // Bounds check (parity: methods.rs:226-227)
        if !self.receiver_is_map(receiver_term, Some(rname)) {
            self.add_seq_index_bounds_check(receiver_term, Some(rname), idx, "update")?;
        }
        let val = self.encode_subexpr(&args[1])?;
        let val = self.coerce_value_for_store_in_int_mode(val, receiver_term, Some(rname))?;
        let result = self
            .solver
            .try_store(receiver_term, idx, val)
            .map_err(|e| e.to_string())?;
        // Element-preservation for Seq update.
        if !self.receiver_is_map(receiver_term, Some(rname)) {
            // NOTE: `result` here is the literal `store(receiver, idx, val)`
            // term, so the element-preservation axiom
            //   `forall i. i != idx => select(store(receiver,idx,val), i)
            //                          == select(receiver, i)`
            // is a pure read-over-write TAUTOLOGY of the SMT array theory — it
            // adds no logical content over what `select`/`store` already
            // guarantee. Originally emitted (#1979) as a defensive E-matching
            // aid, but as a `forall` it actively derails ay's SAT model
            // generation: any later obligation that accumulates it as an
            // assumption fails to materialize a standalone Int length variable
            // in the model, so a genuinely-false read (e.g. `x.set(0,5);
            // assert(x[0]==7)`) could not be refuted with a counterexample and
            // failed closed with a solver `internal-error` instead. ay resolves
            // the different-index read-over-write natively, so we no longer emit
            // the redundant quantifier. (The non-redundant push variant
            // `assert_store_preservation` is unaffected.)
            //
            // Register metadata for chained ops (e.g. s.update(i,v).index(j))
            // Fail-closed: return error if no length tracked (was silently skipped). Fixes #2142.
            let len = self
                .lookup_collection_len(receiver_term, Some(rname))
                .ok_or_else(|| format!("No length tracked for collection '{}' in update", rname))?;
            self.register_seq_len(result, len, receiver_term, Some(rname));
            // Note: update reuses the source's len term, so no explicit
            // length axiom is needed (it would be a tautology: len == len).
        }
        Ok(result)
    }

    pub(in crate::encoder::ir_encoder) fn encode_seq_first(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        rname: &str,
    ) -> TrustVcResult<Term> {
        // Verus precondition: self.len() >= 1 (parity: methods.rs:214)
        self.add_seq_nonempty_check(receiver_term, receiver_name, "first")?;
        // Use coerce_seq_index to produce the same term as index(0).
        let pw = crate::ir::pointer_width();
        let zero = self.solver.try_bv_const(0, pw).map_err(|e| e.to_string())?;
        self.term_widths.insert(zero, (pw, false));
        let idx = self.coerce_seq_index(receiver_term, Some(rname), zero)?;
        let result = self
            .solver
            .try_select(receiver_term, idx)
            .map_err(|e| e.to_string())?;
        // Register element width (parity: methods.rs:226-228)
        if let Some(info) = self.element_width_info(receiver_term, Some(rname)) {
            self.term_widths.insert(result, info);
        }
        self.coerce_element_for_int_mode(result, receiver_term, Some(rname))
    }

    pub(in crate::encoder::ir_encoder) fn encode_seq_last(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        rname: &str,
    ) -> TrustVcResult<Term> {
        // Verus precondition: self.len() >= 1 (parity: methods.rs:238)
        self.add_seq_nonempty_check(receiver_term, receiver_name, "last")?;
        if let Some(len_term) = self.lookup_collection_len(receiver_term, receiver_name) {
            let pw = crate::ir::pointer_width();
            // last_idx = len - 1 is an array INDEX; bridge the (Int) length to a
            // BV index before subtracting.
            //
            // Route A (#2779): the pure-BV companion asserts a top-level
            // `bv2int(companion) == int_len` bridge so ay-dpll can model-validate
            // the select inside QUANTIFIED contexts. But a `bv2int(...)` term in
            // the query blocks ay's SAT model validation (the B2 Int-vs-BitVec
            // model-validation asymmetry) — so at quantifier depth 0 it turns any
            // legitimately-SAT obligation in the SAME query into Unknown, e.g.
            // the empty `[u8; 0]` last() whose `len >= 1` precondition must
            // *refute* (Counterexample) — `first()`, having no companion, refutes
            // cleanly. At depth 0 the per-length correctness of last() is carried
            // entirely by the ground `len == k+1 => last == a[k]` instances
            // (`assert_last_ground_insts`), so the select index itself need not be
            // bridged: a fresh BV index keeps the query bv2int-free (SAT-
            // validatable) and stays sound (an unbridged index can only leave an
            // out-of-ground-range read unconstrained → Unknown, never a false
            // Verify). The companion is retained inside quantifiers, where ground
            // instances do not cover the bound length.
            let len_bv = if self.quantifier_depth == 0 {
                self.solver
                    .fresh_var("__trust_vc_last_idx", ay_dpll::api::Sort::bitvec(pw))
            } else {
                self.len_index_companion(len_term)?
            };
            let one = self.solver.try_bv_const(1, pw).map_err(|e| e.to_string())?;
            let last_idx = self
                .solver
                .try_bvsub(len_bv, one)
                .map_err(|e| e.to_string())?;
            self.term_widths.insert(last_idx, (pw, false));
            let idx = self.coerce_seq_index(receiver_term, Some(rname), last_idx)?;
            let result = self
                .solver
                .try_select(receiver_term, idx)
                .map_err(|e| e.to_string())?;

            // Ground instantiations for last() (#1979, parity: methods.rs)
            self.assert_last_ground_insts(receiver_term, len_term, result)?;

            // Register element width (parity: methods.rs:260-262)
            if let Some(info) = self.element_width_info(receiver_term, Some(rname)) {
                self.term_widths.insert(result, info);
            }
            self.coerce_element_for_int_mode(result, receiver_term, Some(rname))
        } else {
            Err(format!(
                "collection `{rname}` has no tracked length — ensure the Seq/Set/Map \
                 variable is declared as a function parameter or let-binding before use"
            )
            .into())
        }
    }

    pub(in crate::encoder::ir_encoder) fn encode_seq_drop_last(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        rname: &str,
    ) -> TrustVcResult<Term> {
        self.add_seq_nonempty_check(receiver_term, receiver_name, "drop_last")?;
        let pw = crate::ir::pointer_width();
        let len = self
            .lookup_collection_len(receiver_term, receiver_name)
            .ok_or_else(|| format!("No length tracked for collection '{}'", rname))?;
        // new_len = len - 1 is a LENGTH (Int, no wrap — nonempty guarded above).
        let one_len = self.len_const_like(len, 1)?;
        let new_len = self.len_sub(len, one_len)?;
        // Create fresh array term to avoid corrupting source metadata.
        // Previously returned `receiver_term` directly, overwriting the
        // source sequence's length. Fixes #2148.
        let zero_ptr = self.solver.try_bv_const(0, pw).map_err(|e| e.to_string())?;
        self.encode_index_shifted_seq(receiver_term, receiver_name, zero_ptr, new_len)
    }

    pub(in crate::encoder::ir_encoder) fn encode_seq_drop_first(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        rname: &str,
    ) -> TrustVcResult<Term> {
        self.add_seq_nonempty_check(receiver_term, receiver_name, "drop_first")?;
        let pw = crate::ir::pointer_width();
        let len = self
            .lookup_collection_len(receiver_term, receiver_name)
            .ok_or_else(|| format!("No length tracked for collection '{}'", rname))?;
        // new_len = len - 1 is a LENGTH (Int); offset 1 is a BV array index.
        let one_len = self.len_const_like(len, 1)?;
        let new_len = self.len_sub(len, one_len)?;
        let one = self.solver.try_bv_const(1, pw).map_err(|e| e.to_string())?;
        self.encode_index_shifted_seq(receiver_term, receiver_name, one, new_len)
    }

    #[allow(clippy::indexing_slicing)] // args[0] guarded by args.len() == 1 above
    pub(in crate::encoder::ir_encoder) fn encode_seq_take(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        rname: &str,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 1 {
            return Err(format!("take() expects 1 argument, got {}", args.len()).into());
        }
        let len = self
            .lookup_collection_len(receiver_term, receiver_name)
            .ok_or_else(|| format!("No length tracked for collection '{}'", rname))?;
        let n = self.encode_subexpr(&args[0])?;
        // Discharge `n <= len` in the LENGTH's native domain. Under Route A the
        // length is unbounded `Int`, so lift the ORIGINAL `n` (at its own width)
        // straight to that sort via `len_match_sort` and compare Int-to-Int.
        // Lifting `n` directly — rather than the pointer-width-widened `n_pw` —
        // keeps the obligation's `bv2int(n)` syntactically tied to the caller's
        // BV bound (`n <= 5`) without an intervening zero-extension that the
        // solver discharges incompletely. The obligation stays free of an
        // `int2bv(int_len)` subterm (which would gate the query Unknown — see
        // `len_as_index_bv`). In any legacy path that still produces a BV length,
        // `len_match_sort`/`len_le` degrade to the previous BV comparison. The
        // result LENGTH stored in metadata is `n` lifted to the length's sort
        // (Route A #2779).
        let n_len = self.len_match_sort(len, n)?;
        let n_le_len = self.len_le(n_len, len)?;
        self.overflow_checks
            .push(("Seq::take(n) requires n <= len".into(), n_le_len));
        let zero_ptr = self
            .solver
            .try_bv_const(0, crate::ir::pointer_width())
            .map_err(|e| e.to_string())?;
        self.encode_index_shifted_seq(receiver_term, receiver_name, zero_ptr, n_len)
    }

    #[allow(clippy::indexing_slicing)] // args[0] guarded by args.len() == 1 above
    pub(in crate::encoder::ir_encoder) fn encode_seq_skip(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        rname: &str,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 1 {
            return Err(format!("skip() expects 1 argument, got {}", args.len()).into());
        }
        let len = self
            .lookup_collection_len(receiver_term, receiver_name)
            .ok_or_else(|| format!("No length tracked for collection '{}'", rname))?;
        let n = self.encode_subexpr(&args[0])?;
        let n_pw = self.coerce_to_len_width(n)?;
        // Discharge `n <= len` in the LENGTH's native domain (Int under Route A),
        // lifting the ORIGINAL `n` to match — keeps the obligation's `bv2int(n)`
        // tied to the caller's BV bound without a zero-extension, and free of an
        // `int2bv(int_len)` gate (see `encode_seq_take`). The result LENGTH
        // `len - n` is Int; the array shift offset stays pointer-width BV.
        let n_len = self.len_match_sort(len, n)?;
        let n_le_len = self.len_le(n_len, len)?;
        self.overflow_checks
            .push(("Seq::skip(n) requires n <= len".into(), n_le_len));
        let new_len = self.len_sub(len, n_len)?;
        // n_pw is already pointer_width — no zero-extension needed (#1745).
        self.encode_index_shifted_seq(receiver_term, receiver_name, n_pw, new_len)
    }
}
