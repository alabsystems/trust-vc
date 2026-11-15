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
        let own = self.own_sign(index, None);
        let idx = self.coerce_seq_index(lhs, lhs_name, idx, own)?;
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
        let raw_key = key;
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
            let own = self.own_sign(&args[0], None);
            let key = self.coerce_seq_index(receiver_term, Some(rname), key, own)?;
            self.coerce_key_for_store_in_int_mode(key, receiver_term, Some(rname))?
        };
        let in_bounds = if is_map {
            self.add_map_index_domain_check(receiver_term, Some(rname), key, "get")?;
            None
        } else {
            self.add_seq_index_bounds_check(receiver_term, Some(rname), key, "index")?
        };
        let result = self
            .solver
            .try_select(receiver_term, key)
            .map_err(|e| e.to_string())?;
        let result = if is_map {
            result
        } else {
            self.read_within_carrier(receiver_term, raw_key, result, in_bounds)?
        };
        // Register element width for downstream coercion (parity: methods.rs:42-47)
        if let Some(info) = self.element_width_info(receiver_term, Some(rname)) {
            self.term_widths.insert(result, info);
        }
        // In int_mode, convert BV element to Int (parity: methods.rs:47)
        self.coerce_element_for_int_mode(result, receiver_term, Some(rname))
    }

    /// `s.update(i, v)`: the store. For a sequence, its LENGTH is the
    /// receiver's only inside the update's domain `0 <= i < len` (`i` read at
    /// its own value), and an unspecified `nat` outside it
    /// (`length_within_domain`), as Verus's `axiom_seq_update_len` requires.
    /// The domain is also pushed as an obligation, but a spec function's
    /// defining axiom (and every broadcast / ground / trigger re-encoding)
    /// drops obligations, and there the receiver's length defined the
    /// out-of-domain update's: `spec fn upl(s: Seq<u8>, i: int) -> int {
    /// s.update(i, 0u8).len() as int }` made `upl(s, -1) == 300` (`s.len() ==
    /// 300`) `Verified` (§5b rule 10). A fixed-size ARRAY keeps its length,
    /// which is its type's (`[T; N]`).
    #[allow(clippy::indexing_slicing)] // args[0]/args[1] guarded by args.len() == 2 above
    pub(in crate::encoder::ir_encoder) fn encode_seq_update(
        &mut self,
        receiver: &TrustVcExpr,
        receiver_term: Term,
        rname: &str,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 2 {
            return Err(format!("update() expects 2 arguments, got {}", args.len()).into());
        }
        let is_map = self.receiver_is_map(receiver_term, Some(rname));
        let raw_idx = self.encode_subexpr(&args[0])?;
        let own = self.own_sign(&args[0], None);
        let idx = self.coerce_seq_index(receiver_term, Some(rname), raw_idx, own)?;
        let idx = self.coerce_key_for_store_in_int_mode(idx, receiver_term, Some(rname))?;
        // Bounds check (parity: methods.rs:226-227)
        if !is_map {
            self.add_seq_index_bounds_check(receiver_term, Some(rname), idx, "update")?;
        }
        let val = self.encode_subexpr(&args[1])?;
        let val = self.coerce_value_for_store_in_int_mode(val, receiver_term, Some(rname))?;
        let stored = self
            .solver
            .try_store(receiver_term, idx, val)
            .map_err(|e| e.to_string())?;
        if is_map {
            return Ok(stored);
        }
        // (No element-preservation quantifier: for the literal `store` it is a
        // read-over-write tautology of the array theory, and as a `forall` it
        // derailed ay's model generation — #1979.)
        let len = self
            .lookup_collection_len(receiver_term, Some(rname))
            .ok_or_else(|| format!("No length tracked for collection '{}' in update", rname))?;
        let fixed_size = matches!(
            crate::ir_lowering::infer_expr_type(receiver),
            TrustVcType::Array(..)
        );
        if fixed_size || !self.len_is_int(len) {
            // The legacy bit-vector length path keeps its bounded-width guards.
            self.register_seq_len(stored, len, receiver_term, Some(rname));
            return Ok(stored);
        }
        let i_len = self.own_value_as_length(len, raw_idx, own)?;
        let i_lt_len = self.len_lt(i_len, len)?;
        let in_domain = self.count_in_domain(i_len, i_lt_len)?;
        let new_len =
            self.length_within_domain("update", receiver_term, len, len, in_domain, &[i_len, val])?;
        let result = if self.drops_domain_obligations() {
            // Out of its domain an update is an UNSPECIFIED sequence — a
            // function of the update's arguments, not the receiver's cells
            // with the value stored at the wrapped index: `spec fn upd0(s:
            // Seq<u8>, i: int) -> int { s.update(i, 0u8)[0] as int }` made
            // `upd0(s, -1) == s[0]` `Verified` (the store landed at 2^64 - 1),
            // and `s.update(2^64, 7u8)[2^64] == 7` too. Only where the domain
            // obligation is not checked (a spec function's defining axiom, a
            // broadcast, an assumption); elsewhere the checked obligation
            // makes the two encodings agree.
            let unspecified =
                self.unspecified_of("seq_update_cells", receiver_term, &[len, i_len, val])?;
            self.solver
                .try_ite(in_domain, stored, unspecified)
                .map_err(|e| e.to_string())?
        } else {
            stored
        };
        self.register_seq_len(result, new_len, receiver_term, Some(rname));
        Ok(result)
    }

    /// Whether the obligations this encoding pushes (`overflow_checks`: an
    /// operation's domain, a read's bounds) are DROPPED rather than checked:
    /// an assumption encoded without its side conditions (a spec function's
    /// defining axiom, a broadcast lemma, a ground or trigger re-encoding of
    /// one) and a demand-inline retry, whose expanded bodies the checked pass
    /// never saw (rule 9). There an operation's value outside its domain must
    /// be unspecified, since nothing refuses it (§5b rule 10). A `requires`
    /// checks its side conditions, and an assertion's are checked by its own
    /// pass: both keep the plain encoding, whose terms their goals match.
    pub(in crate::encoder) fn drops_domain_obligations(&self) -> bool {
        self.obligations_unchecked
    }

    /// An UNSPECIFIED value of `receiver`'s sort (an array carrier) or of its
    /// element sort (`element`), as an uninterpreted function of `receiver`
    /// and `arguments` (one function per signature): the value an operation
    /// takes outside its domain.
    pub(in crate::encoder::ir_encoder) fn unspecified_of(
        &mut self,
        op: &str,
        receiver: Term,
        arguments: &[Term],
    ) -> TrustVcResult<Term> {
        self.unspecified_value(op, receiver, arguments, None)
    }

    pub(in crate::encoder::ir_encoder) fn unspecified_value(
        &mut self,
        op: &str,
        receiver: Term,
        arguments: &[Term],
        result_sort: Option<ay_dpll::api::Sort>,
    ) -> TrustVcResult<Term> {
        let receiver_sort = self.solver.term_sort(receiver);
        let result_sort = result_sort.unwrap_or_else(|| receiver_sort.clone());
        let mut domain = vec![receiver_sort];
        domain.extend(
            arguments
                .iter()
                .map(|argument| self.solver.term_sort(*argument)),
        );
        let name = format!(
            "__trust_vc_{op}_unspecified_{:016x}",
            stable_hash(&format!("{domain:?}->{result_sort:?}"))
        );
        let decl = self
            .solver
            .try_declare_fun(&name, &domain, result_sort)
            .map_err(|e| e.to_string())?;
        let mut args = vec![receiver];
        args.extend_from_slice(arguments);
        self.solver
            .try_apply(&decl, &args)
            .map_err(|e| e.to_string().into())
    }

    /// A sequence read `read` at the index `index` (read at its own value),
    /// where the encoding drops its bounds obligation, is an unspecified value
    /// of `(receiver, index)` outside the read's domain. For an `Int` index
    /// that is the carrier's index range (the carrier is indexed by
    /// `BitVec(pw)` and `int2bv` WRAPS): `spec fn at(s: Seq<u8>, i: int) ->
    /// int { s[i] as int }` made `at(s, -1) == at(s, 2^64 - 1)` and `at(s,
    /// 2^64) == s[0]` `Verified`. For a receiver that SHARES its carrier with
    /// another sequence — a `store` (an update, a push) or a conditional over
    /// such — it is also the bound `in_bounds` the checked encoding pushes
    /// (`0 <= i < len`): past the end, an update's carrier is its receiver's,
    /// so `spec fn up(s: Seq<u8>) -> u8 { s.update(5, 7u8)[300] }` gave
    /// `up(s) == s[300]` for `s.len() == 300`, where Verus relates the cells
    /// of an update to its receiver's only in domain
    /// (`axiom_seq_update_different`; §5b rule 10). A variable's or a
    /// function result's carrier is a function of that value alone, and keeps
    /// its plain read. Any other read is `read`.
    /// Whether the sequence `receiver` shares its carrier with another
    /// sequence: a `store` (an update, a push) or a conditional over such.
    fn receiver_shares_carrier(&self, receiver: Term) -> bool {
        match self.solver.term_kind(receiver) {
            ay_dpll::api::TermKind::App { name, .. } => name == "store",
            ay_dpll::api::TermKind::Ite | ay_dpll::api::TermKind::Let => true,
            _ => false,
        }
    }

    pub(in crate::encoder::ir_encoder) fn read_within_carrier(
        &mut self,
        receiver: Term,
        index: Term,
        read: Term,
        in_bounds: Option<Term>,
    ) -> TrustVcResult<Term> {
        if !self.drops_domain_obligations() {
            return Ok(read);
        }
        let shares_carrier = self.receiver_shares_carrier(receiver);
        let mut domain = in_bounds.filter(|_| shares_carrier);
        if matches!(self.solver.term_sort(index), ay_dpll::api::Sort::Int) {
            let pw = crate::ir::pointer_width();
            let zero = self.solver.int_const(0);
            let max = (num_bigint::BigInt::from(1u8) << pw) - 1;
            let max = self.solver.int_const_bigint(&max);
            let nonneg = self.solver.try_le(zero, index).map_err(|e| e.to_string())?;
            let below = self.solver.try_le(index, max).map_err(|e| e.to_string())?;
            let in_carrier = self
                .solver
                .try_and(nonneg, below)
                .map_err(|e| e.to_string())?;
            domain = Some(match domain {
                Some(bound) => self
                    .solver
                    .try_and(in_carrier, bound)
                    .map_err(|e| e.to_string())?,
                None => in_carrier,
            });
        }
        let Some(domain) = domain else {
            return Ok(read);
        };
        let element_sort = self.solver.term_sort(read);
        let unspecified =
            self.unspecified_value("seq_index_read", receiver, &[index], Some(element_sort))?;
        let guarded = self
            .solver
            .try_ite(domain, read, unspecified)
            .map_err(|e| e.to_string())?;
        if let Some(info) = self.term_widths.get(&read).copied() {
            self.term_widths.insert(guarded, info);
        }
        Ok(guarded)
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
        let idx = self.coerce_seq_index(
            receiver_term,
            Some(rname),
            zero,
            crate::encoder::width_coercion::OwnSign::of_constructed(false),
        )?;
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
            let idx = self.coerce_seq_index(
                receiver_term,
                Some(rname),
                last_idx,
                crate::encoder::width_coercion::OwnSign::of_constructed(false),
            )?;
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
        // new_len = len - 1 is a LENGTH (Int), specified only when nonempty.
        let one_len = self.len_const_like(len, 1)?;
        let exact_len = self.len_sub(len, one_len)?;
        let nonempty = self.len_ge(len, one_len)?;
        let new_len =
            self.length_within_domain("drop_last", receiver_term, len, exact_len, nonempty, &[])?;
        // Create fresh array term to avoid corrupting source metadata.
        // Previously returned `receiver_term` directly, overwriting the
        // source sequence's length. Fixes #2148.
        let zero_ptr = self.solver.try_bv_const(0, pw).map_err(|e| e.to_string())?;
        self.encode_index_shifted_seq(
            receiver_term,
            receiver_name,
            zero_ptr,
            new_len,
            Some(nonempty),
        )
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
        // new_len = len - 1 is a LENGTH (Int), specified only when nonempty;
        // offset 1 is a BV array index.
        let one_len = self.len_const_like(len, 1)?;
        let exact_len = self.len_sub(len, one_len)?;
        let nonempty = self.len_ge(len, one_len)?;
        let new_len =
            self.length_within_domain("drop_first", receiver_term, len, exact_len, nonempty, &[])?;
        let one = self.solver.try_bv_const(1, pw).map_err(|e| e.to_string())?;
        self.encode_index_shifted_seq(receiver_term, receiver_name, one, new_len, Some(nonempty))
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
        let n_own = self.own_sign(&args[0], None);
        // Discharge `n <= len` in the LENGTH's native domain. Under Route A the
        // length is unbounded `Int`, so lift the ORIGINAL `n` (at its own width,
        // by its own sign — `count_as_length`) straight to that sort and compare
        // Int-to-Int. Lifting `n` directly — rather than the pointer-width-widened
        // `n_pw` — keeps the obligation's `bv2int(n)` syntactically tied to the
        // caller's BV bound (`n <= 5`) without an intervening zero-extension that
        // the solver discharges incompletely. The obligation stays free of an
        // `int2bv(int_len)` subterm (which would gate the query Unknown — see
        // `len_as_index_bv`). In any legacy path that still produces a BV length,
        // `len_match_sort`/`len_le` degrade to the previous BV comparison. The
        // result LENGTH stored in metadata is `n` lifted to the length's sort
        // (Route A #2779).
        let n_len = self.count_as_length(len, n, n_own, "Seq::take(n) requires 0 <= n")?;
        let n_le_len = self.len_le(n_len, len)?;
        self.overflow_checks
            .push(("Seq::take(n) requires n <= len".into(), n_le_len));
        let in_domain = self.count_in_domain(n_len, n_le_len)?;
        let new_len =
            self.length_within_domain("take", receiver_term, len, n_len, in_domain, &[n_len])?;
        let zero_ptr = self
            .solver
            .try_bv_const(0, crate::ir::pointer_width())
            .map_err(|e| e.to_string())?;
        self.encode_index_shifted_seq(
            receiver_term,
            receiver_name,
            zero_ptr,
            new_len,
            Some(in_domain),
        )
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
        let n_own = self.own_sign(&args[0], None);
        let n_pw = self.coerce_to_len_width(n, n_own)?;
        // Discharge `n <= len` in the LENGTH's native domain (Int under Route A),
        // lifting the ORIGINAL `n` to match — keeps the obligation's `bv2int(n)`
        // tied to the caller's BV bound without a zero-extension, and free of an
        // `int2bv(int_len)` gate (see `encode_seq_take`). The result LENGTH
        // `len - n` is Int; the array shift offset stays pointer-width BV.
        let n_len = self.count_as_length(len, n, n_own, "Seq::skip(n) requires 0 <= n")?;
        let n_le_len = self.len_le(n_len, len)?;
        self.overflow_checks
            .push(("Seq::skip(n) requires n <= len".into(), n_le_len));
        let exact_len = self.len_sub(len, n_len)?;
        let in_domain = self.count_in_domain(n_len, n_le_len)?;
        let new_len =
            self.length_within_domain("skip", receiver_term, len, exact_len, in_domain, &[n_len])?;
        // n_pw is already pointer_width — no zero-extension needed (#1745).
        self.encode_index_shifted_seq(receiver_term, receiver_name, n_pw, new_len, Some(in_domain))
    }

    /// A `take`/`skip` COUNT `n` as a length in the sort of `len`, read at ITS
    /// OWN value (§5b rule 10): a bit-vector count is lifted by the sign of its
    /// own type, and a count that can be negative — a signed or an `int` one —
    /// carries the `0 <= n` precondition (`nonneg_label`), as `subrange`'s
    /// start does. `len_match_sort` lifts every bit-vector UNSIGNED, so an `i8`
    /// count of -1 read 255: with `s.len() == 300`, `s.skip(n).len() == 45` and
    /// `s.take(n).len() == 255` were `Verified`; and an `int` count met no
    /// lower bound at all (`s.skip(-1 as int).len() == 301` was `Verified`).
    fn count_as_length(
        &mut self,
        len: Term,
        n: Term,
        own: crate::encoder::width_coercion::OwnSign,
        nonneg_label: &str,
    ) -> TrustVcResult<Term> {
        if self.bv_term_width(n).is_some() && own.get() == Some(false) {
            return self.len_match_sort(len, n);
        }
        let exact = self.lift_bv_operand_to_int(n, own)?;
        self.push_int_bound_nonneg_check(exact, nonneg_label)?;
        self.len_match_sort(len, exact)
    }

    /// The integer `n` denotes — a bit-vector read by ITS OWN sign — in the
    /// sort of the length `len`.
    fn own_value_as_length(
        &mut self,
        len: Term,
        n: Term,
        own: crate::encoder::width_coercion::OwnSign,
    ) -> TrustVcResult<Term> {
        if self.bv_term_width(n).is_some() && own.get() == Some(false) {
            return self.len_match_sort(len, n);
        }
        let exact = self.lift_bv_operand_to_int(n, own)?;
        self.len_match_sort(len, exact)
    }

    /// `0 <= n && n <= len` for a count `n` already lifted to its own value
    /// (`n_le_len` is the second conjunct).
    fn count_in_domain(&mut self, n_len: Term, n_le_len: Term) -> TrustVcResult<Term> {
        if !self.len_is_int(n_len) {
            return Ok(n_le_len);
        }
        let zero = self.solver.int_const(0);
        let nonneg = self.solver.try_le(zero, n_len).map_err(|e| e.to_string())?;
        self.solver
            .try_and(nonneg, n_le_len)
            .map_err(|e| e.to_string().into())
    }

    /// The LENGTH of a length-DECREASING view of `receiver` (`take`, `skip`,
    /// `subrange`, `drop_first`, `drop_last`): its `exact` length where the
    /// operation's precondition `in_domain` holds, and an UNSPECIFIED `nat`
    /// otherwise — Verus's `subrange` (which `take`/`skip`/`drop_*` unfold
    /// to) is specified only for `0 <= i <= j <= len`, and every `len()` is a
    /// `nat`. The unspecified length is an uninterpreted function of the
    /// receiver and the operation's arguments, clamped at 0.
    ///
    /// The precondition is also pushed as an OBLIGATION (`overflow_checks`),
    /// but only the contexts that CHECK those obligations (an assertion's
    /// overflow pass, a typed assumption's side conditions) enforce it; a
    /// spec function's defining axiom, a broadcast lemma, a ground-pool or
    /// trigger re-encoding drop them. There the exact length defined the
    /// out-of-domain one: `spec fn tkl8(s: Seq<u8>, n: i8) -> int {
    /// s.take(n).len() as int }` made `tkl8(s, -1) < 0` `Verified` (a negative
    /// length) and `requires tkl8(s, -1) >= 0 ensures s.len() == 7` vacuous,
    /// and `skli(s, -1) == 301` (`s.skip(n)`, `n: int`, `s.len() == 300`) was
    /// `Verified` (design-trust-proof-backend.md §5b rule 10).
    ///
    /// Every argument of the operation is an argument of the unspecified
    /// length (`arguments`, each at its own sort — an `update`'s stored value
    /// included): two out-of-domain updates at one index storing different
    /// values are two unrelated sequences, and a length that ignored the
    /// value made `s.update(-1, 0u8).len() == s.update(-1, 7u8).len()`
    /// `Verified`.
    pub(in crate::encoder::ir_encoder) fn length_within_domain(
        &mut self,
        op: &str,
        receiver: Term,
        len: Term,
        exact: Term,
        in_domain: Term,
        arguments: &[Term],
    ) -> TrustVcResult<Term> {
        if !self.len_is_int(len) || !self.len_is_int(exact) {
            // The legacy bit-vector length path keeps its bounded-width guards.
            return Ok(exact);
        }
        let mut domain = vec![self.solver.term_sort(receiver), ay_dpll::api::Sort::Int];
        domain.extend(
            arguments
                .iter()
                .map(|argument| self.solver.term_sort(*argument)),
        );
        let name = format!(
            "__trust_vc_seq_{op}_len_unspecified_{:016x}",
            stable_hash(&format!("{domain:?}"))
        );
        let decl = self
            .solver
            .try_declare_fun(&name, &domain, ay_dpll::api::Sort::Int)
            .map_err(|e| e.to_string())?;
        let mut args = vec![receiver, len];
        args.extend_from_slice(arguments);
        let unspecified = self
            .solver
            .try_apply(&decl, &args)
            .map_err(|e| e.to_string())?;
        let zero = self.solver.int_const(0);
        let nonneg = self
            .solver
            .try_ge(unspecified, zero)
            .map_err(|e| e.to_string())?;
        let unspecified_nat = self
            .solver
            .try_ite(nonneg, unspecified, zero)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_ite(in_domain, exact, unspecified_nat)
            .map_err(|e| e.to_string().into())
    }
}

/// FNV-1a over `text`: a stable per-signature suffix for a function name
/// (a solver name has one signature).
fn stable_hash(text: &str) -> u64 {
    text.bytes().fold(0xcbf2_9ce4_8422_2325, |hash, byte| {
        (hash ^ u64::from(byte)).wrapping_mul(0x0100_0000_01b3)
    })
}
