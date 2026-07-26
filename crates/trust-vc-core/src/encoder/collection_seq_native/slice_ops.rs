//! Native Seq slicing and concatenation operations.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::Term;

use super::super::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::TrustVcExpr;

impl<'a> AstExpressionParser<'a> {
    /// `Seq::drop_first()` → `seq.extract(s, 1, len - 1)` with nonempty check.
    pub(super) fn native_seq_drop_first(&mut self, receiver: Term) -> TrustVcResult<Term> {
        let nonempty = self.native_seq_nonempty_check(receiver, None, "drop_first")?;
        let len = self.native_seq_len(receiver, None)?;
        let one = self.solver.int_const(1);
        let new_len = self
            .solver
            .try_sub(len, one)
            .map_err(|e| format!("native seq drop_first len: {e}"))?;
        let result = self
            .solver
            .try_seq_extract(receiver, one, new_len)
            .map_err(|e| format!("native seq.extract for drop_first: {e}"))?;
        self.emit_nth_extract_bridge_axiom(
            receiver,
            one,
            new_len,
            result,
            Some(nonempty),
            "drop_first",
        )?;
        self.register_native_seq_len(result, new_len, receiver, None);
        Ok(result)
    }

    /// `Seq::drop_last()` → `seq.extract(s, 0, len - 1)` with nonempty check.
    pub(super) fn native_seq_drop_last(&mut self, receiver: Term) -> TrustVcResult<Term> {
        let nonempty = self.native_seq_nonempty_check(receiver, None, "drop_last")?;
        let len = self.native_seq_len(receiver, None)?;
        let one = self.solver.int_const(1);
        let new_len = self
            .solver
            .try_sub(len, one)
            .map_err(|e| format!("native seq drop_last len: {e}"))?;
        let zero = self.solver.int_const(0);
        let result = self
            .solver
            .try_seq_extract(receiver, zero, new_len)
            .map_err(|e| format!("native seq.extract for drop_last: {e}"))?;
        self.emit_nth_extract_bridge_axiom(
            receiver,
            zero,
            new_len,
            result,
            Some(nonempty),
            "drop_last",
        )?;
        self.register_native_seq_len(result, new_len, receiver, None);
        Ok(result)
    }

    /// `Seq::take(n)` → `seq.extract(s, 0, n)` with 0 <= n <= len checks.
    pub(super) fn native_seq_take(
        &mut self,
        receiver: Term,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 1 {
            return Err(format!("take() expects 1 argument, got {}", args.len()).into());
        }
        let n = self.native_seq_coerce_to_int_index(&args[0])?;
        let n_nonnegative = self.native_seq_nonnegative_index_check(n, "take")?;
        let len = self.native_seq_len(receiver, None)?;
        let n_le_len = self
            .solver
            .try_le(n, len)
            .map_err(|e| format!("native seq take bounds: {e}"))?;
        self.overflow_checks
            .push(("Seq::take(n) requires n <= len".into(), n_le_len));
        let guard = self
            .solver
            .try_and(n_nonnegative, n_le_len)
            .map_err(|e| format!("native seq take guard: {e}"))?;
        let zero = self.solver.int_const(0);
        let result = self
            .solver
            .try_seq_extract(receiver, zero, n)
            .map_err(|e| format!("native seq.extract for take: {e}"))?;
        self.emit_nth_extract_bridge_axiom(receiver, zero, n, result, Some(guard), "take")?;
        self.register_guarded_native_seq_len(result, n, guard, receiver, None, "take")?;
        Ok(result)
    }

    /// `Seq::skip(n)` → `seq.extract(s, n, len - n)` with 0 <= n <= len checks.
    pub(super) fn native_seq_skip(
        &mut self,
        receiver: Term,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 1 {
            return Err(format!("skip() expects 1 argument, got {}", args.len()).into());
        }
        let n = self.native_seq_coerce_to_int_index(&args[0])?;
        let n_nonnegative = self.native_seq_nonnegative_index_check(n, "skip")?;
        let len = self.native_seq_len(receiver, None)?;
        let n_le_len = self
            .solver
            .try_le(n, len)
            .map_err(|e| format!("native seq skip bounds: {e}"))?;
        self.overflow_checks
            .push(("Seq::skip(n) requires n <= len".into(), n_le_len));
        let guard = self
            .solver
            .try_and(n_nonnegative, n_le_len)
            .map_err(|e| format!("native seq skip guard: {e}"))?;
        let remainder = self
            .solver
            .try_sub(len, n)
            .map_err(|e| format!("native seq skip remainder: {e}"))?;
        let result = self
            .solver
            .try_seq_extract(receiver, n, remainder)
            .map_err(|e| format!("native seq.extract for skip: {e}"))?;
        self.emit_nth_extract_bridge_axiom(receiver, n, remainder, result, Some(guard), "skip")?;
        self.register_guarded_native_seq_len(result, remainder, guard, receiver, None, "skip")?;
        Ok(result)
    }

    /// `Seq::subrange(start, end)` → `seq.extract(s, start, end - start)`.
    ///
    /// Overflow checks use Int domain (0 <= start <= end <= len).
    pub(super) fn native_seq_subrange(
        &mut self,
        receiver: Term,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 2 {
            return Err(format!("subrange() expects 2 arguments, got {}", args.len()).into());
        }
        let start = self.native_seq_coerce_to_int_index(&args[0])?;
        let end = self.native_seq_coerce_to_int_index(&args[1])?;
        let start_nonnegative = self.native_seq_nonnegative_index_check(start, "subrange")?;
        let end_nonnegative = self.native_seq_nonnegative_index_check(end, "subrange")?;
        let len = self.native_seq_len(receiver, None)?;
        let start_le_end = self
            .solver
            .try_le(start, end)
            .map_err(|e| format!("native seq subrange bounds: {e}"))?;
        self.overflow_checks.push((
            "Seq::subrange(start, end) requires start <= end".into(),
            start_le_end,
        ));
        let end_le_len = self
            .solver
            .try_le(end, len)
            .map_err(|e| format!("native seq subrange bounds: {e}"))?;
        self.overflow_checks.push((
            "Seq::subrange(start, end) requires end <= len".into(),
            end_le_len,
        ));
        let guard = self
            .solver
            .try_and(start_nonnegative, end_nonnegative)
            .map_err(|e| format!("native seq subrange nonnegative guard: {e}"))?;
        let guard = self
            .solver
            .try_and(guard, start_le_end)
            .map_err(|e| format!("native seq subrange ordered guard: {e}"))?;
        let guard = self
            .solver
            .try_and(guard, end_le_len)
            .map_err(|e| format!("native seq subrange upper guard: {e}"))?;
        let extract_len = self
            .solver
            .try_sub(end, start)
            .map_err(|e| format!("native seq subrange len: {e}"))?;
        let result = self
            .solver
            .try_seq_extract(receiver, start, extract_len)
            .map_err(|e| format!("native seq.extract for subrange: {e}"))?;
        self.emit_nth_extract_bridge_axiom(
            receiver,
            start,
            extract_len,
            result,
            Some(guard),
            "subrange",
        )?;
        self.register_guarded_native_seq_len(
            result,
            extract_len,
            guard,
            receiver,
            None,
            "subrange",
        )?;
        Ok(result)
    }

    /// `Seq::concat(other)` / `Seq::add(other)` → `seq.++(s, t)`.
    pub(super) fn native_seq_concat(&mut self, lhs: Term, rhs: Term) -> TrustVcResult<Term> {
        let lhs_len = self.native_seq_len(lhs, None)?;
        let rhs_len = self.native_seq_len(rhs, None)?;
        let result = self
            .solver
            .try_seq_concat(lhs, rhs)
            .map_err(|e| format!("native seq.concat: {e}"))?;
        let new_len = self
            .solver
            .try_add(lhs_len, rhs_len)
            .map_err(|e| format!("native seq concat len: {e}"))?;
        self.register_native_seq_len(result, new_len, lhs, None);
        Ok(result)
    }
}
