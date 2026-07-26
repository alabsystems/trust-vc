//! Native ay Seq theory encoding for Seq<T> operations.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Feature-gated behind `native-seq` (#2680 Slice 2). When enabled,
//! `TrustVcType::Seq(T)` maps to `Sort::Seq(T)` and operations use ay's
//! native sequence theory (seq.unit, seq.concat, seq.len, seq.nth, etc.)
//! instead of the array-based encoding with manual __len tracking.
//!
//! ## Int-sorted length encoding
//!
//! ay-seq operations use Int-sorted lengths and indices. To avoid
//! bv2int/int2bv cross-theory terms (which ay-dpll's model validator
//! cannot evaluate), the native-seq encoding is **purely Int-sorted**:
//!
//! - `native_seq_len()` returns `seq.len(s)` (Int).
//! - Overflow checks use Int comparisons (`idx >= 0 && idx < len`).
//! - Literal indices are encoded directly as Int constants.
//! - BV-sorted index variables use `bv2int` (rare; tests with BV
//!   variable indices may get Unknown from model validation failure).
//!
//! The comparison encoder detects native-seq Len results via
//! `infer_effective_expr_type` returning `MathInt` (see compare.rs).
//!
//! Higher-order operations (map, filter, fold, to_set, count) are encoded
//! using quantified axioms over `seq.nth` with Int-sorted bound variables.
//! flat_map and to_multiset remain unsupported under native-seq.

mod core_ops;
mod helpers;
mod higher_order;
mod slice_ops;
mod string_ops;

use ay_dpll::api::Term;

use super::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{CollectionOp, TrustVcExpr};

impl<'a> AstExpressionParser<'a> {
    /// Top-level dispatch for Seq operations using native ay Seq theory.
    ///
    /// Called from `encode_collection_op` when `native-seq` is enabled and the
    /// receiver is a Seq type. Returns `Err` for unsupported higher-order ops.
    #[allow(clippy::indexing_slicing)] // args bounds checked per-arm
    pub(in crate::encoder) fn encode_native_seq_op(
        &mut self,
        op: CollectionOp,
        receiver: &TrustVcExpr,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let receiver_term = self.encode_subexpr(receiver)?;
        let receiver_term = self.resolve_native_seq_receiver(receiver_term);

        match op {
            CollectionOp::Len => self.native_seq_len(receiver_term, receiver_name),
            CollectionOp::IsEmpty => self.native_seq_is_empty(receiver_term),
            CollectionOp::Get => self.native_seq_get(receiver_term, receiver_name, args),
            CollectionOp::Push => self.native_seq_push(receiver_term, args),
            CollectionOp::First => self.native_seq_first(receiver_term),
            CollectionOp::Last => self.native_seq_last(receiver_term),
            CollectionOp::DropFirst => self.native_seq_drop_first(receiver_term),
            CollectionOp::DropLast => self.native_seq_drop_last(receiver_term),
            CollectionOp::Take => self.native_seq_take(receiver_term, args),
            CollectionOp::Skip => self.native_seq_skip(receiver_term, args),
            CollectionOp::Subrange => self.native_seq_subrange(receiver_term, args),
            CollectionOp::Concat | CollectionOp::Add => {
                if args.len() != 1 {
                    return Err(format!("concat() expects 1 argument, got {}", args.len()).into());
                }
                let other = self.encode_subexpr(&args[0])?;
                self.native_seq_concat(receiver_term, other)
            }
            CollectionOp::Contains => self.native_seq_contains(receiver_term, args),
            CollectionOp::Update => self.native_seq_update(receiver_term, args),
            CollectionOp::Reverse => self.native_seq_reverse(receiver_term, receiver_name),
            CollectionOp::NoDuplicates => {
                self.native_seq_no_duplicates(receiver_term, receiver_name)
            }
            // View is identity for Seq (ghost erasure already handled).
            CollectionOp::View => Ok(receiver_term),
            // Higher-order ops: encoded via quantified axioms over seq.nth
            CollectionOp::SeqMapValues => {
                self.native_seq_map_values(receiver_term, receiver_name, args)
            }
            CollectionOp::SeqMap => self.native_seq_map(receiver_term, receiver_name, args),
            CollectionOp::SeqFilter => self.native_seq_filter(receiver_term, receiver_name, args),
            CollectionOp::SeqFoldLeft => {
                self.native_seq_fold_left(receiver_term, receiver_name, args)
            }
            CollectionOp::SeqFoldRight => {
                self.native_seq_fold_right(receiver_term, receiver_name, args)
            }
            CollectionOp::ToSet => self.native_seq_to_set(receiver_term, receiver_name),
            CollectionOp::Count => self.native_seq_count(receiver_term, receiver_name, args),
            // flat_map and to_multiset remain unsupported under native-seq for now.
            CollectionOp::SeqFlatMap | CollectionOp::ToMultiset => {
                self.native_seq_unsupported_op(op)
            }
            // Set/Map/Multiset operations should not reach native Seq dispatch.
            _ => Err(format!(
                "Non-Seq operation {:?} incorrectly dispatched to native Seq encoder",
                op
            )
            .into()),
        }
    }

    /// Encode `TrustVcExpr::Index` for native Seq: `seq.nth(s, i)` with bounds check.
    ///
    /// Called from `ir_encoder/indexing.rs` under `native-seq`.
    pub(in crate::encoder) fn encode_native_seq_index(
        &mut self,
        receiver: &TrustVcExpr,
        index: &TrustVcExpr,
    ) -> TrustVcResult<Term> {
        let receiver_name = match receiver {
            TrustVcExpr::Var { name, .. } => Some(name.as_str()),
            _ => None,
        };
        let receiver_term = self.encode_subexpr(receiver)?;
        let receiver_term = self.resolve_native_seq_receiver(receiver_term);
        let idx = self.native_seq_coerce_to_int_index(index)?;
        self.native_seq_bounds_check(receiver_term, receiver_name, idx, "index")?;
        if let Some(concrete_idx) = crate::encoder::AYEncoder::try_reduce_to_int(index) {
            return self.native_seq_ground_element_alias(
                receiver_term,
                receiver_name,
                idx,
                concrete_idx,
                "Index",
            );
        }
        self.solver
            .try_seq_nth(receiver_term, idx)
            .map_err(|e| format!("native seq.nth for Index: {e}").into())
    }
}
