//! Unicode scalar validity helpers for char-bearing SMT terms.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::{Sort, Term};

use crate::error::{TrustVcError, TrustVcResult};

use super::AYEncoder;

impl AYEncoder {
    /// Assert that a BV32 term denotes a valid Rust `char`.
    pub(crate) fn assert_valid_char_term(&mut self, term: Term) -> TrustVcResult<()> {
        let valid = self.build_valid_char_predicate(term, "declare char variable")?;
        self.solver
            .try_assert_term(valid)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare char variable",
                detail: format!("Failed to assert Unicode scalar invariant: {e}"),
            })
    }

    /// Assert `forall i < len. seq[i]` is a valid Rust `char`.
    ///
    /// `len_term` may be Int (Route A array-seq length, #2779) or BitVec
    /// (legacy/feature paths). When Int, the index is quantified over Int and
    /// the bound becomes `0 <= i < len` (the array index passed to `select` is
    /// still BV(pw) — bridged via `int2bv`). When BitVec the original
    /// BV-indexed form is preserved.
    pub(crate) fn assert_valid_char_sequence(
        &mut self,
        seq_term: Term,
        len_term: Term,
    ) -> TrustVcResult<()> {
        if matches!(self.solver.term_sort(len_term), Sort::Int) {
            return self.assert_valid_char_sequence_int_len(seq_term, len_term);
        }
        let pw = crate::ir::pointer_width();
        let idx = self
            .solver
            .fresh_var("__trust_vc_char_idx", Sort::bitvec(pw));
        let idx_in_range =
            self.solver
                .try_bvult(idx, len_term)
                .map_err(|e| TrustVcError::Encoding {
                    context: "declare string view variable",
                    detail: format!("Failed to build char-sequence bound: {e}"),
                })?;
        let elem = self
            .solver
            .try_select(seq_term, idx)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare string view variable",
                detail: format!("Failed to select char-sequence element: {e}"),
            })?;
        let elem_valid = self.build_valid_char_predicate(elem, "declare string view variable")?;
        let body = self
            .solver
            .try_implies(idx_in_range, elem_valid)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare string view variable",
                detail: format!("Failed to build char-sequence implication: {e}"),
            })?;
        let quantified = self
            .solver
            .try_forall_with_triggers(&[idx], body, &[&[elem]])
            .map_err(|e| TrustVcError::Encoding {
                context: "declare string view variable",
                detail: format!("Failed to quantify char-sequence invariant: {e}"),
            })?;
        self.solver
            .try_assert_term(quantified)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare string view variable",
                detail: format!("Failed to assert char-sequence invariant: {e}"),
            })
    }

    /// Int-length variant of `assert_valid_char_sequence` for the Route A
    /// array-seq path (#2779): the LENGTH is Int but the char carrier is still
    /// `Array(BV(pw), BV(32))`, so the index is quantified over Int with bound
    /// `0 <= i < len` and lowered to BV(pw) via `int2bv` for the array
    /// `select`. The Unicode scalar predicate on the BV(32) element is
    /// identical.
    fn assert_valid_char_sequence_int_len(
        &mut self,
        seq_term: Term,
        len_term: Term,
    ) -> TrustVcResult<()> {
        let pw = crate::ir::pointer_width();
        let idx = self.solver.fresh_var("__trust_vc_char_idx", Sort::Int);
        let zero = self.solver.int_const(0);
        let idx_ge_zero = self
            .solver
            .try_ge(idx, zero)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare string view variable",
                detail: format!("Failed to build char-sequence lower bound: {e}"),
            })?;
        let idx_lt_len = self
            .solver
            .try_lt(idx, len_term)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare string view variable",
                detail: format!("Failed to build char-sequence upper bound: {e}"),
            })?;
        let idx_in_range =
            self.solver
                .try_and(idx_ge_zero, idx_lt_len)
                .map_err(|e| TrustVcError::Encoding {
                    context: "declare string view variable",
                    detail: format!("Failed to build char-sequence range: {e}"),
                })?;
        let idx_bv = self
            .solver
            .try_int2bv(idx, pw)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare string view variable",
                detail: format!("Failed to lower char-sequence index to BV: {e}"),
            })?;
        let elem =
            self.solver
                .try_select(seq_term, idx_bv)
                .map_err(|e| TrustVcError::Encoding {
                    context: "declare string view variable",
                    detail: format!("Failed to select char-sequence element: {e}"),
                })?;
        let elem_valid = self.build_valid_char_predicate(elem, "declare string view variable")?;
        let body = self
            .solver
            .try_implies(idx_in_range, elem_valid)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare string view variable",
                detail: format!("Failed to build char-sequence implication: {e}"),
            })?;
        let quantified = self
            .solver
            .try_forall_with_triggers(&[idx], body, &[&[elem]])
            .map_err(|e| TrustVcError::Encoding {
                context: "declare string view variable",
                detail: format!("Failed to quantify char-sequence invariant: {e}"),
            })?;
        self.solver
            .try_assert_term(quantified)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare string view variable",
                detail: format!("Failed to assert char-sequence invariant: {e}"),
            })
    }

    /// Assert `forall 0 <= i < len. seq.nth(s, i)` is a valid Rust `char`.
    ///
    /// Native-seq variant: uses Int-sorted index and seq.nth element access
    /// instead of BV-sorted index and array select. The element is still BV(32)
    /// so the Unicode scalar predicate is identical. Part of #2680 Slice 3.
    #[cfg(feature = "native-seq")]
    pub(crate) fn assert_valid_char_sequence_native_seq(
        &mut self,
        seq_term: Term,
        len_term: Term,
    ) -> TrustVcResult<()> {
        let idx = self.solver.fresh_var("__trust_vc_char_idx", Sort::Int);
        let zero = self.solver.int_const(0);
        let idx_ge_zero = self
            .solver
            .try_ge(idx, zero)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare string variable (native-seq)",
                detail: format!("Failed to build char-sequence lower bound: {e}"),
            })?;
        let idx_lt_len = self
            .solver
            .try_lt(idx, len_term)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare string variable (native-seq)",
                detail: format!("Failed to build char-sequence upper bound: {e}"),
            })?;
        let idx_in_range =
            self.solver
                .try_and(idx_ge_zero, idx_lt_len)
                .map_err(|e| TrustVcError::Encoding {
                    context: "declare string variable (native-seq)",
                    detail: format!("Failed to build char-sequence range: {e}"),
                })?;
        let elem = self
            .solver
            .try_seq_nth(seq_term, idx)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare string variable (native-seq)",
                detail: format!("Failed to access seq.nth for char validation: {e}"),
            })?;
        let elem_valid =
            self.build_valid_char_predicate(elem, "declare string variable (native-seq)")?;
        let body = self
            .solver
            .try_implies(idx_in_range, elem_valid)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare string variable (native-seq)",
                detail: format!("Failed to build char-sequence implication: {e}"),
            })?;
        let quantified = self
            .solver
            .try_forall_with_triggers(&[idx], body, &[&[elem]])
            .map_err(|e| TrustVcError::Encoding {
                context: "declare string variable (native-seq)",
                detail: format!("Failed to quantify char-sequence invariant: {e}"),
            })?;
        self.solver
            .try_assert_term(quantified)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare string variable (native-seq)",
                detail: format!("Failed to assert char-sequence invariant: {e}"),
            })
    }

    fn build_valid_char_predicate(
        &mut self,
        term: Term,
        context: &'static str,
    ) -> TrustVcResult<Term> {
        let max_scalar =
            self.solver
                .try_bv_const(0x10FFFF_i64, 32)
                .map_err(|e| TrustVcError::Encoding {
                    context,
                    detail: format!("Failed to create char max bound: {e}"),
                })?;
        let surrogate_start =
            self.solver
                .try_bv_const(0xD800_i64, 32)
                .map_err(|e| TrustVcError::Encoding {
                    context,
                    detail: format!("Failed to create surrogate start bound: {e}"),
                })?;
        let surrogate_end =
            self.solver
                .try_bv_const(0xDFFF_i64, 32)
                .map_err(|e| TrustVcError::Encoding {
                    context,
                    detail: format!("Failed to create surrogate end bound: {e}"),
                })?;

        let in_scalar_range =
            self.solver
                .try_bvule(term, max_scalar)
                .map_err(|e| TrustVcError::Encoding {
                    context,
                    detail: format!("Failed to build scalar upper bound: {e}"),
                })?;
        let below_surrogates =
            self.solver
                .try_bvult(term, surrogate_start)
                .map_err(|e| TrustVcError::Encoding {
                    context,
                    detail: format!("Failed to build surrogate lower exclusion: {e}"),
                })?;
        let above_surrogates =
            self.solver
                .try_bvugt(term, surrogate_end)
                .map_err(|e| TrustVcError::Encoding {
                    context,
                    detail: format!("Failed to build surrogate upper exclusion: {e}"),
                })?;
        let not_surrogate = self
            .solver
            .try_or(below_surrogates, above_surrogates)
            .map_err(|e| TrustVcError::Encoding {
                context,
                detail: format!("Failed to combine surrogate exclusions: {e}"),
            })?;
        self.solver
            .try_and(in_scalar_range, not_surrogate)
            .map_err(|e| TrustVcError::Encoding {
                context,
                detail: format!("Failed to build Unicode scalar predicate: {e}"),
            })
    }
}
