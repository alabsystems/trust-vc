// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Exact integer/real arithmetic normalization for TrustVcExpr trees.
//!
//! ay-dpll does not uniformly discharge commutativity/associativity for exact
//! Int/Real arithmetic, so `mul(q, mul(d, q2))` and `mul(d, mul(q, q2))` produce structurally
//! different ay terms. This module normalizes TrustVcExpr trees BEFORE encoding
//! so that algebraically equivalent expressions produce identical ay terms.
//!
//! Normalization rules (exact integer/real arithmetic only, applied recursively):
//! 1. Flatten nested associative ops: `(a + b) + c` → flat `[a, b, c]`
//! 2. Sort commutative operands canonically: `[c, a, b]` → `[a, b, c]`
//! 3. Rebuild as left-associative: `((a + b) + c)`
//!
//! This ensures `q * (d * q2)` and `d * (q * q2)` both normalize to
//! `((d * q) * q2)` and produce the same ay `mul(d, mul(q, q2))` term.
//!
//! Part of #2187 (VerifyThis Path A arithmetic normalization).
//! Split from monolithic normalize.rs as part of #2476.

mod arith;
mod substitution;

#[cfg(test)]
mod tests_arith;
#[cfg(test)]
mod tests_boundary;
#[cfg(test)]
mod tests_substitution;

pub(crate) use arith::normalize_int_expr;
pub(crate) use substitution::{
    accumulate_equality_binding, extract_equality_binding, insert_and_back_propagate,
    substitute_and_normalize, substitute_vars,
};
