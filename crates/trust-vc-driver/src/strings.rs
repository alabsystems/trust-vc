//! #5 Exact string/byte proofs — `String`/`str` + `Seq` + BV reasoning.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This superiority capability exercises trust-vc's encoding of Rust's runtime
//! string surfaces (`str` and `String`) as a *spec collection view*: a
//! [`TrustVcType::StrSlice`] / [`TrustVcType::String`] value has
//! [`view_collection_type`](trust_vc_core::ir::TrustVcType::view_collection_type)
//! `Seq<char>`, where each element is a Unicode scalar value encoded as a 32-bit
//! bitvector ([`TrustVcType::Char`]). That single fact lets a verifier reason
//! about three layers at once:
//!
//! * **String length** — `s.len()` lowers to [`CollectionOp::Len`] over the
//!   string's `Seq<char>` view, an integer-typed term usable in ordinary
//!   integer obligations (`a.len() < b.len()`, `s.len() == 3 ==> s.len() < 10`).
//! * **Character indexing** — `s[i]` lowers to an [`TrustVcExpr::Index`] whose
//!   element type is `char` (a `BitVec(32)`), so a proof can name and relate the
//!   individual code points of a symbolic string.
//! * **Mixed integer/string VCs** — because the length view is an integer term,
//!   a postcondition can be refuted by a concrete integer counterexample while a
//!   string parameter is in scope (the seam stays *sound*, not a rubber stamp).
//!
//! Verus reaches the same surface only by routing `str`/`String` through Z3's
//! string theory, whose quantifier instantiation (MBQI) is fragile; here the
//! `Seq<char>` view is a first-class IR shape with a native length companion, so
//! the load-bearing length/index facts decide without that fragility.
//!
//! ## Scope and fail-closed boundary
//!
//! These helpers build the *exact shapes the encoder supports today* in the
//! default (non-`native-strings`) build: the `Seq<char>` length view, integer
//! relations over those lengths, and `char`-typed indexing/equality. They are
//! deliberately conservative — an obligation the backend cannot decide comes
//! back [`Outcome::Unknown`], never a false [`Outcome::Verified`]. The companion
//! `tests/strings.rs` pins both a proven length relation and a refuted
//! (counterexample-bearing) postcondition end to end through the real ay backend.

use trust_vc_core::ir::{ArithOp, CollectionOp, CompareOp, LogicOp, TrustVcExpr, TrustVcType};

pub use crate::lower::Outcome;

/// The integer type used for string-length and index obligations.
///
/// String lengths and indices are non-negative magnitudes; `i64` is wide enough
/// for any realistic length and keeps the term in the integer theory the length
/// companion is encoded against.
#[must_use]
pub fn len_int() -> TrustVcType {
    TrustVcType::Int { width: 64 }
}

/// The Rust `str` runtime surface type (`view()` = `Seq<char>`).
#[must_use]
pub fn str_slice() -> TrustVcType {
    TrustVcType::StrSlice
}

/// The owned Rust `String` runtime surface type (`view()` = `Seq<char>`).
#[must_use]
pub fn string() -> TrustVcType {
    TrustVcType::String
}

/// The `char` element type of a string view: a Unicode scalar (`BitVec(32)`).
#[must_use]
pub fn char_ty() -> TrustVcType {
    TrustVcType::Char
}

/// A typed reference to a string-like parameter named `name`.
///
/// `ty` must be string-like ([`str_slice`] or [`string`]); the function is
/// total but only string-like types expose the `Seq<char>` view the other
/// helpers reason about.
#[must_use]
pub fn str_var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}

/// `name.view().len()` — the length of a string's `Seq<char>` view, as an
/// `i64`-typed integer term ([`CollectionOp::Len`]).
///
/// `ty` is the receiver's string-like type. The `receiver_name` is threaded so
/// the encoder can attach the value's length companion.
#[must_use]
pub fn str_len(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Len,
        receiver: Box::new(str_var(name, ty)),
        receiver_name: Some(name.to_string()),
        args: vec![],
        ty: len_int(),
    }
}

/// `name[index]` — the `char` at a constant index of a string's `Seq<char>`
/// view ([`TrustVcExpr::Index`], element type `char`).
#[must_use]
pub fn char_at(name: &str, ty: TrustVcType, index: i128) -> TrustVcExpr {
    TrustVcExpr::Index {
        receiver: Box::new(str_var(name, ty)),
        index: Box::new(TrustVcExpr::IntLit {
            value: index,
            ty: len_int(),
        }),
        receiver_name: Some(name.to_string()),
        elem_ty: char_ty(),
    }
}

/// A `char` literal as a 32-bit value (the Unicode scalar of `c`).
#[must_use]
pub fn char_lit(c: char) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value: i128::from(u32::from(c)),
        ty: char_ty(),
    }
}

/// An `i64` integer literal for length/index obligations.
#[must_use]
pub fn len_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: len_int(),
    }
}

/// `left <op> right` comparison (for length/index/char relations).
#[must_use]
pub fn compare(op: CompareOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}

/// `left + right` over `i64` length terms.
#[must_use]
pub fn len_add(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(left),
        right: Box::new(right),
        ty: len_int(),
    }
}

/// `left && right`.
#[must_use]
pub fn all(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(left),
        right: Box::new(right),
    }
}

/// A grounding assumption `name.len() >= 0` that keeps a string parameter's
/// length view in scope **without** pinning its length array to a concrete
/// value.
///
/// This is the fail-closed seam for *refutation* in the presence of a string:
/// the encoder can build a model for a free string of unconstrained length, so a
/// false integer postcondition is refuted with a concrete counterexample, while
/// an equality such as `name.len() == k` (which forces a precise length-array
/// model) is intentionally avoided here.
#[must_use]
pub fn len_nonneg(name: &str, ty: TrustVcType) -> TrustVcExpr {
    compare(CompareOp::Ge, str_len(name, ty), len_lit(0))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn str_len_is_collection_len_over_view() {
        match str_len("s", str_slice()) {
            TrustVcExpr::CollectionOp {
                op,
                receiver_name,
                ty,
                ..
            } => {
                assert_eq!(op, CollectionOp::Len);
                assert_eq!(receiver_name.as_deref(), Some("s"));
                assert_eq!(ty, len_int());
            }
            other => panic!("expected CollectionOp::Len, got {other:?}"),
        }
    }

    #[test]
    fn string_like_types_view_as_seq_char() {
        // The whole capability rests on this view identity.
        let seq_char = TrustVcType::Seq(Box::new(TrustVcType::Char));
        assert_eq!(str_slice().view_collection_type(), Some(seq_char.clone()));
        assert_eq!(string().view_collection_type(), Some(seq_char));
        assert!(str_slice().is_string_like());
        assert!(string().is_string_like());
    }

    #[test]
    fn char_at_indexes_with_char_element_type() {
        match char_at("s", string(), 0) {
            TrustVcExpr::Index {
                elem_ty,
                receiver_name,
                ..
            } => {
                assert_eq!(elem_ty, char_ty());
                assert_eq!(receiver_name.as_deref(), Some("s"));
            }
            other => panic!("expected Index, got {other:?}"),
        }
    }

    #[test]
    fn char_lit_encodes_unicode_scalar() {
        match char_lit('A') {
            TrustVcExpr::IntLit { value, ty } => {
                assert_eq!(value, 65);
                assert_eq!(ty, char_ty());
            }
            other => panic!("expected IntLit, got {other:?}"),
        }
    }
}
