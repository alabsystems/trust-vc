//! TrustVc standard library scaffold.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

/// Arithmetic lemma specifications for integer types.
pub mod arithmetic;
/// Map lemma specifications for `trust_vc_types::Map`.
pub mod map;
/// Multiset lemma specifications for `trust_vc_types::Multiset`.
pub mod multiset;
/// Sequence lemma specifications for `trust_vc_types::Seq`.
pub mod seq;
/// Set lemma specifications for `trust_vc_types::Set`.
pub mod set;

/// End-to-end opacity tests for `arithmetic::{mul, add, sub}` imported ACROSS a
/// file boundary (`use crate::arithmetic::…`) — the cross-file analogue of the
/// in-file `arithmetic::opaque_arith` tests. Test-only.
#[cfg(test)]
mod cross_file_arith_import;
