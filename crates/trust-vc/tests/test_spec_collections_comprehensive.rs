// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Comprehensive tests for spec collections (Seq, Set, Map)
//!
//! Known gap (#2274 Group D): Ghost collection methods (Seq::index, Map::get)
//! panic at runtime. The assert_by! macro evaluates expressions at runtime in
//! test mode, which conflicts with spec-only ghost methods. These tests document
//! the limitation until the encoder can handle collection operations symbolically.

use trust_vc::assert_by;
use trust_vc_types::{Map, Seq, Set};

mod common;
use common::*;

/// Documentation test showing spec collection usage
/// ```
/// use trust_vc_types::{Seq, Set, Map};
/// use trust_vc::{assert_by};
///
/// fn collection_example() {
///     let seq = Seq::empty().push(1).push(2).push(3);
///     assert_by!(seq.len() == 3);
///
///     let set = Set::empty().insert("a").insert("b");
///     assert_by!(set.contains("a"));
///
///     let map = Map::empty().insert("key", 42);
///     assert_by!(map.get("key") == 42);
/// }
/// ```
pub fn collections_example() {}

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // Seq tests — Seq::index is ghost-only, panics at runtime
    // =========================================================================

    #[test]
    fn test_seq_basic_operations() {
        with_clean_verification(|| {
            // Seq is entirely ghost — len() always returns 0 at runtime
            let empty = Seq::<i32>::empty();
            assert_eq!(empty.len(), 0); // ghost len

            // push() returns a new phantom Seq — len() still 0 at runtime
            let s = Seq::<i32>::empty().push(42);
            assert_eq!(s.len(), 0); // ghost: logical len is 1, runtime len is 0

            // index() is ghost-only — panics at runtime
            let result = std::panic::catch_unwind(|| s.index(0));
            assert!(
                result.is_err(),
                "Seq::index is ghost-only, should panic at runtime"
            );
        });
    }

    #[test]
    fn test_seq_indexing() {
        with_clean_verification(|| {
            // Seq construction doesn't panic
            let s = Seq::empty().push(10).push(20).push(30);
            // Runtime len is always 0 (ghost type)
            assert_eq!(s.len(), 0);

            // Indexing panics — ghost-only method
            let result = std::panic::catch_unwind(|| s.index(0));
            assert!(
                result.is_err(),
                "Seq::index is ghost-only, should panic at runtime"
            );
        });
    }

    #[test]
    fn test_seq_slice() {
        with_clean_verification(|| {
            let s = Seq::empty().push(1).push(2).push(3).push(4).push(5);
            // Runtime len is always 0 (ghost type)
            assert_eq!(s.len(), 0);

            // subrange returns a new ghost Seq
            let sub = s.subrange(1, 3);
            assert_eq!(sub.len(), 0); // ghost

            // Indexing into the slice panics — ghost-only
            let result = std::panic::catch_unwind(|| sub.index(0));
            assert!(
                result.is_err(),
                "Seq::index is ghost-only, should panic at runtime"
            );
        });
    }

    // =========================================================================
    // Set tests — encoder gaps for Set::empty, Set::union in TypeEnv
    // =========================================================================

    #[test]
    fn test_set_basic_operations() {
        with_clean_verification(|| {
            // Set construction works at runtime
            let empty = Set::<i32>::empty();
            let s1 = empty.insert(10);
            let s2 = s1.insert(20);
            let _s3 = s2.insert(10); // duplicate

            // assert_by! with set operations hits encoder "unresolved variable" gap
            assert_by!(!empty.contains(42));
            let pipeline =
                trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
            let result = pipeline.verify();
            // Known gap: encoder cannot resolve Set variable names
            assert!(
                !matches!(result, trust_vc_core::VerifyResult::Verified),
                "Set encoder gap — expected Error, got: {:?}",
                result
            );
        });
    }

    #[test]
    fn test_set_operations() {
        with_clean_verification(|| {
            let s1 = Set::empty().insert(1).insert(2).insert(3);
            let s2 = Set::empty().insert(2).insert(3).insert(4);
            let _union = s1.union(s2);

            // assert_by! with union hits encoder gap
            assert_by!(s1.contains(1));
            let pipeline =
                trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
            let result = pipeline.verify();
            // Known gap: encoder cannot resolve Set operation variables
            assert!(
                !matches!(result, trust_vc_core::VerifyResult::Verified),
                "Set encoder gap — expected Error, got: {:?}",
                result
            );
        });
    }

    // =========================================================================
    // Map tests — Map::get is ghost-only, panics at runtime
    // =========================================================================

    #[test]
    fn test_map_basic_operations() {
        with_clean_verification(|| {
            let empty = Map::<i32, String>::empty();
            let m1 = empty.insert(10, "ten".to_string());
            let _m2 = m1.clone().insert(20, "twenty".to_string());

            // Map::get is ghost-only — panics at runtime
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| m1.get(10)));
            assert!(
                result.is_err(),
                "Map::get is ghost-only, should panic at runtime"
            );
        });
    }

    #[test]
    fn test_map_complex_values() {
        with_clean_verification(|| {
            let m = Map::<String, Seq<i32>>::empty()
                .insert("a".to_string(), Seq::empty().push(1).push(2));

            // Map::get is ghost-only
            let result =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| m.get("a".to_string())));
            assert!(
                result.is_err(),
                "Map::get is ghost-only, should panic at runtime"
            );
        });
    }

    #[test]
    fn test_nested_collections() {
        with_clean_verification(|| {
            // Nested collection construction works at runtime
            let seq_of_sets = Seq::<Set<i32>>::empty()
                .push(Set::empty().insert(1).insert(2))
                .push(Set::empty().insert(3).insert(4));
            assert_eq!(seq_of_sets.len(), 0); // ghost: runtime len always 0

            // But indexing into nested collections panics — ghost-only
            let result = std::panic::catch_unwind(|| seq_of_sets.index(0));
            assert!(
                result.is_err(),
                "Seq::index is ghost-only, should panic at runtime"
            );
        });
    }

    /// Collection operations with quantifiers — compilation test only
    #[test]
    fn test_collections_with_quantifiers() {
        with_clean_verification(|| {
            let s = Seq::empty().push(2).push(4).push(6).push(8);

            // Compilation test only — `s` is runtime, not verifiable through pipeline
            let _ = trust_vc::forall!(|i: usize| i >= s.len() || s.index(i) % 2 == 0);
            let _ = trust_vc::exists!(|i: usize| i < s.len() && s.index(i) == 6);

            let ctx = trust_vc_core::verify_macro::get_context();
            assert!(ctx.is_some(), "Quantifier obligations should be collected");
        });
    }
}
