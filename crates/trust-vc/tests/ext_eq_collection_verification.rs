// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verification coverage for collection-aware extensional equality macros.
//!
//! These tests exercise the actual `ext_eq!` / `ext_ne!` macro surface through
//! proof functions and `VerificationPipeline`, not hand-written `==` strings.

use trust_vc_core::VerifyResult;
mod common;

#[test]
fn test_seq_ext_eq_same_elements_verified() {
    let result = common::verify_should_pass(|| {
        trust_vc::assert!(trust_vc::ext_eq!(
            trust_vc_types::Seq::<i32>::empty().push(10).push(20),
            trust_vc_types::Seq::<i32>::empty().push(10).push(20)
        ));
    });

    assert!(
        matches!(result, VerifyResult::Verified),
        "equal Seq values should verify under ext_eq!, got {result:?}"
    );
}

#[test]
fn test_assert_seqs_equal_binary_syntax_verified() {
    let result = common::verify_should_pass(|| {
        trust_vc::assert_seqs_equal!(
            trust_vc_types::Seq::<i32>::empty().push(10).push(20)
                == trust_vc_types::Seq::<i32>::empty().push(10).push(20)
        );
    });

    assert!(
        matches!(result, VerifyResult::Verified),
        "equal Seq values should verify under assert_seqs_equal!, got {result:?}"
    );
}

#[test]
fn test_assert_seqs_equal_binary_syntax_different_length_fails() {
    let result = common::verify_should_fail(|| {
        trust_vc::assert_seqs_equal!(
            trust_vc_types::Seq::<i32>::empty().push(10)
                == trust_vc_types::Seq::<i32>::empty().push(10).push(20)
        );
    });

    assert!(
        matches!(
            result,
            VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
        ),
        "different-length Seq values should refute assert_seqs_equal!, got {result:?}"
    );
}

#[test]
fn test_seq_ext_eq_different_length_fails() {
    let result = common::verify_should_fail(|| {
        trust_vc::assert!(trust_vc::ext_eq!(
            trust_vc_types::Seq::<i32>::empty().push(10),
            trust_vc_types::Seq::<i32>::empty().push(10).push(20)
        ));
    });

    assert!(
        matches!(
            result,
            VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
        ),
        "different-length Seq values should refute ext_eq!, got {result:?}"
    );
}

#[test]
fn test_seq_ext_ne_different_length_verified() {
    let result = common::verify_should_pass(|| {
        trust_vc::assert!(trust_vc::ext_ne!(
            trust_vc_types::Seq::<i32>::empty().push(10),
            trust_vc_types::Seq::<i32>::empty().push(10).push(20)
        ));
    });

    assert!(
        matches!(result, VerifyResult::Verified),
        "different-length Seq values should verify under ext_ne!, got {result:?}"
    );
}

#[test]
fn test_set_ext_eq_same_membership_verified() {
    let result = common::verify_should_pass(|| {
        trust_vc::assert!(trust_vc::ext_eq!(
            trust_vc_types::Set::<u32>::empty().insert(1).insert(2),
            trust_vc_types::Set::<u32>::empty().insert(2).insert(1)
        ));
    });

    assert!(
        matches!(result, VerifyResult::Verified),
        "equal Set membership should verify under ext_eq!, got {result:?}"
    );
}

#[test]
fn test_set_ext_eq_extra_member_fails() {
    let result = common::verify_should_fail(|| {
        trust_vc::assert!(trust_vc::ext_eq!(
            trust_vc_types::Set::<u32>::empty().insert(1).insert(2),
            trust_vc_types::Set::<u32>::empty().insert(1)
        ));
    });

    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "mismatched Set membership should refute ext_eq!, got {result:?}"
    );
}

#[test]
fn test_map_ext_eq_same_entries_verified() {
    let result = common::verify_should_pass(|| {
        trust_vc::assert!(trust_vc::ext_eq!(
            trust_vc_types::Map::<u64, i32>::empty()
                .insert(1, 10)
                .insert(2, 20),
            trust_vc_types::Map::<u64, i32>::empty()
                .insert(2, 20)
                .insert(1, 10)
        ));
    });

    assert!(
        matches!(result, VerifyResult::Verified),
        "equal Map entries should verify under ext_eq!, got {result:?}"
    );
}

#[test]
fn test_map_ext_eq_different_value_fails() {
    let result = common::verify_should_fail(|| {
        trust_vc::assert!(trust_vc::ext_eq!(
            trust_vc_types::Map::<u64, i32>::empty().insert(1, 10),
            trust_vc_types::Map::<u64, i32>::empty().insert(1, 99)
        ));
    });

    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "mismatched Map values should refute ext_eq!, got {result:?}"
    );
}

#[test]
fn test_multiset_ext_eq_same_multiplicity_verified() {
    let result = common::verify_should_pass(|| {
        trust_vc::assert!(trust_vc::ext_eq!(
            trust_vc_types::Multiset::<i32>::empty().insert(7).insert(7),
            trust_vc_types::Multiset::<i32>::singleton(7).insert(7)
        ));
    });

    assert!(
        matches!(result, VerifyResult::Verified),
        "equal Multiset multiplicities should verify under ext_eq!, got {result:?}"
    );
}

#[test]
fn test_multiset_ext_eq_different_multiplicity_fails() {
    let result = common::verify_should_fail(|| {
        trust_vc::assert!(trust_vc::ext_eq!(
            trust_vc_types::Multiset::<i32>::empty().insert(7),
            trust_vc_types::Multiset::<i32>::empty().insert(7).insert(7)
        ));
    });

    assert!(
        matches!(
            result,
            VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
        ),
        "mismatched Multiset multiplicities should refute ext_eq!, got {result:?}"
    );
}

/// `{7}` and `{7, 7}` differ in the count of 7, so `ext_ne!` is true. Both
/// operands are `empty()`-rooted insert chains, whose counts are zero off their
/// inserted keys, so `ext_eq!` between them is decided on that finite support
/// and its negation needs no witness search.
#[test]
fn test_multiset_ext_ne_different_multiplicity_verified() {
    let result = common::verify_should_pass(|| {
        trust_vc::assert!(trust_vc::ext_ne!(
            trust_vc_types::Multiset::<i32>::empty().insert(7),
            trust_vc_types::Multiset::<i32>::empty().insert(7).insert(7)
        ));
    });

    assert!(
        matches!(result, VerifyResult::Verified),
        "Multisets with different multiplicities should verify under ext_ne!, got {result:?}"
    );
}

/// Refuted twin of the test above: one operand differs, and the two multisets
/// are now equal.
#[test]
fn test_multiset_ext_ne_same_multiplicity_fails() {
    let result = common::verify_should_fail(|| {
        trust_vc::assert!(trust_vc::ext_ne!(
            trust_vc_types::Multiset::<i32>::empty().insert(7).insert(7),
            trust_vc_types::Multiset::<i32>::empty().insert(7).insert(7)
        ));
    });

    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "equal Multisets should refute ext_ne!, got {result:?}"
    );
}

/// The finite support is deduplicated by expression, so the order of inserts
/// must not make equal multisets look different.
#[test]
fn test_multiset_ext_ne_permuted_inserts_fails() {
    let result = common::verify_should_fail(|| {
        trust_vc::assert!(trust_vc::ext_ne!(
            trust_vc_types::Multiset::<i32>::empty()
                .insert(7)
                .insert(8)
                .insert(7),
            trust_vc_types::Multiset::<i32>::empty()
                .insert(8)
                .insert(7)
                .insert(7)
        ));
    });

    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Multisets equal up to insert order should refute ext_ne!, got {result:?}"
    );
}
