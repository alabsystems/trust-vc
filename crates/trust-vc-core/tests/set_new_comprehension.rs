// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! End-to-end guards for the `Set::new(|x| pred)` set-comprehension constructor
//! (upstream `rust_verify_test/tests/sets.rs` `test1`).
//!
//! The comprehension lowers to the `__trust_vc_set_new` builtin, encoded as a
//! fresh set `s` constrained by `forall x. s.contains(x) <-> pred(x)`. These
//! tests prove the defining membership equivalence verifies, and — crucially —
//! that out-of-predicate / negated-membership claims fail closed (never a false
//! `Verified`).

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    let dir = Path::new("target/set_new_comprehension");
    fs::create_dir_all(dir).unwrap();
    let f = dir.join(format!("{name}.rs"));
    fs::write(&f, code).unwrap();
    trust_vc_core::verify_function_from_file(f.to_str().unwrap(), name)
}

/// `Set::new(|i| i >= 0).contains(2)` verifies — 2 satisfies the predicate.
#[test]
fn set_new_member_in_predicate_verifies() {
    let code = r#"
#[trust_vc::requires(s.contains(2 as int))]
#[trust_vc::ensures(true)]
fn set_new_inline(s: Set<int>) {
    trust_vc::assert!(Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int))).contains(2 as int));
}
"#;
    let r = verify(code, "set_new_inline");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "predicate-true member should verify, got {:?}",
        r
    );
}

/// Upstream `test1` shape: comprehension then `filter`, positive member.
#[test]
fn set_new_then_filter_member_verifies() {
    let code = r#"
#[trust_vc::ensures(true)]
fn set_new_filter(s: Set<int>) {
    trust_vc::assert!(
        Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int)))
            .filter(SpecFn::new(|i: int| i > (0 as int)))
            .contains(3 as int)
    );
}
"#;
    let r = verify(code, "set_new_filter");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "filtered comprehension member should verify, got {:?}",
        r
    );
}

/// SOUNDNESS: asserting membership of an element the predicate EXCLUDES must NOT
/// verify (here `0` against predicate `i >= 1`). Fail-closed is required.
#[test]
fn set_new_member_outside_predicate_does_not_verify() {
    let code = r#"
#[trust_vc::ensures(true)]
fn set_new_unsound(s: Set<int>) {
    trust_vc::assert!(Set::<int>::new(SpecFn::new(|i: int| i >= (1 as int))).contains(0 as int));
}
"#;
    let r = verify(code, "set_new_unsound");
    assert!(
        !matches!(r, Ok(VerifyResult::Verified)),
        "predicate-false member must NOT verify, got {:?}",
        r
    );
}

/// SOUNDNESS: asserting NON-membership of an element the predicate INCLUDES must
/// NOT verify (here `!contains(2)` against predicate `i >= 0`). Fail-closed.
#[test]
fn set_new_negated_member_in_predicate_does_not_verify() {
    let code = r#"
#[trust_vc::ensures(true)]
fn set_new_neg(s: Set<int>) {
    trust_vc::assert!(!Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int))).contains(2 as int));
}
"#;
    let r = verify(code, "set_new_neg");
    assert!(
        !matches!(r, Ok(VerifyResult::Verified)),
        "non-membership of a predicate-true element must NOT verify, got {:?}",
        r
    );
}

/// The empty-set constructor `Set::<int>::new()` (0-arg) is unaffected by the
/// comprehension form and still aliases the empty set.
#[test]
fn set_new_empty_constructor_still_works() {
    let code = r#"
#[trust_vc::ensures(true)]
fn set_new_empty() {
    trust_vc::assert!(!Set::<int>::new().contains(0 as int));
}
"#;
    let r = verify(code, "set_new_empty");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "empty Set::new() should still verify non-membership, got {:?}",
        r
    );
}
