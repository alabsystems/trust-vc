// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression: `<composed seq literal>.to_set().contains(x)` for a PRESENT
//! member must verify. A derived Set from `seq.to_set()` answers `contains`
//! as membership in the source sequence; for a source with a fully-determined
//! static length that is not a bare literal length term — a `subrange()` view,
//! a `push`-chain literal, an `add()` — the derived-Set contains path now
//! recovers that length (`seq_static_len` on the `.to_set()` receiver's source
//! expression) and delegates to the general `encode_seq_contains` with it as a
//! finite-length hint, so the concrete-index membership folds. Previously such
//! composed sources fell to a bespoke `0..5` enumeration that did not fold
//! through the composition and returned Unknown.
//!
//! SCOPE: this covers PRESENT-member membership. Refuting an ABSENT member of a
//! composed view (`...subrange(1,4).to_set().contains(40)`) still returns
//! Unknown — the fixed-array path proves a present member via one true disjunct
//! but cannot construct the counterexample for an absent one; that needs the
//! range-guarded refutation path and is tracked separately. The absent case is
//! asserted here only to be NON-verifying (soundness), not to refute cleanly.

use super::*;
use crate::encoder::VerifyResult;

fn verdict(code: &str, name: &str) -> VerifyResult {
    let file = parse_file(code).expect("fixture should parse");
    let func =
        find_function(&file, name).unwrap_or_else(|| panic!("fixture should define fn {name}"));
    extract_verification_conditions(func)
        .unwrap_or_else(|err| panic!("fn {name} should extract: {err}"))
        .verify()
}

fn assert_verified(code: &str, name: &str) {
    match verdict(code, name) {
        VerifyResult::Verified => {}
        other => panic!("fn {name} should verify (composed to_set present member), got: {other:?}"),
    }
}

/// SOUNDNESS: an ABSENT member must NOT verify. Fail-closed (Unknown/CE) is
/// acceptable; `Verified` would be a false-Verified from the delegation.
fn assert_not_verified(code: &str, name: &str) {
    match verdict(code, name) {
        VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. } => {}
        VerifyResult::Verified => {
            panic!("fn {name} must NOT verify (absent member) — a false Verified is unsound")
        }
        other => panic!("fn {name} unexpected verdict: {other:?}"),
    }
}

/// `subrange(1,4)` of `[0,10,20,30,40]` is `[10,20,30]`; `to_set().contains(20)` holds.
#[test]
fn subrange_to_set_present_member_verifies() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            trust_vc::assert!(
                trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32]
                    .subrange(1usize, 4usize)
                    .to_set()
                    .contains(20i32)
            );
        }
    "#;
    assert_verified(code, "test");
}

/// Push-chain literal `[10,20,30]`; `to_set().contains(30)` holds.
#[test]
fn pushchain_to_set_present_member_verifies() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            trust_vc::assert!(
                trust_vc_types::seq![10i32, 20i32, 30i32].to_set().contains(30i32)
            );
        }
    "#;
    assert_verified(code, "test");
}

/// SOUNDNESS: `[10,20,30].to_set().contains(15)` — 15 is absent, must NOT verify.
#[test]
fn to_set_absent_member_does_not_verify() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            trust_vc::assert!(
                trust_vc_types::seq![10i32, 20i32, 30i32].to_set().contains(15i32)
            );
        }
    "#;
    assert_not_verified(code, "test");
}
