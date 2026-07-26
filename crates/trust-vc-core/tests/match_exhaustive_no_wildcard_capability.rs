// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An EXHAUSTIVE `match` with no `_` wildcard arm (bool `true`/`false`, an
//! all-variants enum, …) in obligation position is now modeled: the LAST arm is
//! rendered `_` so the encoder — which requires a catch-all else branch — accepts
//! it (previously it failed closed with "Every non-wildcard arm must have an else
//! branch" / "Failed to encode overflow assumptions").
//!
//! SOUNDNESS: the input is valid Rust so the match is exhaustive; by top-to-bottom
//! arm order the residual after the earlier arms is exactly the last arm's cases,
//! so `_` denotes the same set (semantically exact, not an over-approximation that
//! admits a new case). The rewrite is DECLINED when the last arm binds an
//! identifier its body reads (`Some(v) => v`), so no used binding is ever dropped.
//! A false postcondition must still COUNTEREXAMPLE.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(name: &str, src: &str, target: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_match_nw_{}_{}.rs", std::process::id(), name));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), target).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

// CAPABILITY: both arms equal -> result is a constant; the postcondition holds.
const BOTH_EQUAL: &str = r#"
#[trust_vc::ensures(result == 5u32)]
fn t(x: bool) -> u32 { match x { true => 5u32, false => 5u32 } }
"#;

// CAPABILITY: a `requires` pins the scrutinee, so the matched arm's value is known.
const GUARDED: &str = r#"
#[trust_vc::requires(x == true)]
#[trust_vc::ensures(result == 10u32)]
fn t(x: bool) -> u32 { match x { true => 10u32, false => 20u32 } }
"#;

// SOUNDNESS: result depends on x, so `result == 10` is not always true -> CE.
const FALSE_ARM: &str = r#"
#[trust_vc::ensures(result == 10u32)]
fn t(x: bool) -> u32 { match x { true => 10u32, false => 20u32 } }
"#;

// SOUNDNESS: the other arm's value must also refute -> `result == 20` is not
// implied (x could be true) -> CE. Confirms the `_` arm is not a blanket true.
const FALSE_OTHER_ARM: &str = r#"
#[trust_vc::ensures(result == 20u32)]
fn t(x: bool) -> u32 { match x { true => 10u32, false => 20u32 } }
"#;

// SOUNDNESS (binding preservation): `Some(v) => v` binds `v` used in its body, so
// the last arm `None => 0` is NOT the one that would drop a binding; but the point
// is the value is `v` (5 here), so `result == 0` must NOT verify.
const BINDING_PRESERVED: &str = r#"
#[trust_vc::ensures(result == 0u32)]
fn t() -> u32 { let o: Option<u32> = Some(5u32); match o { Some(v) => v, None => 0u32 } }
"#;

#[test]
fn both_arms_equal_verifies() {
    assert!(
        matches!(verify("both", BOTH_EQUAL, "t"), VerifyResult::Verified),
        "an exhaustive wildcard-less bool match with equal arms must verify `result == 5`"
    );
}

#[test]
fn scrutinee_pinned_arm_verifies() {
    assert!(
        matches!(verify("guarded", GUARDED, "t"), VerifyResult::Verified),
        "`requires(x == true)` must pin the matched arm so `result == 10` verifies"
    );
}

#[test]
fn false_postcondition_counterexamples() {
    let r = verify("false_arm", FALSE_ARM, "t");
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "CARDINAL: `result == 10` is not implied (x could be false -> 20); must CE; got {r:?}"
    );
}

#[test]
fn other_arm_false_postcondition_counterexamples() {
    let r = verify("false_other", FALSE_OTHER_ARM, "t");
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "CARDINAL: the `_` arm is not a blanket-true; `result == 20` must CE (x could be true); got {r:?}"
    );
}

#[test]
fn used_binding_not_dropped() {
    let r = verify("binding", BINDING_PRESERVED, "t");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL: `Some(v) => v` value is 5, not 0; `result == 0` must NOT verify (binding preserved); got {r:?}"
    );
}
