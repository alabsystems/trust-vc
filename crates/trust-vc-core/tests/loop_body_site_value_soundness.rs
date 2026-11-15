// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS GUARD — loop-body obligations read the SITE value, not the head
//! value (measured 2026-09-10).
//!
//! Inside a loop body the exec-arithmetic obligations (and, since the same
//! day, body `assert!`s) are rendered over fresh loop-head symbols and weakened
//! by the guard and invariants. Under that rendering a loop-modified variable
//! resolved STRAIGHT to its head symbol even after a body assignment, so a site
//! after `i = i + (MAX - 15)` checked `head + 100` instead of
//! `head + (MAX - 15) + 100`, and a genuine overflow was `Verified`. The fix
//! substitutes the head symbols INTO the site's scoped value.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_lbsv_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

const SRC: &str = r#"
// LIAR: `i + (MAX - 15)` is safe at every head (i <= 10), but `i + 100` on the
// UPDATED value overflows for every head. Verus rejects this.
#[trust_vc::requires(i <= 10u64)]
#[trust_vc::ensures(true)]
pub fn overflow_after_body_assignment(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        i = i + 18446744073709551600u64;
        let y = i + 100u64;
        i = 0u64;
    }
}

// CONTROL: the same site, but the update keeps the operand small — no overflow.
#[trust_vc::requires(i <= 10u64)]
#[trust_vc::ensures(true)]
pub fn safe_after_body_assignment(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
        let y = i + 100u64;
    }
}

// LIAR through a body-local that captured the modified var before the update.
#[trust_vc::requires(i <= 10u64)]
#[trust_vc::ensures(true)]
pub fn overflow_through_captured_local(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        i = i + 18446744073709551600u64;
        let k = i;
        let y = k + 100u64;
        i = 0u64;
    }
}
"#;

#[test]
fn overflow_after_a_body_assignment_is_refuted() {
    let result = verify("s1", "overflow_after_body_assignment", SRC);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "SOUNDNESS: the site value `head + (MAX - 15) + 100` overflows and must be refuted: {result:?}"
    );
}

#[test]
fn safe_arithmetic_after_a_body_assignment_still_verifies() {
    let result = verify("s2", "safe_after_body_assignment", SRC);
    assert!(
        matches!(result, VerifyResult::Verified),
        "no over-rejection: `head + 1 + 100` with head <= 10 is safe: {result:?}"
    );
}

#[test]
fn overflow_through_a_captured_local_does_not_verify() {
    let result = verify("s3", "overflow_through_captured_local", SRC);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "SOUNDNESS: a local that captured the updated value must not launder the overflow: {result:?}"
    );
}
