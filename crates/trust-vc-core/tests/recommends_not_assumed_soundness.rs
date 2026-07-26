// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CARDINAL / SOUNDNESS REGRESSION: a function's own `#[recommends(P)]` was
//! ASSUMED as a body-level hypothesis (treated like `#[requires(P)]`), letting a
//! false postcondition/assert verify. Verus recommends is ADVISORY — it creates
//! NO body assumption; the ensures must be proven WITHOUT it (recommends is only
//! a soft-warning check). Root cause: the assumption partition
//! (prepared_context/validation.rs) pushed a BodyLevel `Recommends` obligation to
//! `assumptions`. Found by the 2026-07-24 adversarial false-verify hunt; fixed by
//! routing recommends to the soft-check `recommends` list at all modes (and
//! removing it from the loop-head frame re-assumption + the has_* queries).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_rec_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}
fn verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}

const SRC: &str = r#"
// LIAR: recommends(x==0) + ensures(result==0), body returns x — false for x!=0.
// Must NOT verify (recommends must not be assumed in the body).
#[trust_vc::recommends(x == 0i32)]
#[trust_vc::ensures(result == 0i32)]
fn rec_ensures_liar(x: i32) -> i32 { x }
// LIAR: recommends used to prove a false assert.
#[trust_vc::recommends(x == 5i32)]
#[trust_vc::ensures(true)]
fn rec_assert_liar(x: i32) { trust_vc::assert!(x == 5i32); }
// POSITIVE: recommends present, but the ensures holds WITHOUT it — must verify
// (recommends is advisory / verdict-neutral, so no over-rejection).
#[trust_vc::recommends(x > 0i32)]
#[trust_vc::ensures(result == x)]
fn rec_positive(x: i32) -> i32 { x }
// POSITIVE: a genuinely-satisfiable ensures with an unrelated recommends.
#[trust_vc::recommends(x < 100i32)]
#[trust_vc::ensures(result >= x)]
fn rec_positive2(x: i32) -> i32 { x }
"#;

#[test]
fn recommends_is_not_assumed_in_body() {
    for f in ["rec_ensures_liar", "rec_assert_liar"] {
        assert!(
            !verified(&verify(f, f, SRC)),
            "CARDINAL: `{f}`: a function's own recommends must NOT be assumed as a body \
             hypothesis — a false ensures/assert must be refuted; got {:?}",
            verify(f, f, SRC)
        );
    }
}

#[test]
fn recommends_is_verdict_neutral_for_valid_functions() {
    for f in ["rec_positive", "rec_positive2"] {
        assert!(
            verified(&verify(f, f, SRC)),
            "`{f}`: a valid function with a recommends clause must still verify (recommends is \
             advisory / verdict-neutral, not an over-rejection); got {:?}",
            verify(f, f, SRC)
        );
    }
}
