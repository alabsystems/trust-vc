// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CARDINAL / SOUNDNESS REGRESSION: the file-path extractor rewrites a
//! wildcard-less match's LAST arm as a catch-all `_` (the cefc47d "exhaustive
//! match with no `_`" transformation). That rewrite is sound ONLY for an
//! EXHAUSTIVE match — but the syn file-path never exhaustiveness-checked, so a
//! NON-exhaustive `match x { A(_)=>10, B(_)=>20 }` (missing `C`) pinned the
//! uncovered `C` case to the last arm (20) and verified a false postcondition.
//! Found by the 2026-07-24 adversarial false-verify hunt; fixed by gating the
//! rewrite on a real exhaustiveness check (all-variants enum / both-values bool),
//! else the encoder fail-closes ("every non-wildcard arm must have an else").

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_nex_{}_{}.rs", std::process::id(), id));
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
enum Three { A(u64), B(u64), C(u64) }
// NON-exhaustive (no C arm, no wildcard): C is uncovered. Claiming result == 20
// for `x is C` must NOT verify — C is not handled.
#[trust_vc::requires(x is C)]
#[trust_vc::ensures(result == 20u64)]
fn nonexhaustive_liar(x: Three) -> u64 { match x { Three::A(_) => 10u64, Three::B(_) => 20u64 } }
// EXHAUSTIVE (all three variants, no wildcard) — the cefc47d capability. Must
// still verify (no over-rejection): x is C → 30.
#[trust_vc::requires(x is C)]
#[trust_vc::ensures(result == 30u64)]
fn exhaustive_ok(x: Three) -> u64 {
    match x { Three::A(_) => 10u64, Three::B(_) => 20u64, Three::C(_) => 30u64 }
}
// EXHAUSTIVE liar: claim result == 31 (real C arm is 30) — must be refuted.
#[trust_vc::requires(x is C)]
#[trust_vc::ensures(result == 31u64)]
fn exhaustive_liar(x: Three) -> u64 {
    match x { Three::A(_) => 10u64, Three::B(_) => 20u64, Three::C(_) => 30u64 }
}
"#;

#[test]
fn nonexhaustive_match_does_not_pin_uncovered_case() {
    assert!(
        !verified(&verify("nonexhaustive_liar", "nonexhaustive_liar", SRC)),
        "CARDINAL: a non-exhaustive match must NOT pin its uncovered variant to the last arm \
         — `result == 20` for an uncovered `C` must not verify; got {:?}",
        verify("nonexhaustive_liar", "nonexhaustive_liar", SRC)
    );
}

#[test]
fn exhaustive_wildcardless_match_still_works() {
    assert!(
        verified(&verify("exhaustive_ok", "exhaustive_ok", SRC)),
        "an exhaustive wildcard-less match (all variants) must still verify (the fix is \
         fail-closed for non-exhaustive only, not over-rejecting); got {:?}",
        verify("exhaustive_ok", "exhaustive_ok", SRC)
    );
    assert!(
        !verified(&verify("exhaustive_liar", "exhaustive_liar", SRC)),
        "CARDINAL: an exhaustive match's wrong value must still be refuted; got {:?}",
        verify("exhaustive_liar", "exhaustive_liar", SRC)
    );
}
