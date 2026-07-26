// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The std `matches!(EXPR, PAT [if GUARD])` macro now lowers everywhere — it was
//! previously an unsupported macro that fail-closed the function.
//! `matches_macro_desugar.rs` rewrites it to its exact expansion
//! `match EXPR { PAT [if GUARD] => true, _ => false }`, which the encoder already
//! handles soundly, in the body, `assert!` bodies, and contract attributes.
//!
//! SOUNDNESS: the rewrite is the macro's definitional expansion (behavior-
//! preserving), so it can only turn a fail-closed function into a soundly
//! verified or refuted one — a false `matches!` in an assert is refuted.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_mm_{}_{}.rs", std::process::id(), id));
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
// matches! in a requires clause
#[trust_vc::requires(matches!(o, Some(_)))]
#[trust_vc::ensures(result == 1u64)]
fn in_requires(o: Option<u64>) -> u64 { match o { Some(_) => 1u64, None => 0u64 } }
// matches! with an `if` guard on the pattern
#[trust_vc::requires(matches!(o, Some(n) if n > 3u64))]
#[trust_vc::ensures(result >= 4u64)]
fn with_guard(o: Option<u64>) -> u64 { match o { Some(n) => n, None => 0u64 } }
// matches! inside an assert!
#[trust_vc::requires(o == Some(5u64))]
#[trust_vc::ensures(true)]
fn in_assert(o: Option<u64>) { trust_vc::assert!(matches!(o, Some(_))); }
// matches! as the exec return value
#[trust_vc::requires(o == Some(5u64))]
#[trust_vc::ensures(result)]
fn in_body(o: Option<u64>) -> bool { matches!(o, Some(_)) }
// CARDINAL LIAR: a false matches! in an assert must be refuted
#[trust_vc::requires(o == None)]
#[trust_vc::ensures(true)]
fn liar(o: Option<u64>) { trust_vc::assert!(matches!(o, Some(_))); }
"#;

#[test]
fn matches_macro_lowers_everywhere() {
    for f in ["in_requires", "with_guard", "in_assert", "in_body"] {
        assert!(
            verified(&verify(f, f, SRC)),
            "`{f}`: `matches!` should lower to its `match` expansion and verify; got {:?}",
            verify(f, f, SRC)
        );
    }
}

#[test]
fn false_matches_in_assert_fails_closed() {
    assert!(
        !verified(&verify("liar", "liar", SRC)),
        "CARDINAL: `assert!(matches!(o, Some(_)))` with `o == None` must NOT verify"
    );
}
