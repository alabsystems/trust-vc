// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Row 438 (never-type / diverging expressions) slice: an `if` whose sole
//! diverging branch is a `panic!`/`unreachable!`/`todo!`/`unimplemented!` block
//! now verifies (previously "Unsupported panic!()" fail-closed the whole
//! function). `diverging_if_desugar.rs` rewrites it to
//! `{ let fresh = guard; trust_vc::assert!(fresh); <surviving branch> }` — the
//! ordinary local preserves single evaluation, side effects, and exec panic
//! obligations; the assert is the diverging arm's UNREACHABILITY obligation.
//!
//! SOUNDNESS: an ordinary local evaluates the guard exactly once through the
//! extractor's normal exec path before the assertion adds its proof obligation.
//! Thus a guard that itself panics is still rejected, a side-effecting guard is
//! not duplicated or erased, a reachable panic fails, and a false ensures fails.
//! Generated local names cannot shadow source identifiers. A non-diverging `if`
//! and an `if let`/let-chain condition are untouched.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_dif_{}_{}.rs", std::process::id(), id));
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

fn rejected_without_encoding_error(r: &VerifyResult) -> bool {
    matches!(
        r,
        VerifyResult::Counterexample { .. }
            | VerifyResult::NotProved { .. }
            | VerifyResult::Unknown { .. }
    )
}

const SRC: &str = r#"
// panic in the else arm; the requires makes it unreachable
#[trust_vc::requires(c)]
#[trust_vc::ensures(result == 1u64)]
fn guarded_else(c: bool) -> u64 { if c { 1u64 } else { panic!() } }
// panic in the then arm
#[trust_vc::requires(!c)]
#[trust_vc::ensures(result == 2u64)]
fn guarded_then(c: bool) -> u64 { if c { panic!() } else { 2u64 } }
// unreachable! in value position (let-bound)
#[trust_vc::requires(x < 10u64)]
#[trust_vc::ensures(result == x)]
fn value_position(x: u64) -> u64 { let y = if x < 10u64 { x } else { unreachable!() }; y }
// CARDINAL: no guard → the panic is reachable → must fail
#[trust_vc::ensures(result == 1u64)]
fn unguarded(c: bool) -> u64 { if c { 1u64 } else { panic!() } }
// CARDINAL: guarded but a false ensures must still fail
#[trust_vc::requires(c)]
#[trust_vc::ensures(result == 9u64)]
fn liar(c: bool) -> u64 { if c { 1u64 } else { unreachable!() } }
// control: a non-diverging if is untouched and still verifies
#[trust_vc::ensures(result == if c { 1u64 } else { 2u64 })]
fn non_diverging(c: bool) -> u64 { if c { 1u64 } else { 2u64 } }
// The generated guard local must not shadow a source binding.
#[trust_vc::requires(c)]
#[trust_vc::ensures(result == 7u64)]
fn fresh_name_collision(c: bool) -> u64 {
    let __trust_vc_diverging_if_guard_0 = 7u64;
    if c { __trust_vc_diverging_if_guard_0 } else { panic!() }
}
// The guard mutates x once. Erasing or duplicating its evaluation changes the result.
#[trust_vc::ensures(result == 1u64)]
fn side_effecting_guard_once() -> u64 {
    let mut x = 0u64;
    if { x += 1u64; x == 1u64 } { 1u64 } else { panic!() }
}
// CARDINAL: the branch guard is logically true under SMT signed-division
// semantics, but evaluating it in Rust panics at i32::MIN / -1.
#[trust_vc::requires(a == -2147483648i32)]
#[trust_vc::requires(b == -1i32)]
#[trust_vc::ensures(result == 1u64)]
fn panicking_guard(a: i32, b: i32) -> u64 {
    if a / b == a { 1u64 } else { panic!() }
}
"#;

#[test]
fn guarded_diverging_arm_verifies() {
    for f in [
        "guarded_else",
        "guarded_then",
        "value_position",
        "non_diverging",
        "fresh_name_collision",
        "side_effecting_guard_once",
    ] {
        assert!(
            verified(&verify(f, f, SRC)),
            "`{f}`: an `if` with a provably-unreachable panic/unreachable arm should verify; \
             got {:?}",
            verify(f, f, SRC)
        );
    }
}

#[test]
fn reachable_panic_and_liar_fail_closed() {
    let unguarded = verify("unguarded", "unguarded", SRC);
    assert!(
        rejected_without_encoding_error(&unguarded),
        "CARDINAL: an unguarded (reachable) panic must be rejected by a real obligation, \
         not an encoding error; got {unguarded:?}"
    );
    let liar = verify("liar", "liar", SRC);
    assert!(
        rejected_without_encoding_error(&liar),
        "CARDINAL: a false ensures must be rejected by a real obligation, \
         not an encoding error; got {liar:?}"
    );
}

#[test]
fn guard_evaluation_is_single_and_panic_faithful() {
    let panicking = verify("panicking_guard", "panicking_guard", SRC);
    assert!(
        rejected_without_encoding_error(&panicking),
        "CARDINAL: i32::MIN / -1 in the guard must retain its exec panic obligation; \
         got {panicking:?}"
    );
}
