// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the file-path closure! def-side spec adversarial soundness suite.
// Verified via verify_function_from_file in closure_spec_soundness.rs.

// ---------------------------------------------------------------------------
// POSITIVE: a def-side-valid, never-called closure verifies.
// requires y == 2; body y; result == y; under the requires, result == 2, so
// ensures(z == 2) holds. VERIFIED (one obligation).
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn def_side_valid_verified() {
    let _ = trust_vc::closure!(
        |y: u64| -> u64
        requires(y == 2u64)
        ensures(|z: u64| z == 2u64)
        y
    );
}

// ---------------------------------------------------------------------------
// NEGATIVE (bad ensures): body y with requires y == 2 gives result == 2, but the
// ensures claims z == 3. COUNTEREXAMPLE on the def-side ensures. Must not verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn def_side_bad_ensures_counterexample() {
    let _ = trust_vc::closure!(
        |y: u64| -> u64
        requires(y == 2u64)
        ensures(|z: u64| z == 3u64)
        y
    );
}

// ---------------------------------------------------------------------------
// ASSUME-LEAK PROBE (lying ensures): requires true, body y (arbitrary), so
// result == y for an arbitrary y, but the ensures claims z == 100. The def-side
// check REJECTS this lie ⇒ COUNTEREXAMPLE. This is exactly the closure a naive
// call-site-ensures injection would false-verify; the mandatory def-side check
// kills it. Must not verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn lying_ensures_rejected_counterexample() {
    let _ = trust_vc::closure!(
        |y: u64| -> u64
        requires(true)
        ensures(|z: u64| z == 100u64)
        y
    );
}

// ---------------------------------------------------------------------------
// CAPTURE PROBE (mutation-capture false-verify): the ensures references a
// captured outer variable `c`. Even though it "holds" at definition time, `c`
// could change afterward, so trusting this ensures anywhere would false-verify.
// Must fail closed (the capture guard, or lowering of an unmodeled name). Must
// not verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn capture_in_ensures_fail_closed() {
    let c = 5u64;
    let _ = trust_vc::closure!(
        |y: u64| -> u64
        requires(y == 2u64)
        ensures(|z: u64| z == c)
        c
    );
    trust_vc::assert!(c == 5u64);
}

// ---------------------------------------------------------------------------
// CALL-SITE INJECTION PROBE: a def-side-VALID closure is then CALLED. The call
// site must NOT trust the closure's ensures / return value — it stays fail
// closed ("unknown return type for function 'f'"). If the call assumed ensures,
// `t == 100` would false-verify. Must not verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn call_site_does_not_trust_ensures() {
    let f = trust_vc::closure!(
        |y: u64| -> u64
        requires(true)
        ensures(|z: u64| z == y)
        y
    );
    let t = f(3u64);
    trust_vc::assert!(t == 100u64);
}

// `requires(false)` belongs inside the closure contract.  Exporting it as an
// enclosing-function assumption would make the false assertion vacuous.
#[trust_vc::ensures(true)]
fn requires_false_cannot_poison_parent() {
    let _ = trust_vc::closure!(
        |y: u64| -> u64
        requires(false)
        ensures(|z: u64| z == y)
        y
    );
    trust_vc::assert!(false);
}
