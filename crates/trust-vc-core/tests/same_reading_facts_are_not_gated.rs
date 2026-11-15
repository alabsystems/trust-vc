// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! THE READING GATE IS A NO-OP ON A SAME-READING FACT — the load-bearing claim
//! behind the round-5 attribution of the two nested-loop summary reds.
//!
//! `encoder::verification::arith_reading::fact_admission` answers `AsIs`
//! immediately when `fact_reading(fact) == into`, so a fact established in the
//! fixed-width universe reaches a fixed-width solve UNCHANGED however much
//! wrapping arithmetic it carries. Every fixture in
//! `nested_for_summary_capability` and `nested_modifying_loop_summary_capability`
//! is exactly that shape — no `by(...)` hint, no `decreases`, so both the fact
//! and the encoder read fixed width — which is why the gate (`b716c2c7`), its
//! guard (`8d980359`) and the scope-aware range guard (`e694f4b7`) cannot be
//! what changed those suites. Measured paired at identical load: merge base
//! `6913d45f` 2435.37 s, `8870e317` 2432.34 s, HEAD `40aea85c` 2416.33 s, all
//! three `ok` on the same control.
//!
//! These pins fail the moment the gate starts charging a same-reading fact:
//! drop the invariant and the post-loop assertion it entails is refuted. Each
//! carries its REFUTED liar twin, so none can pass vacuously.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_srfng_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, SRC).expect("write fixture");
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
// CONTROL: the invariant carries fixed-width `+`, which the gate CHARGES as
// reading differently across universes — but this obligation's solve reads
// fixed width too, so it must cross unchanged.
#[trust_vc::requires(n < 100u32)]
#[trust_vc::ensures(true)]
pub fn additive_invariant_crosses_same_reading(n: u32) {
    let mut i: u32 = 0;
    let mut t: u32 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(t == i + i);
        t = t + 2u32;
        i = i + 1u32;
    }
    trust_vc::assert!(t == n + n);
}

// LIAR: the same shape one off. Without a REFUTED twin the control could pass
// on a vacuous hypothesis set rather than on the invariant.
#[trust_vc::requires(n < 100u32)]
#[trust_vc::ensures(true)]
pub fn additive_invariant_off_by_one(n: u32) {
    let mut i: u32 = 0;
    let mut t: u32 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(t == i + i);
        t = t + 2u32;
        i = i + 1u32;
    }
    trust_vc::assert!(t == n + n + 1u32);
}

// CONTROL: `*` is the strongest charge the gate makes short of a shift, and it
// must still cross into a same-reading solve.
#[trust_vc::requires(n < 100u32)]
#[trust_vc::ensures(true)]
pub fn multiplicative_invariant_crosses_same_reading(n: u32) {
    let mut i: u32 = 0;
    let mut t: u32 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(t == 2u32 * i);
        t = t + 2u32;
        i = i + 1u32;
    }
    trust_vc::assert!(t == 2u32 * n);
}

// LIAR.
#[trust_vc::requires(n < 100u32)]
#[trust_vc::ensures(true)]
pub fn multiplicative_invariant_off_by_one(n: u32) {
    let mut i: u32 = 0;
    let mut t: u32 = 0;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(t == 2u32 * i);
        t = t + 2u32;
        i = i + 1u32;
    }
    trust_vc::assert!(t == 2u32 * n + 1u32);
}

// CONTROL: a `requires` reads MATHEMATICAL since `d93f0223`, so it is a
// CROSS-reading fact on the way into this fixed-width body solve. A bare
// comparison is `CrossReading::Identical`, so it must still arrive.
#[trust_vc::requires(a < 10u32)]
#[trust_vc::ensures(true)]
pub fn bare_comparison_requires_reaches_a_fixed_width_body(a: u32) {
    trust_vc::assert!(a + 1u32 <= 10u32);
}

// LIAR: the same clause cannot prove one more than it says.
#[trust_vc::requires(a < 10u32)]
#[trust_vc::ensures(true)]
pub fn bare_comparison_requires_does_not_overreach(a: u32) {
    trust_vc::assert!(a + 1u32 <= 9u32);
}
"#;

fn expect_verified(id: &str, func: &str) {
    match verify(id, func) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

fn expect_counterexample(id: &str, func: &str) {
    match verify(id, func) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("{func}: expected Counterexample, got {other:?}"),
    }
}

#[test]
fn control_additive_invariant_crosses_same_reading() {
    expect_verified("c1", "additive_invariant_crosses_same_reading");
}

#[test]
fn liar_additive_invariant_off_by_one() {
    expect_counterexample("l1", "additive_invariant_off_by_one");
}

#[test]
fn control_multiplicative_invariant_crosses_same_reading() {
    expect_verified("c2", "multiplicative_invariant_crosses_same_reading");
}

#[test]
fn liar_multiplicative_invariant_off_by_one() {
    expect_counterexample("l2", "multiplicative_invariant_off_by_one");
}

#[test]
fn control_bare_comparison_requires_reaches_a_fixed_width_body() {
    expect_verified("c3", "bare_comparison_requires_reaches_a_fixed_width_body");
}

#[test]
fn liar_bare_comparison_requires_does_not_overreach() {
    expect_counterexample("l3", "bare_comparison_requires_does_not_overreach");
}
