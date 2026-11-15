// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// LEG 2. Byte-identical to `const_scope_triple_alone.rs` except for ONE added
// function that `cv_probe` never calls, whose BODY declares `const cv`. In Rust
// that const is scoped to `cv_other`'s body and is NOT in scope in `cv_probe`,
// so `cv_probe`'s arm is still a BINDER and its verdict must not move.
//
// It did move. `ScopeScan` collected const names from the WHOLE file, so the
// arm became a fail-closed const-pattern marker and `cv_probe` stopped
// verifying — a const in a function the probe never calls decided the probe's
// verdict.
#![allow(non_upper_case_globals)]

#[trust_vc::requires(n < 100)]
#[trust_vc::ensures(result == n)]
pub fn cv_probe(n: u64) -> u64 {
    match n {
        cv => cv,
    }
}

#[trust_vc::requires(n < 100)]
#[trust_vc::ensures(result == n + 1)]
pub fn cv_probe_liar_must_not_verify(n: u64) -> u64 {
    match n {
        cv => cv,
    }
}

/// The only difference from leg 1. `cv_probe` does not call it.
#[trust_vc::requires(z < 100)]
pub fn cv_other(z: u64) {
    const cv: [u64; 3] = [1u64, 2u64, 3u64];
    trust_vc::assert!(z == z);
}
