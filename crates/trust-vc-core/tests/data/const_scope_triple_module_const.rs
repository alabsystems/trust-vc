// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// LEG 3, the leg that separates a correct scope model from a blanket change.
// The SAME const name, moved to MODULE scope, where it really IS in scope in
// every function of the module. `cv_probe`'s arm is therefore NOT a binder: it
// is a const pattern, and since `[u64; 3]` is not a foldable literal the pass
// must fail CLOSED on it rather than let the arm bind.
//
// A fix that simply narrowed the scan to "this function's own body" would make
// this leg bind and verify — a FALSE VERIFY. That is what this file is for.
#![allow(non_upper_case_globals)]

pub const cv: [u64; 3] = [1u64, 2u64, 3u64];

#[trust_vc::requires(n < 100)]
#[trust_vc::ensures(result == n)]
pub fn cv_probe(n: u64) -> u64 {
    match n {
        cv => cv,
    }
}

/// The CAPABILITY half of leg 3: a module-scope const that IS foldable must
/// still supply its value, or "fails closed" would be indistinguishable from
/// "the feature is off".
pub const cw: u64 = 5;

#[trust_vc::requires(n < 100)]
pub fn cw_value_is_modeled(n: u64) {
    match n {
        cw => {
            trust_vc::assert!(n == 5);
        }
        _ => {}
    }
}

/// Its DISCRIMINATOR: the arm supplies `n == 5`, so `n == 6` must refute.
#[trust_vc::requires(n < 100)]
pub fn cw_value_liar_must_not_verify(n: u64) {
    match n {
        cw => {
            trust_vc::assert!(n == 6);
        }
        _ => {}
    }
}
