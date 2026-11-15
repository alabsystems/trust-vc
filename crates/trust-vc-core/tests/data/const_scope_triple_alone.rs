// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// LEG 1 of the decisive triple for `const_pattern_desugar`'s scope model.
// `cv_probe` is a bare BINDER arm and NOTHING else is in this file. The three
// legs share this function byte for byte; only what surrounds it moves.
#![allow(non_upper_case_globals)]

#[trust_vc::requires(n < 100)]
#[trust_vc::ensures(result == n)]
pub fn cv_probe(n: u64) -> u64 {
    match n {
        cv => cv,
    }
}

/// The DISCRIMINATOR. A binder binds the scrutinee, it does not constrain it,
/// so the false claim of the identical shape must refute. Without this the pin
/// above proves only that something verified.
#[trust_vc::requires(n < 100)]
#[trust_vc::ensures(result == n + 1)]
pub fn cv_probe_liar_must_not_verify(n: u64) -> u64 {
    match n {
        cv => cv,
    }
}
