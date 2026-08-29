// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Fixture for `const_pattern_arm_soundness.rs`.
//!
//! A bare identifier in pattern position is Rust ITEM resolution, not a
//! binding, whenever a `const` of that name is in scope. Every function here
//! exists in a matched pair: the const-named form and the literal form that is
//! its exact Rust equivalent. The two must reach the SAME verdict.
#![allow(non_upper_case_globals)]
#![allow(dead_code)]

pub const K: u64 = 5;
pub const lower_k: u64 = 5;

// ---- THE CARDINAL FALSE VERIFY --------------------------------------------
// The `K` arm was classified "always matches", so the wildcard arm's
// prior-negation became `!(true)` — FALSE — and vacuously discharged its
// assertion. The `5` twin below is the discriminator: it always refuted.

#[trust_vc::requires(n < 100)]
pub fn const_arm_sibling_must_not_verify(n: u64) {
    match n {
        K => {}
        _ => {
            assert!(false);
        }
    }
}

#[trust_vc::requires(n < 100)]
pub fn literal_arm_sibling_must_not_verify(n: u64) {
    match n {
        5 => {}
        _ => {
            assert!(false);
        }
    }
}

/// The lowercase spelling of the same hole. `#![allow(non_upper_case_globals)]`
/// makes this legal Rust, and `E0530` still resolves the pattern to the const.
#[trust_vc::requires(n < 100)]
pub fn lowercase_const_arm_sibling_must_not_verify(n: u64) {
    match n {
        lower_k => {}
        _ => {
            assert!(false);
        }
    }
}

// ---- LIAR PINS -------------------------------------------------------------
// The const arm now SUPPLIES the fact `n == 5`. A false claim of the same shape
// must still be refuted, or the capability gain would itself be a false verify.

#[trust_vc::requires(n < 100)]
pub fn const_arm_liar_must_not_verify(n: u64) {
    match n {
        K => {
            assert!(n == 6);
        }
        _ => {}
    }
}

#[trust_vc::requires(n < 100)]
pub fn wildcard_arm_liar_must_not_verify(n: u64) {
    match n {
        K => {}
        _ => {
            assert!(n == 5);
        }
    }
}

// ---- CAPABILITY ------------------------------------------------------------

/// The selected arm knows the scrutinee equals the const's value.
#[trust_vc::requires(n < 100)]
pub fn const_arm_supplies_its_value(n: u64) {
    match n {
        K => {
            assert!(n == 5);
        }
        _ => {}
    }
}

/// The sibling arm knows the scrutinee does NOT equal it — the obligation that
/// used to be vacuous.
#[trust_vc::requires(n < 100)]
pub fn wildcard_arm_knows_the_negation(n: u64) {
    match n {
        K => {}
        _ => {
            assert!(n != 5);
        }
    }
}

// ---- NARROWNESS PINS -------------------------------------------------------
// Reclassifying a bare ident is decided by DECLARATION. An ordinary binder must
// keep binding: that is the overwhelmingly common case and breaking it would be
// a capability disaster.

#[trust_vc::requires(n < 100)]
pub fn ordinary_binder_still_binds(n: u64) {
    match n {
        m => {
            assert!(m == n);
        }
    }
}

#[trust_vc::requires(n < 100)]
pub fn ordinary_binder_liar_must_not_verify(n: u64) {
    match n {
        m => {
            assert!(m == 5);
        }
    }
}

/// A binder whose name collides with an ASSOCIATED const still binds — a bare
/// `assoc_named` never resolves to `Holder::assoc_named`.
pub struct Holder;
impl Holder {
    pub const assoc_named: u64 = 9;
}

#[trust_vc::requires(n < 100)]
pub fn binder_colliding_with_assoc_const_still_binds(n: u64) {
    match n {
        assoc_named => {
            assert!(assoc_named == n);
        }
    }
}

// ---- FAIL-CLOSED, NOT FOLDED ----------------------------------------------

/// A name declared TWICE cannot be folded to either value, so it routes to the
/// fail-closed marker. It must not verify a claim that only one of the two
/// values would support.
pub mod shadowing {
    pub const dup_k: u64 = 9;
}
pub const dup_k: u64 = 5;

#[trust_vc::requires(n < 100)]
pub fn duplicated_const_must_not_verify(n: u64) {
    match n {
        dup_k => {
            assert!(n == 5);
        }
        _ => {}
    }
}
