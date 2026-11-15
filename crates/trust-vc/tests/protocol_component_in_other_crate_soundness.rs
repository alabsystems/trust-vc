// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A protocol's model holds every component declared for it, in whichever
//! crate it is declared and whatever that crate was built with.
//!
//! `trust_vc_protocol_fixture_mc` (built with `--cfg trust_mc`) declares
//! `Calm { x: u8 }`: `settle` sets `x` to 1 and `small` is `x < 5`.
//! `trust_vc_protocol_fixture_plain`, built as any library a test links is
//! (neither `test` nor `trust_mc`), declares
//! `#[trust_vc::action(Calm)] fn jump(&mut self) { self.x = 7 }`. The
//! component's entry was compiled only under the DECLARING crate's
//! `cfg(any(test, trust_mc))`, so `jump` was left out of the model and `Calm`
//! came back `Verified` while `jump` breaks `small` in Rust.
//!
//! Requires the `ty` feature: `targo --unverified test -p trust-vc --features ty`

#![cfg(feature = "ty")]

mod common;

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;
use trust_vc_protocol_fixture_mc::{Calm, Gate, Still};
use trust_vc_protocol_fixture_plain::Jump;

fn verify(register: fn()) -> VerifyResult {
    common::with_clean_verification(|| {
        register();
        VerificationPipeline::collect_from_macros().verify()
    })
}

/// A counterexample to the property named `property`.
#[track_caller]
fn assert_violates(result: &VerifyResult, property: &str, label: &str) {
    assert!(
        matches!(
            result,
            VerifyResult::Counterexample { obligation_name, .. } if obligation_name == property
        ),
        "{label}: expected a counterexample to {property}, got {result:?}"
    );
}

#[test]
fn a_component_declared_in_a_crate_built_without_trust_mc_is_in_the_model() {
    let mut calm = Calm::default();
    calm.settle();
    calm.jump();
    assert!(!calm.small(), "ground truth: jump breaks small");
    assert_violates(
        &verify(Calm::__trust_vc_register_protocol),
        "small",
        "jump is declared in the plain crate",
    );
    assert_violates(
        &verify(Gate::__trust_vc_register_protocol),
        "small",
        "control: jump is declared in the trust_mc crate",
    );
    assert_eq!(
        verify(Still::__trust_vc_register_protocol),
        VerifyResult::Verified,
        "twin: no jump, x stays in 0..1"
    );
}
