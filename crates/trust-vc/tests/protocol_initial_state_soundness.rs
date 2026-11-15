// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A `#[protocol]` model starts where Rust starts it: the struct's
//! `Default::default()`.
//!
//! The model's `Init` put every field at `0` / `FALSE`, documented as
//! `Default::default()`, and never read the struct's own `Default`:
//! `Started::default()` is `x == 200`, which breaks `small`, and `Started`
//! came back `Verified`. A struct without `Default` has no initial state the
//! lane can read, and one whose `Default::default()` returns two different
//! states has no one initial state; both are refused.
//!
//! Requires the `ty` feature: `targo --unverified test -p trust-vc --features ty`

#![cfg(feature = "ty")]

mod common;

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

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

/// A refusal whose message names `why`.
#[track_caller]
fn assert_refused(result: &VerifyResult, why: &str, label: &str) {
    assert!(
        matches!(result, VerifyResult::Error { message } if message.contains(why)),
        "{label}: expected a refusal naming {why:?}, got {result:?}"
    );
}

/// `Started::default()` is `x == 200`: `small` fails in the initial state.
#[trust_vc::protocol]
pub struct Started {
    pub x: u8,
}

impl Default for Started {
    fn default() -> Self {
        Started { x: 200 }
    }
}

impl Started {
    #[trust_vc::action(Started)]
    pub fn reset(&mut self) {
        self.x = 0;
    }

    #[trust_vc::safety(Started)]
    pub fn small(&self) -> bool {
        self.x < 100
    }
}

/// `Armed::default()` is `on == true`: `off` fails in the initial state.
#[trust_vc::protocol]
pub struct Armed {
    pub on: bool,
}

impl Default for Armed {
    fn default() -> Self {
        Armed { on: true }
    }
}

impl Armed {
    #[trust_vc::action(Armed)]
    pub fn disarm(&mut self) {
        self.on = false;
    }

    #[trust_vc::safety(Armed)]
    pub fn off(&self) -> bool {
        !self.on
    }
}

/// The twin: the derived `Default` is `x == 0`, and `x` stays 0.
#[trust_vc::protocol]
#[derive(Default)]
pub struct Calm {
    pub x: u8,
}

impl Calm {
    #[trust_vc::action(Calm)]
    pub fn reset(&mut self) {
        self.x = 0;
    }

    #[trust_vc::safety(Calm)]
    pub fn small(&self) -> bool {
        self.x < 100
    }
}

/// No `Default`: no initial state the lane can read.
#[trust_vc::protocol]
pub struct Bare {
    pub x: u8,
}

impl Bare {
    #[trust_vc::action(Bare)]
    pub fn reset(&mut self) {
        self.x = 0;
    }

    #[trust_vc::safety(Bare)]
    pub fn small(&self) -> bool {
        self.x < 100
    }
}

static DRIFT: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(0);

/// Each `Drifting::default()` starts one further along.
#[trust_vc::protocol]
pub struct Drifting {
    pub x: u8,
}

impl Default for Drifting {
    fn default() -> Self {
        let x = DRIFT.fetch_add(1, std::sync::atomic::Ordering::SeqCst) % 50;
        Drifting { x }
    }
}

impl Drifting {
    #[trust_vc::action(Drifting)]
    pub fn reset(&mut self) {
        self.x = 0;
    }

    #[trust_vc::safety(Drifting)]
    pub fn small(&self) -> bool {
        self.x < 100
    }
}

#[test]
fn the_initial_state_is_the_structs_default() {
    assert!(!Started::default().small(), "ground truth: x == 200");
    assert_violates(
        &verify(Started::__trust_vc_register_protocol),
        "small",
        "Started::default() is x == 200",
    );
    assert!(!Armed::default().off(), "ground truth: on == true");
    assert_violates(
        &verify(Armed::__trust_vc_register_protocol),
        "off",
        "Armed::default() is on == true",
    );
    assert!(Calm::default().small(), "ground truth: x == 0");
    assert_eq!(
        verify(Calm::__trust_vc_register_protocol),
        VerifyResult::Verified,
        "twin: the derived Default is x == 0"
    );
}

#[test]
fn a_protocol_without_one_default_state_is_refused() {
    let bare = Bare { x: 0 };
    assert!(bare.small());
    assert_refused(
        &verify(Bare::__trust_vc_register_protocol),
        "Default",
        "Bare has no Default",
    );
    let (first, second) = (Drifting::default(), Drifting::default());
    assert_ne!(first.x, second.x, "ground truth: two different states");
    assert!(first.small() && second.small());
    assert_refused(
        &verify(Drifting::__trust_vc_register_protocol),
        "Default",
        "Drifting::default() is not one state",
    );
}
