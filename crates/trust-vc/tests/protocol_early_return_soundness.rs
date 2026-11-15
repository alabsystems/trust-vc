// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An action's model is what Rust runs: a statement that does not return does
//! not stop the statements after it.
//!
//! An action's bare `bool` statement (`self.x < 100;`) was read as a guard
//! that disables the action, but Rust evaluates it, discards it and runs on:
//! `Guarded::step` overflows at `200 + 100` and `Once::step` reaches
//! `x == 200`, and both came back `Verified`. Such a statement is now refused;
//! a guard is an early return, `if <bool> { return; }`, before any
//! assignment, which is read as the action being disabled where it returns (a
//! step that changes nothing, as the model's stutter step is).
//!
//! Requires the `ty` feature: `targo --unverified test -p trust-vc --features ty`

#![cfg(feature = "ty")]
// A bare comparison statement is what these cases are about.
#![allow(unused_must_use, unused_comparisons)]

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

/// Rust: 0 -> 100 -> 200 -> overflow (a panic in debug) on the third step.
#[trust_vc::protocol]
#[derive(Default)]
pub struct Guarded {
    pub x: u8,
}

impl Guarded {
    #[trust_vc::action(Guarded)]
    pub fn step(&mut self) {
        self.x < 100;
        self.x = self.x + 100;
    }
}

/// Rust: the second step sets `x` to 200 and `small` fails.
#[trust_vc::protocol]
#[derive(Default)]
pub struct Once {
    pub x: u8,
    pub done: bool,
}

impl Once {
    #[trust_vc::action(Once)]
    pub fn step(&mut self) {
        !self.done;
        self.x = self.x + 100;
        self.done = true;
    }

    #[trust_vc::safety(Once)]
    pub fn small(&self) -> bool {
        self.x < 150
    }
}

/// The twin of `Guarded` with its guard an early return: Rust stops at 100.
#[trust_vc::protocol]
#[derive(Default)]
pub struct Returns {
    pub x: u8,
}

impl Returns {
    #[trust_vc::action(Returns)]
    pub fn step(&mut self) {
        if self.x >= 100 {
            return;
        }
        self.x = self.x + 100;
    }
}

/// An early return that does not stop the overflow: Rust runs `200 + 100`.
#[trust_vc::protocol]
#[derive(Default)]
pub struct ReturnsLate {
    pub x: u8,
}

impl ReturnsLate {
    #[trust_vc::action(ReturnsLate)]
    pub fn step(&mut self) {
        if self.x >= 250 {
            return;
        }
        self.x = self.x + 100;
    }
}

/// The twin of `Once` with its guard an early return: Rust stops at 100.
#[trust_vc::protocol]
#[derive(Default)]
pub struct OnceReturns {
    pub x: u8,
    pub done: bool,
}

impl OnceReturns {
    #[trust_vc::action(OnceReturns)]
    pub fn step(&mut self) {
        if self.done {
            return;
        }
        self.x = self.x + 100;
        self.done = true;
    }

    #[trust_vc::safety(OnceReturns)]
    pub fn small(&self) -> bool {
        self.x < 150
    }
}

/// An early return after an assignment: Rust has already set `x` when it
/// returns, which "the action is disabled" would not model.
#[trust_vc::protocol]
#[derive(Default)]
pub struct AssignsThenReturns {
    pub x: u8,
    pub done: bool,
}

impl AssignsThenReturns {
    #[trust_vc::action(AssignsThenReturns)]
    pub fn step(&mut self) {
        self.x = 7;
        if self.done {
            return;
        }
        self.done = true;
    }
}

/// Run `step` three times; whether Rust panicked.
fn panics(step: impl Fn()) -> bool {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(step)).is_err()
}

#[test]
fn a_bare_bool_statement_is_not_a_guard() {
    assert!(
        panics(|| {
            let mut state = Guarded::default();
            state.step();
            state.step();
            state.step();
        }),
        "ground truth: the third Rust step overflows"
    );
    assert_refused(
        &verify(Guarded::__trust_vc_register_protocol),
        "early return",
        "Guarded::step overflows at 200 + 100",
    );

    let mut once = Once::default();
    once.step();
    once.step();
    assert!(!once.small(), "ground truth: x is 200 after two Rust steps");
    assert_refused(
        &verify(Once::__trust_vc_register_protocol),
        "early return",
        "Once::small fails after two Rust steps",
    );
}

#[test]
fn an_early_return_is_a_guard() {
    assert!(!panics(|| {
        let mut state = Returns::default();
        state.step();
        state.step();
        state.step();
    }));
    assert_eq!(
        verify(Returns::__trust_vc_register_protocol),
        VerifyResult::Verified,
        "Returns stops at 100"
    );

    assert!(
        panics(|| {
            let mut state = ReturnsLate::default();
            state.step();
            state.step();
            state.step();
        }),
        "ground truth: the third Rust step overflows"
    );
    assert_violates(
        &verify(ReturnsLate::__trust_vc_register_protocol),
        "NoPanic_step",
        "ReturnsLate runs 200 + 100",
    );

    let mut once = OnceReturns::default();
    once.step();
    once.step();
    assert!(once.small(), "ground truth: x stays 100");
    assert_eq!(
        verify(OnceReturns::__trust_vc_register_protocol),
        VerifyResult::Verified,
        "OnceReturns stops at 100"
    );

    let mut late = AssignsThenReturns { x: 0, done: true };
    late.step();
    assert_eq!(late.x, 7, "ground truth: x is set before the return");
    assert_refused(
        &verify(AssignsThenReturns::__trust_vc_register_protocol),
        "before",
        "an early return after an assignment",
    );
}
