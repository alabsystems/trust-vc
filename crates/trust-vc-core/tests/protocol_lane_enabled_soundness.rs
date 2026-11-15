//! The ty protocol lane answers ENABLED by its meaning where an older ty's
//! ENABLED search read a set filter's predicate in the wrong scope, and no
//! setting of this process's environment reconfigures the ty run.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Each case below but the twins came back `Verified`, at the ty this lane
//! once linked, for a property that does not hold:
//! - that ty's ENABLED search tested the predicate of a set filter it met as
//!   a value in the scope of the ENABLED expression: with
//!   `F(k) == {s \in SUBSET {1, 2} : k \in s}`, `\A k \in {2} : ENABLED
//!   (x' \in F(7) /\ x' = {2})` read `F(7)` with `k = 2`. The lane refused
//!   every such shape; it now requires `check-enabled-contract-v1` of the
//!   run, so each must be refuted;
//! - `TY_SKIP_LIVENESS` in the environment made ty skip every liveness
//!   property and report success. The lane refused any `TY_*` variable; it
//!   now runs ty with the environment cleared, so the property is checked.
//!
//! The twins show what the lane still checks: ENABLED over a filter whose
//! predicate reads no bound name, fairness, and the same capture shapes in
//! `Next`.
//!
//! Requires the `ty` feature and a `ty` advertising every required
//! capability (`TRUST_VC_TY_BIN`, else `ty` on `PATH`):
//! `targo --unverified test -p trust-vc-core --features ty`

#![cfg(feature = "ty")]

mod common;

use trust_vc_core::protocol::ProtocolObligation;
use trust_vc_core::verification_bridge::{
    register_protocol, register_protocol_action, register_protocol_liveness,
    register_protocol_state_var, VerificationPipeline,
};
use trust_vc_core::VerifyResult;

fn raw_spec(spec: String, config: &str) -> VerifyResult {
    common::with_clean_verification(|| {
        register_protocol(ProtocolObligation {
            name: "R".into(),
            spec,
            config: config.into(),
            shape: None,
        });
        VerificationPipeline::collect_from_macros().verify()
    })
}

/// The subsets of `{1, 2}` holding `k`.
const F: &str = "F(k) == {s \\in SUBSET {1, 2} : k \\in s}";
/// `F(2)` and `F(7)` with the element written in place.
const G: &str = "G2 == {s \\in SUBSET {1, 2} : 2 \\in s}\nG7 == {s \\in SUBSET {1, 2} : 7 \\in s}";

/// `x` starts at `{}`, with `defs` defined.
fn set_spec(defs: &str, next: &str, inv: &str) -> VerifyResult {
    raw_spec(
        format!(
            "---- MODULE R ----\nEXTENDS Naturals\nVARIABLE x\n{defs}\n\
             Init == x = {{}}\nNext == {next}\nInv == {inv}\n====\n"
        ),
        "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
    )
}

/// `x` counts 0, 1, 2, 0, … and the config checks `Prop`.
fn counter_property(prop: &str) -> VerifyResult {
    raw_spec(
        format!(
            "---- MODULE R ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\n\
             Next == x' = (x + 1) % 3\nProp == {prop}\n====\n"
        ),
        "INIT Init\nNEXT Next\nPROPERTY Prop\n",
    )
}

/// `P { x: u8 }`, `x` goes 0, 1, 2 (plus the generated stutter step), and one
/// `#[liveness]` property with the given TLA+ text.
fn liveness(text: &str) -> VerifyResult {
    common::with_clean_verification(|| {
        register_protocol_state_var("P", "x", "u8");
        register_protocol_action(
            "P",
            "Up",
            "{ if self.x >= 2 { return; } self.x = self.x + 1 }",
        );
        let body = format!("{{ trust_vc :: temporal ! ({text:?}) }}");
        register_protocol_liveness("P", "Live", &body, "");
        VerificationPipeline::collect_from_macros().verify()
    })
}

#[track_caller]
fn assert_counterexample(result: &VerifyResult, label: &str) {
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{label}: expected a counterexample, got {result:?}"
    );
}

/// Each of these is FALSE in the only reachable state, and the older ty's
/// ENABLED search held it: `F(7)` (empty) read with the caller's `k = 2`,
/// and `~ENABLED` over `F(2)` read with `k = 7`.
#[test]
fn enabled_over_a_filter_that_reads_a_bound_name_is_refuted() {
    for (label, inv) in [
        (
            "mirror",
            "\\A k \\in {2} : ENABLED (x' \\in F(7) /\\ x' = {2})",
        ),
        (
            "mirror, \\E",
            "\\E k \\in {2} : ENABLED (x' \\in F(7) /\\ x' = {2})",
        ),
        (
            "mirror, LET",
            "LET k == 2 IN ENABLED (x' \\in F(7) /\\ x' = {2})",
        ),
        (
            "negated",
            "\\A k \\in {7} : ~ENABLED (x' \\in F(2) /\\ x' = {2})",
        ),
    ] {
        assert_counterexample(&set_spec(F, "UNCHANGED x", inv), label);
    }
}

/// Twins: ENABLED over a filter whose predicate reads no bound name is still
/// checked, both ways; so is a filter that reads one outside ENABLED.
#[test]
fn enabled_over_a_closed_filter_and_open_filters_elsewhere_are_checked() {
    let enabled = |g: &str| format!("\\A k \\in {{7}} : ENABLED (x' \\in {g} /\\ x' = {{2}})");
    assert_eq!(
        set_spec(G, "UNCHANGED x", &enabled("G2")),
        VerifyResult::Verified
    );
    assert_counterexample(&set_spec(G, "UNCHANGED x", &enabled("G7")), "G7 is empty");
    assert_counterexample(
        &set_spec(F, "UNCHANGED x", "\\A k \\in {2} : {2} \\in F(7)"),
        "no ENABLED",
    );
    assert_eq!(
        set_spec(F, "UNCHANGED x", "\\A k \\in {7} : {2} \\in F(2)"),
        VerifyResult::Verified
    );
}

/// `Next` is enumerated without the ENABLED search, and reads `F(7)` and
/// `F(2)` correctly under a binder of `k`.
#[test]
fn the_capture_shapes_in_next_are_checked() {
    assert_eq!(
        set_spec(F, "\\E k \\in {2} : x' \\in F(7) /\\ x' = {2}", "x = {}"),
        VerifyResult::Verified
    );
    for (label, next) in [
        ("\\E", "\\E k \\in {7} : x' \\in F(2) /\\ x' = {2}"),
        ("LET", "LET k == 7 IN x' \\in F(2) /\\ x' = {2}"),
        ("plain", "x' \\in F(2) /\\ x' = {2}"),
    ] {
        assert_counterexample(&set_spec(F, next, "x = {}"), label);
    }
}

/// The `#[liveness]` text path: the open filter is refuted (`F(7)` is
/// empty), and a closed filter is checked both ways.
#[test]
fn liveness_text_over_filters_is_checked() {
    let open = r"LET F(k) == {s \in 0..3 : s = k} IN [](\A k \in {2} : ENABLED (x' \in F(7)))";
    assert_counterexample(&liveness(open), "liveness, open filter");
    assert_eq!(
        liveness(r"[](ENABLED (x' \in {s \in 0..3 : s = 2}))"),
        VerifyResult::Verified
    );
    assert_counterexample(
        &liveness(r"[](ENABLED (x' \in {s \in 0..3 : s = 7}))"),
        "liveness, empty filter",
    );
}

/// Fairness over a spec without filters is checked: the counter reaches 2
/// under weak fairness, and may stutter at 0 forever without it.
#[test]
fn fairness_is_checked() {
    assert_eq!(
        counter_property("WF_x(Next) => <>(x = 2)"),
        VerifyResult::Verified
    );
    assert_counterexample(&counter_property("<>(x = 2)"), "no fairness");
}

const CHILD: &str = "a_violated_liveness_property_under_the_environment";

/// `<>(x = 5)` never holds: a counterexample, run plainly and run by
/// [`a_ty_variable_in_the_environment_does_not_reach_ty`] with
/// `TY_SKIP_LIVENESS=1`, which made ty skip the property and report success.
#[test]
fn a_violated_liveness_property_under_the_environment() {
    let result = counter_property("<>(x = 5)");
    eprintln!("{CHILD}: {result:?}");
    assert_counterexample(&result, "TY_SKIP_LIVENESS set or not");
}

#[test]
fn a_ty_variable_in_the_environment_does_not_reach_ty() {
    let test_binary = std::env::current_exe().expect("the test binary's path");
    let output = std::process::Command::new(test_binary)
        .args(["--exact", CHILD, "--test-threads", "1", "--nocapture"])
        .env("TY_SKIP_LIVENESS", "1")
        .output()
        .expect("the test binary runs");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success() && stdout.contains("1 passed"),
        "{stdout}\n{stderr}"
    );
}
