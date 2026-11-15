//! The ty protocol lane never answers `Verified` for a protocol whose property
//! does not hold, or for a spec or run that checked nothing.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Each case below but the twins used to come back `Verified`:
//! - a `#[safety]` or `#[action]` body was rewritten from Rust to TLA+ as
//!   TEXT, so an operator spelled the same in both languages but meaning
//!   something else (`^`, `%`), or an integer that overflows in Rust and not
//!   in TLA+, stated a different property;
//! - ty's parser recovers from a syntax error and its lexer drops a character
//!   it cannot read, and what was left was checked; of two modules ty checked
//!   the first, and of two definitions of one name it kept one;
//! - a registered name could replace a generated definition (`TypeOK`) or
//!   another registration;
//! - a config that names no property was checked vacuously, and one that
//!   restricted the model (`CONSTRAINT`, `ACTION_CONSTRAINT`, `VIEW`),
//!   replaced a definition (`Op <- Other`) or named `NEXT` twice was checked
//!   as ty read it.
//!
//! Each violated case has a control: the same protocol with an invariant that
//! names the violating state is a counterexample, so the state is reachable.
//!
//! Requires the `ty` feature: `targo --unverified test -p trust-vc-core --features ty`

#![cfg(feature = "ty")]

mod common;

use trust_vc_core::protocol::ProtocolObligation;
use trust_vc_core::verification_bridge::{
    register_protocol, register_protocol_action, register_protocol_invariant,
    register_protocol_liveness, register_protocol_state_var, VerificationPipeline,
};
use trust_vc_core::VerifyResult;

/// `P { x: <ty>, b: bool }` with the given actions and `Inv == <invariant>`.
fn translated(ty: &str, actions: &[&str], invariant: &str) -> VerifyResult {
    common::with_clean_verification(|| {
        register_protocol_state_var("P", "x", ty);
        register_protocol_state_var("P", "b", "bool");
        for (index, action) in actions.iter().enumerate() {
            register_protocol_action("P", &format!("Step{index}"), action);
        }
        register_protocol_invariant("P", "Inv", invariant);
        VerificationPipeline::collect_from_macros().verify()
    })
}

/// A raw TLA+ obligation.
fn raw_spec(spec: &str, config: &str) -> VerifyResult {
    common::with_clean_verification(|| {
        register_protocol(ProtocolObligation {
            name: "R".into(),
            spec: spec.into(),
            config: config.into(),
            shape: None,
        });
        VerificationPipeline::collect_from_macros().verify()
    })
}

/// A raw TLA+ obligation over `x`, with `Init`, `Next` and `Inv` as given.
fn raw(init: &str, next: &str, inv: &str, config: &str) -> VerifyResult {
    raw_spec(
        &format!(
            "---- MODULE R ----\nEXTENDS Naturals\nVARIABLE x\nInit == {init}\n\
             Next == {next}\nInv == {inv}\n===="
        ),
        config,
    )
}

/// `x` counts 0, 1, 2, 0, … and the config checks `Inv`.
fn counter(inv: &str) -> VerifyResult {
    raw(
        "x = 0",
        "x' = (x + 1) % 3",
        inv,
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    )
}

#[track_caller]
fn assert_counterexample(result: &VerifyResult, label: &str) {
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{label}: expected a counterexample, got {result:?}"
    );
}

#[track_caller]
fn assert_not_verified(result: &VerifyResult, label: &str) {
    assert!(
        !matches!(result, VerifyResult::Verified),
        "{label}: a property that does not hold, or was not checked, came back Verified"
    );
}

#[track_caller]
fn assert_refused(result: &VerifyResult, label: &str) {
    assert!(
        matches!(result, VerifyResult::Error { .. }),
        "{label}: expected a refusal, got {result:?}"
    );
}

/// `x` reaches 0, 1, 2.
const UP: &str = "{ if self.x >= 2 { return; } self.x = self.x + 1 }";
/// `x` reaches 0, -3.
const DOWN: &str = "{ if self.x <= -4 { return; } self.x = self.x - 3 }";
/// `x` reaches 0, 100, 200.
const BY_HUNDREDS: &str = "{ if self.x >= 200 { return; } self.x = self.x + 100 }";

/// Rust `^` is XOR: at `x == 2`, `2 ^ 1 == 3`. TLA+ read a power, `2 ^ 1 == 2`.
#[test]
fn a_rust_xor_is_not_read_as_a_power() {
    assert_counterexample(&translated("u8", &[UP], "{ self.x != 2 }"), "control");
    assert_not_verified(&translated("u8", &[UP], "{ self.x ^ 1 != 3 }"), "xor");
}

/// Rust `%` truncates: at `x == -3`, `-3 % 2 == -1`. TLA+ `%` is the
/// non-negative modulus, `1`.
#[test]
fn a_rust_remainder_is_not_read_as_a_modulus() {
    assert_counterexample(&translated("i8", &[DOWN], "{ self.x != -3 }"), "control");
    assert_not_verified(&translated("i8", &[DOWN], "{ self.x % 2 != -1 }"), "rem");
}

/// At `x == 200`, `self.x * 2` overflows `u8` (a panic in debug, 144 in
/// release), so the invariant does not hold there. TLA+ computed 400.
#[test]
fn an_invariant_over_overflowing_arithmetic_is_not_verified() {
    assert_counterexample(
        &translated("u8", &[BY_HUNDREDS], "{ self.x < 128 }"),
        "control",
    );
    let result = translated(
        "u8",
        &[BY_HUNDREDS],
        "{ self.x * 2 >= 255 || self.x < 128 }",
    );
    assert_counterexample(&result, "mul");
}

/// A guard (an early return) that overflows: at `x == 200`, `self.x * 2`
/// panics in debug and is 144 in release, where it does not return and `b`
/// is set. TLA+ computed 400 and disabled the action, so `b` never became
/// true.
#[test]
fn a_guard_over_overflowing_arithmetic_is_not_a_disabled_action() {
    let set_b = "{ if self.x * 2 != 144 { return; } self.b = true }";
    assert_counterexample(
        &translated("u8", &[BY_HUNDREDS], "{ self.x != 200 }"),
        "control",
    );
    assert_counterexample(
        &translated("u8", &[BY_HUNDREDS, set_b], "{ !self.b }"),
        "guard",
    );
}

/// An assigned value whose intermediate overflows: at `x == 100`, `x + 200`
/// overflows `u8` before `- 100` brings it back in range.
#[test]
fn an_assignment_through_an_overflowing_intermediate_is_not_verified() {
    let step = "{ if self.x >= 200 { return; } self.x = self.x + 200 - 100 }";
    assert_counterexample(&translated("u8", &[step], "{ self.x != 100 }"), "control");
    assert_counterexample(
        &translated("u8", &[step], "{ self.x <= 200 }"),
        "intermediate",
    );
}

/// A spec ty's parser or lexer complains about is not the spec that was
/// written: each of these checked `x < 3`, which holds, in place of text that
/// is not TLA+. `¬(x < 3)` (TLA+'s Unicode `~`) never holds; the lexer dropped
/// the `¬`.
#[test]
fn a_spec_ty_does_not_read_whole_is_not_verified() {
    assert_counterexample(&counter("x < 3 /\\ x < 2"), "control");
    assert_eq!(counter("x < 3"), VerifyResult::Verified, "twin");
    for inv in [
        "(x < 3) (x < 2)",
        "x < 3 /\\ x !! 2",
        "x < 3 $",
        "\u{ac}(x < 3)",
    ] {
        assert_refused(&counter(inv), inv);
    }
}

/// TLA+ checks a file's last module; ty lowered the first.
#[test]
fn a_spec_with_two_modules_is_not_verified() {
    let counter_module = |name: &str, inv: &str| {
        format!(
            "---- MODULE {name} ----\nVARIABLE x\nInit == x = 0\n\
             Next == x' = (x + 1) % 3\nInv == {inv}\n====\n"
        )
    };
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    assert_counterexample(&raw_spec(&counter_module("R", "x < 2"), cfg), "control");
    let two = counter_module("A", "x < 3") + &counter_module("R", "x < 2");
    assert_refused(&raw_spec(&two, cfg), "two modules");
}

/// A name is defined once; of two definitions ty kept the first.
#[test]
fn a_name_defined_twice_is_not_verified() {
    assert_counterexample(&counter("x < 2"), "control");
    assert_refused(&counter("x < 3\nInv == x < 2"), "Inv defined twice");
}

/// `P { x: u8 }` with the given actions and invariants.
fn named(actions: &[(&str, &str)], invariants: &[(&str, &str)]) -> VerifyResult {
    common::with_clean_verification(|| {
        register_protocol_state_var("P", "x", "u8");
        for (name, body) in actions {
            register_protocol_action("P", name, body);
        }
        for (name, body) in invariants {
            register_protocol_invariant("P", name, body);
        }
        VerificationPipeline::collect_from_macros().verify()
    })
}

/// A `#[safety]` invariant named `TypeOK` replaced the generated `TypeOK`, so
/// the `u8` overflow at `x == 255` went unreported.
#[test]
fn an_invariant_cannot_replace_the_generated_type_invariant() {
    let past_255 = "{ if self.x > 255 { return; } self.x = self.x + 1 }";
    assert_counterexample(&named(&[("Step", past_255)], &[]), "control");
    assert_refused(
        &named(&[("Step", past_255)], &[("TypeOK", "{ true }")]),
        "TypeOK",
    );
}

/// Two different actions registered as `Step` left one of them unchecked.
#[test]
fn two_actions_under_one_name_are_not_verified() {
    let (up, stay) = (("Step", UP), ("Step", "{ self.x = self.x }"));
    assert_counterexample(&named(&[up], &[("Inv", "{ self.x < 2 }")]), "one Step");
    assert_refused(
        &named(&[up, stay], &[("Inv", "{ self.x < 2 }")]),
        "two Steps",
    );
}

/// A config that names no property, and a spec with no initial state, check
/// nothing.
#[test]
fn a_run_that_checks_nothing_is_not_verified() {
    let no_property = raw("x = 0", "x' = x", "x > 5", "INIT Init\nNEXT Next\n");
    assert_refused(&no_property, "no property");
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let no_state = raw("x = 0 /\\ FALSE", "x' = x", "x > 5", cfg);
    assert_not_verified(&no_state, "no initial state");
    assert_counterexample(&raw("x = 0", "x' = x", "x > 5", cfg), "control");
}

/// Twins: protocols with nothing the lane misreads verify or refute as before,
/// including arithmetic that stays in range.
#[test]
fn the_translatable_twins_are_unchanged() {
    assert_eq!(
        translated("u8", &[UP], "{ self.x < 3 }"),
        VerifyResult::Verified
    );
    assert_eq!(
        translated("i8", &[DOWN], "{ self.x > -7 }"),
        VerifyResult::Verified
    );
    assert_eq!(
        translated("u8", &[UP], "{ self.x + 1 <= 3 }"),
        VerifyResult::Verified
    );
    let doubling_guard = "{ if self.x * 2 >= 4 { return; } self.x = self.x + 1 }";
    assert_eq!(
        translated("u8", &[doubling_guard], "{ self.x < 3 && !self.b }"),
        VerifyResult::Verified
    );
    assert_counterexample(&translated("u8", &[UP], "{ self.x < 2 }"), "u8 twin");
    assert_counterexample(
        &translated(
            "u8",
            &[BY_HUNDREDS],
            "{ self.x * 2 >= 255 || self.x < 100 }",
        ),
        "a mul twin violated before any overflow",
    );
}

/// The lane reads a config itself: one `INIT`, one `NEXT`, each `INVARIANT`
/// and `PROPERTY` on its own line, an optional `CHECK_DEADLOCK`, and nothing
/// else, each naming an operator the module defines without parameters. On
/// ty's own reading, `x` reaches 2 and `Inv == x < 2`, yet each config in the
/// first list came back `Verified`: it explored part of the model
/// (`ACTION_CONSTRAINT`, `CONSTRAINT`, `VIEW`), replaced a definition (`<-`),
/// or kept the last of two `NEXT`s or the first line of a `NEXT` block.
#[test]
fn a_config_the_lane_does_not_read_whole_is_refused() {
    let module = |defs: &str| {
        format!(
            "---- MODULE R ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\n\
             Next == x' = (x + 1) % 3\nInv == x < 2\nHolds == x < 3\n{defs}\n===="
        )
    };
    let base = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    assert_counterexample(&raw_spec(&module(""), base), "control");
    assert_counterexample(
        &raw_spec(&module(""), &format!("{base}CHECK_DEADLOCK FALSE\n")),
        "control, deadlock unchecked",
    );
    assert_eq!(
        raw_spec(&module(""), "INIT Init\nNEXT Next\nINVARIANT Holds\n"),
        VerifyResult::Verified,
        "twin"
    );
    for (defs, config) in [
        ("C == FALSE", format!("{base}ACTION_CONSTRAINT C")),
        ("C == x < 1", format!("{base}CONSTRAINT C")),
        ("V == 0", format!("{base}VIEW V")),
        ("V == x % 2", format!("{base}VIEW V")),
        ("T == TRUE", format!("{base}CONSTANT Inv <- T")),
        ("S == UNCHANGED x", format!("{base}CONSTANT Next <- S")),
        ("S == UNCHANGED x", format!("{base}NEXT S")),
        (
            "S == UNCHANGED x",
            "INIT Init\nNEXT\nS\nNext\nINVARIANT Inv\n".to_string(),
        ),
    ] {
        assert_refused(&raw_spec(&module(defs), &config), &config);
    }
    // Outside the lane's grammar, whatever ty makes of them.
    let holds = "INIT Init\nNEXT Next\nINVARIANT Holds\n";
    for (defs, config) in [
        ("P == FALSE", format!("{holds}POSTCONDITION P")),
        ("Sym == {}", format!("{holds}SYMMETRY Sym")),
        ("T == x = 1", format!("{holds}TERMINAL T")),
        ("A == x", format!("{holds}ALIAS A")),
        ("I2 == x = 5", format!("{base}INIT I2")),
        ("", format!("{holds}INVARIANT TRUE")),
        ("", format!("{holds}INVARIANT x")),
        ("P(n) == n > 5", format!("{holds}INVARIANT P")),
        ("", "INIT Init\nNEXT Next\nINVARIANTS Holds\n".to_string()),
        (
            "Spec == Init /\\ [][Next]_x",
            "SPECIFICATION Spec\nINVARIANT Holds\n".to_string(),
        ),
    ] {
        assert_refused(&raw_spec(&module(defs), &config), &config);
    }
}

/// `P { x: u8 }`, `Step` sets `x` to 1, and two `#[liveness]` properties,
/// `L` with the given TLA+ text and `M == <>(x = 0)`.
fn with_liveness_text(text: &str) -> VerifyResult {
    common::with_clean_verification(|| {
        register_protocol_state_var("P", "x", "u8");
        register_protocol_action("P", "Step", "{ self . x = 1 }");
        register_protocol_invariant("P", "Inv", "{ self . x < 2 }");
        // `text` is the body of a Rust string literal: its `\n` is a newline.
        register_protocol_liveness("P", "L", &format!("{{ temporal ! (\"{text}\") }}"), "");
        register_protocol_liveness("P", "M", r#"{ temporal ! ("<>(x = 0)") }"#, "");
        VerificationPipeline::collect_from_macros().verify()
    })
}

/// A liveness property's TLA+ text is placed in the module: text that adds,
/// replaces or cuts off a definition (a second `TypeOK`, an `Extra`, a `====`
/// that ends the module before `M`, a comment that swallows the rest) is
/// refused, because the module ty read is not the one emitted.
#[test]
fn a_liveness_text_cannot_reshape_the_module() {
    assert_eq!(
        with_liveness_text("<>(x = 0)"),
        VerifyResult::Verified,
        "control"
    );
    for text in [
        "<>(x = 0)\nTypeOK == TRUE",
        "<>(x = 0) Extra == TRUE",
        "<>(x = 0)\n====",
        "<>(x = 0) (*",
    ] {
        assert_refused(&with_liveness_text(text), text);
    }
}
