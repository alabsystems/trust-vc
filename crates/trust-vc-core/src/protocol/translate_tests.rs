// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::translate_protocol;
use crate::verification_bridge::{
    ProtocolActionDef, ProtocolInitial, ProtocolInvariantDef, ProtocolLivenessDef,
    ProtocolStateVarDef, ProtocolValue,
};

fn var(name: &str, ty: &str) -> ProtocolStateVarDef {
    starting(name, ty, ProtocolInitial::Zero)
}

fn starting(name: &str, ty: &str, initial: ProtocolInitial) -> ProtocolStateVarDef {
    ProtocolStateVarDef {
        protocol_name: "P".to_string(),
        field_name: name.to_string(),
        rust_type: ty.to_string(),
        initial,
    }
}

fn act(name: &str, body: &str) -> ProtocolActionDef {
    ProtocolActionDef {
        protocol_name: "P".to_string(),
        name: name.to_string(),
        body: body.to_string(),
    }
}

fn inv(name: &str, expr: &str) -> ProtocolInvariantDef {
    ProtocolInvariantDef {
        protocol_name: "P".to_string(),
        name: name.to_string(),
        expr: expr.to_string(),
    }
}

fn live(name: &str, expr: &str) -> ProtocolLivenessDef {
    ProtocolLivenessDef {
        protocol_name: "P".to_string(),
        name: name.to_string(),
        expr: expr.to_string(),
        fairness: String::new(),
    }
}

type Translation = Result<(String, String), String>;

fn translate(
    vars: &[ProtocolStateVarDef],
    actions: &[ProtocolActionDef],
    invariants: &[ProtocolInvariantDef],
    liveness: &[ProtocolLivenessDef],
) -> Translation {
    let refs: Vec<&ProtocolStateVarDef> = vars.iter().collect();
    translate_protocol("P", &refs, actions, invariants, liveness)
        .map(|t| (t.spec, t.config))
        .map_err(|error| error.to_string())
}

/// One `u8` field `x`, one `bool` field `b`, `Step == <action>` and
/// `Inv == <invariant>`.
fn one(action: &str, invariant: &str) -> Translation {
    translate(
        &[var("x", "u8"), var("b", "bool")],
        &[act("Step", action)],
        &[inv("Inv", invariant)],
        &[],
    )
}

#[track_caller]
fn refused(result: &Translation, why: &str) {
    match result {
        Err(error) => assert!(error.contains(why), "refused for another reason: {error}"),
        Ok((spec, _)) => panic!("translated, expected a refusal naming {why:?}:\n{spec}"),
    }
}

#[test]
fn a_counter_translates_to_the_module_and_shape_emitted() {
    let (spec, config) = translate(
        &[var("x", "u8"), var("enabled", "bool")],
        &[act(
            "Increment",
            "{ if self . enabled == false { return ; } self . x = self . x + 1 }",
        )],
        &[inv("Bounded", "{ self . x <= 10 }")],
        &[],
    )
    .expect("translates");
    for line in [
        "---- MODULE P ----",
        "VARIABLE x, enabled",
        "  /\\ x \\in 0..255",
        "  /\\ enabled \\in BOOLEAN",
        "  /\\ x = 0",
        "  /\\ enabled = FALSE",
        "Increment ==\n  /\\ (~(enabled = FALSE))\n  /\\ x' = (x + 1)\n  /\\ UNCHANGED enabled",
        "Next ==\n  \\/ Increment\n  \\/ UNCHANGED <<x, enabled>>",
        "NoPanic_Increment ==\n  ((~(enabled = FALSE)) => ((x + 1) \\in 0..255))",
        "Bounded ==\n  (x <= 10)",
    ] {
        assert!(spec.contains(line), "{line:?} missing from:\n{spec}");
    }
    assert_eq!(
        config,
        "INIT Init\nNEXT Next\nINVARIANT TypeOK\nINVARIANT NoPanic_Increment\n\
         INVARIANT Bounded\n"
    );
    let refs = [var("x", "u8"), var("enabled", "bool")];
    let refs: Vec<&ProtocolStateVarDef> = refs.iter().collect();
    let shape = translate_protocol(
        "P",
        &refs,
        &[act(
            "Increment",
            "{ if self . enabled == false { return ; } self . x = self . x + 1 }",
        )],
        &[inv("Bounded", "{ self . x <= 10 }")],
        &[],
    )
    .expect("translates")
    .shape;
    // What ty's `source.units` must hold: exactly these, in this order for
    // the variables.
    assert_eq!(shape.variables, ["x", "enabled"]);
    let mut operators = shape.operators.clone();
    operators.sort_unstable();
    assert_eq!(
        operators,
        [
            "Bounded",
            "Increment",
            "Init",
            "Next",
            "NoPanic_Increment",
            "TypeOK"
        ]
    );
}

#[test]
fn an_action_without_arithmetic_has_no_panic_operator() {
    let (spec, config) = one("{ self . b = ! self . b }", "{ self . x == 0 }").expect("translates");
    assert!(
        spec.contains("  /\\ b' = (~b)\n  /\\ UNCHANGED x"),
        "{spec}"
    );
    assert!(!spec.contains("NoPanic"), "{spec}");
    assert!(!config.contains("NoPanic"), "{config}");
}

#[test]
fn only_bool_and_fixed_width_integer_state_is_translated() {
    for ty in [
        "Vec < u8 >",
        "Option < u8 >",
        "Option < Option < u8 > >",
        "u128",
        "String",
    ] {
        refused(
            &translate(&[var("x", ty)], &[], &[], &[]),
            "unsupported protocol state type",
        );
    }
    let (spec, _) =
        translate(&[var("x", "i8"), var("y", "usize")], &[], &[], &[]).expect("translates");
    assert!(spec.contains("x \\in (-128)..127"), "{spec}");
    assert!(spec.contains("y \\in 0..4294967295"), "{spec}");
}

/// Each operator whose Rust meaning differs from its TLA+ spelling, and each
/// construct outside the subset, is refused rather than passed through.
#[test]
fn divergent_operators_and_other_constructs_are_refused() {
    for body in [
        "{ self . x ^ 1 != 3 }",
        "{ self . x % 2 != 1 }",
        "{ self . x / 2 != 1 }",
        "{ (self . x << 1) != 4 }",
        "{ (self . x >> 1) != 4 }",
        "{ self . x & 1 == 0 }",
        "{ self . x | 1 == 3 }",
        "{ ! self . x == 253 }",
        "{ self . x as u16 != 2 }",
        "{ self . x . min (5) != 2 }",
        "{ ! matches ! (self . x , 2) }",
        "{ if self . x < 3 { true } else { false } }",
        "{ let y = self . x ; y < 3 }",
        "{ self . y < 3 }",
        "{ x < 3 }",
        "{ self . x < 2.0 }",
        "{ self . x < 3 ; }",
        "{ self . x }",
        "{ self . b < true }",
        "{ - self . x == 0 }",
        "{ # [cfg (any ())] self . x < 3 }",
    ] {
        match one("{ }", body) {
            Err(error) => assert!(
                error.contains("cannot translate invariant 'Inv'"),
                "{error}"
            ),
            Ok((spec, _)) => panic!("{body} translated:\n{spec}"),
        }
    }
}

#[test]
fn a_literal_must_fit_its_type() {
    refused(&one("{ }", "{ self . x < 256 }"), "out of range for u8");
    refused(
        &one("{ }", "{ self . x < 3u16 }"),
        "compares a u8 with a u16",
    );
    refused(
        &one("{ self . x = 300 }", "{ true }"),
        "out of range for u8",
    );
    let (spec, _) = one("{ }", "{ self . x < 0xff_u8 && 1_0 == 10 }").expect("translates");
    assert!(spec.contains("((x < 255) /\\ (10 = 10))"), "{spec}");
    let (spec, _) = translate(
        &[var("x", "i8")],
        &[],
        &[inv("Inv", "{ self . x != - 128 && self . x != - (- 5) }")],
        &[],
    )
    .expect("translates");
    assert!(spec.contains("(x # (-128))"), "{spec}");
    assert!(
        spec.contains("((-(-5)) \\in (-128)..127)"),
        "a negation that is not a literal is range-checked:\n{spec}"
    );
}

/// `&&` and `||` short-circuit: the right operand's arithmetic can overflow
/// only when the left does not decide.
#[test]
fn definedness_follows_short_circuiting() {
    let (spec, _) = one("{ }", "{ self . x >= 128 || self . x * 2 < 250 }").expect("translates");
    assert!(
        spec.contains(
            "Inv ==\n  (((x >= 128) \\/ ((x * 2) \\in 0..255)) /\\ ((x >= 128) \\/ ((x * 2) < 250)))"
        ),
        "{spec}"
    );
}

#[test]
fn an_action_is_early_returns_then_assignments_over_the_old_state() {
    refused(
        &one("{ self . x = 1 ; self . x = 2 }", "{ true }"),
        "assigned twice",
    );
    refused(
        &translate(
            &[var("x", "u8"), var("y", "u8")],
            &[act("Copy", "{ self . x = 1 ; self . y = self . x }")],
            &[],
            &[],
        ),
        "read after it is assigned",
    );
    refused(
        &one(
            "{ self . x = 1 ; if self . x < 3 { return ; } }",
            "{ true }",
        ),
        "read after it is assigned",
    );
    refused(
        &one("{ self . x += 1 }", "{ true }"),
        "cannot translate action 'Step'",
    );
    refused(&one("{ self . z = 1 }", "{ true }"), "not a state variable");
    refused(&one("{ self . b = 1 }", "{ true }"), "not a bool literal");
    let (spec, _) = one("{ }", "{ true }").expect("an empty action stutters");
    assert!(spec.contains("Step ==\n  /\\ UNCHANGED <<x, b>>"), "{spec}");
}

#[test]
fn names_are_tla_identifiers_used_once() {
    for (action, invariant) in [
        ("Step", "TypeOK"),
        ("Init", "Inv"),
        ("Next", "Inv"),
        ("Step", "Step"),
        ("Step", "NoPanic_Step"),
        ("Step", "x"),
        ("Step", "TRUE"),
        ("Step", "WF_x"),
        ("r#Step", "Inv"),
        ("Step", "caf\u{e9}"),
    ] {
        let result = translate(
            &[var("x", "u8")],
            &[act(
                action,
                "{ if self . x >= 3 { return ; } self . x = self . x + 1 }",
            )],
            &[inv(invariant, "{ true }")],
            &[],
        );
        assert!(result.is_err(), "{action}/{invariant}: {result:?}");
    }
    refused(
        &translate(&[var("x", "u8"), var("x", "u8")], &[], &[], &[]),
        "already a name",
    );
    let twice = [
        act("Step", "{ self . x = 1 }"),
        act("Step", "{ self . x = 1 }"),
    ];
    translate(&[var("x", "u8")], &twice, &[], &[]).expect("a repeated registration is one action");
    let differ = [
        act("Step", "{ self . x = 1 }"),
        act("Step", "{ self . x = 2 }"),
    ];
    refused(
        &translate(&[var("x", "u8")], &differ, &[], &[]),
        "already a name",
    );
}

#[test]
fn a_liveness_body_is_one_temporal_call() {
    for body in [
        r#"{ trust_vc :: temporal ! ("<>(x = 0)") }"#,
        r#"{ temporal ! ("<>(x = 0)") }"#,
    ] {
        let (spec, config) =
            translate(&[var("x", "u8")], &[], &[], &[live("L", body)]).expect("translates");
        assert!(spec.contains("L ==\n  <>(x = 0)\n"), "{spec}");
        assert!(config.ends_with("PROPERTY L\n"), "{config}");
    }
    for body in [
        "{ self . x < 3 }",
        r#"{ other :: temporal ! ("<>(x = 0)") }"#,
        r#"{ temporal ! ("<>(x = 0)") ; }"#,
        r#"{ temporal ! ("") }"#,
        r#"{ temporal ! (concat ! ("<>", "(x = 0)")) }"#,
    ] {
        let result = translate(&[var("x", "u8")], &[], &[], &[live("L", body)]);
        assert!(result.is_err(), "{body}: {result:?}");
    }
}

/// A property's TLA+ text cannot add, drop or redefine an operator of the
/// module around it.
/// `Init` is each field's value in `Default::default()`, read from Rust; a
/// struct without `Default`, a `Default` that returned two different states,
/// and a value that is not of the field's type have no initial state.
#[test]
fn init_is_the_registered_initial_state() {
    let default = |values: [Option<ProtocolValue>; 2]| ProtocolInitial::Default(values);
    let int = |value| Some(ProtocolValue::Int(value));
    let (spec, _) = translate(
        &[
            starting("x", "u8", default([int(200), int(200)])),
            starting("y", "i8", default([int(-5), int(-5)])),
            starting("b", "bool", default([Some(ProtocolValue::Bool(true)); 2])),
            var("z", "u16"),
        ],
        &[],
        &[],
        &[],
    )
    .expect("translates");
    assert!(
        spec.contains("Init ==\n  /\\ x = 200\n  /\\ y = (-5)\n  /\\ b = TRUE\n  /\\ z = 0\n"),
        "{spec}"
    );
    for (initial, why) in [
        (ProtocolInitial::NoDefault, "does not implement `Default`"),
        (default([int(1), int(2)]), "no one initial state"),
        (default([int(256), int(256)]), "not a value of its type"),
        (default([int(-1), int(-1)]), "not a value of its type"),
        (
            default([Some(ProtocolValue::Bool(false)); 2]),
            "not a value of its type",
        ),
        (default([None, None]), "not a value of its type"),
    ] {
        refused(
            &translate(&[starting("x", "u8", initial)], &[], &[], &[]),
            why,
        );
    }
}

/// A bare `bool` statement is not a guard: Rust evaluates it, discards it and
/// runs the statements after it. A guard is an early return before every
/// assignment; the action is disabled where it returns.
#[test]
fn a_guard_is_an_early_return_before_every_assignment() {
    for body in [
        "{ self . x < 3 ; self . x = self . x + 1 }",
        "{ ! self . b ; self . b = true }",
        "{ self . x < 3 }",
        "{ true ; }",
        "{ self . x == 0 || self . b ; self . b = true }",
    ] {
        refused(&one(body, "{ true }"), "it is not a guard");
    }
    for body in [
        "{ if self . x >= 3 { return ; } else { } self . x = 1 }",
        "{ if self . x >= 3 { } self . x = 1 }",
        "{ if self . x >= 3 { self . x = 1 ; } }",
        "{ if self . x >= 3 { return ; return ; } self . x = 1 }",
        "{ if self . x >= 3 { return () ; } self . x = 1 }",
    ] {
        refused(&one(body, "{ true }"), "the only `if` in an action");
    }
    refused(
        &one(
            "{ if let 3 = self . x { return ; } self . b = true }",
            "{ true }",
        ),
        "cannot translate action 'Step'",
    );
    refused(
        &one(
            "{ self . b = true ; if self . x >= 3 { return ; } }",
            "{ true }",
        ),
        "must come before every assignment",
    );
    let (spec, _) = one(
        "{ if self . x >= 3 { return } if self . b { return ; } self . x = self . x + 1 }",
        "{ true }",
    )
    .expect("translates");
    for line in [
        "Step ==\n  /\\ (~(x >= 3))\n  /\\ (~b)\n  /\\ x' = (x + 1)\n  /\\ UNCHANGED b",
        "NoPanic_Step ==\n  ((~(x >= 3)) => ((~b) => ((x + 1) \\in 0..255)))",
    ] {
        assert!(spec.contains(line), "{line:?} missing from:\n{spec}");
    }
    let (spec, _) = one("{ if self . x * 2 >= 4 { return ; } }", "{ true }").expect("translates");
    assert!(
        spec.contains("NoPanic_Step ==\n  ((x * 2) \\in 0..255)"),
        "the condition itself runs in every state:\n{spec}"
    );
}
