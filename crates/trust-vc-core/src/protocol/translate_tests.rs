// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    extract_temporal_macro, rust_type_default, rust_type_to_tla_domain, strip_braces,
    translate_protocol, translate_rust_expr,
};
use crate::verification_bridge::{ProtocolActionDef, ProtocolInvariantDef, ProtocolStateVarDef};

#[test]
fn test_rust_type_to_tla_domain() {
    assert_eq!(rust_type_to_tla_domain("bool"), "BOOLEAN");
    assert_eq!(rust_type_to_tla_domain("u8"), "0..255");
    assert_eq!(rust_type_to_tla_domain("usize"), "0..4294967295");
    assert_eq!(rust_type_to_tla_domain("i8"), "-128..127");
    assert!(rust_type_to_tla_domain("Option<u8>").contains("\"None\""));
    assert!(rust_type_to_tla_domain("Option<u8>").contains("0..255"));
}

#[test]
fn test_rust_type_default() {
    assert_eq!(rust_type_default("bool"), "FALSE");
    assert_eq!(rust_type_default("u32"), "0");
    assert_eq!(rust_type_default("Option<u8>"), "\"None\"");
}

#[test]
fn test_translate_rust_expr_assignment() {
    let vars = vec!["x", "y"];
    assert_eq!(
        translate_rust_expr("self.x = self.y + 1", &vars),
        "x' = y + 1"
    );
}

#[test]
fn test_translate_rust_expr_comparison() {
    let vars = vec!["x"];
    assert_eq!(translate_rust_expr("self.x == 0", &vars), "x = 0");
}

#[test]
fn test_translate_rust_expr_logical() {
    let vars = vec!["x", "y"];
    assert_eq!(
        translate_rust_expr("self.x > 0 && self.y == true", &vars),
        "x > 0 /\\ y = TRUE"
    );
}

#[test]
fn test_translate_rust_expr_logical_not() {
    let vars = vec!["flag"];
    assert_eq!(translate_rust_expr("! self.flag", &vars), "~ flag");
    assert_eq!(
        translate_rust_expr("self.flag != true", &vars),
        "flag # TRUE"
    );
}

#[test]
fn test_translate_rust_expr_keyword_replacement_is_token_safe() {
    let vars = vec!["is_true", "false_alarm"];
    assert_eq!(
        translate_rust_expr("self.is_true == true && self.false_alarm == false", &vars),
        "is_true = TRUE /\\ false_alarm = FALSE"
    );
}

#[test]
fn test_strip_braces() {
    assert_eq!(strip_braces("{ x = 1 ; }").trim(), "x = 1 ;");
    assert_eq!(strip_braces("no braces"), "no braces");
}

#[test]
fn test_extract_temporal_macro() {
    let input = r#"trust_vc :: temporal ! ("[]<>(head != tail)")"#;
    assert_eq!(
        extract_temporal_macro(input),
        Some("[]<>(head != tail)".to_string())
    );
}

#[test]
fn test_full_translation() {
    let vars = vec![ProtocolStateVarDef {
        protocol_name: "Counter".to_string(),
        field_name: "x".to_string(),
        rust_type: "u8".to_string(),
    }];
    let var_refs: Vec<&ProtocolStateVarDef> = vars.iter().collect();
    let actions = vec![ProtocolActionDef {
        protocol_name: "Counter".to_string(),
        name: "Increment".to_string(),
        body: "{ self.x = self.x + 1 }".to_string(),
    }];
    let invariants = vec![ProtocolInvariantDef {
        protocol_name: "Counter".to_string(),
        name: "Bounded".to_string(),
        expr: "{ self.x <= 10 }".to_string(),
    }];

    let result = translate_protocol("Counter", &var_refs, &actions, &invariants, &[])
        .expect("protocol translates");

    assert!(result.spec.contains("---- MODULE Counter ----"));
    assert!(result.spec.contains("VARIABLE x"));
    assert!(result.spec.contains("x \\in 0..255"));
    assert!(result.spec.contains("Init =="));
    assert!(result.spec.contains("x = 0"));
    assert!(result.spec.contains("Increment =="));
    assert!(result.spec.contains("x' = x + 1"));
    assert!(result.spec.contains("Next =="));
    assert!(result.spec.contains("\\/ Increment"));
    assert!(result.spec.contains("UNCHANGED x")); // stutter step
    assert!(result.spec.contains("Bounded =="));
    assert!(result.config.contains("INIT Init"));
    assert!(result.config.contains("NEXT Next"));
    assert!(result.config.contains("INVARIANT TypeOK"));
    assert!(result.config.contains("INVARIANT Bounded"));
}

#[test]
fn test_full_translation_parses_and_lowers() {
    let vars = vec![
        ProtocolStateVarDef {
            protocol_name: "Counter".to_string(),
            field_name: "x".to_string(),
            rust_type: "u8".to_string(),
        },
        ProtocolStateVarDef {
            protocol_name: "Counter".to_string(),
            field_name: "enabled".to_string(),
            rust_type: "bool".to_string(),
        },
    ];
    let var_refs: Vec<&ProtocolStateVarDef> = vars.iter().collect();
    let actions = vec![ProtocolActionDef {
        protocol_name: "Counter".to_string(),
        name: "Increment".to_string(),
        body: "{ self.enabled == true ; self.x = self.x + 1 }".to_string(),
    }];
    let invariants = vec![ProtocolInvariantDef {
        protocol_name: "Counter".to_string(),
        name: "Bounded".to_string(),
        expr: "{ self.x <= 10 }".to_string(),
    }];

    let result = translate_protocol("Counter", &var_refs, &actions, &invariants, &[])
        .expect("protocol translates");
    let tree = tla_core::parse_to_syntax_tree(&result.spec);
    let lowered = tla_core::lower(tla_core::FileId(0), &tree);

    assert!(
        lowered.errors.is_empty(),
        "generated TLA+ should lower without errors: {:?}",
        lowered.errors
    );
    assert!(
        lowered.module.is_some(),
        "generated TLA+ should lower to a module"
    );
}

#[test]
fn test_translate_protocol_rejects_unsupported_state_type() {
    let vars = vec![ProtocolStateVarDef {
        protocol_name: "P".to_string(),
        field_name: "xs".to_string(),
        rust_type: "Vec < u8 >".to_string(),
    }];
    let var_refs: Vec<&ProtocolStateVarDef> = vars.iter().collect();

    let result = translate_protocol("P", &var_refs, &[], &[], &[]);
    assert!(
        result.is_err(),
        "unsupported protocol state types must fail closed"
    );
}

#[test]
fn test_unchanged_generation() {
    let vars = vec![
        ProtocolStateVarDef {
            protocol_name: "P".to_string(),
            field_name: "x".to_string(),
            rust_type: "u8".to_string(),
        },
        ProtocolStateVarDef {
            protocol_name: "P".to_string(),
            field_name: "y".to_string(),
            rust_type: "u8".to_string(),
        },
    ];
    let var_refs: Vec<&ProtocolStateVarDef> = vars.iter().collect();
    let actions = vec![ProtocolActionDef {
        protocol_name: "P".to_string(),
        name: "SetX".to_string(),
        body: "{ self.x = 1 }".to_string(),
    }];

    let result =
        translate_protocol("P", &var_refs, &actions, &[], &[]).expect("protocol translates");
    assert!(result.spec.contains("UNCHANGED y"));
}

#[test]
fn test_translate_action_rejects_duplicate_state_assignments() {
    let vars = vec![ProtocolStateVarDef {
        protocol_name: "P".to_string(),
        field_name: "x".to_string(),
        rust_type: "u8".to_string(),
    }];
    let var_refs: Vec<&ProtocolStateVarDef> = vars.iter().collect();
    let actions = vec![ProtocolActionDef {
        protocol_name: "P".to_string(),
        name: "SetTwice".to_string(),
        body: "{ self.x = 1 ; self.x = 2 }".to_string(),
    }];

    let result = translate_protocol("P", &var_refs, &actions, &[], &[]);
    assert!(
        result.is_err(),
        "duplicate assignments must fail closed instead of disabling the action"
    );
}

#[test]
fn test_translate_action_rejects_read_after_write() {
    let vars = vec![
        ProtocolStateVarDef {
            protocol_name: "P".to_string(),
            field_name: "x".to_string(),
            rust_type: "u8".to_string(),
        },
        ProtocolStateVarDef {
            protocol_name: "P".to_string(),
            field_name: "y".to_string(),
            rust_type: "u8".to_string(),
        },
    ];
    let var_refs: Vec<&ProtocolStateVarDef> = vars.iter().collect();
    let actions = vec![ProtocolActionDef {
        protocol_name: "P".to_string(),
        name: "CopyAfterWrite".to_string(),
        body: "{ self.x = 1 ; self.y = self.x }".to_string(),
    }];

    let result = translate_protocol("P", &var_refs, &actions, &[], &[]);
    assert!(
        result.is_err(),
        "read-after-write must fail closed because TLA+ RHS reads old state"
    );
}
