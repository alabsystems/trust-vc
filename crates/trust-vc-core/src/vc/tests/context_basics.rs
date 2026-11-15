// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ir::{CompareOp, StructDef, TrustVcExpr, TrustVcType};

#[test]
fn test_verification_context() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert("identity", "x + 0 == x"));

    assert_eq!(ctx.variables.len(), 1);
    assert_eq!(ctx.obligations.len(), 1);
    assert!(ctx.has_assertions());
}

#[test]
fn test_multiple_variables_and_constraints() {
    let mut ctx = VerificationContext::new();

    // Declare multiple variables of different types
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("y", TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("flag", TrustVcType::Bool);
    ctx.declare_var_typed("data", TrustVcType::Uint { width: 8 });

    assert_eq!(ctx.variables.len(), 4);
    assert_eq!(ctx.variables[0].name, "x");
    assert_eq!(ctx.variables[0].ty, TrustVcType::Int { width: 32 });
    assert_eq!(ctx.variables[3].name, "data");
    assert_eq!(ctx.variables[3].ty, TrustVcType::Uint { width: 8 });

    // Add multiple assumptions
    ctx.push_obligation(ProofObligation::assume("x_positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assume("y_bound", "y <= 100"));
    ctx.push_obligation(ProofObligation::assume("flag_set", "flag == true"));

    // Add multiple assertions
    ctx.push_obligation(ProofObligation::assert("sum_check", "x + y < 200"));
    ctx.push_obligation(ProofObligation::assert("product_check", "x * y > 0"));

    assert_eq!(ctx.obligations.len(), 5);

    // Verify the right mix of obligation kinds
    let assumes = ctx
        .obligations
        .iter()
        .filter(|o| o.kind == ObligationKind::Assume)
        .count();
    let asserts = ctx
        .obligations
        .iter()
        .filter(|o| o.kind == ObligationKind::Assert)
        .count();

    assert_eq!(assumes, 3);
    assert_eq!(asserts, 2);
}

#[test]
fn test_proof_obligation_builders() {
    // Test assert builder
    let obligation = ProofObligation::assert("test_assert", "x > 0");
    assert_eq!(obligation.name, "test_assert");
    assert_eq!(obligation.condition, "x > 0");
    assert_eq!(obligation.kind, ObligationKind::Assert);
    assert_eq!(obligation.location, None);

    // Test assume builder
    let obligation = ProofObligation::assume("test_assume", "y < 100");
    assert_eq!(obligation.name, "test_assume");
    assert_eq!(obligation.condition, "y < 100");
    assert_eq!(obligation.kind, ObligationKind::Assume);
    assert_eq!(obligation.location, None);

    // Test with_location
    let obligation = ProofObligation::assert("located", "z != 0").with_location("file.rs:10:5");
    assert_eq!(obligation.location, Some("file.rs:10:5".to_string()));
}

#[test]
fn test_empty_context() {
    let ctx = VerificationContext::new();

    assert_eq!(ctx.variables.len(), 0);
    assert_eq!(ctx.obligations.len(), 0);
    assert!(!ctx.has_assertions());
}

#[test]
#[allow(deprecated)]
fn test_string_conversion_types() {
    let mut ctx = VerificationContext::new();

    // Test that declare_var accepts &str parameters
    ctx.declare_var_typed("string_var", TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("str_var", TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assert("string_assert", "true"));
    ctx.push_obligation(ProofObligation::assume("str_assume", "false"));

    assert_eq!(ctx.variables.len(), 2);
    assert_eq!(ctx.obligations.len(), 2);
}

#[test]
fn test_verification_context_default() {
    // Test that Default trait is properly implemented
    let ctx = VerificationContext::default();

    assert_eq!(ctx.obligations.len(), 0);
    assert_eq!(ctx.variables.len(), 0);
    assert!(ctx.function_context.is_none());
    assert!(!ctx.has_assertions());
}

#[test]
fn test_from_parts_deduplicates_duplicate_variable_names() {
    let ctx = VerificationContext::from_parts(
        vec![
            VariableDecl {
                bounded_len: false,
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 32 },
            },
            VariableDecl {
                bounded_len: false,
                name: "flag".to_string(),
                ty: TrustVcType::Bool,
            },
            VariableDecl {
                bounded_len: false,
                name: "x".to_string(),
                ty: TrustVcType::Uint { width: 64 },
            },
        ],
        vec![ProofObligation::assert("check", "true")],
    );

    // After #2668 Slice 2: duplicate declarations set the error flag and
    // keep the first type (first-wins). prepare_context will fail-closed.
    assert_eq!(ctx.variables.len(), 2);
    assert_eq!(ctx.variables[0].name, "x");
    assert_eq!(ctx.variables[1].name, "flag");
    assert_eq!(
        ctx.get_variable_type("x"),
        Some(&TrustVcType::Int { width: 32 })
    );
    assert!(
        ctx.duplicate_var_error.is_some(),
        "duplicate variable declaration must set error flag"
    );
}

// === declare_const (#2423) ===

#[test]
#[allow(deprecated)]
fn test_declare_const_creates_variable_and_assumption() {
    let mut ctx = VerificationContext::new();
    ctx.declare_const("MAX_SIZE", "u64", "1000");

    assert_eq!(ctx.variables.len(), 1);
    assert_eq!(ctx.variables[0].name, "MAX_SIZE");
    assert_eq!(ctx.variables[0].ty, TrustVcType::Uint { width: 64 });

    // Should have exactly one assumption: MAX_SIZE == 1000
    assert_eq!(ctx.obligations.len(), 1);
    assert_eq!(ctx.obligations[0].kind, ObligationKind::Assume);
    assert_eq!(ctx.obligations[0].name, "MAX_SIZE_value");
    assert_eq!(ctx.obligations[0].condition, "MAX_SIZE == 1000");
}

#[test]
fn test_declare_const_typed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_const_typed("N", TrustVcType::Nat, "42");

    assert_eq!(ctx.variables.len(), 1);
    assert_eq!(ctx.variables[0].ty, TrustVcType::Nat);
    assert_eq!(ctx.obligations[0].condition, "N == 42");
}

#[test]
fn test_declare_const_usable_in_assertions() {
    let mut ctx = VerificationContext::new();
    ctx.declare_const_typed("LIMIT", TrustVcType::Int { width: 32 }, "100");
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("x_bounded", "x >= 0 && x < LIMIT"));
    ctx.push_obligation(ProofObligation::assert("check", "x < 100"));

    assert!(ctx.has_assertions());
    assert!(ctx.has_assumptions());
}

// === add_assert_forall_by (#2416) ===

#[test]
fn test_assert_forall_by_scopes_bound_vars_and_creates_assert_by() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });

    ctx.add_assert_forall_by_typed(
        "forall_pos",
        "k > 0",
        vec![("k", TrustVcType::Uint { width: 32 })],
        vec![ProofObligation::assume("k_hint", "k >= 1")],
    );

    // Bound var "k" is scoped to this forall proof, not globally declared.
    assert!(!ctx.has_variable("k"));
    assert_eq!(ctx.get_variable_type("k"), None);
    assert_eq!(ctx.variables.len(), 1);
    assert_eq!(
        ctx.forall_bound_vars["forall_pos"][0].ty,
        TrustVcType::Uint { width: 32 }
    );

    // The obligation is an AssertBy
    let assert_bys = ctx
        .obligations
        .iter()
        .filter(|o| o.kind == ObligationKind::AssertBy)
        .count();
    assert_eq!(assert_bys, 1);

    // Scoped obligations are stored in assert_by_scopes
    assert!(ctx.assert_by_scopes.contains_key("forall_pos"));
    assert_eq!(ctx.assert_by_scopes["forall_pos"].len(), 1);
}

#[test]
fn test_assert_forall_by_typed_scopes_typed_bound_vars() {
    let mut ctx = VerificationContext::new();

    ctx.add_assert_forall_by_typed(
        "forall_nat",
        "n >= 0",
        vec![("n", TrustVcType::Nat)],
        vec![],
    );

    assert!(!ctx.has_variable("n"));
    assert_eq!(ctx.variables.len(), 0);
    assert_eq!(ctx.forall_bound_vars["forall_nat"][0].ty, TrustVcType::Nat);
}

#[test]
fn test_assert_forall_by_multiple_bound_vars_stay_scoped() {
    let mut ctx = VerificationContext::new();

    ctx.add_assert_forall_by_typed(
        "forall_pair",
        "a + b >= 0",
        vec![
            ("a", TrustVcType::Uint { width: 32 }),
            ("b", TrustVcType::Uint { width: 32 }),
        ],
        vec![ProofObligation::assume("hint", "true")],
    );

    assert!(!ctx.has_variable("a"));
    assert!(!ctx.has_variable("b"));
    assert_eq!(ctx.variables.len(), 0);
    assert_eq!(ctx.forall_bound_vars["forall_pair"].len(), 2);
    assert_eq!(ctx.assert_by_scopes["forall_pair"].len(), 1);
}

#[test]
#[should_panic(expected = "invariant: duplicate assert_by scope name `dup_scope`")]
fn test_add_assert_by_rejects_duplicate_scope_names() {
    let mut ctx = VerificationContext::new();
    ctx.add_assert_by("dup_scope", "x > 0", vec![]);
    ctx.add_assert_by("dup_scope", "x > 1", vec![]);
}

#[test]
fn test_two_forall_by_same_bound_var_name_no_corruption() {
    let mut ctx = VerificationContext::new();

    ctx.add_assert_forall_by_typed(
        "forall_u32",
        "k >= 0",
        vec![("k", TrustVcType::Uint { width: 32 })],
        vec![ProofObligation::assume("hint_u32", "true")],
    );
    ctx.add_assert_forall_by_typed(
        "forall_i32",
        "k <= 0",
        vec![("k", TrustVcType::Int { width: 32 })],
        vec![ProofObligation::assume("hint_i32", "true")],
    );

    assert!(!ctx.has_variable("k"));
    assert_eq!(ctx.variables.len(), 0);
    assert_eq!(
        ctx.forall_bound_vars["forall_u32"][0].ty,
        TrustVcType::Uint { width: 32 }
    );
    assert_eq!(
        ctx.forall_bound_vars["forall_i32"][0].ty,
        TrustVcType::Int { width: 32 }
    );
}

#[test]
fn test_set_type_invariant_accepts_registered_struct_type() {
    let mut ctx = VerificationContext::new();
    ctx.register_struct_type(StructDef::new(
        "Counter",
        vec![("count".to_string(), TrustVcType::Uint { width: 32 })],
    ));

    ctx.set_type_invariant(
        "Counter",
        TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(TrustVcExpr::Var {
                name: "count".to_string(),
                ty: TrustVcType::Uint { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Uint { width: 32 },
            }),
        },
    );

    assert!(ctx.type_invariants.contains_key("Counter"));
}

#[test]
#[should_panic(
    expected = "invariant: cannot register type invariant for unknown struct type `Missing`"
)]
fn test_set_type_invariant_rejects_unknown_struct_type() {
    let mut ctx = VerificationContext::new();
    ctx.set_type_invariant("Missing", TrustVcExpr::BoolLit(true));
}

#[test]
fn test_subsequent_obligation_cannot_see_forall_bound_var() {
    let mut ctx = VerificationContext::new();

    ctx.add_assert_forall_by_typed(
        "forall_pos",
        "k > 0",
        vec![("k", TrustVcType::Uint { width: 32 })],
        vec![ProofObligation::assume("hint", "k >= 1")],
    );
    ctx.push_obligation(ProofObligation::assert("after_forall", "k > 0"));

    assert!(!ctx.has_variable("k"));
    assert_eq!(ctx.get_variable_type("k"), None);
}

// === Invariant mask (#2427) ===

#[test]
fn test_invariant_mask_defaults_to_any() {
    let ctx = VerificationContext::new();
    assert_eq!(ctx.invariant_mask, InvariantMask::Any);
}

#[test]
fn test_set_invariant_mask_namespaces() {
    let mut ctx = VerificationContext::new();
    ctx.set_invariant_mask(InvariantMask::Namespaces(vec![1, 2, 3]));
    assert!(ctx.invariant_mask.allows(1));
    assert!(ctx.invariant_mask.allows(2));
    assert!(ctx.invariant_mask.allows(3));
    assert!(!ctx.invariant_mask.allows(4));
}

#[test]
fn test_set_invariant_mask_none_blocks_all() {
    let mut ctx = VerificationContext::new();
    ctx.set_invariant_mask(InvariantMask::None);
    assert!(!ctx.invariant_mask.allows(0));
    assert!(!ctx.invariant_mask.allows(42));
}

#[test]
fn test_invariant_namespace_on_proof_obligation() {
    let obligation =
        ProofObligation::invariant_open("inv_open", "__trust_vc_invariant_open(inv, x)")
            .with_invariant_namespace(42);
    assert_eq!(obligation.invariant_namespace, Some(42));
}

#[test]
fn test_invariant_namespace_default_is_none() {
    let obligation =
        ProofObligation::invariant_open("inv_open", "__trust_vc_invariant_open(inv, x)");
    assert_eq!(obligation.invariant_namespace, None);
}

// ── ROUND 7: FIELD-LEVEL COLLECTION PROVENANCE, the side-table contract ────

/// A MISSING entry and a recorded `Unknown` are the SAME fail-closed answer, and
/// a conflicting re-registration degrades to it rather than letting the last
/// writer win. This is what lets every `StructDef` built outside the
/// source-struct seam keep meaning what it meant.
#[test]
fn field_provenance_is_positive_only_and_conflicts_fail_closed() {
    use crate::vc::CollectionOrigin;
    let mut ctx = VerificationContext::new();
    // Never observed.
    assert_eq!(
        ctx.struct_field_collection_origin("Holder", "data"),
        CollectionOrigin::Unknown
    );
    // Observed, and readable.
    ctx.register_struct_field_collection_origin("Holder", "data", CollectionOrigin::Exec);
    assert_eq!(
        ctx.struct_field_collection_origin("Holder", "data"),
        CollectionOrigin::Exec
    );
    // Writing `Unknown` records NOTHING, so it can never overwrite a measurement
    // with an absence.
    ctx.register_struct_field_collection_origin("Holder", "data", CollectionOrigin::Unknown);
    assert_eq!(
        ctx.struct_field_collection_origin("Holder", "data"),
        CollectionOrigin::Exec
    );
    // A DISAGREEING registration (two structs sharing a name) degrades to the
    // fail-closed answer instead of letting one spelling answer for the other.
    ctx.register_struct_field_collection_origin("Holder", "data", CollectionOrigin::Spec);
    assert_eq!(
        ctx.struct_field_collection_origin("Holder", "data"),
        CollectionOrigin::Unknown
    );
    // The tuple-component table obeys the same three rules.
    assert_eq!(
        ctx.binding_tuple_component_origin("t", "0"),
        CollectionOrigin::Unknown
    );
    ctx.register_binding_tuple_component_origin("t", "0", CollectionOrigin::Spec);
    assert_eq!(
        ctx.binding_tuple_component_origin("t", "0"),
        CollectionOrigin::Spec
    );
    ctx.register_binding_tuple_component_origin("t", "0", CollectionOrigin::Exec);
    assert_eq!(
        ctx.binding_tuple_component_origin("t", "0"),
        CollectionOrigin::Unknown
    );
}

/// PARTICIPATION IN THE QUERY KEY, pinned rather than asserted in prose. A
/// context that has recorded a field's provenance produces a DIFFERENT number of
/// obligations from one that has not, so the two must never share a cache entry.
/// The second half is the liar twin: contexts recording the SAME provenance must
/// still share a key, or the pin would pass for a key that merely varies.
#[test]
fn field_provenance_separates_query_keys_and_only_when_it_differs() {
    use crate::vc::CollectionOrigin;
    let build = |origin: Option<CollectionOrigin>, tuple: Option<CollectionOrigin>| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("b", TrustVcType::Int { width: 32 });
        if let Some(origin) = origin {
            ctx.register_struct_field_collection_origin("Holder", "data", origin);
        }
        if let Some(tuple) = tuple {
            ctx.register_binding_tuple_component_origin("t", "0", tuple);
        }
        ctx.isolated_query_key()
    };
    let none = build(None, None);
    let exec = build(Some(CollectionOrigin::Exec), None);
    let spec = build(Some(CollectionOrigin::Spec), None);
    let tuple = build(None, Some(CollectionOrigin::Spec));
    assert_ne!(none, exec, "an UNRECORDED field must not share a key");
    assert_ne!(exec, spec, "exec and spec provenance must not share a key");
    assert_ne!(none, tuple, "an unrecorded tuple component must not share");
    assert_eq!(
        exec,
        build(Some(CollectionOrigin::Exec), None),
        "the SAME provenance must still share a key"
    );
}
