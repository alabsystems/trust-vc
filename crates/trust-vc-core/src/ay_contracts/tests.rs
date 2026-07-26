// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::{HashMap, HashSet};

use super::*;

// -----------------------------------------------------------------------
// ContractLiteral encoding tests
// -----------------------------------------------------------------------

#[test]
fn test_contract_literal_positive_encoding() {
    let var = ContractVariable(5);
    let lit = ContractLiteral::positive(var);
    assert!(lit.is_positive());
    assert_eq!(lit.variable(), var);
    assert_eq!(lit.0, 10); // 5 << 1 = 10
}

#[test]
fn test_contract_literal_negative_encoding() {
    let var = ContractVariable(5);
    let lit = ContractLiteral::negative(var);
    assert!(!lit.is_positive());
    assert_eq!(lit.variable(), var);
    assert_eq!(lit.0, 11); // (5 << 1) | 1 = 11
}

#[test]
fn test_contract_literal_zero_variable() {
    let var = ContractVariable(0);
    let pos = ContractLiteral::positive(var);
    let neg = ContractLiteral::negative(var);
    assert!(pos.is_positive());
    assert!(!neg.is_positive());
    assert_eq!(pos.variable(), var);
    assert_eq!(neg.variable(), var);
}

// -----------------------------------------------------------------------
// term_to_literal contract tests
// -----------------------------------------------------------------------

#[test]
fn test_term_to_literal_registered_positive() {
    let mut registry = HashMapAtomRegistry::new();
    registry.register(ContractTermId(42), ContractVariable(7));

    let result = registry.term_to_literal(ContractTermId(42), true);
    assert!(result.is_some());

    let lit = result.unwrap();
    assert_eq!(lit.variable(), ContractVariable(7));
    assert!(lit.is_positive());

    assert!(validate_term_to_literal_postcondition(
        &registry,
        ContractTermId(42),
        true,
        result,
    ));
}

#[test]
fn test_term_to_literal_registered_negative() {
    let mut registry = HashMapAtomRegistry::new();
    registry.register(ContractTermId(42), ContractVariable(7));

    let result = registry.term_to_literal(ContractTermId(42), false);
    assert!(result.is_some());

    let lit = result.unwrap();
    assert_eq!(lit.variable(), ContractVariable(7));
    assert!(!lit.is_positive());

    assert!(validate_term_to_literal_postcondition(
        &registry,
        ContractTermId(42),
        false,
        result,
    ));
}

#[test]
fn test_term_to_literal_unregistered_returns_none() {
    let registry = HashMapAtomRegistry::new();

    let result = registry.term_to_literal(ContractTermId(999), true);
    assert!(result.is_none());

    assert!(validate_term_to_literal_postcondition(
        &registry,
        ContractTermId(999),
        true,
        result,
    ));
}

#[test]
fn test_term_to_literal_multiple_registrations() {
    let mut registry = HashMapAtomRegistry::new();
    registry.register(ContractTermId(1), ContractVariable(10));
    registry.register(ContractTermId(2), ContractVariable(20));
    registry.register(ContractTermId(3), ContractVariable(30));

    // All registered terms should produce Some
    for &(term_id, var_id) in &[(1, 10), (2, 20), (3, 30)] {
        let term = ContractTermId(term_id);
        let expected_var = ContractVariable(var_id);

        let pos = registry.term_to_literal(term, true);
        assert!(pos.is_some());
        assert_eq!(pos.unwrap().variable(), expected_var);
        assert!(pos.unwrap().is_positive());

        let neg = registry.term_to_literal(term, false);
        assert!(neg.is_some());
        assert_eq!(neg.unwrap().variable(), expected_var);
        assert!(!neg.unwrap().is_positive());
    }

    // Unregistered term should produce None
    let result = registry.term_to_literal(ContractTermId(99), true);
    assert!(result.is_none());
}

// -----------------------------------------------------------------------
// Postcondition validator tests (contract violation detection)
// -----------------------------------------------------------------------

#[test]
fn test_postcondition_rejects_some_for_unregistered_term() {
    let registry = HashMapAtomRegistry::new();
    // Fabricate a wrong result: Some when term is not registered
    let bogus_result = Some(ContractLiteral::positive(ContractVariable(0)));

    assert!(!validate_term_to_literal_postcondition(
        &registry,
        ContractTermId(999),
        true,
        bogus_result,
    ));
}

#[test]
fn test_postcondition_rejects_none_for_registered_term() {
    let mut registry = HashMapAtomRegistry::new();
    registry.register(ContractTermId(42), ContractVariable(7));

    assert!(!validate_term_to_literal_postcondition(
        &registry,
        ContractTermId(42),
        true,
        None,
    ));
}

#[test]
fn test_postcondition_rejects_wrong_variable() {
    let mut registry = HashMapAtomRegistry::new();
    registry.register(ContractTermId(42), ContractVariable(7));

    // Correct polarity but wrong variable
    let wrong_var = Some(ContractLiteral::positive(ContractVariable(99)));

    assert!(!validate_term_to_literal_postcondition(
        &registry,
        ContractTermId(42),
        true,
        wrong_var,
    ));
}

#[test]
fn test_postcondition_rejects_wrong_polarity() {
    let mut registry = HashMapAtomRegistry::new();
    registry.register(ContractTermId(42), ContractVariable(7));

    // Correct variable but wrong polarity (negative when positive requested)
    let wrong_polarity = Some(ContractLiteral::negative(ContractVariable(7)));

    assert!(!validate_term_to_literal_postcondition(
        &registry,
        ContractTermId(42),
        true, // requested positive
        wrong_polarity,
    ));
}

// -----------------------------------------------------------------------
// TheoryKindLabel contract tests
// -----------------------------------------------------------------------

#[test]
fn test_theory_kind_as_str_all_variants_non_empty() {
    let variants = [
        ContractTheoryKind::Euf,
        ContractTheoryKind::Lra,
        ContractTheoryKind::Nia,
        ContractTheoryKind::BitVector,
        ContractTheoryKind::Array,
        ContractTheoryKind::Sequence,
        ContractTheoryKind::Other,
    ];

    for variant in &variants {
        let label = variant.as_str();
        assert!(
            validate_as_str_postcondition(label),
            "{variant:?}::as_str() returned empty string"
        );
    }
}

#[test]
fn test_theory_kind_as_str_distinct_labels() {
    let variants = [
        ContractTheoryKind::Euf,
        ContractTheoryKind::Lra,
        ContractTheoryKind::Nia,
        ContractTheoryKind::BitVector,
        ContractTheoryKind::Array,
        ContractTheoryKind::Sequence,
        ContractTheoryKind::Other,
    ];

    let labels: Vec<&str> = variants.iter().map(|v| v.as_str()).collect();

    // Check all pairs are distinct
    for i in 0..labels.len() {
        for j in (i + 1)..labels.len() {
            assert_ne!(
                labels[i], labels[j],
                "{:?} and {:?} have the same label: {}",
                variants[i], variants[j], labels[i]
            );
        }
    }
}

#[test]
fn test_theory_kind_as_str_matches_trust_vc_kernel_bridge() {
    // Verify our labels match the known AYTheoryKind::as_str values
    // from trust-vc-kernel/src/bridge.rs
    assert_eq!(ContractTheoryKind::Euf.as_str(), "EUF");
    assert_eq!(ContractTheoryKind::Lra.as_str(), "LRA");
    assert_eq!(ContractTheoryKind::Nia.as_str(), "NIA");
    assert_eq!(ContractTheoryKind::BitVector.as_str(), "BV");
    assert_eq!(ContractTheoryKind::Array.as_str(), "Array");
    assert_eq!(ContractTheoryKind::Sequence.as_str(), "Seq");
    assert_eq!(ContractTheoryKind::Other.as_str(), "Other");
}

// -----------------------------------------------------------------------
// as_str postcondition validator tests
// -----------------------------------------------------------------------

#[test]
fn test_as_str_postcondition_rejects_empty() {
    assert!(!validate_as_str_postcondition(""));
}

#[test]
fn test_as_str_postcondition_accepts_non_empty() {
    assert!(validate_as_str_postcondition("EUF"));
    assert!(validate_as_str_postcondition("x"));
}

// -----------------------------------------------------------------------
// extern_spec registration integration tests
// -----------------------------------------------------------------------

#[test]
fn test_register_ay_term_to_literal_contract_creates_obligations() {
    crate::extern_spec_verify::clear_extern_contracts();

    register_ay_term_to_literal_contract();

    let mut ctx = crate::vc::VerificationContext::new();
    crate::extern_spec_verify::apply_extern_specs_to_context(&mut ctx)
        .expect("applying ay term_to_literal contract should succeed");

    // requires: 1 assert (the "true" precondition)
    // ensures: 2 assumes (registered => Some, !registered => None)
    assert_eq!(ctx.obligations.len(), 3);

    let names: Vec<&str> = ctx.obligations.iter().map(|o| o.name.as_str()).collect();
    assert!(
        names
            .iter()
            .any(|n| n.contains("term_to_literal") && n.contains("requires")),
        "should have term_to_literal requires obligation, got: {names:?}"
    );
    assert!(
        names
            .iter()
            .any(|n| n.contains("term_to_literal") && n.contains("ensures")),
        "should have term_to_literal ensures obligation, got: {names:?}"
    );
}

#[test]
fn test_register_ay_theory_kind_as_str_contract_creates_obligations() {
    crate::extern_spec_verify::clear_extern_contracts();

    register_ay_theory_kind_as_str_contract();

    let mut ctx = crate::vc::VerificationContext::new();
    crate::extern_spec_verify::apply_extern_specs_to_context(&mut ctx)
        .expect("applying ay theory kind as_str contract should succeed");

    // requires: 1 assert ("true"), ensures: 1 assume ("!result.is_empty()")
    assert_eq!(ctx.obligations.len(), 2);

    let names: Vec<&str> = ctx.obligations.iter().map(|o| o.name.as_str()).collect();
    assert!(
        names
            .iter()
            .any(|n| n.contains("AYTheoryKind") && n.contains("requires")),
        "should have AYTheoryKind requires obligation, got: {names:?}"
    );
    assert!(
        names
            .iter()
            .any(|n| n.contains("AYTheoryKind") && n.contains("ensures")),
        "should have AYTheoryKind ensures obligation, got: {names:?}"
    );
}

#[test]
fn test_both_contracts_registered_together_produce_combined_obligations() {
    crate::extern_spec_verify::clear_extern_contracts();

    register_ay_term_to_literal_contract();
    register_ay_theory_kind_as_str_contract();

    let mut ctx = crate::vc::VerificationContext::new();
    crate::extern_spec_verify::apply_extern_specs_to_context(&mut ctx)
        .expect("applying both ay contracts should succeed");

    // term_to_literal: 1 requires + 2 ensures = 3
    // as_str: 1 requires + 1 ensures = 2
    // Total: 5
    assert_eq!(ctx.obligations.len(), 5);

    let names: Vec<&str> = ctx.obligations.iter().map(|o| o.name.as_str()).collect();
    assert!(
        names.iter().any(|n| n.contains("term_to_literal")),
        "should have term_to_literal obligations, got: {names:?}"
    );
    assert!(
        names.iter().any(|n| n.contains("AYTheoryKind")),
        "should have AYTheoryKind obligations, got: {names:?}"
    );
}

// -----------------------------------------------------------------------
// ContractLiteral negation/raw tests
// -----------------------------------------------------------------------

#[test]
fn test_contract_literal_negation_roundtrip() {
    let var = ContractVariable(3);
    let pos = ContractLiteral::positive(var);
    let neg = pos.negated();
    assert!(!neg.is_positive());
    assert_eq!(neg.variable(), var);
    assert_eq!(neg.negated(), pos);
}

#[test]
fn test_contract_literal_raw_encoding() {
    let var = ContractVariable(7);
    assert_eq!(ContractLiteral::positive(var).raw(), 14);
    assert_eq!(ContractLiteral::negative(var).raw(), 15);
}

// -----------------------------------------------------------------------
// BCP propagation contract tests
// -----------------------------------------------------------------------

#[test]
fn test_bcp_no_clauses_no_propagation() {
    let mut bcp = ReferenceBcp::new(4);
    let snap = bcp.propagate();
    assert!(snap.conflict.is_none());
    assert_eq!(snap.trail_after.len(), 0);
    assert!(validate_propagation_postcondition(&snap));
}

#[test]
fn test_bcp_unit_clause_propagates() {
    let mut bcp = ReferenceBcp::new(4);
    let a = ContractLiteral::positive(ContractVariable(0));
    bcp.add_clause(vec![a]);
    let snap = bcp.propagate();
    assert!(snap.conflict.is_none());
    assert_eq!(snap.trail_after.len(), 1);
    assert_eq!(snap.trail_after[0], a);
    assert!(validate_propagation_postcondition(&snap));
}

#[test]
fn test_bcp_binary_clause_propagation() {
    let mut bcp = ReferenceBcp::new(4);
    let a = ContractLiteral::positive(ContractVariable(0));
    let b = ContractLiteral::positive(ContractVariable(1));
    bcp.add_clause(vec![a, b]);
    bcp.assign(a.negated());
    let snap = bcp.propagate();
    assert!(snap.conflict.is_none());
    assert_eq!(snap.trail_after[1], b);
    assert!(validate_propagation_postcondition(&snap));
}

#[test]
fn test_bcp_chain_propagation() {
    let mut bcp = ReferenceBcp::new(4);
    let a = ContractLiteral::positive(ContractVariable(0));
    let b = ContractLiteral::positive(ContractVariable(1));
    let c = ContractLiteral::positive(ContractVariable(2));
    bcp.add_clause(vec![a]);
    bcp.add_clause(vec![a.negated(), b]);
    bcp.add_clause(vec![b.negated(), c]);
    let snap = bcp.propagate();
    assert!(snap.conflict.is_none());
    assert_eq!(snap.trail_after.len(), 3);
    assert!(validate_propagation_postcondition(&snap));
}

#[test]
fn test_bcp_conflict_detection() {
    let mut bcp = ReferenceBcp::new(4);
    let a = ContractLiteral::positive(ContractVariable(0));
    bcp.add_clause(vec![a]);
    bcp.add_clause(vec![a.negated()]);
    let snap = bcp.propagate();
    assert!(snap.conflict.is_some());
    assert!(validate_propagation_postcondition(&snap));
}

#[test]
fn test_bcp_conflict_all_literals_false() {
    let mut bcp = ReferenceBcp::new(4);
    let a = ContractLiteral::positive(ContractVariable(0));
    let b = ContractLiteral::positive(ContractVariable(1));
    bcp.add_clause(vec![a, b]);
    bcp.assign(a.negated());
    bcp.assign(b.negated());
    let snap = bcp.propagate();
    assert!(snap.conflict.is_some());
    let cref = snap.conflict.unwrap();
    for lit in &snap.clauses[cref.0 as usize] {
        assert_eq!(
            snap.assignment.get(&lit.raw()),
            Some(&ContractAssignmentValue::False)
        );
    }
    assert!(validate_propagation_postcondition(&snap));
}

#[test]
fn test_bcp_no_conflict_qhead_equals_trail() {
    let mut bcp = ReferenceBcp::new(4);
    let a = ContractLiteral::positive(ContractVariable(0));
    bcp.add_clause(vec![a, ContractLiteral::positive(ContractVariable(1))]);
    bcp.assign(a);
    let snap = bcp.propagate();
    assert!(snap.conflict.is_none());
    assert_eq!(snap.qhead_after, snap.trail_after.len());
    assert!(validate_propagation_postcondition(&snap));
}

#[test]
fn test_bcp_trail_monotonicity() {
    let mut bcp = ReferenceBcp::new(4);
    bcp.add_clause(vec![ContractLiteral::positive(ContractVariable(0))]);
    bcp.assign(ContractLiteral::positive(ContractVariable(1)));
    let snap = bcp.propagate();
    assert!(snap.trail_after.len() >= snap.trail_before.len());
    assert!(validate_propagation_postcondition(&snap));
}

#[test]
fn test_bcp_no_duplicate_propagation() {
    let mut bcp = ReferenceBcp::new(4);
    let a = ContractLiteral::positive(ContractVariable(0));
    let b = ContractLiteral::positive(ContractVariable(1));
    bcp.add_clause(vec![a.negated(), b]);
    bcp.add_clause(vec![a.negated(), b]);
    bcp.assign(a);
    let snap = bcp.propagate();
    let bc = snap
        .trail_after
        .iter()
        .filter(|l| l.variable() == ContractVariable(1))
        .count();
    assert_eq!(bc, 1);
    assert!(validate_propagation_postcondition(&snap));
}

// -----------------------------------------------------------------------
// Propagation postcondition validator negative tests
// -----------------------------------------------------------------------

#[test]
fn test_propagation_rejects_incomplete() {
    let a = ContractLiteral::positive(ContractVariable(0));
    let snap = PropagationSnapshot {
        trail_before: vec![],
        trail_after: vec![a],
        qhead_before: 0,
        qhead_after: 0,
        clauses: vec![vec![a]],
        assignment: {
            let mut m = HashMap::new();
            m.insert(a.raw(), ContractAssignmentValue::True);
            m
        },
        conflict: None,
    };
    assert!(!validate_propagation_postcondition(&snap));
}

#[test]
fn test_propagation_rejects_non_falsified_conflict() {
    let a = ContractLiteral::positive(ContractVariable(0));
    let snap = PropagationSnapshot {
        trail_before: vec![],
        trail_after: vec![],
        qhead_before: 0,
        qhead_after: 0,
        clauses: vec![vec![a]],
        assignment: {
            let mut m = HashMap::new();
            m.insert(a.raw(), ContractAssignmentValue::True);
            m
        },
        conflict: Some(ContractClauseRef(0)),
    };
    assert!(!validate_propagation_postcondition(&snap));
}

#[test]
fn test_propagation_rejects_shrinking_trail() {
    let a = ContractLiteral::positive(ContractVariable(0));
    let b = ContractLiteral::positive(ContractVariable(1));
    let snap = PropagationSnapshot {
        trail_before: vec![a, b],
        trail_after: vec![a],
        qhead_before: 2,
        qhead_after: 1,
        clauses: vec![],
        assignment: HashMap::new(),
        conflict: None,
    };
    assert!(!validate_propagation_postcondition(&snap));
}

#[test]
fn test_propagation_rejects_duplicate_var() {
    let a = ContractLiteral::positive(ContractVariable(0));
    let snap = PropagationSnapshot {
        trail_before: vec![],
        trail_after: vec![a, a],
        qhead_before: 0,
        qhead_after: 2,
        clauses: vec![vec![a], vec![a]],
        assignment: {
            let mut m = HashMap::new();
            m.insert(a.raw(), ContractAssignmentValue::True);
            m.insert(a.negated().raw(), ContractAssignmentValue::False);
            m
        },
        conflict: None,
    };
    assert!(!validate_propagation_postcondition(&snap));
}

// -----------------------------------------------------------------------
// Decision contract tests
// -----------------------------------------------------------------------

#[test]
fn test_decision_basic() {
    let mut dec = ReferenceDecision::new(10);
    let snap = dec.decide(ContractLiteral::positive(ContractVariable(3)));
    assert!(validate_decision_precondition(&snap));
    assert!(validate_decision_postcondition(&snap));
    assert_eq!(snap.level_after, 1);
}

#[test]
fn test_decision_after_propagation() {
    let mut dec = ReferenceDecision::new(10);
    dec.assign_propagated(ContractLiteral::positive(ContractVariable(0)));
    dec.assign_propagated(ContractLiteral::negative(ContractVariable(1)));
    let snap = dec.decide(ContractLiteral::positive(ContractVariable(5)));
    assert!(validate_decision_precondition(&snap));
    assert!(validate_decision_postcondition(&snap));
    assert_eq!(snap.level_after, 1);
}

#[test]
fn test_decision_multiple_levels() {
    let mut dec = ReferenceDecision::new(10);
    let s1 = dec.decide(ContractLiteral::positive(ContractVariable(0)));
    assert_eq!(s1.level_after, 1);
    dec.set_qhead(dec.trail.len());
    let s2 = dec.decide(ContractLiteral::positive(ContractVariable(1)));
    assert_eq!(s2.level_after, 2);
    dec.set_qhead(dec.trail.len());
    let s3 = dec.decide(ContractLiteral::positive(ContractVariable(2)));
    assert_eq!(s3.level_after, 3);
}

#[test]
fn test_decision_rejects_assigned() {
    let mut dec = ReferenceDecision::new(10);
    dec.assign_propagated(ContractLiteral::positive(ContractVariable(3)));
    let snap = dec.decide(ContractLiteral::positive(ContractVariable(3)));
    assert!(!validate_decision_precondition(&snap));
}

#[test]
fn test_decision_rejects_removed() {
    let mut dec = ReferenceDecision::new(10);
    dec.remove_var(5);
    let snap = dec.decide(ContractLiteral::positive(ContractVariable(5)));
    assert!(!validate_decision_precondition(&snap));
}

#[test]
fn test_decision_rejects_pending_props() {
    let mut dec = ReferenceDecision::new(10);
    dec.assign_propagated(ContractLiteral::positive(ContractVariable(0)));
    dec.set_qhead(0);
    let snap = dec.decide(ContractLiteral::positive(ContractVariable(3)));
    assert!(!validate_decision_precondition(&snap));
}

#[test]
fn test_decision_rejects_out_of_bounds() {
    let mut dec = ReferenceDecision::new(5);
    let snap = dec.decide(ContractLiteral::positive(ContractVariable(10)));
    assert!(!validate_decision_precondition(&snap));
}

// -----------------------------------------------------------------------
// extern_spec registration for new contracts
// -----------------------------------------------------------------------

#[test]
fn test_register_propagation_contract() {
    crate::extern_spec_verify::clear_extern_contracts();
    register_ay_propagation_contract();
    let mut ctx = crate::vc::VerificationContext::new();
    crate::extern_spec_verify::apply_extern_specs_to_context(&mut ctx).unwrap();
    assert_eq!(ctx.obligations.len(), 4);
    let names: Vec<&str> = ctx.obligations.iter().map(|o| o.name.as_str()).collect();
    assert!(names.iter().any(|n| n.contains("propagate_bcp")));
}

#[test]
fn test_register_decision_contract() {
    crate::extern_spec_verify::clear_extern_contracts();
    register_ay_decision_contract();
    let mut ctx = crate::vc::VerificationContext::new();
    crate::extern_spec_verify::apply_extern_specs_to_context(&mut ctx).unwrap();
    assert_eq!(ctx.obligations.len(), 4);
    let names: Vec<&str> = ctx.obligations.iter().map(|o| o.name.as_str()).collect();
    assert!(names.iter().any(|n| n.contains("Solver::decide")));
}

#[test]
fn test_all_four_contracts_combined() {
    crate::extern_spec_verify::clear_extern_contracts();
    register_ay_term_to_literal_contract();
    register_ay_theory_kind_as_str_contract();
    register_ay_propagation_contract();
    register_ay_decision_contract();
    let mut ctx = crate::vc::VerificationContext::new();
    crate::extern_spec_verify::apply_extern_specs_to_context(&mut ctx).unwrap();
    assert_eq!(ctx.obligations.len(), 13);
}

// Helper: build a decision-level map from a slice of (variable, level) pairs.
fn make_levels(pairs: &[(u32, usize)]) -> HashMap<ContractVariable, usize> {
    pairs
        .iter()
        .map(|&(v, l)| (ContractVariable(v), l))
        .collect()
}

// Helper: build an assignment map where given literals are all false.
fn make_all_false(lits: &[ContractLiteral]) -> HashMap<u32, ContractAssignmentValue> {
    let mut m = HashMap::new();
    for lit in lits {
        m.insert(lit.raw(), ContractAssignmentValue::False);
    }
    m
}

// -----------------------------------------------------------------------
// ConflictAnalysisResult validation tests
// -----------------------------------------------------------------------

#[test]
fn test_cdcl_valid_single_literal_learned_clause() {
    // Learned clause with a single literal at the current level.
    // Backjump level should be 0.
    let uip = ContractLiteral::negative(ContractVariable(3));
    let result = ConflictAnalysisResult {
        learned_clause: vec![uip],
        backjump_level: 0,
        uip_literal: uip,
    };
    let levels = make_levels(&[(3, 5)]);
    let assignment = make_all_false(&[uip]);
    assert!(validate_conflict_analysis(&result, 5, &levels, &assignment));
}

#[test]
fn test_cdcl_valid_two_literal_learned_clause() {
    // Learned clause: [~x3 @ level 5, ~x1 @ level 2]
    // UIP is ~x3, backjump to level 2.
    let uip = ContractLiteral::negative(ContractVariable(3));
    let other = ContractLiteral::negative(ContractVariable(1));
    let result = ConflictAnalysisResult {
        learned_clause: vec![uip, other],
        backjump_level: 2,
        uip_literal: uip,
    };
    let levels = make_levels(&[(3, 5), (1, 2)]);
    let assignment = make_all_false(&[uip, other]);
    assert!(validate_conflict_analysis(&result, 5, &levels, &assignment));
}

#[test]
fn test_cdcl_valid_three_literal_learned_clause() {
    // Learned clause: [~x5 @ level 7, ~x2 @ level 3, ~x4 @ level 5]
    // UIP is ~x5, backjump to level 5 (second-highest).
    let uip = ContractLiteral::negative(ContractVariable(5));
    let lit2 = ContractLiteral::negative(ContractVariable(2));
    let lit3 = ContractLiteral::negative(ContractVariable(4));
    let result = ConflictAnalysisResult {
        learned_clause: vec![uip, lit2, lit3],
        backjump_level: 5,
        uip_literal: uip,
    };
    let levels = make_levels(&[(5, 7), (2, 3), (4, 5)]);
    let assignment = make_all_false(&[uip, lit2, lit3]);
    assert!(validate_conflict_analysis(&result, 7, &levels, &assignment));
}

#[test]
fn test_cdcl_rejects_empty_clause() {
    let uip = ContractLiteral::positive(ContractVariable(0));
    let result = ConflictAnalysisResult {
        learned_clause: vec![],
        backjump_level: 0,
        uip_literal: uip,
    };
    let levels = make_levels(&[]);
    let assignment = HashMap::new();
    assert!(!validate_conflict_analysis(
        &result,
        3,
        &levels,
        &assignment
    ));
}

#[test]
fn test_cdcl_rejects_non_asserting_two_at_current_level() {
    // Two literals at current level = not asserting.
    let lit1 = ContractLiteral::negative(ContractVariable(1));
    let lit2 = ContractLiteral::negative(ContractVariable(2));
    let result = ConflictAnalysisResult {
        learned_clause: vec![lit1, lit2],
        backjump_level: 0,
        uip_literal: lit1,
    };
    let levels = make_levels(&[(1, 5), (2, 5)]);
    let assignment = make_all_false(&[lit1, lit2]);
    assert!(!validate_conflict_analysis(
        &result,
        5,
        &levels,
        &assignment
    ));
}

#[test]
fn test_cdcl_rejects_zero_at_current_level() {
    // No literal at current level = not asserting.
    let lit1 = ContractLiteral::negative(ContractVariable(1));
    let lit2 = ContractLiteral::negative(ContractVariable(2));
    let result = ConflictAnalysisResult {
        learned_clause: vec![lit1, lit2],
        backjump_level: 2,
        uip_literal: lit1,
    };
    let levels = make_levels(&[(1, 3), (2, 2)]);
    let assignment = make_all_false(&[lit1, lit2]);
    assert!(!validate_conflict_analysis(
        &result,
        5,
        &levels,
        &assignment
    ));
}

#[test]
fn test_cdcl_rejects_uip_not_in_clause() {
    let uip = ContractLiteral::negative(ContractVariable(9));
    let lit1 = ContractLiteral::negative(ContractVariable(3));
    let result = ConflictAnalysisResult {
        learned_clause: vec![lit1],
        backjump_level: 0,
        uip_literal: uip,
    };
    let levels = make_levels(&[(3, 5), (9, 5)]);
    let assignment = make_all_false(&[lit1]);
    assert!(!validate_conflict_analysis(
        &result,
        5,
        &levels,
        &assignment
    ));
}

#[test]
fn test_cdcl_rejects_uip_at_wrong_level() {
    // UIP literal is in the clause but not at the current decision level.
    let uip = ContractLiteral::negative(ContractVariable(3));
    let other = ContractLiteral::negative(ContractVariable(1));
    let result = ConflictAnalysisResult {
        learned_clause: vec![uip, other],
        backjump_level: 2,
        uip_literal: uip,
    };
    // UIP at level 2 instead of current level 5.
    let levels = make_levels(&[(3, 2), (1, 2)]);
    let assignment = make_all_false(&[uip, other]);
    assert!(!validate_conflict_analysis(
        &result,
        5,
        &levels,
        &assignment
    ));
}

#[test]
fn test_cdcl_rejects_wrong_backjump_level() {
    let uip = ContractLiteral::negative(ContractVariable(3));
    let other = ContractLiteral::negative(ContractVariable(1));
    let result = ConflictAnalysisResult {
        learned_clause: vec![uip, other],
        backjump_level: 1, // Wrong! Should be 2.
        uip_literal: uip,
    };
    let levels = make_levels(&[(3, 5), (1, 2)]);
    let assignment = make_all_false(&[uip, other]);
    assert!(!validate_conflict_analysis(
        &result,
        5,
        &levels,
        &assignment
    ));
}

#[test]
fn test_cdcl_rejects_literal_not_false() {
    let uip = ContractLiteral::negative(ContractVariable(3));
    let other = ContractLiteral::negative(ContractVariable(1));
    let result = ConflictAnalysisResult {
        learned_clause: vec![uip, other],
        backjump_level: 2,
        uip_literal: uip,
    };
    let levels = make_levels(&[(3, 5), (1, 2)]);
    // Only uip is assigned false; other is True (not all false).
    let mut assignment = HashMap::new();
    assignment.insert(uip.raw(), ContractAssignmentValue::False);
    assignment.insert(other.raw(), ContractAssignmentValue::True);
    assert!(!validate_conflict_analysis(
        &result,
        5,
        &levels,
        &assignment
    ));
}

#[test]
fn test_cdcl_rejects_tautological_clause() {
    // Clause contains x3 positive and x3 negative = tautology.
    let pos3 = ContractLiteral::positive(ContractVariable(3));
    let neg3 = ContractLiteral::negative(ContractVariable(3));
    let result = ConflictAnalysisResult {
        learned_clause: vec![pos3, neg3],
        backjump_level: 0,
        uip_literal: pos3,
    };
    let levels = make_levels(&[(3, 5)]);
    let mut assignment = HashMap::new();
    assignment.insert(pos3.raw(), ContractAssignmentValue::False);
    assignment.insert(neg3.raw(), ContractAssignmentValue::False);
    // Even if other checks pass, tautology check should fail.
    // Note: the asserting check will also fail since both literals are at level 5,
    // but the tautology check is a separate invariant we want to exercise.
    assert!(!validate_conflict_analysis(
        &result,
        5,
        &levels,
        &assignment
    ));
}

#[test]
fn test_cdcl_rejects_literal_unassigned() {
    let uip = ContractLiteral::negative(ContractVariable(3));
    let other = ContractLiteral::negative(ContractVariable(1));
    let result = ConflictAnalysisResult {
        learned_clause: vec![uip, other],
        backjump_level: 2,
        uip_literal: uip,
    };
    let levels = make_levels(&[(3, 5), (1, 2)]);
    // uip is false but other is unassigned.
    let mut assignment = HashMap::new();
    assignment.insert(uip.raw(), ContractAssignmentValue::False);
    assignment.insert(other.raw(), ContractAssignmentValue::Unassigned);
    assert!(!validate_conflict_analysis(
        &result,
        5,
        &levels,
        &assignment
    ));
}

#[test]
fn test_cdcl_valid_positive_uip() {
    // UIP can be a positive literal too.
    let uip = ContractLiteral::positive(ContractVariable(7));
    let other = ContractLiteral::negative(ContractVariable(2));
    let result = ConflictAnalysisResult {
        learned_clause: vec![uip, other],
        backjump_level: 1,
        uip_literal: uip,
    };
    let levels = make_levels(&[(7, 4), (2, 1)]);
    let assignment = make_all_false(&[uip, other]);
    assert!(validate_conflict_analysis(&result, 4, &levels, &assignment));
}

#[test]
fn test_cdcl_backjump_to_zero_with_two_lits() {
    // Two literals: UIP at current level, other at level 0.
    let uip = ContractLiteral::negative(ContractVariable(5));
    let other = ContractLiteral::negative(ContractVariable(0));
    let result = ConflictAnalysisResult {
        learned_clause: vec![uip, other],
        backjump_level: 0,
        uip_literal: uip,
    };
    let levels = make_levels(&[(5, 3), (0, 0)]);
    let assignment = make_all_false(&[uip, other]);
    assert!(validate_conflict_analysis(&result, 3, &levels, &assignment));
}

#[test]
fn test_cdcl_multi_level_backjump() {
    // Clause with literals at levels 10, 7, 4, 1.
    // UIP at level 10, backjump to level 7.
    let uip = ContractLiteral::negative(ContractVariable(10));
    let l7 = ContractLiteral::negative(ContractVariable(7));
    let l4 = ContractLiteral::negative(ContractVariable(4));
    let l1 = ContractLiteral::negative(ContractVariable(1));
    let result = ConflictAnalysisResult {
        learned_clause: vec![uip, l7, l4, l1],
        backjump_level: 7,
        uip_literal: uip,
    };
    let levels = make_levels(&[(10, 10), (7, 7), (4, 4), (1, 1)]);
    let assignment = make_all_false(&[uip, l7, l4, l1]);
    assert!(validate_conflict_analysis(
        &result,
        10,
        &levels,
        &assignment
    ));
}

// -----------------------------------------------------------------------
// BacktrackSnapshot validation tests
// -----------------------------------------------------------------------

#[test]
fn test_backtrack_valid_simple() {
    // Trail: [x0@1, x1@2, x2@3]. Backtrack to level 1.
    // After: only x0 remains.
    let l0 = ContractLiteral::positive(ContractVariable(0));
    let l1 = ContractLiteral::positive(ContractVariable(1));
    let l2 = ContractLiteral::positive(ContractVariable(2));
    let mut assignment_after = HashMap::new();
    assignment_after.insert(l0.raw(), ContractAssignmentValue::True);
    assignment_after.insert(l1.raw(), ContractAssignmentValue::Unassigned);
    assignment_after.insert(l2.raw(), ContractAssignmentValue::Unassigned);
    let snap = BacktrackSnapshot {
        target_level: 1,
        trail_before: vec![l0, l1, l2],
        trail_after: vec![l0],
        trail_levels: vec![1, 2, 3],
        assignment_after,
    };
    assert!(validate_backtrack(&snap));
}

#[test]
fn test_backtrack_to_level_zero() {
    // Backtrack to level 0 removes everything.
    let l0 = ContractLiteral::positive(ContractVariable(0));
    let l1 = ContractLiteral::positive(ContractVariable(1));
    let mut assignment_after = HashMap::new();
    assignment_after.insert(l0.raw(), ContractAssignmentValue::Unassigned);
    assignment_after.insert(l1.raw(), ContractAssignmentValue::Unassigned);
    let snap = BacktrackSnapshot {
        target_level: 0,
        trail_before: vec![l0, l1],
        trail_after: vec![],
        trail_levels: vec![1, 2],
        assignment_after,
    };
    assert!(validate_backtrack(&snap));
}

#[test]
fn test_backtrack_preserves_lower_levels() {
    // Trail: [x0@1, x1@1, x2@2, x3@3]. Backtrack to level 2.
    // After: [x0, x1, x2].
    let l0 = ContractLiteral::positive(ContractVariable(0));
    let l1 = ContractLiteral::positive(ContractVariable(1));
    let l2 = ContractLiteral::positive(ContractVariable(2));
    let l3 = ContractLiteral::positive(ContractVariable(3));
    let mut assignment_after = HashMap::new();
    assignment_after.insert(l0.raw(), ContractAssignmentValue::True);
    assignment_after.insert(l1.raw(), ContractAssignmentValue::True);
    assignment_after.insert(l2.raw(), ContractAssignmentValue::True);
    assignment_after.insert(l3.raw(), ContractAssignmentValue::Unassigned);
    let snap = BacktrackSnapshot {
        target_level: 2,
        trail_before: vec![l0, l1, l2, l3],
        trail_after: vec![l0, l1, l2],
        trail_levels: vec![1, 1, 2, 3],
        assignment_after,
    };
    assert!(validate_backtrack(&snap));
}

#[test]
fn test_backtrack_rejects_above_level_still_in_trail() {
    // Literal at level 3 still in trail_after when target is 1.
    let l0 = ContractLiteral::positive(ContractVariable(0));
    let l1 = ContractLiteral::positive(ContractVariable(1));
    let mut assignment_after = HashMap::new();
    assignment_after.insert(l0.raw(), ContractAssignmentValue::True);
    assignment_after.insert(l1.raw(), ContractAssignmentValue::True);
    let snap = BacktrackSnapshot {
        target_level: 1,
        trail_before: vec![l0, l1],
        trail_after: vec![l0, l1], // l1 at level 3 should be removed!
        trail_levels: vec![1, 3],
        assignment_after,
    };
    assert!(!validate_backtrack(&snap));
}

#[test]
fn test_backtrack_rejects_above_level_still_assigned() {
    // Literal above target still assigned True in the map.
    let l0 = ContractLiteral::positive(ContractVariable(0));
    let l1 = ContractLiteral::positive(ContractVariable(1));
    let mut assignment_after = HashMap::new();
    assignment_after.insert(l0.raw(), ContractAssignmentValue::True);
    assignment_after.insert(l1.raw(), ContractAssignmentValue::True); // Should be Unassigned!
    let snap = BacktrackSnapshot {
        target_level: 1,
        trail_before: vec![l0, l1],
        trail_after: vec![l0],
        trail_levels: vec![1, 2],
        assignment_after,
    };
    assert!(!validate_backtrack(&snap));
}

#[test]
fn test_backtrack_rejects_missing_preserved_literal() {
    // Literal at level 1 (at/below target) is missing from trail_after.
    let l0 = ContractLiteral::positive(ContractVariable(0));
    let l1 = ContractLiteral::positive(ContractVariable(1));
    let l2 = ContractLiteral::positive(ContractVariable(2));
    let mut assignment_after = HashMap::new();
    assignment_after.insert(l0.raw(), ContractAssignmentValue::True);
    assignment_after.insert(l1.raw(), ContractAssignmentValue::True);
    assignment_after.insert(l2.raw(), ContractAssignmentValue::Unassigned);
    let snap = BacktrackSnapshot {
        target_level: 2,
        trail_before: vec![l0, l1, l2],
        trail_after: vec![l0], // Missing l1 which is at level 1!
        trail_levels: vec![1, 1, 3],
        assignment_after,
    };
    assert!(!validate_backtrack(&snap));
}

#[test]
fn test_backtrack_rejects_trail_grew() {
    // Trail after is longer than trail before.
    let l0 = ContractLiteral::positive(ContractVariable(0));
    let l1 = ContractLiteral::positive(ContractVariable(1));
    let assignment_after = HashMap::new();
    let snap = BacktrackSnapshot {
        target_level: 1,
        trail_before: vec![l0],
        trail_after: vec![l0, l1],
        trail_levels: vec![1],
        assignment_after,
    };
    assert!(!validate_backtrack(&snap));
}

#[test]
fn test_backtrack_rejects_wrong_order() {
    // Trail after has literals in wrong order relative to trail before.
    let l0 = ContractLiteral::positive(ContractVariable(0));
    let l1 = ContractLiteral::positive(ContractVariable(1));
    let l2 = ContractLiteral::positive(ContractVariable(2));
    let mut assignment_after = HashMap::new();
    assignment_after.insert(l0.raw(), ContractAssignmentValue::True);
    assignment_after.insert(l1.raw(), ContractAssignmentValue::True);
    assignment_after.insert(l2.raw(), ContractAssignmentValue::Unassigned);
    let snap = BacktrackSnapshot {
        target_level: 2,
        trail_before: vec![l0, l1, l2],
        trail_after: vec![l1, l0], // Swapped order!
        trail_levels: vec![1, 2, 3],
        assignment_after,
    };
    assert!(!validate_backtrack(&snap));
}

#[test]
fn test_backtrack_rejects_mismatched_levels_length() {
    let l0 = ContractLiteral::positive(ContractVariable(0));
    let snap = BacktrackSnapshot {
        target_level: 1,
        trail_before: vec![l0],
        trail_after: vec![l0],
        trail_levels: vec![1, 2], // Length mismatch with trail_before!
        assignment_after: HashMap::new(),
    };
    assert!(!validate_backtrack(&snap));
}

// -----------------------------------------------------------------------
// Learned clause quality tests
// -----------------------------------------------------------------------

#[test]
fn test_quality_valid_single_literal() {
    let lit = ContractLiteral::positive(ContractVariable(5));
    assert!(validate_learned_clause_quality(&[lit]));
}

#[test]
fn test_quality_valid_multiple_distinct() {
    let l1 = ContractLiteral::positive(ContractVariable(1));
    let l2 = ContractLiteral::negative(ContractVariable(2));
    let l3 = ContractLiteral::positive(ContractVariable(3));
    assert!(validate_learned_clause_quality(&[l1, l2, l3]));
}

#[test]
fn test_quality_rejects_empty() {
    assert!(!validate_learned_clause_quality(&[]));
}

#[test]
fn test_quality_rejects_duplicate_variable() {
    // Same variable appears twice (same polarity).
    let l1 = ContractLiteral::positive(ContractVariable(3));
    let l2 = ContractLiteral::positive(ContractVariable(3));
    assert!(!validate_learned_clause_quality(&[l1, l2]));
}

#[test]
fn test_quality_rejects_tautology() {
    // Same variable positive and negative.
    let pos = ContractLiteral::positive(ContractVariable(4));
    let neg = ContractLiteral::negative(ContractVariable(4));
    assert!(!validate_learned_clause_quality(&[pos, neg]));
}

#[test]
fn test_quality_rejects_duplicate_negative() {
    // Same variable appears twice as negative.
    let l1 = ContractLiteral::negative(ContractVariable(7));
    let l2 = ContractLiteral::negative(ContractVariable(7));
    assert!(!validate_learned_clause_quality(&[l1, l2]));
}

#[test]
fn test_quality_valid_large_clause() {
    let clause: Vec<ContractLiteral> = (0..20)
        .map(|i| ContractLiteral::negative(ContractVariable(i)))
        .collect();
    assert!(validate_learned_clause_quality(&clause));
}

#[test]
fn test_quality_tautology_among_many() {
    // Tautology hidden among many literals.
    let mut clause: Vec<ContractLiteral> = (0..10)
        .map(|i| ContractLiteral::negative(ContractVariable(i)))
        .collect();
    clause.push(ContractLiteral::positive(ContractVariable(5))); // tautology with ~x5
    assert!(!validate_learned_clause_quality(&clause));
}

// -------------------------------------------------------------------
// Luby sequence tests
// -------------------------------------------------------------------

#[test]
fn test_luby_sequence_first_fifteen() {
    // Known Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8
    let expected = [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];
    for (i, &exp) in expected.iter().enumerate() {
        assert_eq!(
            luby(i + 1),
            exp,
            "luby({}) should be {}, got {}",
            i + 1,
            exp,
            luby(i + 1)
        );
    }
}

#[test]
fn test_luby_powers_of_two_minus_one() {
    // luby(1) = 1 = 2^0, luby(3) = 2 = 2^1, luby(7) = 4 = 2^2,
    // luby(15) = 8 = 2^3, luby(31) = 16 = 2^4
    assert_eq!(luby(1), 1);
    assert_eq!(luby(3), 2);
    assert_eq!(luby(7), 4);
    assert_eq!(luby(15), 8);
    assert_eq!(luby(31), 16);
}

// -------------------------------------------------------------------
// Restart decision tests
// -------------------------------------------------------------------

#[test]
fn test_restart_should_restart_when_threshold_reached() {
    let contract = ContractRestart::new(100);
    // luby(1) = 1, threshold = 100. 100 conflicts => should restart.
    let decision = contract.restart_after_conflicts(100, 1);
    assert!(decision.should_restart);
    assert!(validate_restart_decision(
        &decision,
        100,
        1,
        100,
        Some(0),
        5,
        5
    ));
}

#[test]
fn test_restart_should_not_restart_below_threshold() {
    let contract = ContractRestart::new(100);
    // luby(1) = 1, threshold = 100. 50 conflicts => should not restart.
    let decision = contract.restart_after_conflicts(50, 1);
    assert!(!decision.should_restart);
    assert!(validate_restart_decision(&decision, 50, 1, 100, None, 5, 5));
}

#[test]
fn test_restart_next_threshold_follows_luby() {
    let contract = ContractRestart::new(32);
    // luby(1) = 1, so threshold = 32. next = luby(2)*32 = 1*32 = 32.
    let d1 = contract.restart_after_conflicts(32, 1);
    assert_eq!(d1.next_threshold, 32);

    // luby(2) = 1, threshold = 32. next = luby(3)*32 = 2*32 = 64.
    let d2 = contract.restart_after_conflicts(32, 2);
    assert_eq!(d2.next_threshold, 64);

    // luby(3) = 2, threshold = 64. next = luby(4)*32 = 1*32 = 32.
    let d3 = contract.restart_after_conflicts(64, 3);
    assert_eq!(d3.next_threshold, 32);
}

#[test]
fn test_restart_decision_level_must_be_zero_after_restart() {
    let contract = ContractRestart::new(10);
    let decision = contract.restart_after_conflicts(10, 1);
    assert!(decision.should_restart);
    // Decision level 5 after restart => invalid.
    assert!(!validate_restart_decision(
        &decision,
        10,
        1,
        10,
        Some(5),
        0,
        0
    ));
    // Decision level 0 after restart => valid.
    assert!(validate_restart_decision(
        &decision,
        10,
        1,
        10,
        Some(0),
        0,
        0
    ));
}

#[test]
fn test_restart_learned_clauses_preserved() {
    let contract = ContractRestart::new(10);
    let decision = contract.restart_after_conflicts(10, 1);
    assert!(decision.should_restart);
    // learned_count decreased => invalid.
    assert!(!validate_restart_decision(
        &decision,
        10,
        1,
        10,
        Some(0),
        10,
        5
    ));
    // learned_count equal => valid.
    assert!(validate_restart_decision(
        &decision,
        10,
        1,
        10,
        Some(0),
        10,
        10
    ));
    // learned_count increased => also valid (new clause learned during conflict).
    assert!(validate_restart_decision(
        &decision,
        10,
        1,
        10,
        Some(0),
        10,
        11
    ));
}

#[test]
fn test_restart_high_luby_index() {
    let contract = ContractRestart::new(1);
    // luby(7) = 4, threshold = 4.
    let decision = contract.restart_after_conflicts(4, 7);
    assert!(decision.should_restart);
    // luby(8) = 1, next_threshold = 1.
    assert_eq!(decision.next_threshold, 1);
}

// -------------------------------------------------------------------
// Phase saving tests
// -------------------------------------------------------------------

#[test]
fn test_phase_save_and_retrieve() {
    let mut ps = ContractPhaseSaving::new(10);
    ps.save_phase(3, true);
    assert_eq!(ps.get_phase(3), Some(true));
    assert!(validate_phase_save(&ps, 3, true));
}

#[test]
fn test_phase_unsaved_returns_none() {
    let ps = ContractPhaseSaving::new(10);
    assert_eq!(ps.get_phase(5), None);
}

#[test]
fn test_phase_overwrite() {
    let mut ps = ContractPhaseSaving::new(10);
    ps.save_phase(2, true);
    assert_eq!(ps.get_phase(2), Some(true));
    ps.save_phase(2, false);
    assert_eq!(ps.get_phase(2), Some(false));
    assert!(validate_phase_save(&ps, 2, false));
}

#[test]
fn test_phase_clear_all() {
    let mut ps = ContractPhaseSaving::new(5);
    ps.save_phase(0, true);
    ps.save_phase(1, false);
    ps.save_phase(4, true);
    ps.clear_phases();
    assert!(validate_phases_cleared(&ps));
    assert_eq!(ps.get_phase(0), None);
    assert_eq!(ps.get_phase(1), None);
    assert_eq!(ps.get_phase(4), None);
}

#[test]
fn test_phase_out_of_bounds_returns_none() {
    let ps = ContractPhaseSaving::new(3);
    // var 5 is beyond the 3-variable capacity.
    assert_eq!(ps.get_phase(5), None);
}

#[test]
fn test_phase_boundary_variable() {
    let mut ps = ContractPhaseSaving::new(5);
    // Last valid variable = 4.
    ps.save_phase(4, false);
    assert_eq!(ps.get_phase(4), Some(false));
    assert!(validate_phase_save(&ps, 4, false));
}

#[test]
fn test_phase_num_vars() {
    let ps = ContractPhaseSaving::new(42);
    assert_eq!(ps.num_vars(), 42);
}

// -------------------------------------------------------------------
// Clause database tests
// -------------------------------------------------------------------

#[test]
fn test_clause_db_within_budget() {
    let mut db = ContractClauseDatabase::new(3);
    let l1 = ContractLiteral::positive(ContractVariable(0));
    let l2 = ContractLiteral::negative(ContractVariable(1));
    db.add_clause(vec![l1]);
    db.add_clause(vec![l2]);
    assert!(validate_clause_db_budget(&db));
}

#[test]
fn test_clause_db_over_budget() {
    let mut db = ContractClauseDatabase::new(1);
    let l1 = ContractLiteral::positive(ContractVariable(0));
    let l2 = ContractLiteral::negative(ContractVariable(1));
    db.add_clause(vec![l1]);
    db.add_clause(vec![l2]);
    assert!(!validate_clause_db_budget(&db));
}

#[test]
fn test_clause_db_uniform_decay() {
    let mut db = ContractClauseDatabase::new(100);
    let l1 = ContractLiteral::positive(ContractVariable(0));
    let l2 = ContractLiteral::negative(ContractVariable(1));
    let l3 = ContractLiteral::positive(ContractVariable(2));
    db.add_clause(vec![l1]);
    db.add_clause(vec![l2]);
    db.add_clause(vec![l3]);
    db.bump_activity(0, 10.0);
    db.bump_activity(1, 5.0);
    db.bump_activity(2, 20.0);
    let before = db.activities.clone();
    let factor = 0.95;
    db.decay_activities(factor);
    assert!(validate_uniform_decay(&before, &db.activities, factor));
}

#[test]
fn test_clause_db_non_uniform_decay_rejected() {
    let before = vec![10.0, 5.0, 20.0];
    // Manually create non-uniform after (only first decayed).
    let after = vec![9.5, 5.0, 20.0];
    assert!(!validate_uniform_decay(&before, &after, 0.95));
}

#[test]
fn test_clause_db_unit_reasons_preserved() {
    let mut reasons = HashSet::new();
    reasons.insert(1);
    reasons.insert(3);
    // Mapping: clause 0 deleted, 1 kept at 0, 2 deleted, 3 kept at 1.
    let mapping = vec![None, Some(0), None, Some(1)];
    assert!(validate_unit_reasons_preserved(&reasons, &mapping));
}

#[test]
fn test_clause_db_unit_reason_deleted_rejected() {
    let mut reasons = HashSet::new();
    reasons.insert(2);
    // Clause 2 was a unit reason but got deleted.
    let mapping = vec![Some(0), Some(1), None];
    assert!(!validate_unit_reasons_preserved(&reasons, &mapping));
}

#[test]
fn test_clause_db_no_duplicates() {
    let mut db = ContractClauseDatabase::new(100);
    let l1 = ContractLiteral::positive(ContractVariable(0));
    let l2 = ContractLiteral::negative(ContractVariable(1));
    let l3 = ContractLiteral::positive(ContractVariable(2));
    db.add_clause(vec![l1, l2]);
    db.add_clause(vec![l2, l3]);
    db.add_clause(vec![l1, l3]);
    assert!(validate_no_duplicate_clauses(&db));
}

#[test]
fn test_clause_db_duplicate_rejected() {
    let mut db = ContractClauseDatabase::new(100);
    let l1 = ContractLiteral::positive(ContractVariable(0));
    let l2 = ContractLiteral::negative(ContractVariable(1));
    db.add_clause(vec![l1, l2]);
    db.add_clause(vec![l1, l2]); // exact duplicate
    assert!(!validate_no_duplicate_clauses(&db));
}

#[test]
fn test_clause_db_duplicate_reorder_rejected() {
    let mut db = ContractClauseDatabase::new(100);
    let l1 = ContractLiteral::positive(ContractVariable(0));
    let l2 = ContractLiteral::negative(ContractVariable(1));
    db.add_clause(vec![l1, l2]);
    db.add_clause(vec![l2, l1]); // same clause, different order
    assert!(!validate_no_duplicate_clauses(&db));
}

// -------------------------------------------------------------------
// extern_spec registration tests
// -------------------------------------------------------------------

#[test]
fn test_register_restart_contract() {
    crate::extern_spec_verify::clear_extern_contracts();
    register_ay_restart_contract();
    let mut ctx = crate::vc::VerificationContext::new();
    crate::extern_spec_verify::apply_extern_specs_to_context(&mut ctx).unwrap();
    // 1 requires + 3 ensures = 4 obligations
    assert_eq!(ctx.obligations.len(), 4);
    let names: Vec<&str> = ctx.obligations.iter().map(|o| o.name.as_str()).collect();
    assert!(names.iter().any(|n| n.contains("restart")));
}

#[test]
fn test_register_phase_saving_contract() {
    crate::extern_spec_verify::clear_extern_contracts();
    register_ay_phase_saving_contract();
    let mut ctx = crate::vc::VerificationContext::new();
    crate::extern_spec_verify::apply_extern_specs_to_context(&mut ctx).unwrap();
    // 1 requires + 1 ensures = 2 obligations
    assert_eq!(ctx.obligations.len(), 2);
    let names: Vec<&str> = ctx.obligations.iter().map(|o| o.name.as_str()).collect();
    assert!(names.iter().any(|n| n.contains("save_phase")));
}

#[test]
fn test_register_clause_db_contract() {
    crate::extern_spec_verify::clear_extern_contracts();
    register_ay_clause_db_contract();
    let mut ctx = crate::vc::VerificationContext::new();
    crate::extern_spec_verify::apply_extern_specs_to_context(&mut ctx).unwrap();
    // 1 requires + 3 ensures = 4 obligations
    assert_eq!(ctx.obligations.len(), 4);
    let names: Vec<&str> = ctx.obligations.iter().map(|o| o.name.as_str()).collect();
    assert!(names.iter().any(|n| n.contains("ClauseDb")));
}
