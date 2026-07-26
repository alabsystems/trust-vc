// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_core::full_verification::{
    AssuranceLevel, EvidenceRejectionReason, FullVerificationRequest, MemorySafetyFactKind,
    ProofEvidenceSource, ReasoningKind, TypedMemorySafetyFact,
};
use trust_vc_core::ir::{CompareOp, DatatypeVariant, TrustVcExpr, TrustVcType};
use trust_vc_core::vc::{
    ConditionOrigin, ObligationKind, ProofObligation, TypedProofObligation, VariableDecl,
};
use trust_vc_core::VerifyResult;

fn i32_ty() -> TrustVcType {
    TrustVcType::Int { width: 32 }
}

fn owner_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "OwnerState".to_string(),
        variants: vec![DatatypeVariant::new(
            "OwnerState",
            vec![
                ("active_borrow".to_string(), i32_ty()),
                ("inactive_borrow".to_string(), i32_ty()),
            ],
        )],
    }
}

fn seq_i32_ty() -> TrustVcType {
    TrustVcType::Seq(Box::new(i32_ty()))
}

fn i32_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: i32_ty(),
    }
}

fn index_ne(left: &str, right: &str) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Ne,
        left: Box::new(i32_var(left)),
        right: Box::new(i32_var(right)),
    }
}

#[test]
fn full_verification_accepts_typed_disjoint_root_memory_fact() {
    let request = FullVerificationRequest::new()
        .with_variable(VariableDecl::new("left_owner", i32_ty()))
        .with_variable(VariableDecl::new("right_owner", i32_ty()))
        .with_evidence(
            TypedMemorySafetyFact::disjoint_roots(
                "owners_are_disjoint",
                "left_owner",
                i32_ty(),
                "right_owner",
                i32_ty(),
            )
            .with_location("src/lib.rs:10:5"),
        );

    let result = request.verify().expect("typed memory-safety fact verifies");
    assert!(matches!(result.report().result(), VerifyResult::Verified));

    let facts = result.verified_memory_safety_facts();
    assert_eq!(facts.len(), 1);
    assert_eq!(facts[0].name(), "owners_are_disjoint");
    assert_eq!(facts[0].kind(), MemorySafetyFactKind::DisjointRoots);
    assert_eq!(facts[0].location(), Some("src/lib.rs:10:5"));
    assert_eq!(
        facts[0].evidence_source(),
        ProofEvidenceSource::NativeTrustVcExpr
    );
    assert_eq!(facts[0].reasoning_kind(), ReasoningKind::Ownership);
    assert_eq!(facts[0].assurance_level(), AssuranceLevel::StaticProof);

    let evidence = result.verified_evidence();
    assert_eq!(evidence.len(), 1);
    assert_eq!(evidence[0].name(), "owners_are_disjoint");
    assert_eq!(evidence[0].obligation_kind(), ObligationKind::Assert);
    assert_eq!(evidence[0].location(), Some("src/lib.rs:10:5"));
    assert_eq!(
        evidence[0].evidence_source(),
        ProofEvidenceSource::NativeTrustVcExpr
    );
    assert_eq!(evidence[0].reasoning_kind(), ReasoningKind::Ownership);
    assert_eq!(evidence[0].assurance_level(), AssuranceLevel::StaticProof);
    assert_eq!(
        evidence[0].condition_origin(),
        ConditionOrigin::TypedTrustVcExpr
    );
}

#[test]
fn full_verification_accepts_typed_disjoint_field_memory_fact() {
    let request = FullVerificationRequest::new()
        .with_variable(VariableDecl::new("owner", owner_ty()))
        .with_evidence(
            TypedMemorySafetyFact::disjoint_fields(
                "owner_fields_are_disjoint",
                "owner",
                owner_ty(),
                "active_borrow",
                i32_ty(),
                "inactive_borrow",
                i32_ty(),
            )
            .with_location("src/owner.rs:44:9"),
        );

    let result = request
        .verify()
        .expect("typed disjoint-field memory fact verifies");
    assert!(matches!(result.report().result(), VerifyResult::Verified));

    let facts = result.verified_memory_safety_facts();
    assert_eq!(facts.len(), 1);
    assert_eq!(facts[0].name(), "owner_fields_are_disjoint");
    assert_eq!(facts[0].kind(), MemorySafetyFactKind::DisjointFields);
    assert_eq!(facts[0].location(), Some("src/owner.rs:44:9"));
    assert_eq!(
        facts[0].evidence_source(),
        ProofEvidenceSource::NativeTrustVcExpr
    );
}

#[test]
fn full_verification_accepts_typed_disjoint_indexed_memory_fact_with_typed_inequality() {
    let request = FullVerificationRequest::new()
        .with_variable(VariableDecl::new("buffer", seq_i32_ty()))
        .with_variable(VariableDecl::new("read_idx", i32_ty()))
        .with_variable(VariableDecl::new("write_idx", i32_ty()))
        .with_evidence(TypedProofObligation::assume(
            "read_write_indices_differ",
            index_ne("read_idx", "write_idx"),
        ))
        .with_evidence(
            TypedMemorySafetyFact::disjoint_indexed_places(
                "read_write_slots_are_disjoint",
                "buffer",
                seq_i32_ty(),
                i32_var("read_idx"),
                i32_var("write_idx"),
                i32_ty(),
            )
            .with_location("src/ring.rs:18:13"),
        );

    let result = request
        .verify()
        .expect("typed indexed-place memory fact verifies with typed inequality evidence");
    assert!(matches!(result.report().result(), VerifyResult::Verified));

    let facts = result.verified_memory_safety_facts();
    assert_eq!(facts.len(), 1);
    assert_eq!(facts[0].name(), "read_write_slots_are_disjoint");
    assert_eq!(facts[0].kind(), MemorySafetyFactKind::DisjointIndexedPlaces);
    assert_eq!(facts[0].location(), Some("src/ring.rs:18:13"));
    assert_eq!(
        facts[0].evidence_source(),
        ProofEvidenceSource::NativeTrustVcExpr
    );

    let evidence = result.verified_evidence();
    assert_eq!(evidence.len(), 2);
    assert_eq!(evidence[0].name(), "read_write_indices_differ");
    assert_eq!(evidence[0].obligation_kind(), ObligationKind::Assume);
    assert_eq!(evidence[0].reasoning_kind(), ReasoningKind::Deductive);
    assert_eq!(
        evidence[0].assurance_level(),
        AssuranceLevel::AssumedEvidence
    );
    assert_eq!(evidence[1].name(), "read_write_slots_are_disjoint");
    assert_eq!(evidence[1].obligation_kind(), ObligationKind::Assert);
    assert_eq!(evidence[1].reasoning_kind(), ReasoningKind::Ownership);
    assert_eq!(evidence[1].assurance_level(), AssuranceLevel::StaticProof);
}

#[test]
fn full_verification_rejects_typed_disjoint_indexed_memory_fact_without_inequality() {
    let request = FullVerificationRequest::new()
        .with_variable(VariableDecl::new("buffer", seq_i32_ty()))
        .with_variable(VariableDecl::new("read_idx", i32_ty()))
        .with_variable(VariableDecl::new("write_idx", i32_ty()))
        .with_evidence(TypedMemorySafetyFact::disjoint_indexed_places(
            "read_write_slots_are_disjoint",
            "buffer",
            seq_i32_ty(),
            i32_var("read_idx"),
            i32_var("write_idx"),
            i32_ty(),
        ));

    let err = request
        .verify()
        .expect_err("indexed disjointness needs typed index inequality evidence");
    assert!(err.rejected().is_empty());
}

#[test]
fn full_verification_rejects_non_disjoint_field_memory_fact() {
    let request = FullVerificationRequest::new()
        .with_variable(VariableDecl::new("owner", owner_ty()))
        .with_evidence(TypedMemorySafetyFact::disjoint_fields(
            "same_field_is_not_disjoint",
            "owner",
            owner_ty(),
            "active_borrow",
            i32_ty(),
            "active_borrow",
            i32_ty(),
        ));

    let err = request
        .verify()
        .expect_err("same field cannot prove disjointness");
    assert!(err.rejected().is_empty());
}

#[test]
fn full_verification_rejects_context_free_string_backed_trust_obligation() {
    let request = FullVerificationRequest::new().with_evidence(ProofObligation::assert(
        "trust_tRust_ownership_claim",
        "tRust says these owners are disjoint",
    ));

    let err = request
        .verify()
        .expect_err("string-backed tRust evidence must be rejected");
    let rejected = err.rejected();
    assert_eq!(rejected.len(), 1);
    assert_eq!(
        rejected[0].reason(),
        EvidenceRejectionReason::ContextFreeStringBackedObligation
    );
    assert_eq!(rejected[0].obligation_name(), "trust_tRust_ownership_claim");
    assert_eq!(
        rejected[0].condition_origin(),
        ConditionOrigin::LoweredFromCondition
    );
}

#[test]
fn full_verification_rejects_string_backed_obligation_even_with_context() {
    let request = FullVerificationRequest::new()
        .with_variable(VariableDecl::new("left_owner", i32_ty()))
        .with_variable(VariableDecl::new("right_owner", i32_ty()))
        .with_evidence(ProofObligation::assert(
            "string_disjoint_claim",
            "left_owner != right_owner",
        ));

    let err = request
        .verify()
        .expect_err("string-backed evidence with context must still be rejected");
    let rejected = err.rejected();
    assert_eq!(rejected.len(), 1);
    assert_eq!(
        rejected[0].reason(),
        EvidenceRejectionReason::StringBackedObligation
    );
    assert_eq!(rejected[0].obligation_name(), "string_disjoint_claim");
}

#[test]
fn full_verification_rejects_string_evidence_even_with_typed_memory_fact() {
    let request = FullVerificationRequest::new()
        .with_variable(VariableDecl::new("owner", owner_ty()))
        .with_evidence(TypedMemorySafetyFact::disjoint_fields(
            "owner_fields_are_disjoint",
            "owner",
            owner_ty(),
            "active_borrow",
            i32_ty(),
            "inactive_borrow",
            i32_ty(),
        ))
        .with_evidence(ProofObligation::assert(
            "string_borrow_claim",
            "active_borrow is exclusive",
        ));

    let err = request
        .verify()
        .expect_err("mixed typed evidence must not admit string-backed facts");
    let rejected = err.rejected();
    assert_eq!(rejected.len(), 1);
    assert_eq!(
        rejected[0].reason(),
        EvidenceRejectionReason::StringBackedObligation
    );
    assert_eq!(rejected[0].obligation_name(), "string_borrow_claim");
}

#[test]
fn full_verification_reports_deductive_summary_for_typed_trust_contract_obligation() {
    let request = FullVerificationRequest::new()
        .with_variable(VariableDecl::new("owner", i32_ty()))
        .with_evidence(
            TypedProofObligation::assert(
                "trust_contract_owner_reflexive",
                TrustVcExpr::Compare {
                    op: CompareOp::Eq,
                    left: Box::new(i32_var("owner")),
                    right: Box::new(i32_var("owner")),
                },
            )
            .with_location("src/trust_contract.rs:7:9"),
        );

    let result = request
        .verify()
        .expect("typed tRust-style contract obligation verifies");
    let evidence = result.verified_evidence();
    assert_eq!(evidence.len(), 1);
    assert_eq!(evidence[0].name(), "trust_contract_owner_reflexive");
    assert_eq!(evidence[0].obligation_kind(), ObligationKind::Assert);
    assert_eq!(evidence[0].location(), Some("src/trust_contract.rs:7:9"));
    assert_eq!(
        evidence[0].evidence_source(),
        ProofEvidenceSource::NativeTrustVcExpr
    );
    assert_eq!(evidence[0].reasoning_kind(), ReasoningKind::Deductive);
    assert_eq!(evidence[0].assurance_level(), AssuranceLevel::StaticProof);
    assert_eq!(
        evidence[0].condition_origin(),
        ConditionOrigin::TypedTrustVcExpr
    );
    assert!(result.verified_memory_safety_facts().is_empty());
}

#[test]
fn full_verification_marks_raw_typed_obligation_as_compatibility_boundary() {
    let raw_typed = ProofObligation::new_typed(
        "compatibility_typed_claim",
        TrustVcExpr::BoolLit(true),
        ObligationKind::Assert,
    )
    .with_location("src/compat.rs:4:1");

    let result = FullVerificationRequest::new()
        .with_evidence(raw_typed)
        .verify()
        .expect("raw compatibility obligation with typed payload verifies");

    let evidence = result.verified_evidence();
    assert_eq!(evidence.len(), 1);
    assert_eq!(evidence[0].name(), "compatibility_typed_claim");
    assert_eq!(
        evidence[0].evidence_source(),
        ProofEvidenceSource::TypedCompatibilityBoundary
    );
    assert_eq!(evidence[0].reasoning_kind(), ReasoningKind::Deductive);
    assert_eq!(evidence[0].assurance_level(), AssuranceLevel::StaticProof);
    assert_eq!(
        evidence[0].condition_origin(),
        ConditionOrigin::TypedTrustVcExpr
    );
}

#[test]
fn full_verification_rejects_spoofed_typed_origin_without_trust_vc_expr_payload() {
    let spoofed = ProofObligation::assert("spoofed_typed_origin", "true")
        .with_condition_origin(ConditionOrigin::PreBuiltExprCache);

    let err = FullVerificationRequest::new()
        .with_evidence(spoofed)
        .verify()
        .expect_err("condition origin alone must not count as typed proof evidence");
    let rejected = err.rejected();
    assert_eq!(rejected.len(), 1);
    assert_eq!(
        rejected[0].reason(),
        EvidenceRejectionReason::ContextFreeStringBackedObligation
    );
    assert_eq!(rejected[0].obligation_name(), "spoofed_typed_origin");
    assert_eq!(
        rejected[0].condition_origin(),
        ConditionOrigin::PreBuiltExprCache
    );
}
