// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_trust_engine::{
    TrustAliasFact, TrustAliasKind, TrustArithOp, TrustAssuranceLevel, TrustBorrow,
    TrustBorrowKind, TrustCompareOp, TrustContractFrame, TrustExpr, TrustFunctionSignature,
    TrustLifetimeRegion, TrustLogicOp, TrustNativeContext, TrustObligationKind, TrustOldValue,
    TrustOutcome, TrustOwnedPlace, TrustOwnershipState, TrustPointerProvenance,
    TrustPointerProvenanceOrigin, TrustProofEvidenceProfile, TrustProofLineage,
    TrustProofLineageSource, TrustProofPolicy, TrustSort, TrustSourceSpan,
    TrustTrustIrAdapterRequest, TrustTrustIrObligation, TrustTrustIrObligationKind,
    TrustTrustIrProofUnit, TrustUnsupportedTrustIrConstruct, TrustVariable, TrustVcTrustEngine,
    TRUST_TRUST_IR_ADAPTER_SCHEMA_VERSION,
};

const TRUST_X86_LOAD_TRUST_IR_ADAPTER_GOLDEN: &str =
    include_str!("../fixtures/trust_ir_adapter/trust_x86_load_trust_ir_adapter_golden.json");
const TRUST_UNRESOLVED_BRANCH_UNSUPPORTED_TRUST_IR_ADAPTER_GOLDEN: &str = include_str!(
    "../fixtures/trust_ir_adapter/trust_unresolved_indirect_branch_unsupported_trust_ir_adapter_golden.json"
);
const TRUST_INCREMENT_CONTRACT_CFG_TRUST_IR_ADAPTER_GOLDEN: &str = include_str!(
    "../fixtures/trust_ir_adapter/trust_increment_contract_cfg_trust_ir_adapter_golden.json"
);

fn increment_context() -> TrustNativeContext {
    let u32_sort = TrustSort::unsigned(32);
    TrustNativeContext::new(TrustFunctionSignature::new(
        "crate::increment",
        vec![TrustVariable::new("x", u32_sort.clone())],
        u32_sort.clone(),
    ))
    .with_contract_frame(
        TrustContractFrame::new()
            .with_return_value(TrustVariable::new("result", u32_sort.clone()))
            .with_old_value(TrustOldValue::new(
                "x",
                TrustVariable::new("old_x", u32_sort),
            )),
    )
}

fn result_and_old_tautology() -> TrustExpr {
    let u32_sort = TrustSort::unsigned(32);
    TrustExpr::logic(
        TrustLogicOp::And,
        TrustExpr::compare(
            TrustCompareOp::Eq,
            TrustExpr::variable("result", u32_sort.clone()),
            TrustExpr::variable("result", u32_sort.clone()),
        ),
        TrustExpr::compare(
            TrustCompareOp::Eq,
            TrustExpr::old("x", "old_x", u32_sort.clone()),
            TrustExpr::arith(
                TrustArithOp::Add,
                TrustExpr::old("x", "old_x", u32_sort.clone()),
                TrustExpr::int_literal(0, u32_sort.clone()),
                u32_sort,
            ),
        ),
    )
}

fn ownership_context() -> TrustNativeContext {
    TrustNativeContext::new(TrustFunctionSignature::new(
        "crate::take_shared",
        vec![TrustVariable::new("ptr_live", TrustSort::Bool)],
        TrustSort::Bool,
    ))
    .with_ownership(
        TrustOwnershipState::new()
            .with_place(TrustOwnedPlace::new("x", TrustSort::unsigned(32)))
            .with_borrow(TrustBorrow::new("r0", "x", TrustBorrowKind::Shared))
            .with_lifetime(TrustLifetimeRegion::new("r0").with_outlives("static"))
            .with_alias_fact(TrustAliasFact::new("p", "q", TrustAliasKind::NoAlias))
            .with_provenance_fact(TrustPointerProvenance::new(
                "p",
                "prov:p",
                TrustPointerProvenanceOrigin::FunctionArgument,
            )),
    )
}

fn ptr_live_tautology() -> TrustExpr {
    let ptr_live = TrustExpr::variable("ptr_live", TrustSort::Bool);
    TrustExpr::compare(TrustCompareOp::Eq, ptr_live.clone(), ptr_live)
}

#[test]
fn trust_ir_adapter_consumes_real_trust_x86_load_golden_fixture() {
    let engine = TrustVcTrustEngine::new();
    let request: TrustTrustIrAdapterRequest =
        serde_json::from_str(TRUST_X86_LOAD_TRUST_IR_ADAPTER_GOLDEN)
            .expect("checked-in tRust/TrustIr adapter fixture should decode");

    assert_eq!(
        request.source_id(),
        "tRust::trust-integration-tests::binary_decompile_convert_llvm2_production_positive_golden"
    );
    assert_eq!(
        request
            .metadata()
            .get("trust.fixture.symbol")
            .map(String::as_str),
        Some("trust_fixture_x86_load")
    );

    engine
        .validate_trust_ir_adapter_request(&request)
        .expect("real tRust/TrustIr adapter fixture should validate");
    let report = engine
        .verify_trust_ir_adapter_request(&request)
        .expect("real tRust/TrustIr adapter fixture should verify");

    let unit = &report.units()[0];
    assert_eq!(unit.unit_id(), "trust_fixture_x86_load");
    assert!(matches!(unit.outcome(), TrustOutcome::Verified));
    assert_eq!(unit.proof_evidence().len(), 3);

    let ownership = &unit.proof_evidence()[0];
    assert_eq!(ownership.obligation_id(), "trust_ir.memory.no_alias.arg0");
    assert_eq!(
        ownership.evidence_profile(),
        TrustProofEvidenceProfile::OwnershipMemory
    );
    assert_eq!(
        ownership
            .proof_lineage()
            .expect("ownership fixture should preserve lineage")
            .source(),
        &TrustProofLineageSource::TrustIrOwnership
    );
    assert_eq!(ownership.location(), Some("binary:0x400000:1:1-1:3"));
    let cache_key = ownership
        .cache_key()
        .expect("real tRust/TrustIr fixture should produce a cache key");
    assert_eq!(
        cache_key.trust_ir_body_hash(),
        Some("sha256:dbd30d3b634f45a82b2453ef67a7ba279f32be9fddefcb0afb8e6d94dff144b5")
    );
    assert_eq!(
        cache_key.layout_hash(),
        Some("sha256:251757e36749c41d81a42feb4764e9ed80c354990f9de66858a498e549524000")
    );
    assert!(cache_key.ownership_digest().is_some());

    let translation = &unit.proof_evidence()[2];
    assert_eq!(translation.obligation_id(), "trust_ir.translation.return");
    assert_eq!(
        translation.evidence_profile(),
        TrustProofEvidenceProfile::TypedTranslationValidation
    );
}

#[test]
fn trust_ir_adapter_fixture_fails_closed_for_real_unresolved_branch_golden() {
    let engine = TrustVcTrustEngine::new();
    let request: TrustTrustIrAdapterRequest =
        serde_json::from_str(TRUST_UNRESOLVED_BRANCH_UNSUPPORTED_TRUST_IR_ADAPTER_GOLDEN)
            .expect("checked-in unsupported tRust/TrustIr fixture should decode");

    let err = engine
        .lower_trust_ir_adapter_request(&request)
        .expect_err("unsupported tRust/TrustIr fixture must fail closed");

    assert_eq!(
        err,
        trust_vc_trust_engine::TrustEngineError::UnsupportedTrustIrConstruct {
            unit_id: "trust_fixture_unresolved".to_string(),
            obligation_id: "trust_ir.cfg.indirect_branch".to_string(),
            feature: "CFG proof mode".to_string(),
            diagnostic: "tRust binary_unresolved_indirect_branch_golden reports an unresolved indirect branch; TrustVc must fail closed until tRust emits typed CFG proof evidence".to_string(),
        }
    );
}

#[test]
fn trust_ir_adapter_consumes_trust_native_contract_cfg_golden() {
    let engine = TrustVcTrustEngine::new();
    let request: TrustTrustIrAdapterRequest =
        serde_json::from_str(TRUST_INCREMENT_CONTRACT_CFG_TRUST_IR_ADAPTER_GOLDEN)
            .expect("checked-in tRust native adapter fixture should decode");

    assert_eq!(
        request.source_id(),
        "tRust::compiler::trust_vc_trust_ir_adapter::increment_old_result_cfg"
    );
    assert_eq!(
        request
            .metadata()
            .get("trust.issue.refs")
            .map(String::as_str),
        Some("#2789,#2790")
    );
    assert_eq!(
        request.metadata().get("trust.producer").map(String::as_str),
        Some("tRust")
    );

    engine
        .validate_trust_ir_adapter_request(&request)
        .expect("native tRust adapter fixture should validate");
    let report = engine
        .verify_trust_ir_adapter_request(&request)
        .expect("native tRust adapter fixture should verify");

    let unit = &report.units()[0];
    assert_eq!(unit.unit_id(), "trust_vc_fixture::increment_checked");
    assert!(matches!(unit.outcome(), TrustOutcome::Verified));
    assert_eq!(unit.proof_evidence().len(), 3);

    let requires = &unit.proof_evidence()[0];
    assert_eq!(requires.obligation_id(), "requires.x_nonnegative");
    assert_eq!(
        requires.evidence_profile(),
        TrustProofEvidenceProfile::TypedContractFrame
    );
    assert_eq!(
        requires
            .proof_lineage()
            .expect("requires evidence should preserve tRust lineage")
            .source(),
        &TrustProofLineageSource::TrustTypesContract
    );
    assert_eq!(
        requires.location(),
        Some("crates/trust-trust-vc-lib/fixtures/trust_vc_increment.rs:3:5-3:21")
    );

    let ensures = &unit.proof_evidence()[1];
    assert_eq!(ensures.obligation_id(), "ensures.old_result_reflexive");
    assert_eq!(
        ensures.evidence_profile(),
        TrustProofEvidenceProfile::TypedContractFrame
    );
    assert_eq!(
        ensures
            .proof_lineage()
            .expect("ensures evidence should preserve tRust lineage")
            .rule(),
        "ensures-clause"
    );
    assert!(ensures
        .cache_key()
        .expect("native contract evidence should carry a cache key")
        .proof_lineage_digest()
        .is_some());

    let cfg = &unit.proof_evidence()[2];
    assert_eq!(cfg.obligation_id(), "trust_ir.cfg.entry_to_return");
    assert_eq!(
        cfg.evidence_profile(),
        TrustProofEvidenceProfile::TypedTranslationValidation
    );
    assert_eq!(
        cfg.proof_lineage()
            .expect("CFG evidence should preserve TrustIr lineage")
            .source(),
        &TrustProofLineageSource::TrustIrLowering
    );
    assert_eq!(
        cfg.location(),
        Some("trust_ir:trust_vc_fixture::increment_checked:1:1-1:8")
    );
}

#[test]
fn trust_ir_adapter_lowers_trust_types_contracts_with_lineage_and_spans() {
    let engine = TrustVcTrustEngine::new();
    let request = TrustTrustIrAdapterRequest::new("crate-under-test").with_unit(
        TrustTrustIrProofUnit::new("crate::increment", increment_context())
            .with_obligation(
                TrustTrustIrObligation::expr(
                    "requires.x_reflexive",
                    TrustTrustIrObligationKind::Requires,
                    TrustExpr::compare(
                        TrustCompareOp::Eq,
                        TrustExpr::variable("x", TrustSort::unsigned(32)),
                        TrustExpr::variable("x", TrustSort::unsigned(32)),
                    ),
                    TrustProofLineage::trust_types_contract(
                        "trust-types-json-v1",
                        "requires-clause",
                    )
                    .with_input_digest("sha256:requires"),
                )
                .with_span(TrustSourceSpan::new("src/lib.rs", 4, 5, 4, 22)),
            )
            .with_obligation(
                TrustTrustIrObligation::expr(
                    "ensures.result_old",
                    TrustTrustIrObligationKind::Ensures,
                    result_and_old_tautology(),
                    TrustProofLineage::trust_types_contract(
                        "trust-types-json-v1",
                        "ensures-clause",
                    )
                    .with_input_digest("sha256:ensures"),
                )
                .with_span(TrustSourceSpan::new("src/lib.rs", 5, 5, 5, 36)),
            ),
    );

    assert_eq!(
        request.schema_version(),
        TRUST_TRUST_IR_ADAPTER_SCHEMA_VERSION
    );
    engine
        .validate_trust_ir_adapter_request(&request)
        .expect("typed TrustIr request should pass validation");
    let lowered = engine
        .lower_trust_ir_adapter_request(&request)
        .expect("typed TrustIr request should lower");

    assert_eq!(lowered.source_id(), "crate-under-test");
    assert_eq!(lowered.units()[0].obligations().len(), 2);
    assert_eq!(
        lowered.units()[0].obligations()[1].kind(),
        &TrustObligationKind::Postcondition
    );
    assert_eq!(
        lowered.units()[0].obligations()[1].location(),
        Some("src/lib.rs:5:5-5:36")
    );
    assert_eq!(
        lowered.units()[0].obligations()[1]
            .proof_lineage()
            .expect("lineage should be preserved")
            .source(),
        &TrustProofLineageSource::TrustTypesContract
    );

    let report = engine
        .verify_trust_ir_adapter_request(&request)
        .expect("typed contract request should verify");
    assert!(matches!(
        report.units()[0].outcome(),
        TrustOutcome::Verified
    ));
    let evidence = report.units()[0].proof_evidence();
    assert_eq!(
        evidence[1].evidence_profile(),
        TrustProofEvidenceProfile::TypedContractFrame
    );
    assert_eq!(
        evidence[1]
            .proof_lineage()
            .expect("report evidence should preserve proof lineage")
            .rule(),
        "ensures-clause"
    );
    assert!(evidence[1]
        .cache_key()
        .expect("verified evidence should carry cache key")
        .proof_lineage_digest()
        .is_some());
}

#[test]
fn trust_ir_adapter_preserves_recommends_as_soft_contract_obligation() {
    let engine = TrustVcTrustEngine::new();
    let request = TrustTrustIrAdapterRequest::new("crate-under-test").with_unit(
        TrustTrustIrProofUnit::new("crate::increment", increment_context()).with_obligation(
            TrustTrustIrObligation::expr(
                "recommends.false_soft",
                TrustTrustIrObligationKind::Recommends,
                TrustExpr::bool_literal(false),
                TrustProofLineage::trust_types_contract("trust-types-json-v1", "recommends-clause")
                    .with_input_digest("sha256:recommends"),
            )
            .with_span(TrustSourceSpan::new("src/lib.rs", 4, 5, 4, 42)),
        ),
    );

    engine
        .validate_trust_ir_adapter_request(&request)
        .expect("typed recommends TrustIr request should pass validation");
    let lowered = engine
        .lower_trust_ir_adapter_request(&request)
        .expect("typed recommends TrustIr request should lower");

    assert_eq!(
        lowered.units()[0].obligations()[0].kind(),
        &TrustObligationKind::Recommends
    );

    let report = engine
        .verify_trust_ir_adapter_request(&request)
        .expect("false recommends should verify as a warning-only obligation");
    assert!(matches!(
        report.units()[0].outcome(),
        TrustOutcome::Verified
    ));
    let evidence = &report.units()[0].proof_evidence()[0];
    assert_eq!(
        evidence.evidence_profile(),
        TrustProofEvidenceProfile::TypedContractFrame
    );
    assert_eq!(
        evidence.assurance_level(),
        TrustAssuranceLevel::MetadataOnly
    );
    let lineage = evidence
        .proof_lineage()
        .expect("report evidence should preserve recommends proof lineage");
    assert_eq!(lineage.rule(), "recommends-clause");
    assert_eq!(lineage.input_digest(), Some("sha256:recommends"));
}

#[test]
fn trust_ir_adapter_preserves_compiler_assertion_source_ids_in_artifact_coverage() {
    let engine = TrustVcTrustEngine::new();
    let request = TrustTrustIrAdapterRequest::new("crate-under-test")
        .with_proof_policy(TrustProofPolicy::AttachReplayableCertificates)
        .with_unit(
            TrustTrustIrProofUnit::new("crate::increment", increment_context()).with_obligation(
                TrustTrustIrObligation::expr(
                    "ensures.result_old",
                    TrustTrustIrObligationKind::Ensures,
                    result_and_old_tautology(),
                    TrustProofLineage::trust_types_contract(
                        "trust-types-json-v1",
                        "ensures-clause",
                    ),
                )
                .with_span(TrustSourceSpan::new("src/lib.rs", 5, 5, 5, 36))
                .with_trust_ir_assertion_id(42)
                .with_trust_ir_source_id("hir:crate::increment:ensures:0"),
            ),
        );

    let lowered = engine
        .lower_trust_ir_adapter_request(&request)
        .expect("typed TrustIr request should lower");
    let lowered_obligation = &lowered.units()[0].obligations()[0];
    assert_eq!(lowered_obligation.trust_ir_assertion_id(), Some(42));
    assert_eq!(
        lowered_obligation.trust_ir_source_id(),
        Some("hir:crate::increment:ensures:0")
    );

    let report = engine
        .verify_trust_ir_adapter_request(&request)
        .expect("typed TrustIr request should verify");
    let evidence = &report.units()[0].proof_evidence()[0];
    assert_eq!(evidence.trust_ir_assertion_id(), Some(42));
    assert_eq!(
        evidence.trust_ir_source_id(),
        Some("hir:crate::increment:ensures:0")
    );

    let coverage = report.units()[0]
        .proof_artifact_coverage()
        .expect("artifact capture request should report coverage");
    assert_eq!(coverage.assertion_obligation_ids(), &["ensures.result_old"]);
    assert_eq!(coverage.trust_ir_assertion_ids(), &[42]);
    assert_eq!(
        coverage.covered_trust_ir_assertion_ids().is_empty(),
        coverage.covered_assertion_obligation_ids().is_empty()
    );
    assert_eq!(
        coverage.missing_trust_ir_assertion_ids().is_empty(),
        coverage.missing_assertion_obligation_ids().is_empty()
    );
    let assertion = &coverage.assertions()[0];
    assert_eq!(assertion.obligation_id(), "ensures.result_old");
    assert_eq!(assertion.trust_ir_assertion_id(), Some(42));
    assert_eq!(
        assertion.trust_ir_source_id(),
        Some("hir:crate::increment:ensures:0")
    );
    assert_eq!(
        assertion.covered(),
        !coverage
            .missing_assertion_obligation_ids()
            .contains(&"ensures.result_old".to_string())
    );
}

#[test]
fn trust_ir_adapter_lowers_memory_alias_and_provenance_facts() {
    let engine = TrustVcTrustEngine::new();
    let request = TrustTrustIrAdapterRequest::new("crate-under-test").with_unit(
        TrustTrustIrProofUnit::new("crate::take_shared", ownership_context()).with_obligation(
            TrustTrustIrObligation::expr(
                "trust_ir.memory.no_alias",
                TrustTrustIrObligationKind::MemoryNoAlias,
                ptr_live_tautology(),
                TrustProofLineage::trust_ir_ownership("trust_ir-borrowck", "no-alias-from-borrows"),
            ),
        ),
    );

    let report = engine
        .verify_trust_ir_adapter_request(&request)
        .expect("typed ownership request should verify");

    assert!(matches!(
        report.units()[0].outcome(),
        TrustOutcome::Verified
    ));
    let evidence = &report.units()[0].proof_evidence()[0];
    assert_eq!(
        evidence.evidence_profile(),
        TrustProofEvidenceProfile::OwnershipMemory
    );
    assert_eq!(
        evidence
            .proof_lineage()
            .expect("ownership evidence should preserve lineage")
            .source(),
        &TrustProofLineageSource::TrustIrOwnership
    );
    assert!(evidence
        .cache_key()
        .expect("ownership evidence should carry cache key")
        .ownership_digest()
        .is_some());
}

#[test]
fn trust_ir_adapter_rejects_unsupported_constructs_before_lowering() {
    let engine = TrustVcTrustEngine::new();
    let request = TrustTrustIrAdapterRequest::new("crate-under-test").with_unit(
        TrustTrustIrProofUnit::new("crate::higher_ranked", increment_context()).with_obligation(
            TrustTrustIrObligation::unsupported(
                "ensures.unsupported",
                TrustTrustIrObligationKind::Ensures,
                TrustUnsupportedTrustIrConstruct::new(
                    "higher_ranked_closure_contract",
                    "higher-ranked closure contracts are not mapped into TrustExpr yet",
                ),
                TrustProofLineage::trust_types_contract("trust-types-json-v1", "ensures-clause"),
            ),
        ),
    );

    let err = engine
        .lower_trust_ir_adapter_request(&request)
        .expect_err("unsupported compiler constructs must fail closed");

    assert_eq!(
        err,
        trust_vc_trust_engine::TrustEngineError::UnsupportedTrustIrConstruct {
            unit_id: "crate::higher_ranked".to_string(),
            obligation_id: "ensures.unsupported".to_string(),
            feature: "higher_ranked_closure_contract".to_string(),
            diagnostic: "higher-ranked closure contracts are not mapped into TrustExpr yet"
                .to_string(),
        }
    );
}

#[test]
fn trust_ir_adapter_validation_rejects_unknown_schema_version() {
    let engine = TrustVcTrustEngine::new();
    let request: TrustTrustIrAdapterRequest = serde_json::from_str(
        r#"{
          "schema_version": 99,
          "source_id": "crate-under-test",
          "units": []
        }"#,
    )
    .expect("schema-version probe should decode");

    let err = engine
        .validate_trust_ir_adapter_request(&request)
        .expect_err("unknown adapter schema version must fail closed");

    assert_eq!(
        err,
        trust_vc_trust_engine::TrustEngineError::UnsupportedTrustIrAdapterSchemaVersion {
            actual: 99,
            expected: TRUST_TRUST_IR_ADAPTER_SCHEMA_VERSION,
        }
    );
}

#[test]
fn trust_ir_adapter_validation_rejects_unstructured_lineage() {
    let engine = TrustVcTrustEngine::new();
    let request = TrustTrustIrAdapterRequest::new("crate-under-test").with_unit(
        TrustTrustIrProofUnit::new("crate::increment", increment_context()).with_obligation(
            TrustTrustIrObligation::expr(
                "ensures.result_old",
                TrustTrustIrObligationKind::Ensures,
                result_and_old_tautology(),
                TrustProofLineage::new(
                    TrustProofLineageSource::Other("manual".to_string()),
                    "manual-adapter",
                    "manual",
                    "manual-rule",
                ),
            ),
        ),
    );

    let err = engine
        .validate_trust_ir_adapter_request(&request)
        .expect_err("TrustIr adapter must reject unstructured lineage sources");

    assert_eq!(
        err,
        trust_vc_trust_engine::TrustEngineError::InvalidProofLineage {
            unit_id: "crate::increment".to_string(),
            obligation_id: "ensures.result_old".to_string(),
            message: "TrustIr adapter obligations must use a TrustIr or trust-types lineage source"
                .to_string(),
        }
    );
}
