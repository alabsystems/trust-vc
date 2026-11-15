// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Source-carrier admission at public body, direct-request and bundle entries.
//! Synthetic directives below are transport controls, never proof evidence.

#[path = "support/admission_baseline.rs"]
mod admission_baseline;
#[path = "support/admission_edits.rs"]
mod admission_edits;
#[path = "support/trust_ir_body_fixtures.rs"]
mod fixtures;

use trust_ir::request::{
    NativeBundleProducer, NativeRequestId, NativeVerificationBundle, TrustVcNativeRequest,
    TrustVcVerificationMode,
};
use trust_ir::{
    CertificateBinding, CleanCicKernelRecheck, FuncId, Inst, InstrNode, ModuleCompleteness,
    ProofCertificate, ProofDigest, ProofEvidence, ProofId, UnloweredRow, ValueId,
};
use trust_vc_trust_engine::{
    trust_ir_body_semantic_digest, TrustEngineError, TrustIrBodyError, TrustIrBodyOptions,
    TrustVcTrustEngine,
};

fn request(fixture: &fixtures::Fixture) -> TrustVcNativeRequest {
    TrustVcNativeRequest {
        id: NativeRequestId::new(0),
        mode: TrustVcVerificationMode::DischargeProofObligations,
        obligations: fixture.obligations.clone(),
        certificates: Vec::new(),
        lineage_roots: Vec::new(),
        options: Default::default(),
        diagnostics: Default::default(),
        provenance: Default::default(),
        function: Some(fixture.function()),
    }
}

fn transport_certificate(obligation: ProofId) -> ProofCertificate {
    ProofCertificate {
        obligation,
        prover: "synthetic transport control; not certified".to_string(),
        evidence: ProofEvidence::CleanCic {
            term: Vec::new(),
            context: Vec::new(),
            lineage: ProofDigest::sha256([0x31; 32]),
            kernel_recheck: Some(CleanCicKernelRecheck {
                module: "TransportControl".to_string(),
                theorems: Vec::new(),
                anchor: "not-proof-authority".to_string(),
                allowed_axioms: Vec::new(),
                binding: None,
            }),
        },
        assurance: None,
    }
}

fn bind(certificate: &mut ProofCertificate, seed: u8) {
    let ProofEvidence::CleanCic {
        kernel_recheck: Some(recheck),
        ..
    } = &mut certificate.evidence
    else {
        panic!("transport control must have a recheck directive");
    };
    recheck.binding = Some(Box::new(CertificateBinding::new(
        ProofDigest::sha256([seed; 32]),
        ProofDigest::sha256([seed; 32]),
    )));
}

fn claims(definition: &str) -> Vec<ModuleCompleteness> {
    let row = UnloweredRow {
        symbol: "not_lowered".to_string(),
        display_path: Some("Control::not_lowered".to_string()),
        reason: "transport refusal control".to_string(),
    };
    vec![
        ModuleCompleteness::Complete,
        ModuleCompleteness::Partial(vec![]),
        ModuleCompleteness::Partial(vec![row.clone()]),
        ModuleCompleteness::Partial(vec![row.clone(), row.clone()]),
        ModuleCompleteness::Partial(vec![UnloweredRow {
            symbol: definition.to_string(),
            ..row
        }]),
    ]
}

#[track_caller]
fn assert_body_error(error: TrustIrBodyError, function: FuncId, location: &str, construct: &str) {
    match error {
        TrustIrBodyError::NoWireIdentity {
            function: found_function,
            location: found_location,
            construct: found_construct,
        } => {
            assert_eq!(found_function, function);
            assert_eq!(found_location, location);
            assert_eq!(found_construct, construct);
        }
        other => panic!("expected NoWireIdentity, got {other:?}"),
    }
}

#[track_caller]
fn assert_native_error(error: TrustEngineError, location: &str, construct: &str) {
    match error {
        TrustEngineError::NativeTrustIrModuleHasNoWireIdentity {
            location: found_location,
            construct: found_construct,
        } => {
            assert_eq!(found_location, location);
            assert_eq!(found_construct, construct);
        }
        other => panic!("expected NativeTrustIrModuleHasNoWireIdentity, got {other:?}"),
    }
}

fn assert_direct_refusal(fixture: &fixtures::Fixture, location: &str, construct: &str) {
    let before = fixture.module.clone();
    let request = request(fixture);
    let request_before = request.clone();
    let engine = TrustVcTrustEngine::new();
    assert_body_error(
        trust_ir_body_semantic_digest(&fixture.module, fixture.function())
            .expect_err("original non-wire claim must not be projected away"),
        fixture.function(),
        location,
        construct,
    );
    assert_eq!(fixture.module, before);
    assert_body_error(
        engine
            .discharge_trust_ir_function(
                &fixture.module,
                fixture.function(),
                &TrustIrBodyOptions::default(),
            )
            .expect_err("body entry must refuse before clone/hash"),
        fixture.function(),
        location,
        construct,
    );
    assert_eq!(fixture.module, before);
    assert_native_error(
        engine
            .discharge_native_trust_ir_request(&fixture.module, &request)
            .expect_err("direct request must refuse before either digest"),
        location,
        construct,
    );
    assert_eq!(fixture.module, before);
    assert_eq!(request, request_before);
}

fn assert_bundle_refusal(bundle: &NativeVerificationBundle, location: &str, construct: &str) {
    let before = bundle.clone();
    let engine = TrustVcTrustEngine::new();
    assert_native_error(
        engine
            .consume_native_trust_ir_bundle(bundle)
            .expect_err("raw bundle must refuse"),
        location,
        construct,
    );
    assert_eq!(*bundle, before);
    assert_native_error(
        engine
            .consume_native_tmir_bundle(bundle)
            .expect_err("alias must refuse identically"),
        location,
        construct,
    );
    assert_eq!(*bundle, before);
    assert_native_error(
        engine
            .validate_native_trust_ir_bundle(bundle)
            .expect_err("validation must refuse"),
        location,
        construct,
    );
    assert_eq!(*bundle, before);
}

#[test]
fn ordinary_and_explicitly_unbound_inputs_preserve_both_existing_digests() {
    let engine = TrustVcTrustEngine::new();
    for unbound_certificate in [false, true] {
        let mut fixture = fixtures::guarded_checked_add_u8();
        let semantic = trust_ir_body_semantic_digest(&fixture.module, fixture.function()).unwrap();
        if unbound_certificate {
            fixture
                .module
                .proof_certificates
                .push(transport_certificate(fixture.obligations[0]));
        }
        assert_eq!(fixture.module.completeness, None);
        assert_eq!(fixture.module.first_certificate_binding(), None);
        let before = fixture.module.clone();
        let canonical = fixture.module.stable_digest();
        assert_eq!(
            trust_ir_body_semantic_digest(&fixture.module, fixture.function()).unwrap(),
            semantic
        );
        let body = engine
            .discharge_trust_ir_function(
                &fixture.module,
                fixture.function(),
                &TrustIrBodyOptions::default(),
            )
            .expect("ordinary unbound metadata keeps the existing body lane");
        assert_eq!(body.semantic_digest, semantic);
        let report = engine
            .discharge_native_trust_ir_request(&fixture.module, &request(&fixture))
            .expect("ordinary direct request stays reportable");
        assert!(!report.verdict().is_ok(), "this body lane remains advisory");
        assert!(report.proof_evidence().is_empty());
        let answer = report.advisory_discharge().expect("direct body answer");
        assert_eq!(answer.semantic_digest(), semantic);
        assert_eq!(answer.trust_ir_module_digest(), canonical.to_string());
        assert_eq!(fixture.module, before);
        assert_eq!(fixture.module.stable_digest(), canonical);
    }
}

#[test]
fn semantic_digest_keeps_requested_function_isolation_and_ordinary_debug_stripping() {
    let mut fixture = fixtures::guarded_checked_add_u8();
    let expected = trust_ir_body_semantic_digest(&fixture.module, fixture.function()).unwrap();
    let mut sibling = fixture.module.functions[0].clone();
    sibling.id = FuncId::new(9);
    sibling.name = "unrequested_nonwire_body".to_string();
    sibling.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::MemSet {
            dst: ValueId::new(0),
            byte: ValueId::new(1),
            bytes: ValueId::new(0),
        }),
    );
    fixture.module.functions.push(sibling);
    fixture.module.functions[0].scopes = Some(vec![trust_ir::ScopeData::new(None, None)]);
    let before = fixture.module.clone();
    // Do not hash the whole module: the unrelated instruction has no carrier.
    assert_eq!(
        trust_ir_body_semantic_digest(&fixture.module, fixture.function()).unwrap(),
        expected
    );
    let report = TrustVcTrustEngine::new()
        .discharge_trust_ir_function(
            &fixture.module,
            fixture.function(),
            &TrustIrBodyOptions::default(),
        )
        .expect("the semantic body lane still isolates the requested function");
    assert_eq!(report.semantic_digest, expected);
    assert_eq!(fixture.module, before);
}

#[test]
fn every_completeness_shape_refuses_original_direct_inputs_without_erasure() {
    let baseline = fixtures::guarded_checked_add_u8();
    for claim in claims(&baseline.module.functions[0].name) {
        let mut fixture = fixtures::guarded_checked_add_u8();
        fixture.module.completeness = Some(claim);
        assert_direct_refusal(&fixture, "module", "Module.completeness");
    }
}

#[test]
fn bound_certificates_refuse_before_proof_rows_are_cleared_or_original_module_is_hashed() {
    for seed in [0, 0x42] {
        let mut fixture = fixtures::guarded_checked_add_u8();
        // Include an unbound row first and a bound, unrequested row second:
        // the reported table index is not the obligation id or request scope.
        fixture
            .module
            .proof_certificates
            .push(transport_certificate(fixture.obligations[0]));
        fixture
            .module
            .proof_certificates
            .push(transport_certificate(ProofId::new(91)));
        bind(&mut fixture.module.proof_certificates[1], seed);
        assert_direct_refusal(
            &fixture,
            "certificate #1 for obligation #91",
            "CleanCicKernelRecheck.binding (CertificateBinding)",
        );
    }
}

#[test]
fn ordinary_native_bundle_keeps_exact_original_identity_and_admission() {
    // The baseline is admitted, and the admission pinned here is that verdict,
    // the same through both entry points, with the bundle unchanged.
    let bundle = admission_baseline::native_bundle_fixture();
    assert_eq!(bundle.module.completeness, None);
    assert_eq!(bundle.module.first_certificate_binding(), None);
    let before = bundle.clone();
    let canonical = bundle.module.stable_digest();
    let engine = TrustVcTrustEngine::new();
    let report = engine
        .consume_native_trust_ir_bundle(&bundle)
        .expect("ordinary baseline admits");
    assert_eq!(
        report.verdict(),
        trust_vc_trust_engine::TrustVcNativeTrustIrVerdict::CertificatesAdmitted
    );
    assert!(report.verdict().is_ok());
    assert!(report.requests()[0].proof_evidence()[0]
        .release_admission()
        .rejection_reasons()
        .is_empty());
    assert_eq!(report.trust_ir_module_digest(), canonical.to_string());
    assert_eq!(
        engine
            .consume_native_tmir_bundle(&bundle)
            .unwrap()
            .verdict(),
        report.verdict()
    );
    engine
        .validate_native_trust_ir_bundle(&bundle)
        .expect("baseline validates");
    assert_eq!(bundle, before);
    assert_eq!(bundle.module.stable_digest(), canonical);
    assert_eq!(
        admission_edits::assert_id_and_formula_liars_refused(&bundle),
        1
    );
}

#[test]
fn raw_bundle_entries_refuse_every_claim_before_validation_or_identity() {
    let baseline = admission_baseline::native_bundle_fixture();
    for claim in claims(&baseline.module.functions[0].name) {
        for otherwise_valid in [true, false] {
            let mut bundle = baseline.clone();
            bundle.module.completeness = Some(claim.clone());
            if !otherwise_valid {
                bundle.schema_version = 0;
            }
            assert_bundle_refusal(&bundle, "module", "Module.completeness");
        }
    }
    for seed in [0, 0x42] {
        let mut bundle = baseline.clone();
        let index = bundle.module.proof_certificates.len();
        bundle
            .module
            .proof_certificates
            .push(transport_certificate(ProofId::new(91)));
        bind(&mut bundle.module.proof_certificates[index], seed);
        // Never reseal or hash an unencodable module, including in this test.
        assert_bundle_refusal(
            &bundle,
            &format!("certificate #{index} for obligation #91"),
            "CleanCicKernelRecheck.binding (CertificateBinding)",
        );
    }
}

#[test]
fn clean_producer_label_is_preserved_and_grants_no_claim_bypass() {
    let mut bundle = admission_baseline::native_bundle_fixture();
    let original = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .unwrap();
    // Only the producer enum changes: this is a routing-label control, not a
    // claim that the underlying corpus was emitted by a Clean compiler.
    bundle.producer = NativeBundleProducer::Clean;
    let before = bundle.clone();
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .unwrap();
    assert_eq!(report.producer(), "Clean");
    assert_eq!(report.verdict(), original.verdict());
    assert_eq!(
        report.trust_ir_module_digest(),
        original.trust_ir_module_digest()
    );
    assert_eq!(bundle, before);
    bundle.module.completeness = Some(ModuleCompleteness::Complete);
    assert_bundle_refusal(&bundle, "module", "Module.completeness");
}
