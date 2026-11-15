// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Routing a native TrustIr `DischargeProofObligations` request to the
//! in-process ADVISORY body lane.
//!
//! Three things are measured here, and they are different questions:
//!
//! 1. **The route answers.** A request that names a function and cites
//!    obligations inside it comes back with the body lane's verdicts — a
//!    positive discharged advisorily, a liar refuted, a body outside the lane
//!    not-answerable naming the reason.
//! 2. **The answer cannot be promoted.** Its authority label is a required,
//!    single-valued type; its verdict is never `is_ok`; it mints no proof
//!    artifact and writes back no status.
//! 3. **What still gates the serialized bundle path at the PIN**: upstream's
//!    certificate gate is mode-aware there, so only the mode-independent
//!    provenance gates remain. See
//!    `the_certificate_gate_is_mode_aware_at_the_pinned_trust_ir`.

#[path = "support/trust_ir_body_fixtures.rs"]
mod fixtures;

use fixtures::{Fixture, FIXTURE_FUNCTION};
use trust_ir::request::{NativeRequestId, TrustVcNativeRequest, TrustVcVerificationMode};
use trust_ir::{FuncId, Module, ProofCertificateRef, ProofDigest, ProofId};
use trust_vc_trust_engine::{
    TrustEngineError, TrustVcNativeTrustIrAdvisoryOutcome, TrustVcNativeTrustIrBodyReading,
    TrustVcNativeTrustIrDischargeAuthority, TrustVcNativeTrustIrExitClass,
    TrustVcNativeTrustIrLoweringWitness, TrustVcNativeTrustIrRequestMode,
    TrustVcNativeTrustIrRequestReport, TrustVcNativeTrustIrVerdict, TrustVcTrustEngine,
    HAVOC_INSTANTIATION_NOTE, TRUST_IR_BODY_LANE_SCHEMA,
};

/// A `DischargeProofObligations` request for `function`, citing `obligations`.
///
/// Deliberately hand-built rather than decoded from the checked-in bundle
/// fixture: that fixture is schema 7 and its single request is an IMPORT, and
/// the point here is the discharge shape a Trust-side bridge will mint —
/// `trust-ir-bridge/src/native_request.rs:294-312` already sets
/// `function: Some(owner.function)` on every TrustVc request.
fn discharge_request(function: FuncId, obligations: &[ProofId]) -> TrustVcNativeRequest {
    TrustVcNativeRequest {
        id: NativeRequestId::new(0),
        mode: TrustVcVerificationMode::DischargeProofObligations,
        obligations: obligations.to_vec(),
        certificates: Vec::new(),
        lineage_roots: Vec::new(),
        options: Default::default(),
        diagnostics: Default::default(),
        provenance: Default::default(),
        function: Some(function),
    }
}

fn answer(fixture: &Fixture) -> TrustVcNativeTrustIrRequestReport {
    let request = discharge_request(FIXTURE_FUNCTION, &fixture.obligations);
    TrustVcTrustEngine::new()
        .discharge_native_trust_ir_request(&fixture.module, &request)
        .unwrap_or_else(|error| panic!("{} should reach a report: {error}", fixture.name))
}

fn refusal(module: &Module, request: &TrustVcNativeRequest) -> TrustEngineError {
    TrustVcTrustEngine::new()
        .discharge_native_trust_ir_request(module, request)
        .expect_err("this discharge request must be refused")
}

/// No report from this route may ever read as a clean pass, whatever it says.
#[track_caller]
fn assert_never_a_pass(report: &TrustVcNativeTrustIrRequestReport) {
    assert_eq!(
        report.mode(),
        TrustVcNativeTrustIrRequestMode::DischargeProofObligations
    );
    assert!(
        !report.verdict().is_ok(),
        "an advisory discharge answer must never be a clean pass, got {:?}",
        report.verdict()
    );
    assert_ne!(
        report.verdict().exit_class(),
        TrustVcNativeTrustIrExitClass::Ok
    );
    assert!(
        report.proof_evidence().is_empty(),
        "a discharge answer must never enter the certificate-admission channel"
    );
    assert!(
        report.admit_native_proof_artifacts().is_empty(),
        "a discharge answer must mint no native proof artifact"
    );
    let discharge = report
        .advisory_discharge()
        .expect("a discharge answer must be present");
    assert_eq!(
        discharge.authority(),
        TrustVcNativeTrustIrDischargeAuthority::Advisory
    );
    assert_eq!(
        discharge.lowering_witness(),
        TrustVcNativeTrustIrLoweringWitness::None
    );
    assert_eq!(discharge.lane_schema(), TRUST_IR_BODY_LANE_SCHEMA);
}

// ---------------------------------------------------------------------------
// 1. The route answers
// ---------------------------------------------------------------------------

/// THE POSITIVE PATH, END TO END. Before this change the same request answered
/// `DischargeNotAnswerable` with an empty report whatever the body said.
#[test]
fn a_guarded_body_is_discharged_advisorily_through_the_request_route() {
    let fixture = fixtures::guarded_checked_add_u8();
    let report = answer(&fixture);
    assert_never_a_pass(&report);

    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::DischargedAdvisory
    );
    assert_eq!(report.request_id(), 0);

    let discharge = report.advisory_discharge().expect("answer present");
    assert_eq!(discharge.function(), FIXTURE_FUNCTION.index());
    assert!(
        discharge.function_refusal().is_none(),
        "the body is inside the lane: {:?}",
        discharge.function_refusal()
    );
    assert!(
        !discharge.semantic_digest().is_empty(),
        "the answer must name the body it is about"
    );

    assert_eq!(discharge.obligations().len(), 1);
    let obligation = &discharge.obligations()[0];
    assert_eq!(obligation.obligation_id(), fixture.obligations[0].index());
    assert_eq!(
        obligation.outcome(),
        TrustVcNativeTrustIrAdvisoryOutcome::DischargedAdvisory
    );

    // The havoc disclosure crosses the seam with the answer. Trust's checked-op
    // pack seeds `Inst::Undef`, so this verdict is about the havoc reading, and
    // the wire report says so in two places.
    assert_eq!(
        obligation.reading(),
        TrustVcNativeTrustIrBodyReading::HavocInstantiatedUndef
    );
    assert_eq!(
        discharge.havoc_instantiation_note(),
        Some(HAVOC_INSTANTIATION_NOTE)
    );

    // The producer's own claims were seen and not read as facts.
    assert!(discharge.ignored_inputs().formulas);
    assert!(discharge.ignored_inputs().annotations);
}

/// A LIAR: the same shape with the guards removed. The assert genuinely fails,
/// so the route must come back REFUTED, not discharged, and the process must
/// not exit 0.
#[test]
fn an_unguarded_body_comes_back_refuted_rather_than_discharged() {
    let fixture = fixtures::unguarded_checked_add_u8();
    let report = answer(&fixture);
    assert_never_a_pass(&report);

    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::DischargeRefuted
    );
    assert_eq!(
        report.verdict().exit_class(),
        TrustVcNativeTrustIrExitClass::Refuted
    );

    let obligation = &report
        .advisory_discharge()
        .expect("answer present")
        .obligations()[0];
    assert_eq!(
        obligation.outcome(),
        TrustVcNativeTrustIrAdvisoryOutcome::Refuted
    );
    assert_ne!(
        obligation.outcome(),
        TrustVcNativeTrustIrAdvisoryOutcome::DischargedAdvisory
    );
    // The counterexample's concrete bindings stay in the in-process report.
    let detail = obligation.detail().expect("a refutation says why");
    assert!(
        detail.contains("counterexample") && detail.contains("failing site"),
        "unexpected detail: {detail}"
    );
}

/// EVEN WITH EVERY PRODUCER CLAIM STAMPED ON IT. `NoOverflow` on the node,
/// function annotations and a `proved: true` summary do not move the verdict.
#[test]
fn producer_claims_do_not_turn_a_refutation_into_a_discharge() {
    let fixture = fixtures::unguarded_with_producer_claims();
    let report = answer(&fixture);
    assert_never_a_pass(&report);
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::DischargeRefuted
    );

    let discharge = report.advisory_discharge().expect("answer present");
    assert!(discharge.ignored_inputs().annotations);
    assert!(discharge.ignored_inputs().summary_requires);
}

/// A REFUSED-INSTRUCTION FUNCTION. The lane declines the whole body, so every
/// cited obligation comes back `NotAnswerable` NAMING THE REASON, and the
/// request rolls up to not-answerable.
#[test]
fn a_body_outside_the_lane_comes_back_not_answerable_naming_the_instruction() {
    let fixture = fixtures::extract_uninserted_field();
    let report = answer(&fixture);
    assert_never_a_pass(&report);

    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::DischargeNotAnswerable
    );
    assert_eq!(
        report.verdict().exit_class(),
        TrustVcNativeTrustIrExitClass::Unknown
    );

    let discharge = report.advisory_discharge().expect("answer present");
    let function_refusal = discharge
        .function_refusal()
        .expect("the whole body was refused");
    assert!(
        function_refusal.contains("unsupported instruction ExtractField"),
        "the refusal must name the instruction: {function_refusal}"
    );
    assert!(
        function_refusal.contains("havoc"),
        "the refusal must name the reason: {function_refusal}"
    );

    assert!(!discharge.obligations().is_empty());
    for obligation in discharge.obligations() {
        assert_eq!(
            obligation.outcome(),
            TrustVcNativeTrustIrAdvisoryOutcome::NotAnswerable
        );
        let detail = obligation.detail().expect("a refusal says why");
        assert!(
            detail.contains("ExtractField"),
            "the per-obligation reason must name it too: {detail}"
        );
    }
}

/// A SITE the lane can see but not answer: the obligation is sited on an
/// instruction that is not an `Assert`. The body itself is fine, so this is a
/// PER-OBLIGATION refusal rather than a function-level one.
#[test]
fn a_site_that_is_not_an_assert_is_refused_per_obligation() {
    let mut fixture = fixtures::guarded_checked_add_u8();
    let proof_id = fixture.obligations[0];
    let obligation = fixture
        .module
        .proof_obligations
        .iter_mut()
        .find(|obligation| obligation.id == proof_id)
        .expect("the fixture declares it");
    let site = obligation.site.as_mut().expect("the fixture sites it");
    site.inst_index = 0; // the entry block's first instruction is a `Const`.

    let report = answer(&fixture);
    assert_never_a_pass(&report);
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::DischargeNotAnswerable
    );
    let discharge = report.advisory_discharge().expect("answer present");
    assert!(
        discharge.function_refusal().is_none(),
        "the BODY is still inside the lane: {:?}",
        discharge.function_refusal()
    );
    let detail = discharge.obligations()[0]
        .detail()
        .expect("a refusal says why");
    assert!(
        detail.contains("not an Assert"),
        "unexpected detail: {detail}"
    );
}

// ---------------------------------------------------------------------------
// 2. The answer cannot be promoted
// ---------------------------------------------------------------------------

/// THE ADVISORY LABEL CANNOT BE STRIPPED.
///
/// `authority` is a required serde field with no `default` and exactly one
/// spellable value, so a report that arrives without it — or with anything
/// else in it — does not deserialize at all. That is the difference between a
/// label and a type.
#[test]
fn the_advisory_label_cannot_be_stripped_or_rewritten() {
    let fixture = fixtures::guarded_checked_add_u8();
    let report = answer(&fixture);
    let json = serde_json::to_value(&report).expect("the report serializes");

    assert_eq!(
        json.pointer("/advisory_discharge/authority")
            .and_then(|v| v.as_str()),
        Some("advisory"),
        "the label must be on the wire: {json}"
    );
    assert_eq!(
        json.pointer("/advisory_discharge/lowering_witness")
            .and_then(|v| v.as_str()),
        Some("none")
    );
    assert_eq!(
        json.get("verdict").and_then(|v| v.as_str()),
        Some("discharged_advisory"),
        "even the verdict spelling carries the word"
    );

    // Decodes — carrying no authority: a decoded discharge report is judged
    // by nobody here, so it is `NotJudged`, every outcome `NotJudged`
    // (native_wire_discharge_authority.rs), and it still says `advisory`. It
    // used to round-trip as itself, the producer's verdict read off the wire.
    let restored: TrustVcNativeTrustIrRequestReport =
        serde_json::from_value(json.clone()).expect("the report decodes");
    assert_eq!(restored.verdict(), TrustVcNativeTrustIrVerdict::NotJudged);
    let restored_answer = restored.advisory_discharge().expect("the answer decodes");
    assert_eq!(
        restored_answer.authority(),
        TrustVcNativeTrustIrDischargeAuthority::Advisory
    );
    assert!(restored_answer
        .obligations()
        .iter()
        .all(|o| o.outcome() == TrustVcNativeTrustIrAdvisoryOutcome::NotJudged));
    assert_eq!(
        restored_answer.request_digest(),
        report
            .advisory_discharge()
            .expect("answered")
            .request_digest()
    );

    // Stripped: refused.
    let mut stripped = json.clone();
    stripped
        .pointer_mut("/advisory_discharge")
        .and_then(serde_json::Value::as_object_mut)
        .expect("the discharge answer is an object")
        .remove("authority");
    serde_json::from_value::<TrustVcNativeTrustIrRequestReport>(stripped)
        .expect_err("a discharge answer with no authority label must not deserialize");

    // Rewritten: refused, because `Advisory` is the only value the type has.
    let mut forged = json;
    *forged
        .pointer_mut("/advisory_discharge/authority")
        .expect("the label is there") = serde_json::Value::String("authoritative".to_string());
    serde_json::from_value::<TrustVcNativeTrustIrRequestReport>(forged)
        .expect_err("no authority other than `advisory` can be spelled");
}

/// THE ROLLUP CANNOT AVERAGE AN ADVISORY ANSWER INTO A PASS, and no verdict
/// this route produces exits 0.
#[test]
fn no_discharge_verdict_is_a_pass_or_exits_zero() {
    for verdict in [
        TrustVcNativeTrustIrVerdict::DischargedAdvisory,
        TrustVcNativeTrustIrVerdict::DischargeRefuted,
        TrustVcNativeTrustIrVerdict::DischargeNotAnswerable,
    ] {
        assert!(!verdict.is_ok(), "{verdict:?} must not be a clean pass");
        assert_ne!(
            verdict.exit_class(),
            TrustVcNativeTrustIrExitClass::Ok,
            "{verdict:?} must not exit 0"
        );
    }
    // Of the certificate modes, only an admitted rollup exits 0. A rejected
    // one used to exit 0 as well ("release admission is a grading result"),
    // so a bundle with no release-grade certificate at all validated and
    // exited like a clean pass; it now has an exit class of its own.
    assert!(TrustVcNativeTrustIrVerdict::CertificatesAdmitted.is_ok());
    assert!(!TrustVcNativeTrustIrVerdict::CertificatesRejected.is_ok());
    assert_eq!(
        TrustVcNativeTrustIrVerdict::CertificatesAdmitted.exit_class(),
        TrustVcNativeTrustIrExitClass::Ok
    );
    assert_eq!(
        TrustVcNativeTrustIrVerdict::CertificatesRejected.exit_class(),
        TrustVcNativeTrustIrExitClass::Rejected,
        "a rejected certificate is not a pass"
    );
}

/// A DISCHARGE ANSWER WRITES NOTHING BACK. The obligation arrives already
/// labelled `Discharged` by a producer; the lane answers it from the body,
/// records that it saw the label, and mints no artifact from it.
#[test]
fn a_discharge_answer_reads_no_status_and_mints_no_artifact() {
    let mut fixture = fixtures::unguarded_checked_add_u8();
    for obligation in &mut fixture.module.proof_obligations {
        obligation.status = trust_ir::ProofStatus::Discharged;
    }

    let report = answer(&fixture);
    assert_never_a_pass(&report);
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::DischargeRefuted,
        "a producer's `Discharged` label must not survive contact with the body"
    );

    let discharge = report.advisory_discharge().expect("answer present");
    assert!(
        discharge.ignored_inputs().statuses,
        "the answer must record that it SAW the label"
    );
    // Nothing on the wire carries a trust-ir status or certificate.
    let json = serde_json::to_string(&report).expect("serializes");
    assert!(!json.contains("proof_certificate"), "{json}");
    assert!(
        !json.contains("\"discharged\""),
        "no trust-ir ProofStatus may reach the wire report: {json}"
    );
}

// ---------------------------------------------------------------------------
// 3. Refusals — every one fails closed BEFORE the lane is entered
// ---------------------------------------------------------------------------

#[test]
fn a_discharge_request_naming_no_function_is_refused() {
    let fixture = fixtures::guarded_checked_add_u8();
    let mut request = discharge_request(FIXTURE_FUNCTION, &fixture.obligations);
    request.function = None;

    match refusal(&fixture.module, &request) {
        TrustEngineError::NativeTrustIrDischargeRequestMissingFunction { request_id } => {
            assert_eq!(request_id, 0);
        }
        other => panic!("expected MissingFunction, got {other:?}"),
    }
}

#[test]
fn a_discharge_request_carrying_a_certificate_is_refused() {
    let fixture = fixtures::guarded_checked_add_u8();
    let mut request = discharge_request(FIXTURE_FUNCTION, &fixture.obligations);
    request.certificates.push(ProofCertificateRef {
        obligation: fixture.obligations[0],
        prover: "trust_vc".to_string(),
        evidence_digest: ProofDigest::sha256_domain("test.discharge.certificate", b"forged"),
    });

    match refusal(&fixture.module, &request) {
        TrustEngineError::NativeTrustIrDischargeRequestCarriesCertificate {
            request_id,
            obligation_id,
            prover,
        } => {
            assert_eq!(request_id, 0);
            assert_eq!(obligation_id, fixture.obligations[0].index());
            assert_eq!(prover, "trust_vc");
        }
        other => panic!("expected CarriesCertificate, got {other:?}"),
    }
}

#[test]
fn a_discharge_request_citing_no_obligations_is_refused() {
    let fixture = fixtures::guarded_checked_add_u8();
    let request = discharge_request(FIXTURE_FUNCTION, &[]);

    match refusal(&fixture.module, &request) {
        TrustEngineError::NativeTrustIrDischargeRequestWithoutObligations { request_id } => {
            assert_eq!(request_id, 0);
        }
        other => panic!("expected WithoutObligations, got {other:?}"),
    }
}

#[test]
fn a_discharge_request_citing_an_undeclared_obligation_is_refused() {
    let fixture = fixtures::guarded_checked_add_u8();
    let request = discharge_request(FIXTURE_FUNCTION, &[ProofId::new(97)]);

    match refusal(&fixture.module, &request) {
        TrustEngineError::NativeTrustIrTrustVcRequestUnknownObligation {
            request_id,
            obligation_id,
        } => {
            assert_eq!(request_id, 0);
            assert_eq!(obligation_id, 97);
        }
        other => panic!("expected UnknownObligation, got {other:?}"),
    }
}

/// THE OBLIGATION-SCOPING GATE. Naming a function is what makes this
/// checkable: an obligation neither scoped to nor sited in it is refused
/// outright rather than quietly answered against the wrong body.
#[test]
fn a_discharge_request_citing_an_obligation_outside_the_function_is_refused() {
    let mut fixture = fixtures::guarded_checked_add_u8();
    let proof_id = fixture.obligations[0];
    let foreign = FuncId::new(7);
    let obligation = fixture
        .module
        .proof_obligations
        .iter_mut()
        .find(|obligation| obligation.id == proof_id)
        .expect("the fixture declares it");
    obligation.function = Some(foreign);
    if let Some(site) = obligation.site.as_mut() {
        site.function = foreign;
    }

    let request = discharge_request(FIXTURE_FUNCTION, &fixture.obligations);
    match refusal(&fixture.module, &request) {
        TrustEngineError::NativeTrustIrDischargeRequestObligationOutsideFunction {
            request_id,
            obligation_id,
            function_id,
        } => {
            assert_eq!(request_id, 0);
            assert_eq!(obligation_id, proof_id.index());
            assert_eq!(function_id, FIXTURE_FUNCTION.index());
        }
        other => panic!("expected ObligationOutsideFunction, got {other:?}"),
    }
}

/// The answer is bound to the WHOLE module's `stable_digest`, and trust-ir's
/// binary writer panics on a construct ahead of its wire carrier WHEREVER it
/// sits. A lexical scope's inlining-chain link in a function the request
/// never names must therefore still refuse the request by name — before the
/// lane runs, and without a panic.
#[test]
fn a_module_without_a_wire_identity_is_refused_before_anything_is_hashed() {
    let mut fixture = fixtures::guarded_checked_add_u8();
    let mut sibling = fixture.module.functions[0].clone();
    sibling.id = FuncId::new(1);
    sibling.name = "sibling_with_inlined_scope".to_string();
    let mut inlined = trust_ir::ScopeData::new(Some(0), None);
    inlined.inlined_at = Some(trust_ir::InlinedAt {
        span: trust_ir::SourceSpan {
            file: 0,
            line: 1,
            col: 1,
        },
        callee: "inlined_callee".to_string(),
    });
    sibling.scopes = Some(vec![trust_ir::ScopeData::new(None, None), inlined]);
    fixture.module.functions.push(sibling);

    let request = discharge_request(FIXTURE_FUNCTION, &fixture.obligations);
    match refusal(&fixture.module, &request) {
        TrustEngineError::NativeTrustIrModuleHasNoWireIdentity {
            location,
            construct,
        } => {
            assert_eq!(location, "function #1 scope #1");
            assert!(construct.contains("inlined_at"), "{construct}");
        }
        other => panic!("expected NativeTrustIrModuleHasNoWireIdentity, got {other:?}"),
    }
}

#[test]
fn a_discharge_request_naming_an_absent_function_is_refused() {
    let fixture = fixtures::guarded_checked_add_u8();
    let request = discharge_request(FuncId::new(9), &fixture.obligations);

    // The scope gate fires first, which is correct: an obligation sited in
    // function 0 is not inside function 9 whether or not function 9 exists.
    match refusal(&fixture.module, &request) {
        TrustEngineError::NativeTrustIrDischargeRequestObligationOutsideFunction {
            function_id,
            ..
        } => assert_eq!(function_id, 9),
        other => panic!("expected ObligationOutsideFunction, got {other:?}"),
    }
}

/// A MODE THE RECEIVER DOES NOT IMPLEMENT HERE. The discharge entry answers
/// discharge requests and nothing else; an import must go through
/// `consume_native_trust_ir_bundle`, which validates its lineage and
/// provenance.
#[test]
fn an_import_request_handed_to_the_discharge_entry_is_refused() {
    let fixture = fixtures::guarded_checked_add_u8();
    for mode in [
        TrustVcVerificationMode::ImportProofCertificates,
        TrustVcVerificationMode::MergeProofCertificates,
    ] {
        let mut request = discharge_request(FIXTURE_FUNCTION, &fixture.obligations);
        request.mode = mode;
        match refusal(&fixture.module, &request) {
            TrustEngineError::NativeTrustIrDischargeRequestWrongMode { request_id, .. } => {
                assert_eq!(request_id, 0);
            }
            other => panic!("expected WrongMode for {mode:?}, got {other:?}"),
        }
    }
}

// ---------------------------------------------------------------------------
// 4. The pin
// ---------------------------------------------------------------------------

/// GATE 1 IS MODE-AWARE AT THE PIN: the tripwire this test used to be has
/// fired, and this is what it measured when it did.
///
/// At trust-ir `0.11.0@4803c40`, `request/digest.rs::validate_trust_vc_request`
/// required a certificate for EVERY obligation of a TrustVc request regardless
/// of mode, so a certificate-less discharge bundle was refused before
/// `consume_native_trust_ir_bundle` could route it. At `0.14.0@4f09dab8` that
/// loop is mode-aware (import/merge still require a certificate per
/// obligation; discharge instead requires a named function and NO
/// certificates), so the certificate refusal is gone for this request.
///
/// The hand-built bundle below is still refused — by the MODE-INDEPENDENT
/// gates (lineage roots, per-obligation source mapping and public identity,
/// verifier suite, solver and replay identity), which this fixture does not
/// carry. So a serialized discharge bundle now reaches the routing in
/// `consume_native_trust_ir_bundle` exactly when it carries full provenance,
/// and nothing about the answer changes: it is the same advisory body-lane
/// answer, whose verdict is never `is_ok`.
#[test]
fn the_certificate_gate_is_mode_aware_at_the_pinned_trust_ir() {
    use trust_ir::request::{
        NativeAdapterInput, NativeBundleProducer, NativeVerificationBundle,
        NativeVerificationRequest,
    };

    let fixture = fixtures::guarded_checked_add_u8();
    let module_digest = fixture.module.stable_digest();
    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::TrustIrModule,
        module_digest,
        fixture.module.clone(),
        Default::default(),
    );
    bundle
        .requests
        .push(NativeVerificationRequest::TrustVc(discharge_request(
            FIXTURE_FUNCTION,
            &fixture.obligations,
        )));

    let errors = bundle
        .validate()
        .expect_err("a discharge bundle with no provenance is still refused upstream")
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    let joined = errors.join("; ");
    assert!(
        !joined.contains("no TrustVc certificate evidence for obligation"),
        "the pinned validator must no longer demand a certificate from a discharge \
         request: {joined}"
    );
    assert!(
        !joined.contains("discharge") && !joined.contains("Discharge"),
        "the discharge-specific gates (named function, no certificates, sited \
         obligations) must all be satisfied by this request: {joined}"
    );
    assert!(
        joined.contains("has no lineage roots"),
        "what still refuses it must be the mode-independent provenance gates: {joined}"
    );
}

/// The schema the checked-in bundle fixture declares must equal the schema the
/// LINKED trust-ir enforces.
///
/// `NativeVerificationBundle::validate` matches the schema version EXACTLY, so
/// when the pin moves this test names the stale fixture directly instead of
/// letting twenty unrelated tests in `native_trust_ir_bundle.rs` go red at the
/// door.
#[test]
fn the_checked_in_bundle_fixture_declares_the_linked_schema_version() {
    const FIXTURE: &str =
        include_str!("../fixtures/trust_ir_native/native_request_trust_bundle.json");
    let value: serde_json::Value =
        serde_json::from_str(FIXTURE).expect("the fixture is valid JSON");
    let declared = value
        .get("schema_version")
        .and_then(serde_json::Value::as_u64)
        .expect("the fixture declares a schema version");
    assert_eq!(
        u32::try_from(declared).expect("schema versions are small"),
        trust_ir::request::NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION,
        "the checked-in bundle fixture is stale against the linked trust-ir; \
         regenerate it in the same commit as the pin move"
    );
}

// ---------------------------------------------------------------------------
// 4. The WIRE cannot express a state the producer cannot reach
//
// Every test below was written against a REPRODUCED hole: the advisory
// containment guarded `authority`, which gates nothing, while `verdict` — the
// one field `is_ok()` and `exit_class()` read — was `#[serde(default)]`ed to
// `CertificatesAdmitted`. A discharge report that merely omitted the key
// deserialized as a CLEAN PASS with its advisory answer still attached.
// ---------------------------------------------------------------------------

/// Drop `verdict` from a genuine advisory report: it must no longer
/// deserialize at all.
///
/// Before the fix this returned `verdict = CertificatesAdmitted`,
/// `is_ok = true`, `exit_class = Ok`, with `discharge.authority` still
/// spelled `"advisory"` and simply never consulted.
#[test]
fn a_discharge_report_with_no_verdict_key_does_not_deserialize() {
    let fixture = fixtures::guarded_checked_add_u8();
    let report = answer(&fixture);
    let json = serde_json::to_value(&report).expect("serializes");
    assert_eq!(
        json.get("verdict").and_then(|value| value.as_str()),
        Some("discharged_advisory")
    );

    let mut stripped = json.clone();
    stripped
        .as_object_mut()
        .expect("object")
        .remove("verdict")
        .expect("the key was there");
    let restored = serde_json::from_value::<TrustVcNativeTrustIrRequestReport>(stripped).err();
    assert!(
        restored.is_some(),
        "a report with no verdict must not deserialize as a clean pass"
    );

    // And with the discharge answer removed as well: a discharge-mode report
    // with no answer in it at all used to be a pass.
    let mut hollow = json;
    let object = hollow.as_object_mut().expect("object");
    object.remove("verdict");
    object.remove("advisory_discharge");
    serde_json::from_value::<TrustVcNativeTrustIrRequestReport>(hollow)
        .expect_err("a discharge-mode report with neither verdict nor answer must be refused");
}

/// The MINIMAL shape a hand-writer would reach for. It used to deserialize
/// and read `is_ok = true`.
#[test]
fn a_minimal_hand_written_discharge_report_is_refused() {
    let minimal = serde_json::json!({
        "request_id": 0,
        "mode": "discharge_proof_obligations",
        "lineage_roots": [],
        "proof_evidence": []
    });
    serde_json::from_value::<TrustVcNativeTrustIrRequestReport>(minimal)
        .expect_err("a discharge report with no verdict and no answer must be refused");
}

/// A discharge answer cannot be re-labelled with a certificate-mode verdict,
/// which is how the default used to be spelled by hand.
#[test]
fn a_discharge_answer_cannot_wear_a_certificate_verdict() {
    let fixture = fixtures::guarded_checked_add_u8();
    let report = answer(&fixture);
    let mut json = serde_json::to_value(&report).expect("serializes");
    *json.get_mut("verdict").expect("verdict present") =
        serde_json::Value::String("certificates_admitted".to_string());
    serde_json::from_value::<TrustVcNativeTrustIrRequestReport>(json)
        .expect_err("an advisory answer must not deserialize as an admitted-certificate pass");
}

/// The mirror: a certificate-mode report must not smuggle a discharge answer
/// in, nor wear a discharge verdict.
#[test]
fn a_certificate_report_cannot_carry_a_discharge_answer() {
    let fixture = fixtures::guarded_checked_add_u8();
    let report = answer(&fixture);
    let mut json = serde_json::to_value(&report).expect("serializes");
    *json.get_mut("mode").expect("mode present") =
        serde_json::Value::String("import_proof_certificates".to_string());
    serde_json::from_value::<TrustVcNativeTrustIrRequestReport>(json.clone())
        .expect_err("an import report must not carry a discharge answer");

    let object = json.as_object_mut().expect("object");
    object.remove("advisory_discharge");
    serde_json::from_value::<TrustVcNativeTrustIrRequestReport>(json)
        .expect_err("an import report must not wear a discharge verdict");
}

// ---------------------------------------------------------------------------
// 5. The scope gate is NARROWER than the body lane, and narrower than it was
// ---------------------------------------------------------------------------

/// REPRODUCED: an obligation DECLARING another function while SITED in the
/// named one used to be admitted by the gate's disjunction, and refused a
/// layer down by the lane. upstream trust-ir would never have sanctioned it —
/// it binds a request to the compiler-fact `obligation_source.function` and
/// requires exact equality — so the gate is now a conjunction and refuses it
/// here, with an error naming the disagreement rather than a generic one.
#[test]
fn an_obligation_declaring_one_function_and_sited_in_another_is_refused() {
    let mut fixture = fixtures::guarded_checked_add_u8();
    let proof_id = fixture.obligations[0];
    let obligation = fixture
        .module
        .proof_obligations
        .iter_mut()
        .find(|obligation| obligation.id == proof_id)
        .expect("the fixture declares it");
    // Site stays inside FIXTURE_FUNCTION; the module-declared function does not.
    obligation.function = Some(FuncId::new(1));

    let request = discharge_request(FIXTURE_FUNCTION, &fixture.obligations);
    match refusal(&fixture.module, &request) {
        TrustEngineError::NativeTrustIrDischargeRequestObligationFunctionDisagrees {
            request_id,
            obligation_id,
            declared_function_id,
            function_id,
        } => {
            assert_eq!(request_id, 0);
            assert_eq!(obligation_id, proof_id.index());
            assert_eq!(declared_function_id, 1);
            assert_eq!(function_id, FIXTURE_FUNCTION.index());
        }
        other => panic!("expected ObligationFunctionDisagrees, got {other:?}"),
    }
}

/// THE MIRROR, and the one that matters more: an obligation declaring the
/// named function but SITED somewhere else. The lane proves the `Assert` at
/// the SITE, so this is not an obligation about the named body whatever
/// `function` claims. The old disjunction admitted it.
#[test]
fn an_obligation_sited_outside_the_named_function_is_refused() {
    let mut fixture = fixtures::guarded_checked_add_u8();
    let proof_id = fixture.obligations[0];
    let obligation = fixture
        .module
        .proof_obligations
        .iter_mut()
        .find(|obligation| obligation.id == proof_id)
        .expect("the fixture declares it");
    obligation.function = Some(FIXTURE_FUNCTION);
    let site = obligation.site.as_mut().expect("the fixture sites it");
    site.function = FuncId::new(1);

    let request = discharge_request(FIXTURE_FUNCTION, &fixture.obligations);
    match refusal(&fixture.module, &request) {
        TrustEngineError::NativeTrustIrDischargeRequestObligationOutsideFunction {
            obligation_id,
            function_id,
            ..
        } => {
            assert_eq!(obligation_id, proof_id.index());
            assert_eq!(function_id, FIXTURE_FUNCTION.index());
        }
        other => panic!("expected ObligationOutsideFunction, got {other:?}"),
    }
}

/// AN UNSITED OBLIGATION IS NOT AN OBLIGATION ABOUT A BODY.
///
/// GUARD, not gating evidence: this shape was refused before the gate was
/// narrowed too (the old disjunction is false for `function: None, site:
/// None`). It is pinned because it is exactly the shape upstream trust-ir's
/// own positive discharge fixture is built from, so it is the cross-repo
/// disagreement made executable on this side. `site` is
/// `Option` and `function` is documented `None` for legacy/unscoped
/// obligations, so the shape `function: None, site: None` is expressible — and
/// upstream trust-ir's own positive discharge fixture is built that way. The
/// gate refuses it rather than lowering a site it cannot find.
#[test]
fn an_obligation_with_no_site_is_refused() {
    let mut fixture = fixtures::guarded_checked_add_u8();
    let proof_id = fixture.obligations[0];
    let obligation = fixture
        .module
        .proof_obligations
        .iter_mut()
        .find(|obligation| obligation.id == proof_id)
        .expect("the fixture declares it");
    obligation.function = None;
    obligation.site = None;

    let request = discharge_request(FIXTURE_FUNCTION, &fixture.obligations);
    match refusal(&fixture.module, &request) {
        TrustEngineError::NativeTrustIrDischargeRequestObligationOutsideFunction {
            obligation_id,
            ..
        } => assert_eq!(obligation_id, proof_id.index()),
        other => panic!("expected ObligationOutsideFunction, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 6. The answer says everything the lane knows, and names what it answers
// ---------------------------------------------------------------------------

/// THE LANE'S OWN "NOT EXAMINED" DISCLOSURE MUST CROSS THE SEAM.
///
/// `TrustIrBodyReport::unobligated_asserts` exists to disclose `Assert`s in
/// the function that no obligation covers. It used to be computed in-process
/// and dropped at the wire boundary, so a consumer was told every cited
/// obligation was discharged and told nothing about the assert in the same
/// function that nobody looked at.
#[test]
fn the_answer_discloses_the_asserts_nobody_examined() {
    let fixture = fixtures::unobligated_assert_present();
    let report = answer(&fixture);
    assert_never_a_pass(&report);
    let discharge = report.advisory_discharge().expect("answer present");

    assert!(
        !discharge.unexamined_asserts().is_empty(),
        "this fixture has an assert no obligation cites; the answer must say so"
    );
    for unexamined in discharge.unexamined_asserts() {
        assert_eq!(
            unexamined.label,
            trust_vc_trust_engine::UNOBLIGATED_ASSERT_LABEL
        );
    }

    // And it is on the wire, not merely on the Rust type.
    let json = serde_json::to_value(&report).expect("serializes");
    let wire = json
        .pointer("/advisory_discharge/unexamined_asserts")
        .and_then(|value| value.as_array())
        .expect("the disclosure must be on the wire");
    assert_eq!(wire.len(), discharge.unexamined_asserts().len());

    // A body with nothing unexamined says nothing, rather than saying "none".
    let clean = answer(&fixtures::guarded_checked_add_u8());
    assert!(clean
        .advisory_discharge()
        .expect("answer present")
        .unexamined_asserts()
        .is_empty());
}

/// THE ANSWER NAMES WHAT IT ANSWERS.
///
/// The in-process entry binds the request to nothing — no lineage, no replay
/// identity, no module-digest check — and the answer used to carry only a bare
/// `FuncId` index and a digest the lane computed for itself, so a consumer
/// holding the report could not tell WHICH request or WHICH module it was
/// about. That is not authority either way; it is the difference between a
/// detectable mix-up and a silent one.
#[test]
fn the_answer_is_bound_to_the_request_and_module_it_answers() {
    use trust_ir::request::NativeVerificationRequest;

    let fixture = fixtures::guarded_checked_add_u8();
    let request = discharge_request(FIXTURE_FUNCTION, &fixture.obligations);
    let report = TrustVcTrustEngine::new()
        .discharge_native_trust_ir_request(&fixture.module, &request)
        .expect("the request is well formed");
    let discharge = report.advisory_discharge().expect("answer present");

    let expected_request = NativeVerificationRequest::TrustVc(request.clone())
        .stable_digest()
        .to_string();
    assert_eq!(discharge.request_digest(), expected_request);
    assert_eq!(
        discharge.trust_ir_module_digest(),
        fixture.module.stable_digest().to_string()
    );

    // The mix-up the entry cannot otherwise detect: obligations minted against
    // one module, handed to another. The answer no longer looks identical.
    let other = fixtures::guarded_checked_add_i8();
    let other_report = TrustVcTrustEngine::new()
        .discharge_native_trust_ir_request(&other.module, &request)
        .expect("the ids line up, so the lane answers");
    let other_discharge = other_report.advisory_discharge().expect("answer present");
    assert_eq!(
        other_discharge.request_digest(),
        expected_request,
        "same request"
    );
    assert_ne!(
        other_discharge.trust_ir_module_digest(),
        discharge.trust_ir_module_digest(),
        "different module: the report must not read as the same answer"
    );
}

/// A POSSIBLE FALSE ALARM STILL REPORTS AT REFUTATION GRADE, deliberately.
///
/// GUARD, not gating evidence: the grade is UNCHANGED by this round. The test
/// exists because the conflation was questioned and the answer was "keep it";
/// pinning it makes the next change to either half deliberate.
///
/// `RefutedIgnoringPriorAsserts` means the counterexample may be unreachable,
/// so the request verdict erases a distinction the per-obligation outcome
/// keeps. Demoting it would move the exit class from `Refuted` to `Unknown` —
/// quieter about a possible real defect — so the grade stays and the
/// distinction stays visible on the obligation. Pinned so that a later change
/// to either half is a deliberate one.
#[test]
fn a_prior_assert_blocked_counterexample_stays_at_refutation_grade() {
    let fixture = fixtures::prior_asserts_guard_the_add();
    let report = answer(&fixture);
    assert_never_a_pass(&report);
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::DischargeRefuted
    );
    assert_eq!(
        report.verdict().exit_class(),
        TrustVcNativeTrustIrExitClass::Refuted
    );

    let discharge = report.advisory_discharge().expect("answer present");
    let blocked = discharge.obligations().iter().filter(|obligation| {
        obligation.outcome() == TrustVcNativeTrustIrAdvisoryOutcome::RefutedIgnoringPriorAsserts
    });
    assert!(
        blocked.count() > 0,
        "this fixture is the one that produces the prior-assert-blocked outcome: {:?}",
        discharge
            .obligations()
            .iter()
            .map(|obligation| obligation.outcome())
            .collect::<Vec<_>>()
    );
}
