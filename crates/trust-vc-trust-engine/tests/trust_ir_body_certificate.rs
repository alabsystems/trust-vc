// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Certificate binding for the trust-ir body lane. Only meaningful in the
//! `proof-certificates` build; the default build has no certificate slot to
//! fill and says so in `certificate_note`.

#![cfg(feature = "proof-certificates")]

#[path = "support/trust_ir_body_fixtures.rs"]
mod fixtures;

use trust_vc_trust_engine::{
    trust_ir_body_semantic_digest, BodyReading, TrustIrBodyOptions, TrustIrBodyVerdict,
    TrustProofPolicy, TrustVcTrustEngine, TRUST_IR_BODY_BINDING_SCHEMA,
};

/// MEASURED on the stock lane, 2026-09-17, at the workspace ay pin: ay DOES
/// return a non-empty Alethe proof for this bit-vector site query —
/// `strict_verified=true kernel_verified=true trust_count=0 hole_count=0
/// resolution_count=0 theory_count=1`, 3787 payload bytes. Pinned so a change
/// is loud in either direction and never silently skipped.
///
/// A certificate here still proves only the QUERY, not that the query is the
/// site's meaning: `report_only` stays true and `lowering_witness` "none".
const AY_EMITS_AN_ALETHE_PROOF_FOR_THIS_QUERY: bool = true;

#[test]
fn a_discharged_site_binds_its_certificate_to_the_body_digest() {
    let fixture = fixtures::guarded_checked_add_u8();
    let report = TrustVcTrustEngine::new()
        .discharge_trust_ir_function(
            &fixture.module,
            fixture.function(),
            &TrustIrBodyOptions {
                proof_policy: TrustProofPolicy::AttachReplayableCertificates,
            },
        )
        .expect("fixture is reportable");

    let obligation = &report.obligations[0];
    let TrustIrBodyVerdict::DischargedAdvisory {
        certificate,
        certificate_note,
        ..
    } = &obligation.verdict
    else {
        panic!("expected DischargedAdvisory, got {:?}", obligation.verdict);
    };

    match certificate {
        Some(certificate) => {
            println!(
                "trust-ir body lane certificate: strict_verified={} kernel_verified={} trust_count={} hole_count={} resolution_count={} theory_count={} payload_bytes={}",
                certificate.artifact.strict_verified(),
                certificate.artifact.kernel_verified(),
                certificate.artifact.trust_count(),
                certificate.artifact.hole_count(),
                certificate.artifact.resolution_count(),
                certificate.artifact.theory_count(),
                certificate.artifact.payload().len(),
            );
            let site = obligation.site.expect("the site is reported");
            assert_eq!(certificate.binding.schema, TRUST_IR_BODY_BINDING_SCHEMA);
            assert_eq!(
                certificate.binding.semantic_digest,
                trust_ir_body_semantic_digest(&fixture.module, fixture.function()).unwrap()
            );
            assert_eq!(certificate.binding.semantic_digest, report.semantic_digest);
            assert_eq!(certificate.binding.site, site);
            assert_eq!(certificate.binding.proof_id, obligation.proof_id);
            assert_eq!(
                certificate.artifact.unit_id(),
                certificate.binding.canonical_string()
            );
            assert_eq!(
                certificate.artifact.assertion_obligation_ids(),
                [format!(
                    "tirb_site_b{}_i{}",
                    site.block.index(),
                    site.inst_index
                )]
            );
            assert!(certificate.report_only);
            assert_eq!(certificate.lowering_witness, "none");
            // The certified query is about the HAVOC reading of this body's
            // `Undef` pack, and that cannot be dropped while keeping the
            // certificate: it is part of the canonical string, hence of the
            // artifact's own unit_id, which is asserted above.
            assert_eq!(
                certificate.binding.reading,
                BodyReading::HavocInstantiatedUndef
            );
            assert_eq!(obligation.reading, certificate.binding.reading);
            assert!(certificate
                .artifact
                .unit_id()
                .contains("reading=havoc-instantiated-undef"));
            assert!(certificate_note.is_none(), "{certificate_note:?}");
            assert!(
                certificate.artifact.strict_verified(),
                "the measured certificate was strict-checker accepted"
            );
            assert_eq!(certificate.artifact.hole_count(), 0);
            assert_eq!(certificate.artifact.trust_count(), 0);
            assert!(!certificate.artifact.payload().is_empty());
        }
        None => {
            let note = certificate_note
                .as_ref()
                .expect("an absent certificate must say why");
            println!("trust-ir body lane certificate: absent — {note}");
            assert!(!note.is_empty());
        }
    }

    assert_eq!(
        certificate.is_some(),
        AY_EMITS_AN_ALETHE_PROOF_FOR_THIS_QUERY,
        "the measured certificate availability changed; re-measure and re-pin it"
    );
}

#[test]
fn evidence_only_never_mints_a_certificate() {
    let fixture = fixtures::guarded_checked_add_u8();
    let report = TrustVcTrustEngine::new()
        .discharge_trust_ir_function(
            &fixture.module,
            fixture.function(),
            &TrustIrBodyOptions::default(),
        )
        .expect("fixture is reportable");
    let TrustIrBodyVerdict::DischargedAdvisory {
        certificate,
        certificate_note,
        ..
    } = &report.obligations[0].verdict
    else {
        panic!("expected DischargedAdvisory");
    };
    assert!(certificate.is_none());
    assert!(certificate_note
        .as_ref()
        .is_some_and(|note| note.contains("EvidenceOnly")));
}

fn assert_signed_native_body_artifact(fixture: fixtures::Fixture) {
    let report = TrustVcTrustEngine::new()
        .discharge_trust_ir_function(
            &fixture.module,
            fixture.function(),
            &TrustIrBodyOptions {
                proof_policy: TrustProofPolicy::AttachReplayableCertificates,
            },
        )
        .expect("the original native body is reportable");
    assert_eq!(report.obligations.len(), 1);
    let obligation = &report.obligations[0];
    let TrustIrBodyVerdict::DischargedAdvisory {
        certificate,
        certificate_note,
        ..
    } = &obligation.verdict
    else {
        panic!("{}: {report:?}", fixture.name);
    };
    let certificate = certificate
        .as_ref()
        .unwrap_or_else(|| panic!("{}: {certificate_note:?}", fixture.name));
    assert!(certificate_note.is_none());
    assert_eq!(certificate.binding.schema, TRUST_IR_BODY_BINDING_SCHEMA);
    assert_eq!(certificate.binding.function, fixture.function());
    assert_eq!(certificate.binding.proof_id, obligation.proof_id);
    assert_eq!(certificate.binding.site, obligation.site.unwrap());
    assert_eq!(certificate.binding.reading, obligation.reading);
    assert_eq!(
        certificate.binding.reading,
        BodyReading::HavocInstantiatedUndef
    );
    assert_eq!(
        certificate.binding.semantic_digest,
        trust_ir_body_semantic_digest(&fixture.module, fixture.function()).unwrap()
    );
    assert_eq!(certificate.binding.semantic_digest, report.semantic_digest);
    assert_eq!(
        certificate.artifact.unit_id(),
        certificate.binding.canonical_string()
    );
    let site = certificate.binding.site;
    assert_eq!(
        certificate.artifact.assertion_obligation_ids(),
        [format!(
            "tirb_site_b{}_i{}",
            site.block.index(),
            site.inst_index
        )]
    );
    assert!(certificate.artifact.strict_verified());
    assert!(certificate.artifact.kernel_verified());
    assert_eq!(certificate.artifact.trust_count(), 0);
    assert_eq!(certificate.artifact.hole_count(), 0);
    assert!(!certificate.artifact.query_collapsed());
    assert_eq!(certificate.artifact.assumed_lemma_premises(), 0);
    assert!(certificate.report_only);
    assert_eq!(certificate.lowering_witness, "none");
    // Preserve the actual consumer artifact under --nocapture, through its
    // existing codec, so external replay uses these original bytes.
    println!(
        "signed native body artifact {}",
        serde_json::to_string(&certificate.artifact).unwrap()
    );
}

#[test]
fn signed_native_i8_retains_a_strict_artifact_bound_to_the_original_body() {
    assert_signed_native_body_artifact(fixtures::guarded_checked_add_i8());
}

#[test]
fn signed_native_i16_retains_a_strict_artifact_bound_to_the_original_body() {
    assert_signed_native_body_artifact(fixtures::guarded_wide_add(
        trust_ir::Ty::I16,
        100,
        true,
        "guarded_add_i16",
    ));
}

#[test]
fn signed_native_guard_changes_still_return_counterexamples() {
    for fixture in [
        fixtures::guarded_wide_add(trust_ir::Ty::I8, 100, true, "loose_guard_i8"),
        fixtures::guarded_wide_add(trust_ir::Ty::I16, 30_000, true, "loose_guard_i16"),
        fixtures::unguarded_checked_op(
            "unguarded_add_i8",
            trust_ir::OverflowOp::AddOverflow,
            trust_ir::Ty::I8,
        ),
        fixtures::unguarded_checked_op(
            "unguarded_add_i16",
            trust_ir::OverflowOp::AddOverflow,
            trust_ir::Ty::I16,
        ),
    ] {
        let report = TrustVcTrustEngine::new()
            .discharge_trust_ir_function(
                &fixture.module,
                fixture.function(),
                &TrustIrBodyOptions {
                    proof_policy: TrustProofPolicy::AttachReplayableCertificates,
                },
            )
            .expect("the changed native body is reportable");
        assert_eq!(report.obligations.len(), 1);
        assert!(
            matches!(
                report.obligations[0].verdict,
                TrustIrBodyVerdict::Refuted { .. }
            ),
            "{}: {report:?}",
            fixture.name
        );
    }
}
