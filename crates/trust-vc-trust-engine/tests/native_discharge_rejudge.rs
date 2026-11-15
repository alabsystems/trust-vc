//! Re-deriving a verdict for a DECODED discharge-mode report, and the
//! producer gate that keeps a report's obligation list a set.
//!
//! A decoded discharge report is `NotJudged`
//! (`native_wire_discharge_authority.rs`). A verdict comes back only through
//! `TrustVcTrustEngine::rejudge_native_trust_ir_discharge_report`, which binds
//! the report to the request and module the caller holds — refusing a report
//! whose ids were consistently renamed (`0` -> `4242`), or that answers
//! another request — and then discharges the request afresh, so the verdict is
//! the honest one whatever the report claimed. New API: this file does not
//! compile before it.

#[path = "support/trust_ir_body_fixtures.rs"]
mod fixtures;

use fixtures::{Fixture, FIXTURE_FUNCTION};
use trust_ir::request::{NativeRequestId, TrustVcNativeRequest, TrustVcVerificationMode};
use trust_vc_trust_engine::{TrustVcNativeTrustIrRequestReport, TrustVcTrustEngine};

fn request(fixture: &Fixture) -> TrustVcNativeRequest {
    TrustVcNativeRequest {
        id: NativeRequestId::new(0),
        mode: TrustVcVerificationMode::DischargeProofObligations,
        obligations: fixture.obligations.clone(),
        certificates: Vec::new(),
        lineage_roots: Vec::new(),
        options: Default::default(),
        diagnostics: Default::default(),
        provenance: Default::default(),
        function: Some(FIXTURE_FUNCTION),
    }
}

fn honest(fixture: &Fixture) -> TrustVcNativeTrustIrRequestReport {
    TrustVcTrustEngine::new()
        .discharge_native_trust_ir_request(&fixture.module, &request(fixture))
        .expect("the fixture reaches a report")
}

/// The producer's fold, over declared outcome labels.
fn fold(outcomes: &[&str]) -> &'static str {
    if outcomes
        .iter()
        .any(|o| *o == "refuted" || *o == "refuted_ignoring_prior_asserts")
    {
        "discharge_refuted"
    } else if !outcomes.is_empty() && outcomes.iter().all(|o| *o == "discharged_advisory") {
        "discharged_advisory"
    } else {
        "discharge_not_answerable"
    }
}

/// Set every outcome to `label` and the verdict to their fold: a CONSISTENT
/// edit, which the re-fold cannot see.
fn all_outcomes(json: &mut serde_json::Value, label: &str) {
    let mut labels = Vec::new();
    for o in json["advisory_discharge"]["obligations"]
        .as_array_mut()
        .expect("answer obligations")
    {
        o["outcome"] = serde_json::json!(label);
        labels.push(label);
    }
    json["verdict"] = serde_json::json!(fold(&labels));
}

/// Set the FIRST outcome to `label`, keep the rest, and re-fold the verdict.
fn first_outcome(json: &mut serde_json::Value, label: &str) {
    let obligations = json["advisory_discharge"]["obligations"]
        .as_array_mut()
        .expect("answer obligations");
    obligations[0]["outcome"] = serde_json::json!(label);
    let labels: Vec<String> = obligations
        .iter()
        .map(|o| o["outcome"].as_str().unwrap_or("").to_string())
        .collect();
    let refs: Vec<&str> = labels.iter().map(String::as_str).collect();
    json["verdict"] = serde_json::json!(fold(&refs));
}

/// Rename every obligation id consistently (`id` → `id + 4242`) in both the
/// named list and the answer.
fn renamed(json: &mut serde_json::Value) {
    for id in json["obligations"].as_array_mut().expect("named") {
        *id = serde_json::json!(id.as_u64().expect("id") + 4242);
    }
    for o in json["advisory_discharge"]["obligations"]
        .as_array_mut()
        .expect("answer obligations")
    {
        o["obligation_id"] = serde_json::json!(o["obligation_id"].as_u64().expect("id") + 4242);
    }
}

type Edit = (&'static str, Box<dyn Fn(&mut serde_json::Value)>);

fn edits() -> Vec<Edit> {
    let mut v: Vec<Edit> = vec![("verbatim", Box::new(|_| {}))];
    for label in [
        "refuted",
        "refuted_ignoring_prior_asserts",
        "discharged_advisory",
        "unknown",
        "not_answerable",
    ] {
        v.push((
            match label {
                "refuted" => "all outcomes -> refuted (consistent)",
                "refuted_ignoring_prior_asserts" => {
                    "all outcomes -> refuted_ignoring_prior_asserts (consistent)"
                }
                "discharged_advisory" => "all outcomes -> discharged_advisory (consistent)",
                "unknown" => "all outcomes -> unknown (consistent)",
                _ => "all outcomes -> not_answerable (consistent)",
            },
            Box::new(move |j| all_outcomes(j, label)),
        ));
    }
    v.push((
        "first outcome -> refuted (consistent)",
        Box::new(|j| first_outcome(j, "refuted")),
    ));
    v.push((
        "first outcome -> discharged_advisory (consistent)",
        Box::new(|j| first_outcome(j, "discharged_advisory")),
    ));
    v.push(("ids renamed +4242 (consistent)", Box::new(renamed)));
    v.push((
        "ids renamed +4242, all outcomes -> refuted (consistent)",
        Box::new(|j| {
            renamed(j);
            all_outcomes(j, "refuted");
        }),
    ));
    v
}

fn fixtures_under_test() -> Vec<Fixture> {
    vec![
        fixtures::unguarded_checked_add_u8(),
        fixtures::guarded_checked_add_u8(),
        fixtures::two_checks_chain(),
    ]
}

/// The only way back to a verdict: re-discharge the request the report is
/// bound to. The fresh verdict is the honest one whatever the report claims;
/// a report not bound to the request (renamed ids, another request) is
/// refused.
#[test]
fn rejudging_rederives_from_the_request_and_refuses_what_it_does_not_answer() {
    let engine = TrustVcTrustEngine::new();
    for fixture in fixtures_under_test() {
        let request = request(&fixture);
        let report = honest(&fixture);
        let honest_verdict = report.verdict();

        // Verbatim, and consistently edited to every label: decoded NotJudged,
        // re-judged to the honest verdict.
        for (label, edit) in edits() {
            if label.starts_with("ids renamed") {
                continue;
            }
            let mut json = serde_json::to_value(&report).expect("serializes");
            edit(&mut json);
            let decoded: TrustVcNativeTrustIrRequestReport =
                serde_json::from_value(json).expect("a consistent edit decodes");
            assert_eq!(
                decoded.verdict(),
                trust_vc_trust_engine::TrustVcNativeTrustIrVerdict::NotJudged,
                "{}[{label}]",
                fixture.name
            );
            let rejudged = engine
                .rejudge_native_trust_ir_discharge_report(&fixture.module, &request, &decoded)
                .unwrap_or_else(|e| panic!("{}[{label}] must re-judge: {e}", fixture.name));
            assert_eq!(
                rejudged.verdict(),
                honest_verdict,
                "{}[{label}]: re-judged from the request, not the report",
                fixture.name
            );
        }

        // Renamed ids: decodes (no authority), but is bound to no obligation
        // the request names, so re-judging refuses it.
        for (label, edit) in edits() {
            if !label.starts_with("ids renamed") {
                continue;
            }
            let mut json = serde_json::to_value(&report).expect("serializes");
            edit(&mut json);
            let decoded: TrustVcNativeTrustIrRequestReport =
                serde_json::from_value(json).expect("a consistent rename decodes");
            let refused = engine.rejudge_native_trust_ir_discharge_report(
                &fixture.module,
                &request,
                &decoded,
            );
            assert!(
                matches!(
                    refused,
                    Err(trust_vc_trust_engine::TrustEngineError::NativeTrustIrDischargeReportNotBound { .. })
                ),
                "{}[{label}] must be refused, got {refused:?}",
                fixture.name
            );
        }

        // Another request (a different id): refused.
        let mut other = request.clone();
        other.id = NativeRequestId::new(7);
        let decoded: TrustVcNativeTrustIrRequestReport =
            serde_json::from_value(serde_json::to_value(&report).expect("ser")).expect("decodes");
        assert!(
            engine
                .rejudge_native_trust_ir_discharge_report(&fixture.module, &other, &decoded)
                .is_err(),
            "{}: a report for request 0 must not re-judge against request 7",
            fixture.name
        );
    }
}

/// The producer refuses a request that names one obligation twice, so every
/// report it writes names a set.
#[test]
fn a_discharge_request_naming_an_obligation_twice_is_refused() {
    let fixture = fixtures::guarded_checked_add_u8();
    let mut request = request(&fixture);
    let first = request.obligations[0];
    request.obligations = vec![first, first];
    let refused =
        TrustVcTrustEngine::new().discharge_native_trust_ir_request(&fixture.module, &request);
    assert!(
        matches!(
            refused,
            Err(trust_vc_trust_engine::TrustEngineError::NativeTrustIrDischargeRequestDuplicateObligation { .. })
        ),
        "got {refused:?}"
    );
}
