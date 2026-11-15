//! A DECODED discharge-mode request report carries no authority.
//!
//! The wire report deliberately carries no witness bindings, so nothing a
//! decoder holds can re-check a claimed outcome. Measured at a9edcdd4 (r5
//! re-verification) on fixtures `unguarded_checked_add_u8` (refuted),
//! `guarded_checked_add_u8` (advisory) and `two_checks_chain` (advisory):
//! re-folding the declared outcomes into the declared verdict only caught an
//! INCONSISTENT edit, so a CONSISTENT one (outcomes and verdict edited
//! together) decoded —
//! * refuted → advisory / unknown / not-answerable: exit Refuted → Unknown;
//! * advisory → refuted: a FABRICATED refutation, exit Unknown → Refuted;
//! * a named obligation list `[0, 0]` and consistently renamed ids (`0` →
//!   `4242` in both lists) decoded too.
//!
//! The property pinned here uses only APIs present at a9edcdd4, so it runs
//! (and fails) there: no decodable payload — honest, edited, renamed — decodes
//! to a report whose exit class is `Ok` or `Refuted`, and a named list that
//! repeats an id is refused. A verdict for a decoded report comes back only by
//! re-discharging the request it is bound to (`native_discharge_rejudge.rs`,
//! which needs the new API).

#[path = "support/trust_ir_body_fixtures.rs"]
mod fixtures;

use fixtures::{Fixture, FIXTURE_FUNCTION};
use trust_ir::request::{NativeRequestId, TrustVcNativeRequest, TrustVcVerificationMode};
use trust_vc_trust_engine::{
    TrustVcNativeTrustIrAdvisoryOutcome, TrustVcNativeTrustIrDischargeAnswer,
    TrustVcNativeTrustIrDischargeObligation, TrustVcNativeTrustIrExitClass,
    TrustVcNativeTrustIrRequestReport, TrustVcTrustEngine,
};

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

/// Edits that name an obligation twice: never a report a producer writes.
fn duplicate_edits() -> Vec<Edit> {
    vec![
        (
            "named list duplicated [a, a]",
            Box::new(|j| {
                let first = j["obligations"][0].clone();
                j["obligations"] = serde_json::json!([first.clone(), first]);
            }),
        ),
        (
            "named list [a, a], answer entry duplicated",
            Box::new(|j| {
                let first = j["obligations"][0].clone();
                j["obligations"] = serde_json::json!([first.clone(), first]);
                let entry = j["advisory_discharge"]["obligations"][0].clone();
                j["advisory_discharge"]["obligations"] = serde_json::json!([entry.clone(), entry]);
            }),
        ),
    ]
}

fn fixtures_under_test() -> Vec<Fixture> {
    vec![
        fixtures::unguarded_checked_add_u8(),
        fixtures::guarded_checked_add_u8(),
        fixtures::two_checks_chain(),
    ]
}

/// No decodable payload carries authority: its exit class is never `Ok` and
/// never `Refuted`; and a named list that repeats an id is refused.
#[test]
fn no_decoded_discharge_report_carries_authority() {
    let mut authority = Vec::new();
    let mut duplicates_decoded = Vec::new();
    let mut decoded = 0usize;
    for fixture in fixtures_under_test() {
        let report = honest(&fixture);
        println!(
            "HONEST {}: verdict={:?} exit={:?} obligations={}",
            fixture.name,
            report.verdict(),
            report.verdict().exit_class(),
            fixture.obligations.len()
        );
        for (label, edit) in edits() {
            let mut json = serde_json::to_value(&report).expect("serializes");
            edit(&mut json);
            match serde_json::from_value::<TrustVcNativeTrustIrRequestReport>(json) {
                Ok(d) => {
                    decoded += 1;
                    let exit = d.verdict().exit_class();
                    println!(
                        "WIRE {}[{label}] DECODED verdict={:?} exit={exit:?}",
                        fixture.name,
                        d.verdict()
                    );
                    if matches!(
                        exit,
                        TrustVcNativeTrustIrExitClass::Ok | TrustVcNativeTrustIrExitClass::Refuted
                    ) {
                        authority.push(format!(
                            "{}[{label}] -> {:?} ({exit:?})",
                            fixture.name,
                            d.verdict()
                        ));
                    }
                }
                Err(e) => println!("WIRE {}[{label}] REFUSED: {e}", fixture.name),
            }
        }
        for (label, edit) in duplicate_edits() {
            let mut json = serde_json::to_value(&report).expect("serializes");
            edit(&mut json);
            match serde_json::from_value::<TrustVcNativeTrustIrRequestReport>(json) {
                Ok(d) => {
                    println!(
                        "WIRE {}[{label}] DECODED verdict={:?}",
                        fixture.name,
                        d.verdict()
                    );
                    duplicates_decoded.push(format!("{}[{label}]", fixture.name));
                }
                Err(e) => println!("WIRE {}[{label}] REFUSED: {e}", fixture.name),
            }
        }
    }
    println!("SUMMARY decoded={decoded} authority={authority:#?}");
    println!("SUMMARY duplicates_decoded={duplicates_decoded:?}");
    assert!(
        decoded > 0,
        "nothing decoded: the property would hold vacuously"
    );
    assert!(
        authority.is_empty() && duplicates_decoded.is_empty(),
        "a decoded discharge report carried authority read off the wire: {authority:#?}; \
         a repeated obligation id decoded: {duplicates_decoded:?}"
    );
}

/// No DECODE PATH reads an outcome back: a standalone
/// [`TrustVcNativeTrustIrDischargeAnswer`], a standalone
/// [`TrustVcNativeTrustIrDischargeObligation`] and a report's answer all
/// decode every outcome `NotJudged`, whatever the payload labels it.
///
/// Measured at 50b27076 (r9 verifier): the report erased its answer's
/// outcomes, but the answer and obligation types are public `Deserialize`
/// types, and a standalone decode of an answer whose outcomes were all edited
/// to `refuted` kept them (`obligations()[i].outcome() == Refuted`).
#[test]
fn no_decode_path_reads_a_discharge_outcome() {
    let mut kept = Vec::new();
    let mut decoded = 0usize;
    for fixture in fixtures_under_test() {
        let report = honest(&fixture);
        for label in [
            "refuted",
            "refuted_ignoring_prior_asserts",
            "discharged_advisory",
            "unknown",
            "not_answerable",
        ] {
            let mut json = serde_json::to_value(&report).expect("serializes");
            all_outcomes(&mut json, label);
            let mut outcomes = Vec::new();
            let answer: TrustVcNativeTrustIrDischargeAnswer =
                serde_json::from_value(json["advisory_discharge"].clone())
                    .expect("an answer decodes");
            outcomes.extend(answer.obligations().iter().map(|o| ("answer", o.outcome())));
            for entry in json["advisory_discharge"]["obligations"]
                .as_array()
                .expect("entries")
            {
                let obligation: TrustVcNativeTrustIrDischargeObligation =
                    serde_json::from_value(entry.clone()).expect("an obligation decodes");
                outcomes.push(("obligation", obligation.outcome()));
            }
            if let Ok(decoded_report) =
                serde_json::from_value::<TrustVcNativeTrustIrRequestReport>(json.clone())
            {
                let answer = decoded_report
                    .advisory_discharge()
                    .expect("a discharge report");
                outcomes.extend(answer.obligations().iter().map(|o| ("report", o.outcome())));
            }
            for (path, outcome) in outcomes {
                decoded += 1;
                println!(
                    "WIRE {}[{label}] {path} DECODED outcome={outcome:?}",
                    fixture.name
                );
                if outcome != TrustVcNativeTrustIrAdvisoryOutcome::NotJudged {
                    kept.push(format!("{}[{label}] {path}: {outcome:?}", fixture.name));
                }
            }
        }
    }
    assert!(
        decoded > 0,
        "nothing decoded: the property would hold vacuously"
    );
    assert!(
        kept.is_empty(),
        "a decoded outcome was read off the wire: {kept:#?}"
    );
}
