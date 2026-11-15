//! Request/bundle reports edited on the wire —
//! obligations, evidence, verdicts, modes — for both certificate and
//! discharge modes. Uses only APIs present at 8bbef1af and 2f792110.
//!
//! Two properties:
//! * ADMISSION — no edited payload decodes to a report whose verdict
//!   `is_ok()` (a clean pass);
//! * RE-DERIVATION — a decoded discharge verdict is never read off the wire:
//!   it is `not_judged` whatever the payload declares (it was the fold of the
//!   payload's own declared outcomes, which a consistent edit of outcomes and
//!   verdict passes — native_wire_discharge_authority.rs), so an edit cannot
//!   move a report's exit class, e.g. launder a refutation into "unknown".

#[path = "support/admission_baseline.rs"]
mod admission_baseline;
#[path = "support/trust_ir_body_fixtures.rs"]
mod fixtures;

use admission_baseline::native_bundle_fixture;
use fixtures::FIXTURE_FUNCTION;
use trust_ir::request::{NativeRequestId, TrustVcNativeRequest, TrustVcVerificationMode};
use trust_vc_trust_engine::{
    TrustVcNativeTrustIrBundleReport, TrustVcNativeTrustIrRequestReport,
    TrustVcNativeTrustIrVerdict, TrustVcTrustEngine,
};

type WireEdit<'a> = (&'a str, Box<dyn Fn(&mut serde_json::Value)>);

fn reencoded<T: serde::de::DeserializeOwned>(
    value: &impl serde::Serialize,
    edit: impl FnOnce(&mut serde_json::Value),
) -> Result<T, serde_json::Error> {
    let mut json = serde_json::to_value(value).expect("serializes");
    edit(&mut json);
    serde_json::from_value(json)
}

fn refuted_discharge_report() -> TrustVcNativeTrustIrRequestReport {
    let fixture = fixtures::unguarded_checked_add_u8();
    let request = TrustVcNativeRequest {
        id: NativeRequestId::new(0),
        mode: TrustVcVerificationMode::DischargeProofObligations,
        obligations: fixture.obligations.clone(),
        certificates: Vec::new(),
        lineage_roots: Vec::new(),
        options: Default::default(),
        diagnostics: Default::default(),
        provenance: Default::default(),
        function: Some(FIXTURE_FUNCTION),
    };
    TrustVcTrustEngine::new()
        .discharge_native_trust_ir_request(&fixture.module, &request)
        .expect("reaches a report")
}

fn folded(json: &serde_json::Value) -> &'static str {
    let outcomes: Vec<String> = json["advisory_discharge"]["obligations"]
        .as_array()
        .map(|a| {
            a.iter()
                .map(|o| o["outcome"].as_str().unwrap_or("").to_string())
                .collect()
        })
        .unwrap_or_default();
    if outcomes
        .iter()
        .any(|o| o == "refuted" || o == "refuted_ignoring_prior_asserts")
    {
        "discharge_refuted"
    } else if !outcomes.is_empty() && outcomes.iter().all(|o| o == "discharged_advisory") {
        "discharged_advisory"
    } else {
        "discharge_not_answerable"
    }
}

/// ADMISSION: no edited payload decodes as a clean pass.
#[test]
fn no_wire_edit_decodes_as_a_pass() {
    let (admitted, _) = probe();
    assert!(
        admitted.is_empty(),
        "an edited payload decoded as a pass: {admitted:?}"
    );
}

/// RE-DERIVATION: a discharge report's decoded verdict is never read off the
/// wire. It was the fold of the report's own declared answer (a9edcdd4),
/// which a CONSISTENT edit of outcomes and verdict passes; a decoded
/// discharge report is now `not_judged` whatever it declares
/// (native_wire_discharge_authority.rs), so no wire edit moves its exit
/// class (Refuted -> Unknown, or Unknown -> Refuted).
#[test]
fn a_discharge_verdict_is_rederived_on_decode() {
    let (_, not_rederived) = probe();
    assert!(
        not_rederived.is_empty(),
        "a decoded discharge verdict disagrees with its own answer: {not_rederived:?}"
    );
}

fn probe() -> (Vec<String>, Vec<String>) {
    let mut admitted = Vec::new();
    let mut not_rederived = Vec::new();

    // --- Discharge mode: verdict edits over a REFUTED answer. ---
    let refuted = refuted_discharge_report();
    assert_eq!(
        refuted.verdict(),
        TrustVcNativeTrustIrVerdict::DischargeRefuted
    );
    let edits: Vec<WireEdit<'_>> = vec![
        ("verbatim", Box::new(|_| {})),
        (
            "verdict->not_answerable",
            Box::new(|j| j["verdict"] = serde_json::json!("discharge_not_answerable")),
        ),
        (
            "verdict->discharged_advisory",
            Box::new(|j| j["verdict"] = serde_json::json!("discharged_advisory")),
        ),
        (
            "outcomes emptied, verdict->discharged_advisory",
            Box::new(|j| {
                j["advisory_discharge"]["obligations"] = serde_json::json!([]);
                j["verdict"] = serde_json::json!("discharged_advisory");
            }),
        ),
        (
            "request obligations emptied",
            Box::new(|j| j["obligations"] = serde_json::json!([])),
        ),
        (
            "verdict->certificates_admitted",
            Box::new(|j| j["verdict"] = serde_json::json!("certificates_admitted")),
        ),
        (
            "mode->import, discharge removed, verdict->certificates_admitted",
            Box::new(|j| {
                j["mode"] = serde_json::json!("import_proof_certificates");
                j.as_object_mut().expect("obj").remove("advisory_discharge");
                j["verdict"] = serde_json::json!("certificates_admitted");
            }),
        ),
    ];
    for (label, edit) in &edits {
        let mut json = serde_json::to_value(&refuted).expect("ser");
        edit(&mut json);
        // The content folds to `content`; a decoded discharge report is
        // `not_judged` whatever it folds to.
        let content = folded(&json);
        let want = "not_judged";
        let decoded: Result<TrustVcNativeTrustIrRequestReport, _> =
            serde_json::from_value(json.clone());
        match decoded {
            Ok(d) => {
                let got = serde_json::to_value(d.verdict()).expect("ser");
                println!(
                    "WIRE discharge[{label}] DECODED verdict={got} exit={:?} is_ok={} (content folds to {content}; decoded must be {want})",
                    d.verdict().exit_class(),
                    d.verdict().is_ok()
                );
                if d.verdict().is_ok() {
                    admitted.push(format!("discharge[{label}]"));
                }
                if json.get("advisory_discharge").is_some() && got != serde_json::json!(want) {
                    not_rederived.push(format!("discharge[{label}]: {got} vs {want}"));
                }
            }
            Err(e) => println!("WIRE discharge[{label}] REFUSED: {e}"),
        }
    }

    // --- Certificate mode: a report the engine genuinely ADMITTED, then edits. ---
    let real = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&native_bundle_fixture())
        .expect("baseline is consumable");
    assert_eq!(
        real.verdict(),
        TrustVcNativeTrustIrVerdict::CertificatesAdmitted
    );
    let honest = serde_json::to_value(&real).expect("the admitted report serializes");
    let bundle_edits: Vec<WireEdit<'_>> = vec![
        ("verbatim", Box::new(|_| {})),
        (
            "obligations emptied",
            Box::new(|j| {
                for r in j["requests"].as_array_mut().expect("requests") {
                    r["obligations"] = serde_json::json!([]);
                }
            }),
        ),
        (
            "obligations duplicated",
            Box::new(|j| {
                for r in j["requests"].as_array_mut().expect("requests") {
                    if let Some(first) =
                        r["obligations"].as_array().and_then(|a| a.first()).cloned()
                    {
                        r["obligations"] = serde_json::json!([first.clone(), first]);
                    }
                }
            }),
        ),
        (
            "evidence stripped",
            Box::new(|j| {
                for r in j["requests"].as_array_mut().expect("requests") {
                    r["proof_evidence"] = serde_json::json!([]);
                }
            }),
        ),
        (
            "request duplicated",
            Box::new(|j| {
                let r = j["requests"][0].clone();
                j["requests"].as_array_mut().expect("requests").push(r);
            }),
        ),
        (
            "requests emptied",
            Box::new(|j| j["requests"] = serde_json::json!([])),
        ),
    ];
    for (label, edit) in &bundle_edits {
        let decoded = reencoded::<TrustVcNativeTrustIrBundleReport>(&honest, |j| edit(j));
        match decoded {
            Ok(d) => {
                println!(
                    "WIRE bundle[{label}] DECODED verdict={:?} is_ok={} artifacts_accepted={}",
                    d.verdict(),
                    d.verdict().is_ok(),
                    d.admit_native_proof_artifacts()
                        .iter()
                        .filter(|a| a.admission().is_accepted())
                        .count()
                );
                if d.verdict().is_ok()
                    || d.admit_native_proof_artifacts()
                        .iter()
                        .any(|a| a.admission().is_accepted())
                {
                    admitted.push(format!("bundle[{label}]"));
                }
            }
            Err(e) => println!("WIRE bundle[{label}] REFUSED: {e}"),
        }
    }
    println!("SUMMARY admitted={admitted:?}");
    println!("SUMMARY not_rederived={not_rederived:?}");
    (admitted, not_rederived)
}
