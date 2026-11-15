//! Per-assertion proof certificates for the direct MIR-memory lane (#2654),
//! pinned against the payload shape Trust's compiler producer actually emits.
//!
//! The units below are byte-faithful reconstructions of what
//! `crates/trust-mir-extract/src/verifier_api.rs`'s
//! `trust_vc_mir_memory_proof_unit_payload` writes into the
//! `trust_vc.mir_memory.proof_unit` obligation metadata. The existing coverage
//! in `mir_memory.rs` uses hand-authored units whose contradiction variable is a
//! SIGNATURE PARAM; the compiler's units differ structurally (the contradiction
//! variable is a VERIFIER VARIABLE, the params carry the reference locals, and
//! ownership state is derived from every MIR local). That difference is the
//! reason three separate investigations concluded "trust-vc verifies the unit
//! but mints no certificate" without ever running the compiler's shape.
//!
//! Two facts are pinned here, and they are opposite halves of the same
//! boundary:
//!
//!  * a compiler-shaped unit whose obligation predicate is a real proposition
//!    yields exactly ONE release-admissible certificate PER ASSERTION, strict-
//!    and kernel-verified with zero trust steps and zero holes; and
//!  * a compiler-shaped unit whose obligation predicate is the literal `true`
//!    is REFUSED. That is not a defect to fix here. The producer lowers a
//!    `Formula::Bool(false)` bad-state VC to the proposition `true`
//!    (`TrustVcFormulaLowering::negated_vc_formula`), the assertion is
//!    const-folded before it ever reaches the solver, and there is therefore no
//!    refutation of it in existence. Minting a certificate for that row would
//!    be a proof claim about something nobody proved. If this half ever needs
//!    to change, the change belongs in the producer — give the row a real
//!    proposition — never here.

#![cfg(feature = "proof-certificates")]

use trust_vc_trust_engine::{
    TrustEngineError, TrustMirMemoryProofUnit, TrustOutcome, TrustProofPolicy,
    TrustReleaseProofAdmissionStatus, TrustUnitReport, TrustVcTrustEngine,
};

const MATH_INT: &str = r#"{"kind":"math_int"}"#;

/// `not(and(v < 16, v >= 16))` — the QF_LIA validity whose negation is the
/// Farkas-refutable contradiction the lane's release gate accepts.
fn contradiction_predicate(var: &str) -> String {
    format!(
        r#"{{"kind":"not","expr":{{"kind":"logic","op":"and",
             "left":{{"kind":"compare","op":"lt",
               "left":{{"kind":"variable","name":"{var}","sort":{MATH_INT}}},
               "right":{{"kind":"int_literal","value":"16","sort":{MATH_INT}}}}},
             "right":{{"kind":"compare","op":"ge",
               "left":{{"kind":"variable","name":"{var}","sort":{MATH_INT}}},
               "right":{{"kind":"int_literal","value":"16","sort":{MATH_INT}}}}}}}}}"#
    )
}

/// The compiler producer's unit for `demo::checked_transfer`: one `&u32` param
/// local plus the `_0` return local in ownership state, a shared borrow for the
/// reference local, and the predicate's variables declared as VERIFIER
/// variables because they are not MIR locals.
fn compiler_unit(verifier_variables: &str, obligations: &str) -> TrustMirMemoryProofUnit {
    let payload = format!(
        r#"{{
          "source_id": "trust-mir-extract:demo__checked_transfer",
          "unit_id": "demo::checked_transfer",
          "display_name": "checked_transfer",
          "native_context": {{
            "function_signature": {{
              "name": "demo::checked_transfer",
              "params": [{{"name":"account","sort":{{"kind":"bit_vector","width":32,"signed":false}}}}],
              "return_sort": {{"kind":"bool"}}
            }},
            "ownership": {{
              "places": [
                {{"place":"_0","sort":{{"kind":"bool"}}}},
                {{"place":"account","sort":{{"kind":"bit_vector","width":32,"signed":false}}}}
              ],
              "borrows": [{{"region":"r1","place":"account","kind":"shared"}}]
            }}
          }},
          {verifier_variables}
          "obligations": [{obligations}],
          "metadata": {{"producer":"trust-mir-extract","vc_kind":"aliasing_violation"}}
        }}"#
    );
    serde_json::from_str(&payload).expect("compiler producer payload parses as the consumer type")
}

fn verify(unit: &TrustMirMemoryProofUnit) -> Result<TrustUnitReport, TrustEngineError> {
    TrustVcTrustEngine::new()
        .verify_mir_memory_unit(unit, TrustProofPolicy::RequireReleaseAdmissibleCertificate)
}

/// Every artifact must be a real, independently re-checked refutation.
fn assert_release_admissible(report: &TrustUnitReport, expected_assertion_ids: &[&str]) {
    assert!(
        matches!(report.outcome(), TrustOutcome::Verified),
        "{:?}",
        report.outcome()
    );
    assert_eq!(
        report.proof_artifacts().len(),
        expected_assertion_ids.len(),
        "one certificate per assertion is the whole contract of #2654: {report:#?}"
    );
    for (artifact, expected) in report.proof_artifacts().iter().zip(expected_assertion_ids) {
        assert_eq!(
            artifact.assertion_obligation_ids(),
            &[(*expected).to_string()],
            "each certificate must be bound to exactly the assertion it refutes"
        );
        assert!(
            artifact.strict_verified(),
            "strict checker must accept the certificate"
        );
        assert!(
            artifact.kernel_verified(),
            "the trust-vc kernel must re-check the certificate"
        );
        assert_eq!(
            artifact.trust_count(),
            0,
            "a release-admissible proof has no trusted steps"
        );
        assert_eq!(
            artifact.hole_count(),
            0,
            "a release-admissible proof has no holes"
        );
        assert_eq!(
            artifact.release_admission().status(),
            TrustReleaseProofAdmissionStatus::Admissible,
            "{:?}",
            artifact.release_admission()
        );
        assert!(
            !artifact.payload().is_empty(),
            "the certificate carries its own replayable text"
        );
    }
}

#[test]
fn compiler_shaped_unit_mints_one_release_admissible_certificate_per_assertion() {
    let unit = compiler_unit(
        &format!(r#""verifier_variables": [{{"name":"amount","sort":{MATH_INT}}}],"#),
        &format!(
            r#"{{"id":"vc:demo__checked_transfer:ownership:1","predicate":{},
                 "location":"demo.rs:11:1"}}"#,
            contradiction_predicate("amount")
        ),
    );

    let report = verify(&unit).expect("the compiler's own payload shape is release-admissible");
    assert_release_admissible(&report, &["vc:demo__checked_transfer:ownership:1"]);
}

#[test]
fn compiler_shaped_unit_certifies_each_assertion_separately() {
    let unit = compiler_unit(
        &format!(
            r#""verifier_variables": [
                 {{"name":"amount","sort":{MATH_INT}}},
                 {{"name":"other","sort":{MATH_INT}}}
               ],"#
        ),
        &format!(
            r#"{{"id":"vc:demo__checked_transfer:ownership:1","predicate":{}}},
               {{"id":"vc:demo__checked_transfer:ownership:2","predicate":{}}}"#,
            contradiction_predicate("amount"),
            contradiction_predicate("other")
        ),
    );

    let report = verify(&unit).expect("two independent contradictions are both refutable");
    assert_release_admissible(
        &report,
        &[
            "vc:demo__checked_transfer:ownership:1",
            "vc:demo__checked_transfer:ownership:2",
        ],
    );
    let payloads: Vec<&str> = report
        .proof_artifacts()
        .iter()
        .map(|artifact| artifact.payload())
        .collect();
    assert_ne!(
        payloads[0], payloads[1],
        "a shared unit-level refutation is NOT per-assertion evidence; the two \
         certificates must be distinct refutations of distinct assertions"
    );
}

/// The fail-closed half. Do NOT "fix" this by synthesizing a certificate.
#[test]
fn a_const_folded_literal_true_obligation_is_refused_not_certified() {
    let unit = compiler_unit(
        "",
        r#"{"id":"vc:demo__checked_transfer:ownership:1",
             "predicate":{"kind":"bool_literal","value":true}}"#,
    );

    let error = verify(&unit)
        .expect_err("an assertion that never reached the solver has no refutation to certify");
    assert!(
        matches!(
            error,
            TrustEngineError::ReplayableProofCertificateUnavailable {
                policy: TrustProofPolicy::RequireReleaseAdmissibleCertificate,
                ..
            }
        ),
        "{error:?}"
    );
}
