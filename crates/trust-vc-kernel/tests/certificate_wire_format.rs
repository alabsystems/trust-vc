// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_kernel::export::{export_certificate, ExportFormat};
use trust_vc_kernel::format::{TrustVcProofCertificate, CERTIFICATE_VERSION};

fn certificate() -> TrustVcProofCertificate {
    let json = serde_json::json!({
        "version": CERTIFICATE_VERSION,
        "source_hash": vec![0x11u8; 32],
        "vc_hash": vec![0x22u8; 32],
        "input_clauses": [
            { "id": 1, "literals": [1] },
            { "id": 2, "literals": [-1, 2] }
        ],
        "resolution_steps": [
            {
                "result_id": 20,
                "antecedent_a": 1,
                "antecedent_b": 10,
                "pivot": 1,
                "result_literals": [2]
            }
        ],
        "theory_lemmas": [
            {
                "id": 10,
                "kind": "Euf",
                "literals": [-1, 2],
                "justification": "congruence closure"
            }
        ],
        "empty_clause_id": 20,
        "metadata": {
            "timestamp": "2026-03-29T12:00:00Z",
            "trust_vc_version": "1.0.0",
            "solver_version": "ay-dpll 0.1.0"
        }
    });
    serde_json::from_value(json).expect("wire-format certificate JSON should parse")
}

#[test]
fn test_to_json_matches_export_json() {
    let cert = certificate();
    let direct = cert.to_json().expect("direct JSON");
    let exported = export_certificate(&cert, ExportFormat::Json).expect("exported JSON");
    assert_eq!(direct.as_bytes(), exported);
}

#[test]
fn test_to_bytes_matches_export_binary() {
    let cert = certificate();
    let direct = cert.to_bytes().expect("direct binary");
    let exported = export_certificate(&cert, ExportFormat::Binary).expect("exported binary");
    assert_eq!(direct, exported);
}
