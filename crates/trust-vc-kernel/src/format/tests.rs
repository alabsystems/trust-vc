// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

fn minimal_certificate() -> TrustVcProofCertificate {
    TrustVcProofCertificate {
        version: CERTIFICATE_VERSION,
        source_hash: sha256(b"fn main() {}"),
        vc_hash: sha256(b"(assert (not true))"),
        resolution_steps: vec![],
        theory_lemmas: vec![],
        input_clauses: vec![WireClause {
            id: WireClauseId(0),
            literals: vec![Literal(1), Literal(-2)],
        }],
        empty_clause_id: WireClauseId(0),
        metadata: CertificateMetadata {
            timestamp: "2026-03-28T00:00:00Z".to_string(),
            trust_vc_version: "1.0.0".to_string(),
            solver_version: "ay-dpll 0.1.0".to_string(),
        },
    }
}

fn rich_certificate(num_steps: usize) -> TrustVcProofCertificate {
    let input_clauses = (0..3)
        .map(|i| WireClause {
            id: WireClauseId(i),
            literals: vec![Literal(i as i64 + 1), Literal(-(i as i64 + 2))],
        })
        .collect();

    let theory_lemmas = vec![WireTheoryLemma {
        id: WireClauseId(100),
        kind: TheoryLemmaKind::Euf,
        literals: vec![Literal(1), Literal(-3)],
        justification: Some("congruence closure".to_string()),
    }];

    let resolution_steps = (0..num_steps)
        .map(|i| WireResolutionStep {
            result_id: WireClauseId(1000 + i as u64),
            antecedent_a: WireClauseId(0),
            antecedent_b: WireClauseId(1),
            pivot: Literal(1),
            result_literals: vec![Literal(-2)],
        })
        .collect::<Vec<_>>();

    let empty_clause_id = resolution_steps
        .last()
        .map(|step| step.result_id)
        .unwrap_or(WireClauseId(0));

    TrustVcProofCertificate {
        version: CERTIFICATE_VERSION,
        source_hash: sha256(b"fn verified_function() { requires!(true); }"),
        vc_hash: sha256(b"(assert (not (=> true true)))"),
        resolution_steps,
        theory_lemmas,
        input_clauses,
        empty_clause_id,
        metadata: CertificateMetadata {
            timestamp: "2026-03-28T12:00:00Z".to_string(),
            trust_vc_version: "1.0.0".to_string(),
            solver_version: "ay-dpll 0.1.0".to_string(),
        },
    }
}

fn certificate_with_all_theory_kinds() -> TrustVcProofCertificate {
    TrustVcProofCertificate {
        version: CERTIFICATE_VERSION,
        source_hash: [0u8; 32],
        vc_hash: [0u8; 32],
        resolution_steps: vec![],
        theory_lemmas: vec![
            WireTheoryLemma {
                id: WireClauseId(1),
                kind: TheoryLemmaKind::Euf,
                literals: vec![Literal(1)],
                justification: None,
            },
            WireTheoryLemma {
                id: WireClauseId(2),
                kind: TheoryLemmaKind::Lra,
                literals: vec![Literal(2)],
                justification: Some("simplex".to_string()),
            },
            WireTheoryLemma {
                id: WireClauseId(3),
                kind: TheoryLemmaKind::Nia,
                literals: vec![Literal(3)],
                justification: None,
            },
            WireTheoryLemma {
                id: WireClauseId(4),
                kind: TheoryLemmaKind::BitVector,
                literals: vec![Literal(4)],
                justification: None,
            },
            WireTheoryLemma {
                id: WireClauseId(5),
                kind: TheoryLemmaKind::Array,
                literals: vec![Literal(5)],
                justification: None,
            },
            WireTheoryLemma {
                id: WireClauseId(6),
                kind: TheoryLemmaKind::Sequence,
                literals: vec![Literal(6)],
                justification: None,
            },
            WireTheoryLemma {
                id: WireClauseId(7),
                kind: TheoryLemmaKind::Other,
                literals: vec![Literal(7)],
                justification: Some("custom theory".to_string()),
            },
        ],
        input_clauses: vec![],
        empty_clause_id: WireClauseId(0),
        metadata: CertificateMetadata {
            timestamp: "2026-03-28T00:00:00Z".to_string(),
            trust_vc_version: "1.0.0".to_string(),
            solver_version: "ay-dpll 0.1.0".to_string(),
        },
    }
}

#[test]
fn test_format_json_roundtrip_minimal() {
    let cert = minimal_certificate();
    let recovered = TrustVcProofCertificate::from_json(&cert.to_json().expect("serialize"))
        .expect("deserialize");
    assert_eq!(cert, recovered);
}

#[test]
fn test_format_json_roundtrip_rich() {
    let cert = rich_certificate(5);
    let recovered = TrustVcProofCertificate::from_json(&cert.to_json().expect("serialize"))
        .expect("deserialize");
    assert_eq!(cert, recovered);
}

#[test]
fn test_format_binary_roundtrip_minimal() {
    let cert = minimal_certificate();
    let recovered = TrustVcProofCertificate::from_bytes(&cert.to_bytes().expect("serialize"))
        .expect("deserialize");
    assert_eq!(cert, recovered);
}

#[test]
fn test_format_binary_roundtrip_rich() {
    let cert = rich_certificate(5);
    let recovered = TrustVcProofCertificate::from_bytes(&cert.to_bytes().expect("serialize"))
        .expect("deserialize");
    assert_eq!(cert, recovered);
}

#[test]
fn test_format_binary_magic_present() {
    let bytes = minimal_certificate().to_bytes().expect("serialize");
    assert!(bytes.len() >= MIN_BINARY_HEADER_LEN);
    assert_eq!(&bytes[..4], b"CPRF");
}

#[test]
fn test_format_binary_versions_in_header() {
    let bytes = minimal_certificate().to_bytes().expect("serialize");
    assert_eq!(bytes[4], BINARY_FORMAT_VERSION);
    assert_eq!(bytes[5], CERTIFICATE_VERSION as u8);
}

#[test]
fn test_format_binary_rejects_wrong_magic() {
    let mut bytes = minimal_certificate().to_bytes().expect("serialize");
    bytes[0] = b'X';
    let err = TrustVcProofCertificate::from_bytes(&bytes).expect_err("wrong magic");
    match err {
        FormatError::InvalidMagic { expected, actual } => {
            assert_eq!(expected, BINARY_MAGIC);
            assert_eq!(actual[0], b'X');
        }
        other => panic!("expected InvalidMagic, got {other:?}"),
    }
}

#[test]
fn test_format_binary_rejects_truncated_header() {
    let err = TrustVcProofCertificate::from_bytes(b"CPR").expect_err("truncated");
    match err {
        FormatError::BinaryTooShort { expected, actual } => {
            assert_eq!(expected, MIN_BINARY_HEADER_LEN);
            assert_eq!(actual, 3);
        }
        other => panic!("expected BinaryTooShort, got {other:?}"),
    }
}

#[test]
fn test_format_binary_rejects_empty_input() {
    let err = TrustVcProofCertificate::from_bytes(&[]).expect_err("empty");
    match err {
        FormatError::BinaryTooShort { expected, actual } => {
            assert_eq!(expected, MIN_BINARY_HEADER_LEN);
            assert_eq!(actual, 0);
        }
        other => panic!("expected BinaryTooShort, got {other:?}"),
    }
}

#[test]
fn test_format_binary_rejects_unknown_binary_format_version() {
    let mut bytes = minimal_certificate().to_bytes().expect("serialize");
    bytes[4] = BINARY_FORMAT_VERSION + 1;
    let err = TrustVcProofCertificate::from_bytes(&bytes).expect_err("future binary version");
    match err {
        FormatError::Binary(msg) => assert!(msg.contains("unsupported binary format version")),
        other => panic!("expected Binary, got {other:?}"),
    }
}

#[test]
fn test_format_binary_rejects_future_certificate_version() {
    let mut bytes = minimal_certificate().to_bytes().expect("serialize");
    bytes[5] = (CERTIFICATE_VERSION + 1) as u8;
    let err = TrustVcProofCertificate::from_bytes(&bytes).expect_err("future cert version");
    match err {
        FormatError::UnsupportedVersion {
            found,
            max_supported,
        } => {
            assert_eq!(found, CERTIFICATE_VERSION + 1);
            assert_eq!(max_supported, CERTIFICATE_VERSION);
        }
        other => panic!("expected UnsupportedVersion, got {other:?}"),
    }
}

#[test]
fn test_format_binary_smaller_than_json() {
    let cert = rich_certificate(50);
    let json_len = cert.to_json().expect("json").len();
    let binary_len = cert.to_bytes().expect("binary").len();
    assert!(binary_len < json_len, "binary={binary_len} json={json_len}");
}

#[test]
fn test_format_version_check_rejects_future_json_version() {
    let mut cert = minimal_certificate();
    cert.version = CERTIFICATE_VERSION + 1;
    let json = serde_json::to_string_pretty(&cert).expect("serialize");
    let err = TrustVcProofCertificate::from_json(&json).expect_err("future version");
    match err {
        FormatError::UnsupportedVersion {
            found,
            max_supported,
        } => {
            assert_eq!(found, CERTIFICATE_VERSION + 1);
            assert_eq!(max_supported, CERTIFICATE_VERSION);
        }
        other => panic!("expected UnsupportedVersion, got {other:?}"),
    }
}

#[test]
fn test_format_empty_certificate_roundtrips() {
    let cert = TrustVcProofCertificate {
        version: CERTIFICATE_VERSION,
        source_hash: [0u8; 32],
        vc_hash: [0u8; 32],
        resolution_steps: vec![],
        theory_lemmas: vec![],
        input_clauses: vec![],
        empty_clause_id: WireClauseId(0),
        metadata: CertificateMetadata {
            timestamp: String::new(),
            trust_vc_version: String::new(),
            solver_version: String::new(),
        },
    };
    let from_json =
        TrustVcProofCertificate::from_json(&cert.to_json().expect("json")).expect("json decode");
    let from_bin =
        TrustVcProofCertificate::from_bytes(&cert.to_bytes().expect("binary")).expect("decode");
    assert_eq!(cert, from_json);
    assert_eq!(cert, from_bin);
    assert_eq!(cert.source_hash_hex(), "00".repeat(32));
}

#[test]
fn test_format_large_certificate_roundtrip() {
    let cert = rich_certificate(150);
    let from_json =
        TrustVcProofCertificate::from_json(&cert.to_json().expect("json")).expect("json decode");
    let from_bin =
        TrustVcProofCertificate::from_bytes(&cert.to_bytes().expect("binary")).expect("decode");
    assert_eq!(cert, from_json);
    assert_eq!(cert, from_bin);
}

#[test]
fn test_format_json_and_binary_decode_to_same_value() {
    let cert = rich_certificate(10);
    let from_json =
        TrustVcProofCertificate::from_json(&cert.to_json().expect("json")).expect("json decode");
    let from_bin =
        TrustVcProofCertificate::from_bytes(&cert.to_bytes().expect("binary")).expect("decode");
    assert_eq!(from_json, from_bin);
}

#[test]
fn test_format_hash_display_helpers() {
    let cert = minimal_certificate();
    let source_hex = cert.source_hash_hex();
    let vc_hex = cert.vc_hash_hex();
    assert_eq!(source_hex.len(), 64);
    assert_eq!(vc_hex.len(), 64);
    assert!(source_hex.chars().all(|ch| ch.is_ascii_hexdigit()));
    assert!(vc_hex.chars().all(|ch| ch.is_ascii_hexdigit()));
    let expected = sha256(b"fn main() {}");
    let expected_hex: String = expected.iter().map(|byte| format!("{byte:02x}")).collect();
    assert_eq!(source_hex, expected_hex);
}

#[test]
fn test_format_sha256_is_deterministic() {
    let a = sha256(b"hello");
    let b = sha256(b"hello");
    let c = sha256(b"world");
    assert_eq!(a, b);
    assert_ne!(a, c);
}

#[test]
fn test_format_theory_lemma_kinds_json_roundtrip() {
    let cert = certificate_with_all_theory_kinds();
    let recovered =
        TrustVcProofCertificate::from_json(&cert.to_json().expect("json")).expect("decode");
    assert_eq!(cert.theory_lemmas, recovered.theory_lemmas);
}

#[test]
fn test_format_theory_lemma_kinds_binary_roundtrip() {
    let cert = certificate_with_all_theory_kinds();
    let recovered =
        TrustVcProofCertificate::from_bytes(&cert.to_bytes().expect("binary")).expect("decode");
    assert_eq!(cert.theory_lemmas, recovered.theory_lemmas);
}
