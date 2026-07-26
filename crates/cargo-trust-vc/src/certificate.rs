// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Proof certificate emission for verification-aware optimization hints.

use crate::verify::{FunctionVerification, ObligationStatus, VerdictKind};
use serde::Serialize;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

/// Directory name under the crate root where proof certificates are stored.
pub const CERTIFICATE_DIR: &str = ".trust_vc";
/// Default filename for the emitted JSON proof certificate.
pub const CERTIFICATE_FILENAME: &str = "proof-certificate.json";

/// Top-level proof certificate emitted by `cargo trust_vc check --certificate`.
#[derive(Debug, Serialize)]
pub struct ProofCertificate {
    pub schema_version: u32,
    pub trust_vc_version: &'static str,
    pub generated_at_unix_secs: u64,
    pub crate_name: String,
    pub functions: Vec<FunctionCertificate>,
}

/// Per-function verification result within a proof certificate.
#[derive(Debug, Serialize)]
pub struct FunctionCertificate {
    pub name: String,
    pub file: String,
    pub line: usize,
    pub status: VerdictKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_hash: Option<String>,
    pub obligations: Vec<ObligationCertificate>,
    /// UNSAT proof in Alethe format (SMT-LIB compatible). Present only when the
    /// `proof-certificates` feature is enabled and the function was verified.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_alethe: Option<String>,
    /// Whether ay's strict proof checker accepted the UNSAT proof.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_strict_verified: Option<bool>,
}

/// Per-obligation verification status within a function certificate.
#[derive(Debug, Serialize)]
pub struct ObligationCertificate {
    pub name: String,
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<String>,
    pub condition_hash: String,
    pub status: ObligationStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unknown_category: Option<String>,
}

/// Build a [`ProofCertificate`] from a set of function verification results.
pub fn generate_certificate(
    verifications: &[FunctionVerification],
    crate_root: &Path,
) -> ProofCertificate {
    ProofCertificate {
        schema_version: 1,
        trust_vc_version: env!("CARGO_PKG_VERSION"),
        generated_at_unix_secs: SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs(),
        crate_name: crate_name(crate_root),
        functions: verifications
            .iter()
            .map(|verification| FunctionCertificate::from_verification(verification, crate_root))
            .collect(),
    }
}

/// Serialize a proof certificate as JSON and write it to `<crate_root>/.trust_vc/proof-certificate.json`.
pub fn write_certificate(cert: &ProofCertificate, crate_root: &Path) -> Result<PathBuf, String> {
    let dir = crate_root.join(CERTIFICATE_DIR);
    fs::create_dir_all(&dir).map_err(|err| format!("cannot create {}: {err}", dir.display()))?;

    let path = dir.join(CERTIFICATE_FILENAME);
    let json = serde_json::to_string_pretty(cert)
        .map_err(|err| format!("cannot serialize certificate: {err}"))?;
    fs::write(&path, format!("{json}\n"))
        .map_err(|err| format!("cannot write {}: {err}", path.display()))?;
    Ok(path)
}

impl FunctionCertificate {
    fn from_verification(verification: &FunctionVerification, crate_root: &Path) -> Self {
        let verdict = &verification.verdict;
        let file = verdict
            .function
            .file_path
            .strip_prefix(crate_root)
            .unwrap_or(&verdict.function.file_path)
            .display()
            .to_string();

        #[cfg(feature = "proof-certificates")]
        let proof_alethe = verification.proof_alethe.clone();
        #[cfg(not(feature = "proof-certificates"))]
        let proof_alethe: Option<String> = None;

        #[cfg(feature = "proof-certificates")]
        let proof_strict_verified = verification.proof_strict_verified;
        #[cfg(not(feature = "proof-certificates"))]
        let proof_strict_verified: Option<bool> = None;

        Self {
            name: verdict.function.name.clone(),
            file,
            line: verdict.function.line,
            status: verdict.result.clone(),
            detail: verdict.detail.clone(),
            source_hash: verification.source_hash.clone(),
            obligations: verification
                .obligations
                .iter()
                .map(|obligation| ObligationCertificate {
                    name: obligation.name.clone(),
                    kind: obligation.kind.clone(),
                    location: obligation.location.clone(),
                    condition_hash: obligation.condition_hash.clone(),
                    status: obligation.status,
                    unknown_category: obligation.unknown_category.clone(),
                })
                .collect(),
            proof_alethe,
            proof_strict_verified,
        }
    }
}

fn crate_name(crate_root: &Path) -> String {
    crate_root
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_else(|| ".".to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scan::AnnotatedFunction;
    use crate::verify::{FunctionVerdict, ObligationVerification};

    #[test]
    fn test_generate_certificate_keeps_real_obligation_metadata() {
        let verification = FunctionVerification {
            verdict: FunctionVerdict {
                function: AnnotatedFunction {
                    file_path: PathBuf::from("/project/src/lib.rs"),
                    name: "identity".into(),
                    line: 12,
                    attributes: vec!["ensures".into()],
                },
                result: VerdictKind::Verified,
                duration_ms: 3,
                detail: None,
                localized_failure: None,
                bindings: Vec::new(),
            },
            source_hash: Some("sha256:source".into()),
            obligations: vec![
                ObligationVerification {
                    name: "postcondition".into(),
                    kind: "assert".into(),
                    location: Some("src/lib.rs:12:1".into()),
                    condition_hash: "sha256:condition".into(),
                    status: ObligationStatus::Verified,
                    unknown_category: None,
                },
                ObligationVerification {
                    name: "return_value".into(),
                    kind: "assume".into(),
                    location: None,
                    condition_hash: "sha256:return".into(),
                    status: ObligationStatus::Assumed,
                    unknown_category: None,
                },
            ],
            report: None,
            #[cfg(feature = "proof-certificates")]
            proof_alethe: None,
            #[cfg(feature = "proof-certificates")]
            proof_strict_verified: None,
            warnings: Vec::new(),
        };

        let cert = generate_certificate(&[verification], Path::new("/project"));

        assert_eq!(cert.schema_version, 1);
        assert_eq!(cert.crate_name, "project");
        assert_eq!(cert.functions.len(), 1);
        assert_eq!(
            cert.functions[0].source_hash.as_deref(),
            Some("sha256:source")
        );
        assert_eq!(cert.functions[0].obligations[0].name, "postcondition");
        assert_eq!(
            cert.functions[0].obligations[0].condition_hash,
            "sha256:condition"
        );
        assert_eq!(
            cert.functions[0].obligations[1].status,
            ObligationStatus::Assumed
        );
    }

    #[cfg(feature = "proof-certificates")]
    #[test]
    fn test_certificate_includes_proof_alethe_when_present() {
        let verification = FunctionVerification {
            verdict: FunctionVerdict {
                function: AnnotatedFunction {
                    file_path: PathBuf::from("/project/src/lib.rs"),
                    name: "proven".into(),
                    line: 5,
                    attributes: vec!["ensures".into()],
                },
                result: VerdictKind::Verified,
                duration_ms: 10,
                detail: None,
                localized_failure: None,
                bindings: Vec::new(),
            },
            source_hash: Some("sha256:test".into()),
            obligations: Vec::new(),
            report: None,
            proof_alethe: Some("(assume h1 (>= x 0))\n(step t1 :rule resolution)".into()),
            proof_strict_verified: Some(true),
            warnings: Vec::new(),
        };

        let cert = generate_certificate(&[verification], Path::new("/project"));
        let func = &cert.functions[0];
        assert_eq!(
            func.proof_alethe.as_deref(),
            Some("(assume h1 (>= x 0))\n(step t1 :rule resolution)")
        );
        assert_eq!(func.proof_strict_verified, Some(true));

        let json = serde_json::to_string_pretty(&cert).expect("certificate should serialize");
        assert!(
            json.contains("proof_alethe"),
            "serialized certificate should include proof_alethe field"
        );
        assert!(
            json.contains("proof_strict_verified"),
            "serialized certificate should include proof_strict_verified field"
        );
    }

    #[test]
    fn test_certificate_omits_proof_fields_when_none() {
        let verification = FunctionVerification {
            verdict: FunctionVerdict {
                function: AnnotatedFunction {
                    file_path: PathBuf::from("/project/src/lib.rs"),
                    name: "no_proof".into(),
                    line: 1,
                    attributes: vec!["ensures".into()],
                },
                result: VerdictKind::Counterexample,
                duration_ms: 5,
                detail: Some("x = -1".into()),
                localized_failure: None,
                bindings: Vec::new(),
            },
            source_hash: None,
            obligations: Vec::new(),
            report: None,
            #[cfg(feature = "proof-certificates")]
            proof_alethe: None,
            #[cfg(feature = "proof-certificates")]
            proof_strict_verified: None,
            warnings: Vec::new(),
        };

        let cert = generate_certificate(&[verification], Path::new("/project"));
        let json = serde_json::to_string_pretty(&cert).expect("certificate should serialize");
        assert!(
            !json.contains("proof_alethe"),
            "serialized certificate should omit None proof fields"
        );
    }

    #[test]
    fn test_write_certificate_creates_default_path() {
        let crate_root = std::env::temp_dir().join("cargo_trust_vc_write_certificate");
        let _ = fs::remove_dir_all(&crate_root);
        fs::create_dir_all(crate_root.join("src")).expect("temp crate dir should exist");

        let cert = ProofCertificate {
            schema_version: 1,
            trust_vc_version: "1.0.0",
            generated_at_unix_secs: 1,
            crate_name: "cargo_trust_vc_write_certificate".into(),
            functions: Vec::new(),
        };

        let path = write_certificate(&cert, &crate_root).expect("certificate should be written");
        let parsed: serde_json::Value = serde_json::from_str(
            &fs::read_to_string(&path).expect("certificate file should be readable"),
        )
        .expect("certificate JSON should parse");

        assert_eq!(
            path,
            crate_root.join(CERTIFICATE_DIR).join(CERTIFICATE_FILENAME)
        );
        assert_eq!(parsed["crate_name"], "cargo_trust_vc_write_certificate");

        let _ = fs::remove_dir_all(&crate_root);
    }
}
