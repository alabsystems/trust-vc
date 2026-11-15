// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Deterministic JSON runner for tRust-facing Trust verification requests.
//!
//! Usage:
//!   trust-vc-trust-runner --input request.json --output report.json
//!   trust-vc-trust-runner --input adapter.json --output report.json --input-format trust_ir-adapter
//!   trust-vc-trust-runner --input memory.json --output report.json --input-format mir-memory
//!   trust-vc-trust-runner --input bundle.json --output report.json --input-format native-trust_ir-bundle
//!   trust-vc-trust-runner --input request.json --output report.json --proof-policy evidence-only
//!   trust-vc-trust-runner --input - --output -
//!
//! Exit codes: 0 ok, 1 usage, 2 error, 3 refuted, 4 unknown, 5 rejected (a
//! native TrustIr bundle was consumed, but at least one certificate was
//! refused release admission — see the report's `release_admission` rows).

use serde::{de::DeserializeOwned, Serialize};
use serde_json::Value;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use trust_ir::request::NativeVerificationBundle;
use trust_vc_trust_engine::{
    TrustMirMemoryProofUnit, TrustOutcome, TrustProofPolicy, TrustTrustIrAdapterRequest,
    TrustVcNativeTrustIrBundleReport, TrustVcNativeTrustIrExitClass, TrustVcTrustEngine,
    TrustVerificationReport, TrustVerificationRequest, TrustVerifier,
};

const EXIT_OK: i32 = 0;
const EXIT_USAGE: i32 = 1;
const EXIT_ERROR: i32 = 2;
const EXIT_REFUTED: i32 = 3;
const EXIT_UNKNOWN: i32 = 4;
/// A native TrustIr bundle whose rollup is `CertificatesRejected`. It used to
/// exit 0 (its exit class was `Ok`), so a bundle with no release-grade
/// certificate at all looked, to anything reading the exit status, exactly
/// like one whose every certificate was admitted.
const EXIT_REJECTED: i32 = 5;

fn main() {
    match run(std::env::args().skip(1)) {
        Ok(code) => std::process::exit(code),
        Err(RunnerError::Help) => {
            println!("{}", usage());
            std::process::exit(EXIT_OK);
        }
        Err(RunnerError::Usage(message)) => {
            eprintln!("{message}\n\n{}", usage());
            std::process::exit(EXIT_USAGE);
        }
        Err(error) => {
            eprintln!("Error: {error}");
            std::process::exit(EXIT_ERROR);
        }
    }
}

fn run(args: impl IntoIterator<Item = String>) -> Result<i32, RunnerError> {
    let options = RunnerOptions::parse(args)?;
    let payload = read_input(&options.input)?;
    let report = verify_payload(&payload, &options)?;
    let exit_code = report_exit_code(&report);
    let report_json = serde_json::to_string_pretty(&report).map_err(RunnerError::Encode)?;
    write_output(&options.output, &format!("{report_json}\n"))?;

    Ok(exit_code)
}

fn verify_payload(payload: &str, options: &RunnerOptions) -> Result<RunnerReport, RunnerError> {
    match options.input_format {
        RunnerInputFormat::Auto => {
            let value = serde_json::from_str::<Value>(payload).map_err(|source| {
                RunnerError::DecodeJson {
                    path: options.input.clone(),
                    source,
                }
            })?;
            if looks_like_native_trust_ir_bundle(&value) {
                consume_native_trust_ir_bundle(
                    decode_value(
                        value,
                        &options.input,
                        RunnerInputFormat::NativeTrustIrBundle,
                    )?,
                    options.proof_policy,
                )
                .map(RunnerReport::NativeTrustIr)
            } else if looks_like_mir_memory_proof_unit(&value) {
                verify_mir_memory_proof_unit(
                    decode_value(value, &options.input, RunnerInputFormat::MirMemory)?,
                    options.proof_policy,
                )
                .map(RunnerReport::Trust)
            } else if looks_like_trust_ir_adapter_request(&value) {
                verify_trust_ir_adapter_request(
                    decode_value(value, &options.input, RunnerInputFormat::TrustIrAdapter)?,
                    options.proof_policy,
                )
                .map(RunnerReport::Trust)
            } else {
                verify_trust_request(
                    decode_value(value, &options.input, RunnerInputFormat::TrustRequest)?,
                    options.proof_policy,
                )
                .map(RunnerReport::Trust)
            }
        }
        RunnerInputFormat::TrustRequest => verify_trust_request(
            decode_str(payload, &options.input, RunnerInputFormat::TrustRequest)?,
            options.proof_policy,
        )
        .map(RunnerReport::Trust),
        RunnerInputFormat::TrustIrAdapter => verify_trust_ir_adapter_request(
            decode_str(payload, &options.input, RunnerInputFormat::TrustIrAdapter)?,
            options.proof_policy,
        )
        .map(RunnerReport::Trust),
        RunnerInputFormat::MirMemory => verify_mir_memory_proof_unit(
            decode_str(payload, &options.input, RunnerInputFormat::MirMemory)?,
            options.proof_policy,
        )
        .map(RunnerReport::Trust),
        RunnerInputFormat::NativeTrustIrBundle => consume_native_trust_ir_bundle(
            decode_str(
                payload,
                &options.input,
                RunnerInputFormat::NativeTrustIrBundle,
            )?,
            options.proof_policy,
        )
        .map(RunnerReport::NativeTrustIr),
    }
}

fn verify_trust_request(
    mut request: TrustVerificationRequest,
    proof_policy: Option<TrustProofPolicy>,
) -> Result<TrustVerificationReport, RunnerError> {
    if let Some(proof_policy) = proof_policy {
        request = request.with_proof_policy(proof_policy);
    }

    TrustVcTrustEngine::new()
        .verify(&request)
        .map_err(RunnerError::Verify)
}

fn verify_trust_ir_adapter_request(
    mut request: TrustTrustIrAdapterRequest,
    proof_policy: Option<TrustProofPolicy>,
) -> Result<TrustVerificationReport, RunnerError> {
    if let Some(proof_policy) = proof_policy {
        request = request.with_proof_policy(proof_policy);
    }

    TrustVcTrustEngine::new()
        .verify_trust_ir_adapter_request(&request)
        .map_err(RunnerError::Verify)
}

fn verify_mir_memory_proof_unit(
    unit: TrustMirMemoryProofUnit,
    proof_policy: Option<TrustProofPolicy>,
) -> Result<TrustVerificationReport, RunnerError> {
    TrustVcTrustEngine::new()
        .verify_mir_memory_request(&unit, proof_policy.unwrap_or_default())
        .map_err(RunnerError::Verify)
}

fn consume_native_trust_ir_bundle(
    bundle: NativeVerificationBundle,
    proof_policy: Option<TrustProofPolicy>,
) -> Result<TrustVcNativeTrustIrBundleReport, RunnerError> {
    if proof_policy.is_some() {
        return Err(RunnerError::Usage(
            "--proof-policy does not apply to native TrustIr bundle certificate imports"
                .to_string(),
        ));
    }

    TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .map_err(RunnerError::Verify)
}

fn decode_str<T: DeserializeOwned>(
    payload: &str,
    path: &Path,
    input_format: RunnerInputFormat,
) -> Result<T, RunnerError> {
    serde_json::from_str::<T>(payload).map_err(|source| RunnerError::Decode {
        path: path.to_path_buf(),
        input_format,
        source,
    })
}

fn decode_value<T: DeserializeOwned>(
    value: Value,
    path: &Path,
    input_format: RunnerInputFormat,
) -> Result<T, RunnerError> {
    serde_json::from_value::<T>(value).map_err(|source| RunnerError::Decode {
        path: path.to_path_buf(),
        input_format,
        source,
    })
}

fn looks_like_trust_ir_adapter_request(value: &Value) -> bool {
    let Some(units) = value.get("units").and_then(Value::as_array) else {
        return false;
    };
    if value.get("mode").is_some() {
        return false;
    }

    value.get("schema_version").is_some()
        || units.iter().any(|unit| {
            unit.get("obligations")
                .and_then(Value::as_array)
                .is_some_and(|obligations| {
                    obligations
                        .iter()
                        .any(|obligation| obligation.get("predicate").is_some())
                })
        })
}

fn looks_like_native_trust_ir_bundle(value: &Value) -> bool {
    value.get("trust_ir_module_digest").is_some()
        && value.get("module").is_some()
        && value.get("lineage").is_some()
        && value
            .get("requests")
            .and_then(Value::as_array)
            .is_some_and(|requests| !requests.is_empty())
}

fn looks_like_mir_memory_proof_unit(value: &Value) -> bool {
    value.get("source_id").is_some()
        && value.get("unit_id").is_some()
        && value.get("native_context").is_some()
        && value.get("obligations").is_some()
        && value.get("units").is_none()
}

fn read_input(path: &Path) -> Result<String, RunnerError> {
    if path.as_os_str() == "-" {
        let mut payload = String::new();
        std::io::stdin()
            .read_to_string(&mut payload)
            .map_err(|source| RunnerError::Read {
                path: path.to_path_buf(),
                source,
            })?;
        return Ok(payload);
    }

    std::fs::read_to_string(path).map_err(|source| RunnerError::Read {
        path: path.to_path_buf(),
        source,
    })
}

fn write_output(path: &Path, payload: &str) -> Result<(), RunnerError> {
    if path.as_os_str() == "-" {
        let mut stdout = std::io::stdout().lock();
        stdout
            .write_all(payload.as_bytes())
            .map_err(|source| RunnerError::Write {
                path: path.to_path_buf(),
                source,
            })?;
        return Ok(());
    }

    std::fs::write(path, payload).map_err(|source| RunnerError::Write {
        path: path.to_path_buf(),
        source,
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RunnerOptions {
    input: PathBuf,
    output: PathBuf,
    input_format: RunnerInputFormat,
    proof_policy: Option<TrustProofPolicy>,
}

impl RunnerOptions {
    fn parse(args: impl IntoIterator<Item = String>) -> Result<Self, RunnerError> {
        let mut input = None;
        let mut output = None;
        let mut input_format = RunnerInputFormat::Auto;
        let mut proof_policy = None;
        let mut args = args.into_iter();

        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--help" | "-h" => return Err(RunnerError::Help),
                "--input" => {
                    let value = args
                        .next()
                        .ok_or_else(|| RunnerError::Usage("--input requires a path".to_string()))?;
                    input = Some(PathBuf::from(value));
                }
                "--output" => {
                    let value = args.next().ok_or_else(|| {
                        RunnerError::Usage("--output requires a path".to_string())
                    })?;
                    output = Some(PathBuf::from(value));
                }
                "--proof-policy" => {
                    let value = args.next().ok_or_else(|| {
                        RunnerError::Usage("--proof-policy requires a value".to_string())
                    })?;
                    proof_policy = Some(parse_proof_policy(&value)?);
                }
                "--input-format" => {
                    let value = args.next().ok_or_else(|| {
                        RunnerError::Usage("--input-format requires a value".to_string())
                    })?;
                    input_format = parse_input_format(&value)?;
                }
                other => {
                    return Err(RunnerError::Usage(format!("unknown argument `{other}`")));
                }
            }
        }

        Ok(Self {
            input: input.ok_or_else(|| RunnerError::Usage("--input is required".to_string()))?,
            output: output.ok_or_else(|| RunnerError::Usage("--output is required".to_string()))?,
            input_format,
            proof_policy,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RunnerInputFormat {
    Auto,
    TrustRequest,
    TrustIrAdapter,
    MirMemory,
    NativeTrustIrBundle,
}

impl RunnerInputFormat {
    const fn label(self) -> &'static str {
        match self {
            Self::Auto => "auto-detected Trust input",
            Self::TrustRequest => "TrustVerificationRequest",
            Self::TrustIrAdapter => "TrustTrustIrAdapterRequest",
            Self::MirMemory => "TrustMirMemoryProofUnit",
            Self::NativeTrustIrBundle => "trust_ir::NativeVerificationBundle",
        }
    }
}

fn parse_input_format(value: &str) -> Result<RunnerInputFormat, RunnerError> {
    let normalized = value.replace('-', "_");
    match normalized.as_str() {
        "auto" => Ok(RunnerInputFormat::Auto),
        "trust_request" | "trust_verification_request" => Ok(RunnerInputFormat::TrustRequest),
        "trust_ir_adapter" | "trust_trust_ir_adapter_request" => {
            Ok(RunnerInputFormat::TrustIrAdapter)
        }
        "mir_memory" | "trust_mir_memory" | "trust_mir_memory_proof_unit" => {
            Ok(RunnerInputFormat::MirMemory)
        }
        "native_trust_ir_bundle" | "trust_ir_native_bundle" | "native_verification_bundle" => {
            Ok(RunnerInputFormat::NativeTrustIrBundle)
        }
        _ => Err(RunnerError::Usage(format!(
            "unknown input format `{value}`"
        ))),
    }
}

fn parse_proof_policy(value: &str) -> Result<TrustProofPolicy, RunnerError> {
    let normalized = value.replace('-', "_");
    match normalized.as_str() {
        "evidence_only" => Ok(TrustProofPolicy::EvidenceOnly),
        "attach_replayable_certificates" => Ok(TrustProofPolicy::AttachReplayableCertificates),
        "require_replayable_certificate" => Ok(TrustProofPolicy::RequireReplayableCertificate),
        "require_strict_replayable_certificate" => {
            Ok(TrustProofPolicy::RequireStrictReplayableCertificate)
        }
        "require_release_admissible_certificate" => {
            Ok(TrustProofPolicy::RequireReleaseAdmissibleCertificate)
        }
        _ => Err(RunnerError::Usage(format!(
            "unknown proof policy `{value}`"
        ))),
    }
}

#[derive(Serialize)]
#[serde(untagged)]
enum RunnerReport {
    Trust(TrustVerificationReport),
    NativeTrustIr(TrustVcNativeTrustIrBundleReport),
}

fn report_exit_code(report: &RunnerReport) -> i32 {
    let report = match report {
        RunnerReport::Trust(report) => report,
        // NATIVE BUNDLES USED TO EXIT 0 UNCONDITIONALLY, which meant a request
        // trust-vc could not answer was indistinguishable from one it fully
        // admitted. Read the rollup instead.
        //
        // Scoped deliberately: `CertificatesRejected` stays 0 because release
        // admission is a GRADING result — the bundle was consumed and the
        // report says which certificates are non-release — and promoting it to
        // a failure exit is a separate, user-visible policy change that
        // deserves its own commit.
        //
        // The discharge verdicts are NOT in that category. `Refuted` means the
        // solver produced a counterexample for an obligation the compiler asked
        // trust-vc to prove, and a decline (or a request that never reached the
        // lowering) means trust-vc did not prove it. Both must be visible to a
        // shell that only reads `$?`, so they map onto the exit codes the
        // request lane already uses for exactly these two meanings.
        // MERGED 2026-09-23: the discharge verdicts of BOTH lanes are
        // classified by `exit_class`, which maps `Refuted` / `DischargeRefuted`
        // to EXIT_REFUTED, a decline / not-answerable / advisory discharge to
        // EXIT_UNKNOWN, and `Discharged` to EXIT_OK — the same mapping the match
        // that stood here spelled out by hand.
        //
        // The classification lives on the verdict type, NOT in a match here.
        // This is a separate crate from the library, so `#[non_exhaustive]`
        // would force a `_ =>` arm — and a `_ => EXIT_OK` arm is precisely how
        // a newly added verdict (say, an ADVISORY discharge) would start
        // exiting 0 without anyone noticing. `exit_class` is exhaustive inside
        // the library, so adding a variant breaks the build there instead.
        RunnerReport::NativeTrustIr(native) => {
            return match native.verdict().exit_class() {
                TrustVcNativeTrustIrExitClass::Ok => EXIT_OK,
                TrustVcNativeTrustIrExitClass::Refuted => EXIT_REFUTED,
                TrustVcNativeTrustIrExitClass::Unknown => EXIT_UNKNOWN,
                TrustVcNativeTrustIrExitClass::Rejected => EXIT_REJECTED,
            };
        }
    };

    if report
        .units()
        .iter()
        .any(|unit| matches!(unit.outcome(), TrustOutcome::Error { .. }))
    {
        return EXIT_ERROR;
    }
    if report
        .units()
        .iter()
        .any(|unit| matches!(unit.outcome(), TrustOutcome::Refuted { .. }))
    {
        return EXIT_REFUTED;
    }
    if report
        .units()
        .iter()
        .any(|unit| matches!(unit.outcome(), TrustOutcome::Unknown { .. }))
    {
        return EXIT_UNKNOWN;
    }
    EXIT_OK
}

fn usage() -> &'static str {
    "Usage: trust-vc-trust-runner --input <request.json|-> --output <report.json|-> [--input-format <auto|trust-request|trust_ir-adapter|mir-memory|native-trust_ir-bundle>] [--proof-policy <policy>]\n\nProof policies: evidence-only, attach-replayable-certificates, require-replayable-certificate, require-strict-replayable-certificate, require-release-admissible-certificate\n\nExit codes: 0 ok, 1 usage, 2 error, 3 refuted, 4 unknown, 5 rejected (native bundle consumed, a certificate refused release admission)"
}

#[derive(Debug)]
enum RunnerError {
    Help,
    Usage(String),
    Read {
        path: PathBuf,
        source: std::io::Error,
    },
    Decode {
        path: PathBuf,
        input_format: RunnerInputFormat,
        source: serde_json::Error,
    },
    DecodeJson {
        path: PathBuf,
        source: serde_json::Error,
    },
    Verify(trust_vc_trust_engine::TrustEngineError),
    Encode(serde_json::Error),
    Write {
        path: PathBuf,
        source: std::io::Error,
    },
}

impl std::fmt::Display for RunnerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Help => write!(f, "help requested"),
            Self::Usage(message) => write!(f, "{message}"),
            Self::Read { path, source } => {
                write!(f, "failed to read {}: {source}", path.display())
            }
            Self::Decode {
                path,
                input_format,
                source,
            } => {
                write!(
                    f,
                    "failed to decode {} as {} JSON: {source}",
                    path.display(),
                    input_format.label()
                )
            }
            Self::DecodeJson { path, source } => {
                write!(f, "failed to decode {} as JSON: {source}", path.display())
            }
            Self::Verify(source) => write!(f, "Trust verification failed: {source}"),
            Self::Encode(source) => {
                write!(f, "failed to encode runner report JSON: {source}")
            }
            Self::Write { path, source } => {
                write!(f, "failed to write {}: {source}", path.display())
            }
        }
    }
}

impl std::error::Error for RunnerError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_kebab_case_proof_policy() {
        assert_eq!(
            parse_proof_policy("require-release-admissible-certificate").unwrap(),
            TrustProofPolicy::RequireReleaseAdmissibleCertificate
        );
    }

    #[test]
    fn parses_kebab_case_input_format() {
        assert_eq!(
            parse_input_format("trust_ir-adapter").unwrap(),
            RunnerInputFormat::TrustIrAdapter
        );
        assert_eq!(
            parse_input_format("mir-memory").unwrap(),
            RunnerInputFormat::MirMemory
        );
        assert_eq!(
            parse_input_format("native-trust_ir-bundle").unwrap(),
            RunnerInputFormat::NativeTrustIrBundle
        );
    }

    #[test]
    fn rejects_unknown_proof_policy() {
        assert!(matches!(
            parse_proof_policy("trust-me"),
            Err(RunnerError::Usage(message)) if message.contains("unknown proof policy")
        ));
    }

    #[test]
    fn rejects_unknown_input_format() {
        assert!(matches!(
            parse_input_format("sample"),
            Err(RunnerError::Usage(message)) if message.contains("unknown input format")
        ));
    }
}
