// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! External request paths are test data for the genuine producer, not tokens.

use std::path::{Path, PathBuf};

use super::*;

pub(super) struct Fixture {
    pub(super) request: PinnedFile,
    pub(super) alternate: Option<PinnedFile>,
    pub(super) output: PathBuf,
    pub(super) report: PathBuf,
    manifest: PinnedFile,
}

fn object_keys(value: &Value, allowed: &[&str]) -> Result<(), String> {
    let object = value
        .as_object()
        .ok_or("a native transaction fixture object is missing")?;
    if object.keys().any(|key| !allowed.contains(&key.as_str())) {
        return Err("the native transaction fixture contains an unsupported field".into());
    }
    Ok(())
}

fn pinned(value: &Value) -> Result<PinnedFile, String> {
    object_keys(value, &["path", "sha256"])?;
    let path = PathBuf::from(value["path"].as_str().ok_or("missing fixture pin path")?);
    let text = value["sha256"]
        .as_str()
        .ok_or("missing fixture pin digest")?;
    if text.len() != 64 || !text.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err("the native transaction request digest is invalid".into());
    }
    let mut sha256 = [0; 32];
    for (out, bytes) in sha256.iter_mut().zip(text.as_bytes().as_chunks::<2>().0) {
        let pair = std::str::from_utf8(bytes).map_err(|e| e.to_string())?;
        *out = u8::from_str_radix(pair, 16).map_err(|e| e.to_string())?;
    }
    let pin = PinnedFile { path, sha256 };
    pin.read()?;
    if pin.path.canonicalize().map_err(|e| e.to_string())? != pin.path {
        return Err("the external test request path must be canonical".into());
    }
    Ok(pin)
}

fn request_output(pin: &PinnedFile) -> Result<(PathBuf, PathBuf), String> {
    let request: Value = serde_json::from_slice(&pin.read()?).map_err(|e| e.to_string())?;
    if request["schema"] != "trust-vc.native-declaration-staging-request@2" {
        return Err("transaction controls require an actual fresh schema-2 request".into());
    }
    let source = Path::new(
        request["source_root"]
            .as_str()
            .ok_or("missing actual source root")?,
    )
    .canonicalize()
    .map_err(|e| e.to_string())?;
    let output = inputs::canonical_output(
        Path::new(
            request["output"]
                .as_str()
                .ok_or("missing fresh actual output")?,
        ),
        &source,
    )?;
    Ok((source, output))
}

impl Fixture {
    pub(super) fn load(case: Case) -> Result<Self, String> {
        if std::env::var("VSTD_KIND").as_deref() != Ok("IsVstd") {
            return Err("the standalone test process must start in IsVstd context".into());
        }
        let path = std::env::var_os("TRUST_VC_HELPER_TRANSACTION_FIXTURE")
            .map(PathBuf::from)
            .ok_or("the explicit ignored control requires its exact fixture path")?;
        if !path.is_absolute() || path.canonicalize().map_err(|e| e.to_string())? != path {
            return Err("the transaction fixture path must be absolute and canonical".into());
        }
        let manifest = PinnedFile {
            sha256: inputs::digest(&path)?,
            path,
        };
        let value: Value = serde_json::from_slice(&manifest.read()?).map_err(|e| e.to_string())?;
        object_keys(&value, &["schema", "cases"])?;
        if value["schema"] != "trust-vc.helper-transaction-test-fixture@1" {
            return Err("unsupported transaction test fixture".into());
        }
        object_keys(
            &value["cases"],
            &["reversible", "drop", "diagnostics", "unwind"],
        )?;
        let row = &value["cases"][case.name()];
        object_keys(row, &["request", "alternate_inputs_request", "report"])?;
        let request = pinned(&row["request"])?;
        let (source, output) = request_output(&request)?;
        let alternate = row
            .get("alternate_inputs_request")
            .map(pinned)
            .transpose()?;
        if (case == Case::Reversible) != alternate.is_some() {
            return Err(
                "only the reversible case requires a separate actual Inputs request".into(),
            );
        }
        if let Some(alternate) = &alternate {
            let (other_source, other_output) = request_output(alternate)?;
            if source != other_source || output == other_output {
                return Err("the alternate real construction needs the same source and a fresh distinct output".into());
            }
        }
        let report = Path::new(
            row["report"]
                .as_str()
                .ok_or("missing fresh test report path")?,
        );
        let report = inputs::canonical_output(report, &source)?;
        if report == output {
            return Err("the test report cannot occupy the actual producer output".into());
        }
        Ok(Self {
            request,
            alternate,
            output,
            report,
            manifest,
        })
    }

    pub(super) fn revalidate(&self) -> Result<(), String> {
        self.manifest.read()?;
        self.request.read()?;
        if let Some(alternate) = &self.alternate {
            alternate.read()?;
        }
        Ok(())
    }

    pub(super) fn write(&self, case: Case, sink: &Sink, outcome: &str) -> Result<(), String> {
        let report = {
            let state = sink
                .lock()
                .map_err(|_| "the test outcome lock is poisoned")?;
            json!({"schema": "trust-vc.helper-transaction-test-result@1", "case": case.name(),
                "entered_actual_finish": state.entered, "finished_owned": state.finished_owned,
                "rollback_failed": state.rollback_failed, "cases": state.cases,
                "producer_outcome": outcome, "fixture": self.manifest.path,
                "fixture_sha256": self.manifest.sha256, "request": self.request.path,
                "request_sha256": self.request.sha256,
                "import_authorized": false, "verified_functions": null})
        };
        use std::io::Write;
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&self.report)
            .map_err(|e| e.to_string())?;
        file.write_all(&serde_json::to_vec_pretty(&report).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())
    }
}

#[cfg(test)]
mod tests;
