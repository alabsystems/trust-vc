// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Revoke actual owned script/archive pins without touching executing images.

use super::*;

struct Rollback {
    file: PinnedFile,
    bytes: Vec<u8>,
    restored: bool,
    sink: Sink,
}

impl Rollback {
    fn new(file: PinnedFile, sink: &Sink) -> Result<Self, String> {
        let bytes = file.read()?;
        Ok(Self {
            file,
            bytes,
            restored: false,
            sink: Arc::clone(sink),
        })
    }

    fn restore(&mut self) -> Result<(), String> {
        std::fs::write(&self.file.path, &self.bytes).map_err(|e| e.to_string())?;
        self.file.read()?;
        self.restored = true;
        Ok(())
    }
}

impl Drop for Rollback {
    fn drop(&mut self) {
        if !self.restored {
            if let Err(error) = self.restore() {
                if let Ok(mut state) = self.sink.lock() {
                    state.rollback_failed = true;
                }
                eprintln!("owned transaction test rollback failed: {error}");
            }
        }
    }
}

pub(super) fn changed_bytes(
    scope: &Cohort<'_, '_>,
    seed: &PendingHelpers,
    sink: &Sink,
) -> Result<(), String> {
    let fresh = scope
        .inputs
        .build_origin
        .as_ref()
        .ok_or("the actual mutation control has no fresh construction")?;
    let files = fresh.transaction_files()?;
    for (name, file) in ["owned_script_bytes", "owned_archive_copy_bytes"]
        .into_iter()
        .zip(files)
    {
        let actual = genuine::scope(scope)?;
        let pending = genuine::one(&actual, seed)?;
        actual.current(actual.tcx, actual.inputs, actual.metadata)?;
        actual.owned.revalidate(actual.inputs, actual.metadata)?;
        let mut rollback = Rollback::new(file, sink)?;
        let mut changed = rollback.bytes.clone();
        changed.push(0);
        std::fs::write(&rollback.file.path, changed).map_err(|e| e.to_string())?;
        let changed_hash = inputs::digest(&rollback.file.path)?;
        if changed_hash == rollback.file.sha256 {
            return Err("the owned mutation control did not change its pinned bytes".into());
        }
        rejected(rollback.file.read(), "pinned input bytes changed")?;
        rejected(actual.finish(pending), "pinned input bytes changed")?;
        rollback.restore()?;
        scope.owned.revalidate(scope.inputs, scope.metadata)?;
        record(
            sink,
            name,
            json!({"path": rollback.file.path,
            "original_sha256": rollback.file.sha256, "changed_sha256": changed_hash,
            "restored_sha256": inputs::digest(&rollback.file.path)?,
            "finish": "Rejected", "owned_result": false, "restored_revalidation": "Passed"}),
        )?;
    }
    Ok(())
}
