// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A native SDK reference at the ordinary import operand. This is an explicit
//! Trust format, not serialized Verus VIR or a saved owner. Only its creating
//! PreparedSdk, still borrowing the real producer, can accept the operand.

use std::io::Write;

use super::*;

pub(super) struct NativeReference {
    file: PinnedFile,
    identity: FileId,
    operand: String,
}

impl NativeReference {
    pub(super) fn create(
        owner: &StandaloneImported<'_>,
        root: &Path,
        images: &BTreeMap<PathBuf, NativeAlias>,
    ) -> Result<Self, String> {
        owner.check_retained_inputs()?;
        let library = owner.library();
        let path = root.join("vstd.vir");
        let operand = format!(
            "vstd={}",
            path.to_str()
                .ok_or("the native import operand requires a UTF-8 path")?
        );
        let bytes = serde_json::to_vec_pretty(&serde_json::json!({
            "schema": "trust-vc.native-sdk-reference@1",
            "representation": "live-owner-native-library-reference",
            "library": "vstd",
            "stable_crate_id": library.prepared.erase.view.stable_crate_id,
            "crate_svh": library.prepared.erase.target_svh.to_string(),
            "source_manifest_sha256": library.inputs.sources.identity().manifest_sha256,
            "native_images": images.iter().map(|(alias, image)| serde_json::json!({
                "operand": alias, "actual_target": image.target.path,
                "sha256": image.target.sha256,
            })).collect::<Vec<_>>(),
            "serialized_declarations": false,
            "serialized_bodies": false,
            "permission_from_reference": false,
            "requires_same_live_producer_owner": true,
        }))
        .map_err(|e| e.to_string())?;
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .map_err(|e| e.to_string())?;
        file.write_all(&bytes).map_err(|e| e.to_string())?;
        file.sync_all().map_err(|e| e.to_string())?;
        drop(file);
        let file = PinnedFile {
            sha256: inputs::digest(&path)?,
            path,
        };
        regular(&file)?;
        let identity =
            FileId::of(&std::fs::symlink_metadata(&file.path).map_err(|e| e.to_string())?);
        let result = Self {
            file,
            identity,
            operand,
        };
        result.revalidate()?;
        owner.check_retained_inputs()?;
        Ok(result)
    }

    pub(super) fn path(&self) -> &Path {
        &self.file.path
    }

    pub(super) fn represents(&self, operand: &str) -> bool {
        operand == self.operand
    }

    pub(super) fn revalidate(&self) -> Result<(), String> {
        regular(&self.file)?;
        let metadata = std::fs::symlink_metadata(&self.file.path).map_err(|e| e.to_string())?;
        if FileId::of(&metadata) != self.identity {
            return Err("the native SDK reference was changed or replaced".into());
        }
        Ok(())
    }
}
