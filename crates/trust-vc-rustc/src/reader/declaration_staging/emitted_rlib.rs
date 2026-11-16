//! Join the two real outputs of one fresh Erase compiler invocation.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

/// Byte pins are captured only after the owning compiler has returned.
/// A redirected output is not the artifact in the fresh output plan.
pub(super) fn pin_output(path: &Path) -> Result<PinnedFile, String> {
    if !path.is_absolute()
        || !std::fs::symlink_metadata(path)
            .map_err(|e| e.to_string())?
            .file_type()
            .is_file()
        || path.canonicalize().map_err(|e| e.to_string())? != path
    {
        return Err("fresh native output must be its original regular file".into());
    }
    let file = PinnedFile {
        path: path.to_path_buf(),
        sha256: inputs::digest(path)?,
    };
    file.read()?;
    Ok(file)
}

/// Constructed only after the actual native compiler selected the fresh RLIB
/// and its metadata agreed with the separately loaded fresh RMETA. This is an
/// artifact binding, not a declaration, body or ordinary SDK import permission.
pub(super) struct CheckedRlib {
    file: PinnedFile,
    metadata: Metadata,
    loader_observation: Value,
}

impl CheckedRlib {
    pub(super) fn file(&self) -> &PinnedFile {
        &self.file
    }

    pub(super) fn revalidate(&self) -> Result<(), String> {
        self.file.read()?;
        self.metadata.revalidate()
    }

    pub(super) fn observation(&self) -> Value {
        json!({"path": self.file.path, "sha256": self.file.sha256,
            "loader_invocation": self.loader_observation,
            "same_fresh_emission_as_metadata": true,
            "ordinary_sdk_import_authorized": false})
    }
}

struct LoadRlib<'a> {
    inputs: &'a Inputs,
    metadata: Option<LoadedEraseMetadata>,
    argv: &'a [String],
    result: Option<Result<OwnedErase, String>>,
}

impl Callbacks for LoadRlib<'_> {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        self.result = Some((|| {
            diagnostics(tcx)?;
            self.inputs.revalidate()?;
            let metadata = self
                .metadata
                .take()
                .ok_or("the paired Erase metadata handoff was already consumed")?;
            metadata.file.read()?;
            metadata.target_metadata.revalidate()?;
            metadata.rlib.read()?;
            let loader = Invocation::capture(tcx, self.argv)?;
            if !loader.same_target(&metadata.invocation) {
                return Err("the fresh RLIB loader uses a different native target/sysroot".into());
            }
            let (common, target) = collect::selections(tcx, self.inputs, Some(&metadata.rlib))?;
            let target = target.ok_or("the native compiler did not select the fresh Erase RLIB")?;
            if target.stable_crate_id != metadata.view.stable_crate_id
                || target.svh != metadata.target_svh
            {
                return Err(
                    "the fresh Erase RLIB and RMETA have different native identities".into(),
                );
            }
            let view = collect::view(
                tcx,
                target.native_crate,
                self.inputs,
                &common,
                &metadata.invocation,
                Some(target.file.sha256),
            )?;
            if !roundtrip(&metadata.view, &view)?.is_empty() {
                return Err("the fresh Erase RLIB changed the loaded declaration inventory".into());
            }
            let specs = spec_graph::View::capture(tcx, target.native_crate, self.inputs, &common)?;
            let spec_unknown = spec_graph::roundtrip(&metadata.spec_view, &specs);
            // Unknown companion facts must remain unknown at the same keys.
            // They are retained as refusals, never promoted to equal facts.
            if spec_unknown != spec_graph::roundtrip(&metadata.spec_view, &metadata.spec_view)
                || spec_unknown != spec_graph::roundtrip(&specs, &specs)
            {
                return Err(
                    "the fresh Erase RLIB changed the loaded Spec companion inventory".into(),
                );
            }
            diagnostics(tcx)?;
            let rlib = CheckedRlib {
                file: target.file,
                metadata: target.metadata,
                loader_observation: loader.observation(),
            };
            rlib.revalidate()?;
            Ok(OwnedErase {
                view: metadata.view,
                spec_view: metadata.spec_view,
                spec_roundtrip_unknown: metadata.spec_roundtrip_unknown,
                invocation: metadata.invocation,
                target_metadata: metadata.target_metadata,
                target_svh: metadata.target_svh,
                file: metadata.file,
                roundtrip_unknown: metadata.roundtrip_unknown,
                loader_observation: metadata.loader_observation,
                rlib,
            })
        })());
        Compilation::Stop
    }
}

pub(super) fn load(
    inputs: &Inputs,
    metadata: LoadedEraseMetadata,
    client: &Path,
) -> Result<OwnedErase, String> {
    inputs.revalidate()?;
    let mut argv = inputs.client_args(&metadata.rlib.path, client);
    argv.extend([
        "-o".into(),
        inputs
            .output
            .join("load/rlib-unused.rmeta")
            .display()
            .to_string(),
    ]);
    let mut loader = LoadRlib {
        inputs,
        metadata: Some(metadata),
        argv: &argv,
        result: None,
    };
    let result = run_compiler(&argv, &mut loader);
    record_phase(
        inputs,
        "LoadFreshEraseRlib",
        &result,
        loader.result.as_ref(),
    )?;
    result?;
    let owned = loader
        .result
        .ok_or("the fresh RLIB callback was not reached")??;
    owned.revalidate_artifacts()?;
    inputs.revalidate()?;
    Ok(owned)
}

#[cfg(test)]
pub(in crate::reader::declaration_staging) fn genuine_mutation_controls(library: &StagedLibrary) {
    let erase = &library.prepared.erase;
    erase.revalidate_artifacts().unwrap();
    let mut cases = Vec::new();
    for (name, file) in [("rmeta", &erase.file), ("rlib", &erase.rlib.file)] {
        let original = file.read().unwrap();
        let mut changed = original.clone();
        changed.push(0);
        std::fs::write(&file.path, changed).unwrap();
        let refused = library.write_observation().is_err();
        // Restore before asserting so an assertion never leaves corrupt native
        // artifacts for the remaining genuine transaction controls.
        std::fs::write(&file.path, &original).unwrap();
        erase.revalidate_artifacts().unwrap();
        assert!(
            refused,
            "a changed fresh {name} must revoke the retained owner"
        );
        cases.push(json!({"artifact": name, "path": file.path,
            "original_sha256": file.sha256, "changed_bytes_refused": true,
            "original_bytes_restored_and_revalidated": true}));
    }
    std::fs::write(
        library
            .inputs
            .output
            .join("paired-artifact-mutation-controls.json"),
        serde_json::to_vec_pretty(&cases).unwrap(),
    )
    .unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT: AtomicU64 = AtomicU64::new(0);

    struct Temp(std::path::PathBuf);

    impl Drop for Temp {
        fn drop(&mut self) {
            if !std::thread::panicking() {
                std::fs::remove_dir_all(&self.0).unwrap();
            }
        }
    }

    #[test]
    fn fresh_output_pins_refuse_redirects_and_changed_bytes() {
        let temp = Temp(std::env::temp_dir().join(format!(
            "trust-vc-paired-output-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        )));
        std::fs::create_dir(&temp.0).unwrap();
        let directory = temp.0.canonicalize().unwrap();
        let path = directory.join("libvstd.rlib");
        std::fs::write(&path, b"artifact bytes, not a producer authority").unwrap();
        let pin = pin_output(&path).unwrap();
        std::fs::write(&path, b"changed bytes").unwrap();
        assert!(pin.read().is_err());
        assert!(pin_output(&directory).is_err());
        assert!(pin_output(Path::new("relative.rlib")).is_err());
        #[cfg(unix)]
        {
            let alias = directory.join("alias.rlib");
            std::os::unix::fs::symlink(&path, &alias).unwrap();
            assert!(pin_output(&alias).is_err());
        }
    }
}
