//! Fresh build provenance from the existing genuine builtin staging owner.
//!
//! This value cannot be reconstructed from a receipt or an artifact hash.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::declaration_alignment::source_bindings::{PinnedFile, SourceIdentity, Sources};
use crate::declaration_alignment::Digest;

mod macro_images;
pub(super) use macro_images::{CopiedMacro, LoadedMacro};
mod dependency_view;
pub(super) use dependency_view::DependencyView;

const SCRIPT: &[u8] = include_bytes!("../../../../../scripts/verus_suite/build_verus_builtins.sh");

#[cfg(test)]
mod tests;

// Exact archives selected by the approved upstream source/Cargo.lock.
const ARCHIVES: [(&str, &str); 7] = [
    (
        "unicode-ident-1.0.18.crate",
        "5a5f39404a5da50712a4c1eecf25e90dd62b613502b7e925fd4e4d19b5c96512",
    ),
    (
        "proc-macro2-1.0.101.crate",
        "89ae43fd86e4158d6db51ad8e2b80f313af9cc74f5c0e03ccb87de09998732de",
    ),
    (
        "quote-1.0.40.crate",
        "1885c039570dc00dcb4ff087a89e185fd56bae234ddc7f056a945bf36467248d",
    ),
    (
        "syn-2.0.101.crate",
        "8ce2b7fc941b3a24138a0a7cf8e858bfc6a992e7978a068a5c760deb0ed43caf",
    ),
    (
        "synstructure-0.13.2.crate",
        "728a70f3dbaf5bab7f0c4b1ac8d7ae5ea60a4b5549c8a5914361c99147a709d2",
    ),
    (
        "indexmap-1.9.3.crate",
        "bd070e393353796e801d209ad339e89596eb4c8d430d18ede6a1cced8fafbd99",
    ),
    (
        "hashbrown-0.12.3.crate",
        "8a9ee70c43aaf417c914396645a0fa852624801b24ebb7ae78fe8272889ac888",
    ),
];

const CRATES: [&str; 12] = [
    "libunicode_ident.rlib",
    "libproc_macro2.rlib",
    "libquote.rlib",
    "libsyn.rlib",
    "libsynstructure.rlib",
    "libverus_syn.rlib",
    "libverus_prettyplease.rlib",
    "libverus_builtin.rlib",
    "libhashbrown.rlib",
    "libindexmap.rlib",
    "libverus_builtin_macros.dylib",
    "libverus_state_machines_macros.dylib",
];

/// Only an actual successful owned invocation constructs this type. The source
/// identity still must match the library producer's approved source recipe.
pub(super) struct BuiltCohort {
    source: SourceIdentity,
    script: PinnedFile,
    compiler: PinnedFile,
    compiler_version: String,
    archive_inputs: Vec<PinnedFile>,
    archive_copies: Vec<PinnedFile>,
    artifacts: BTreeMap<PathBuf, PinnedFile>,
    linker: Option<PinnedFile>,
    compiler_driver: PinnedFile,
    host_tools: Vec<PinnedFile>,
    host_links: Vec<(PathBuf, PathBuf)>,
}

/// A selected output of this actual native build. No byte pin or observation
/// decoder can construct the token independently of the staging owner.
pub(super) struct BuiltArtifact {
    file: PinnedFile,
    source: SourceIdentity,
    script: Digest,
    driver: Digest,
}

impl BuiltArtifact {
    pub(super) fn file(&self) -> &PinnedFile {
        &self.file
    }
    pub(super) fn observation(&self) -> serde_json::Value {
        serde_json::json!({"state": "SelectedFreshNativeBuiltinOutput",
            "path": self.file.path, "sha256": self.file.sha256,
            "source_manifest_sha256": self.source.manifest_sha256,
            "builder_script_sha256": self.script, "compiler_driver_sha256": self.driver,
            "import_authorized": false})
    }
}

fn digest(bytes: &[u8]) -> Digest {
    use sha2::{Digest as _, Sha256};
    Sha256::digest(bytes).into()
}

fn hexadecimal(value: Digest) -> String {
    value.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn output_artifact(output: &Path, name: &str) -> Result<PinnedFile, String> {
    let entry = output.join(name);
    // Check the actual output entry before canonicalization can follow a
    // symlink to a preexisting file outside the owned construction directory.
    let metadata = std::fs::symlink_metadata(&entry).map_err(|e| e.to_string())?;
    if !metadata.file_type().is_file() {
        return Err("a genuine builtin output entry is not a regular file".into());
    }
    let path = entry.canonicalize().map_err(|e| e.to_string())?;
    if output.canonicalize().map_err(|e| e.to_string())? != output || !path.starts_with(output) {
        return Err("a genuine builtin output leaves the fresh canonical directory".into());
    }
    Ok(PinnedFile {
        sha256: digest(&std::fs::read(&path).map_err(|e| e.to_string())?),
        path,
    })
}

fn compiler() -> Result<(PinnedFile, String), String> {
    let program = Path::new(env!("VC_SHIM_COMPILER_SYSROOT"))
        .join("bin/trustc")
        .canonicalize()
        .map_err(|e| e.to_string())?;
    let file = PinnedFile {
        sha256: digest(&std::fs::read(&program).map_err(|e| e.to_string())?),
        path: program,
    };
    let version = Command::new(&file.path)
        .arg("-vV")
        .output()
        .map_err(|e| e.to_string())?;
    if !version.status.success() {
        return Err("the genuine native builder compiler did not report its identity".into());
    }
    let version = String::from_utf8(version.stdout).map_err(|e| e.to_string())?;
    if !version
        .lines()
        .any(|line| line == format!("commit-hash: {}", env!("VC_SHIM_COMPILER_COMMIT")))
    {
        return Err(
            "the builtin builder compiler differs from the producer's pinned compiler".into(),
        );
    }
    let actual_root = Command::new(&file.path)
        .args(["--print", "sysroot"])
        .output()
        .map_err(|e| e.to_string())?;
    if !actual_root.status.success() {
        return Err("the builtin compiler did not report its sysroot".into());
    }
    let actual_root = String::from_utf8(actual_root.stdout).map_err(|e| e.to_string())?;
    let actual_root = Path::new(actual_root.trim())
        .canonicalize()
        .map_err(|e| e.to_string())?;
    let expected_root = Path::new(env!("VC_SHIM_COMPILER_SYSROOT"))
        .canonicalize()
        .map_err(|e| e.to_string())?;
    if actual_root != expected_root {
        return Err("the builder compiler uses another native sysroot".into());
    }
    Ok((file, version))
}

pub(super) fn build(
    sources: &Sources,
    archives: &[PinnedFile],
    output: &Path,
    compiler_driver: &PinnedFile,
) -> Result<BuiltCohort, String> {
    sources.revalidate()?;
    let output = super::inputs::canonical_output(output, sources.root())?;
    compiler_driver.read()?;
    if super::identity::loaded_driver_path()? != compiler_driver.path {
        return Err(
            "the builtin constructor is not bound to the actual producer compiler image".into(),
        );
    }
    if archives.len() != ARCHIVES.len() {
        return Err("builtin construction needs all seven locked archives".into());
    }
    let mut selected = BTreeMap::new();
    for archive in archives {
        let name = archive
            .path
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or("registry archive has no represented filename")?;
        let expected = ARCHIVES
            .iter()
            .find(|(expected, _)| *expected == name)
            .ok_or("archive is outside the exact upstream builtin lock closure")?
            .1;
        let bytes = archive.read()?;
        if hexadecimal(digest(&bytes)) != expected
            || selected.insert(name, (archive, bytes)).is_some()
        {
            return Err(
                "registry archive checksum or uniqueness does not match the upstream lock".into(),
            );
        }
    }
    let (compiler, compiler_version) = compiler()?;
    std::fs::create_dir(&output).map_err(|e| e.to_string())?;
    std::fs::create_dir(output.join("src")).map_err(|e| e.to_string())?;
    let mut archive_copies = Vec::new();
    for (name, (archive, bytes)) in selected {
        let path = output.join("src").join(name);
        std::fs::write(&path, bytes).map_err(|e| e.to_string())?;
        let file = PinnedFile {
            path,
            sha256: archive.sha256,
        };
        file.read()?;
        archive_copies.push(file);
    }
    // All seven OUT/src archives precede cached archives in registry_source.
    // Their verified presence makes its registry/src fallback unreachable.
    let script_path = output.join("build-builtins.sh");
    std::fs::write(&script_path, SCRIPT).map_err(|e| e.to_string())?;
    let script = PinnedFile {
        path: script_path,
        sha256: digest(SCRIPT),
    };
    let tools = output.join("tools");
    std::fs::create_dir(&tools).map_err(|e| e.to_string())?;
    let mut host_links = Vec::new();
    let trustc = tools.join("trustc");
    std::os::unix::fs::symlink(&compiler.path, &trustc).map_err(|e| e.to_string())?;
    host_links.push((trustc, compiler.path.clone()));
    let mut host_tools = Vec::new();
    for tool in [
        "/bin/bash",
        "/usr/bin/awk",
        "/usr/bin/shasum",
        "/usr/bin/perl",
        "/usr/bin/tar",
        "/bin/mkdir",
        "/usr/bin/dirname",
        "/usr/bin/tee",
        "/usr/bin/tail",
        "/bin/ls",
    ] {
        let path = Path::new(tool).canonicalize().map_err(|e| e.to_string())?;
        let invocation = tools.join(Path::new(tool).file_name().ok_or("host tool has no name")?);
        std::os::unix::fs::symlink(&path, &invocation).map_err(|e| e.to_string())?;
        host_links.push((invocation, path.clone()));
        host_tools.push(PinnedFile {
            sha256: digest(&std::fs::read(&path).map_err(|e| e.to_string())?),
            path,
        });
    }
    for directory in ["home", "cargo-home", ".ubd"] {
        std::fs::create_dir(output.join(directory)).map_err(|e| e.to_string())?;
    }
    let linker = std::env::var_os("CARGO_TARGET_AARCH64_APPLE_DARWIN_LINKER")
        .map(|path| -> Result<PinnedFile, String> {
            let path = PathBuf::from(path)
                .canonicalize()
                .map_err(|e| e.to_string())?;
            Ok(PinnedFile {
                sha256: digest(&std::fs::read(&path).map_err(|e| e.to_string())?),
                path,
            })
        })
        .transpose()?;
    let mut command = Command::new("/bin/bash");
    command
        .arg(&script.path)
        .arg(&output)
        .arg(sources.root())
        .env_clear()
        .env("PATH", &tools)
        .env("HOME", output.join("home"))
        .env("CARGO_HOME", output.join("cargo-home"))
        .env("TMPDIR", output.join(".ubd"))
        .env("LANG", "C")
        .env("RUST_MIN_STACK", "20971520");
    if let Some(linker) = &linker {
        command.env("TRUST_VC_BUILTINS_LINKER", &linker.path);
    }
    let stdout = std::fs::File::create(output.join("builder.stdout")).map_err(|e| e.to_string())?;
    let stderr = std::fs::File::create(output.join("builder.stderr")).map_err(|e| e.to_string())?;
    let status = command
        .stdout(stdout)
        .stderr(stderr)
        .status()
        .map_err(|e| e.to_string())?;
    std::fs::write(
        output.join("builder-terminal.json"),
        serde_json::to_vec_pretty(&serde_json::json!({
        "exit": status.code(), "signal_or_abnormal": status.code().is_none(),
        "script_sha256": script.sha256, "compiler_sha256": compiler.sha256,
        "source_manifest_sha256": sources.identity().manifest_sha256,
        "scope": "actual native infrastructure build, no proof/import authority"}))
        .map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    if !status.success() {
        return Err("the genuine locked builtin builder failed; first logs preserved".into());
    }
    let reported =
        std::fs::read_to_string(output.join("trustc-version.txt")).map_err(|e| e.to_string())?;
    if reported != compiler_version {
        return Err("builder PATH selected a different native compiler".into());
    }
    let mut artifacts = BTreeMap::new();
    for name in CRATES {
        let file = output_artifact(&output, name)?;
        artifacts.insert(file.path.clone(), file);
    }
    let result = BuiltCohort {
        source: sources.identity(),
        script,
        compiler,
        compiler_version,
        archive_inputs: archives.to_vec(),
        archive_copies,
        artifacts,
        linker,
        compiler_driver: compiler_driver.clone(),
        host_tools,
        host_links,
    };
    result.revalidate(sources)?;
    Ok(result)
}

impl BuiltCohort {
    /// Test-only mutation targets from this completed owned construction.
    /// Compiler images, artifacts and input archives are never returned.
    #[cfg(test)]
    pub(in crate::reader::declaration_staging) fn transaction_files(
        &self,
    ) -> Result<[PinnedFile; 2], String> {
        let root = self
            .script
            .path
            .parent()
            .ok_or("the owned test script has no parent")?;
        if root.canonicalize().map_err(|e| e.to_string())? != root {
            return Err("the owned test construction root is not canonical".into());
        }
        let archive = self
            .archive_copies
            .first()
            .ok_or("the actual construction has no owned archive copy")?;
        let archive_directory = root.join("src");
        if archive.path.parent() != Some(archive_directory.as_path()) {
            return Err("the owned test archive has another construction root".into());
        }
        for file in [&self.script, archive] {
            if !std::fs::symlink_metadata(&file.path)
                .map_err(|e| e.to_string())?
                .file_type()
                .is_file()
                || file.path.canonicalize().map_err(|e| e.to_string())? != file.path
                || !file.path.starts_with(root)
            {
                return Err("a transaction mutation target is not an owned regular leaf".into());
            }
            file.read()?;
        }
        Ok([self.script.clone(), archive.clone()])
    }

    pub(super) fn artifact(&self, name: &str) -> Result<PinnedFile, String> {
        self.artifacts
            .values()
            .find(|file| {
                file.path
                    .file_name()
                    .is_some_and(|file_name| file_name == name)
            })
            .cloned()
            .ok_or_else(|| format!("the actual builtin build has no {name}"))
    }

    pub(super) fn selected(
        &self,
        sources: &Sources,
        path: &Path,
        sha256: Digest,
    ) -> Result<BuiltArtifact, String> {
        self.revalidate(sources)?;
        let file = self
            .artifacts
            .get(path)
            .ok_or("native selection is not an output of this builtin construction")?;
        if file.sha256 != sha256 {
            return Err("native selection differs from the freshly constructed artifact".into());
        }
        Ok(BuiltArtifact {
            file: file.clone(),
            source: self.source,
            script: self.script.sha256,
            driver: self.compiler_driver.sha256,
        })
    }

    pub(super) fn revalidate(&self, sources: &Sources) -> Result<(), String> {
        sources.revalidate()?;
        if sources.identity() != self.source {
            return Err("builtin build source identity changed".into());
        }
        self.script.read()?;
        self.compiler.read()?;
        self.compiler_driver.read()?;
        if super::identity::loaded_driver_path()? != self.compiler_driver.path {
            return Err("the producer compiler image changed after builtin construction".into());
        }
        for file in self
            .archive_inputs
            .iter()
            .chain(&self.archive_copies)
            .chain(self.artifacts.values())
            .chain(&self.host_tools)
        {
            file.read()?;
        }
        if let Some(linker) = &self.linker {
            linker.read()?;
        }
        for (invocation, target) in &self.host_links {
            if !std::fs::symlink_metadata(invocation)
                .map_err(|e| e.to_string())?
                .file_type()
                .is_symlink()
                || std::fs::read_link(invocation).map_err(|e| e.to_string())? != *target
                || invocation.canonicalize().map_err(|e| e.to_string())? != *target
            {
                return Err("an exact native builder command changed its owned resolution".into());
            }
        }
        Ok(())
    }

    pub(super) fn observation(&self) -> serde_json::Value {
        serde_json::json!({"state": "FreshNativeBuiltinBuild",
            "source_manifest_sha256": self.source.manifest_sha256,
            "compatibility_recipe_sha256": self.source.compatibility.recipe_sha256(),
            "compatibility_patch_sha256": self.source.compatibility.patch_sha256(),
            "builder_script_sha256": self.script.sha256,
            "upstream_registry_archive_sha256": self.archive_inputs.iter()
                .map(|file| serde_json::json!({"path": file.path, "sha256": file.sha256}))
                .collect::<Vec<_>>(),
            "actual_compiler_sha256": self.compiler.sha256,
            "actual_compiler_driver_sha256": self.compiler_driver.sha256,
            "actual_compiler_version": self.compiler_version,
            "host_tools": self.host_tools.iter().map(|file| serde_json::json!({
                "path": file.path, "sha256": file.sha256})).collect::<Vec<_>>(),
            "resolved_commands": self.host_links.iter().map(|(invocation, target)|
                serde_json::json!({"invocation": invocation, "canonical_target": target}))
                .collect::<Vec<_>>(),
            "linker": self.linker.as_ref().map(|file| serde_json::json!({
                "path": file.path, "sha256": file.sha256})),
            "artifacts": self.artifacts.values().map(|file| serde_json::json!({
                "path": file.path, "sha256": file.sha256})).collect::<Vec<_>>(),
            "import_authorized": false, "verified_functions": null})
    }
}
