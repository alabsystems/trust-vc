//! A live owner's exact native images published through an owned link layout.
//!
//! The layout borrows its constructor's owner. It supplies neither declarations
//! nor bodies, and a path, hash or serialized observation cannot reconstruct it.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::BTreeMap;
use std::os::unix::fs::{symlink, MetadataExt};
use std::path::{Path, PathBuf};

use super::super::{inputs, PinnedFile};
use super::StandaloneImported;

mod native_reference;
use native_reference::NativeReference;

#[derive(Clone, Copy, PartialEq, Eq)]
struct FileId {
    device: u64,
    inode: u64,
    changed: i64,
    changed_nsec: i64,
}

impl FileId {
    fn of(metadata: &std::fs::Metadata) -> Self {
        Self {
            device: metadata.dev(),
            inode: metadata.ino(),
            changed: metadata.ctime(),
            changed_nsec: metadata.ctime_nsec(),
        }
    }
}

struct NativeAlias {
    target: PinnedFile,
    link_id: FileId,
}

/// Only `prepare` constructs this value, from the same still-live native owner.
/// Its five links are data operands; the native callback must still match the
/// exact original target/common/macro selections and their genuine provenance.
pub(in crate::reader::declaration_staging) struct PreparedSdk<'owner> {
    owner: &'owner StandaloneImported<'owner>,
    root: PathBuf,
    root_id: FileId,
    aliases: BTreeMap<PathBuf, NativeAlias>,
    frontends: BTreeMap<PathBuf, NativeAlias>,
    reference: NativeReference,
}

fn regular(file: &PinnedFile) -> Result<(), String> {
    let metadata = std::fs::symlink_metadata(&file.path).map_err(|e| e.to_string())?;
    if !metadata.file_type().is_file()
        || file.path.canonicalize().map_err(|e| e.to_string())? != file.path
    {
        return Err("a prepared SDK target is not its exact canonical regular file".into());
    }
    file.read()?;
    Ok(())
}

impl<'owner> PreparedSdk<'owner> {
    pub(in crate::reader::declaration_staging) fn prepare(
        owner: &'owner StandaloneImported<'owner>,
        requested: &Path,
    ) -> Result<Self, String> {
        Self::prepare_with_frontends(owner, requested, &[])
    }

    /// Frontends are retained byte inputs, never native library authority.
    /// Publish every selected entry before sealing the final directory; later
    /// staging must neither append entries nor overwrite these owned links.
    pub(in crate::reader::declaration_staging) fn prepare_with_frontends(
        owner: &'owner StandaloneImported<'owner>,
        requested: &Path,
        frontends: &[(&str, PinnedFile)],
    ) -> Result<Self, String> {
        owner.check_retained_inputs()?;
        let library = owner.library();
        let root = inputs::canonical_output(requested, library.inputs.sources.root())?;
        let mut targets = BTreeMap::new();
        for file in [&library.inputs.builtin]
            .into_iter()
            .chain(owner.macro_files())
            .chain(library.prepared.erase.native_images())
        {
            regular(file)?;
            let name = file
                .path
                .file_name()
                .ok_or("a native SDK target has no filename")?;
            if targets.insert(name.to_os_string(), file.clone()).is_some() {
                return Err("the native SDK owner repeats an image filename".into());
            }
        }
        let expected = [
            "libverus_builtin.rlib",
            "libverus_builtin_macros.dylib",
            "libverus_state_machines_macros.dylib",
            "libvstd.rmeta",
            "libvstd.rlib",
        ];
        if targets.len() != expected.len()
            || expected
                .iter()
                .any(|name| !targets.contains_key(std::ffi::OsStr::new(name)))
        {
            return Err("the live SDK owner lacks its exact five native images".into());
        }
        let mut frontend_targets = BTreeMap::new();
        for (name, file) in frontends {
            if !matches!(
                *name,
                "rust_verify"
                    | "rust_verify.real"
                    | "rust_verify.execution.py"
                    | "verus"
                    | "verus.real"
                    | "verus.execution.py"
                    | "execution-lender"
                    | "cargo-verus"
                    | "vstd_metadata_inspect"
                    | "vstd_declaration_observe"
                    | "vstd_declaration_stage"
                    | "vstd_macro_context_observe"
                    | "vstd_declaration_read"
                    | "vstd_declaration_verify"
                    | "vstd_normal_client_verify"
                    | "vstd_sdk_client"
                    | "rust_verify.public"
            ) || frontend_targets.insert(*name, file.clone()).is_some()
            {
                return Err(
                    "the SDK staging frontend inventory has an unrepresented or repeated name"
                        .into(),
                );
            }
            regular(file)?;
        }
        std::fs::create_dir(&root).map_err(|e| e.to_string())?;
        let mut aliases = BTreeMap::new();
        for (name, target) in targets {
            let path = root.join(name);
            symlink(&target.path, &path).map_err(|e| e.to_string())?;
            let metadata = std::fs::symlink_metadata(&path).map_err(|e| e.to_string())?;
            aliases.insert(
                path,
                NativeAlias {
                    target,
                    link_id: FileId::of(&metadata),
                },
            );
        }
        let mut frontends = BTreeMap::new();
        for (name, target) in frontend_targets {
            let path = root.join(name);
            symlink(&target.path, &path).map_err(|e| e.to_string())?;
            let metadata = std::fs::symlink_metadata(&path).map_err(|e| e.to_string())?;
            frontends.insert(
                path,
                NativeAlias {
                    target,
                    link_id: FileId::of(&metadata),
                },
            );
        }
        let reference = NativeReference::create(owner, &root, &aliases)?;
        let root_id = FileId::of(&std::fs::symlink_metadata(&root).map_err(|e| e.to_string())?);
        let layout = Self {
            owner,
            root,
            root_id,
            aliases,
            frontends,
            reference,
        };
        layout.check_owner(owner)?;
        Ok(layout)
    }

    pub(in crate::reader::declaration_staging) fn root(&self) -> &Path {
        &self.root
    }

    pub(in crate::reader::declaration_staging) fn reference_path(&self) -> &Path {
        self.reference.path()
    }

    /// Recognize only this live layout's actual native reference operand.
    /// Its bytes describe the SDK; they never construct an import owner.
    pub(in crate::reader::declaration_staging) fn represents_import(
        &self,
        owner: &StandaloneImported<'_>,
        operand: &str,
    ) -> Result<bool, String> {
        self.check_owner(owner)?;
        Ok(self.reference.represents(operand))
    }

    pub(in crate::reader::declaration_staging) fn check_owner(
        &self,
        owner: &StandaloneImported<'_>,
    ) -> Result<(), String> {
        if !std::ptr::eq(self.owner, owner) {
            return Err("the prepared SDK belongs to another live native owner".into());
        }
        owner.check_retained_inputs()?;
        let metadata = std::fs::symlink_metadata(&self.root).map_err(|e| e.to_string())?;
        if !metadata.file_type().is_dir()
            || FileId::of(&metadata) != self.root_id
            || self.root.canonicalize().map_err(|e| e.to_string())? != self.root
        {
            return Err("the prepared SDK root was changed or replaced".into());
        }
        let actual = std::fs::read_dir(&self.root)
            .map_err(|e| e.to_string())?
            .map(|entry| entry.map(|entry| entry.path()).map_err(|e| e.to_string()))
            .collect::<Result<std::collections::BTreeSet<_>, _>>()?;
        if actual
            != self
                .aliases
                .keys()
                .chain(self.frontends.keys())
                .map(|path| path.as_path())
                .chain(std::iter::once(self.reference.path()))
                .map(Path::to_path_buf)
                .collect()
        {
            return Err("the prepared SDK has missing or unowned directory entries".into());
        }
        for (path, alias) in self.aliases.iter().chain(&self.frontends) {
            let metadata = std::fs::symlink_metadata(path).map_err(|e| e.to_string())?;
            if !metadata.file_type().is_symlink()
                || FileId::of(&metadata) != alias.link_id
                || std::fs::read_link(path).map_err(|e| e.to_string())? != alias.target.path
                || path.canonicalize().map_err(|e| e.to_string())? != alias.target.path
            {
                return Err(
                    "a prepared SDK link no longer selects its exact retained image".into(),
                );
            }
            regular(&alias.target)?;
        }
        self.reference.revalidate()?;
        owner.check_retained_inputs()
    }

    /// Resolve only a link created by this exact live layout. This is not a
    /// general canonical-path equivalence rule for ordinary extern operands.
    pub(in crate::reader::declaration_staging) fn resolve(
        &self,
        owner: &StandaloneImported<'_>,
        operand: &Path,
    ) -> Result<Option<&PinnedFile>, String> {
        self.check_owner(owner)?;
        Ok(self.aliases.get(operand).map(|alias| &alias.target))
    }
}
