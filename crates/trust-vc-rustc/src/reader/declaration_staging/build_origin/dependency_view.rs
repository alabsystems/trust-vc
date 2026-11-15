//! A closed native search directory with unique copied macro candidates.
//!
//! Nonmacro entries are owned symlinks to this actual builtin construction.
//! Native metadata selection must still canonicalize to the original files.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::BTreeSet;
use std::ffi::OsString;
use std::os::unix::fs::MetadataExt;

use super::*;

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

struct NonMacroLink {
    origin: BuiltArtifact,
    path: PathBuf,
    link_id: FileId,
    origin_id: FileId,
}

pub(in crate::reader::declaration_staging) struct DependencyView {
    root: PathBuf,
    root_id: FileId,
    copies: Vec<(PinnedFile, FileId)>,
    links: Vec<NonMacroLink>,
}

fn regular(file: &PinnedFile) -> Result<FileId, String> {
    let metadata = std::fs::symlink_metadata(&file.path).map_err(|e| e.to_string())?;
    if !metadata.file_type().is_file()
        || file.path.canonicalize().map_err(|e| e.to_string())? != file.path
    {
        return Err("the dependency view requires an original regular canonical file".into());
    }
    file.read()?;
    Ok(FileId::of(&metadata))
}

fn check_link(
    path: &Path,
    target: &PinnedFile,
    link_id: FileId,
    origin_id: FileId,
) -> Result<(), String> {
    let metadata = std::fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !metadata.file_type().is_symlink()
        || FileId::of(&metadata) != link_id
        || std::fs::read_link(path).map_err(|e| e.to_string())? != target.path
        || path.canonicalize().map_err(|e| e.to_string())? != target.path
        || regular(target)? != origin_id
    {
        return Err("an owned nonmacro link or its exact original artifact was replaced".into());
    }
    Ok(())
}

fn check_inventory(root: &Path, expected: &BTreeSet<OsString>) -> Result<(), String> {
    let mut actual = BTreeSet::new();
    for entry in std::fs::read_dir(root).map_err(|e| e.to_string())? {
        let name = entry.map_err(|e| e.to_string())?.file_name();
        if !expected.contains(&name) || !actual.insert(name) {
            return Err("the closed client dependency view has extra or repeated entries".into());
        }
    }
    if actual != *expected {
        return Err("the closed client dependency view has missing or extra entries".into());
    }
    Ok(())
}

impl BuiltCohort {
    pub(in crate::reader::declaration_staging) fn dependency_view(
        &self,
        sources: &Sources,
        copies: &[CopiedMacro],
    ) -> Result<DependencyView, String> {
        self.revalidate(sources)?;
        if copies.len() != 2 {
            return Err("the dependency view requires both genuine macro copies".into());
        }
        let root = copies[0]
            .file()
            .path
            .parent()
            .ok_or("copied macro has no directory")?
            .to_path_buf();
        let metadata = std::fs::symlink_metadata(&root).map_err(|e| e.to_string())?;
        if !metadata.is_dir() || root.canonicalize().map_err(|e| e.to_string())? != root {
            return Err("the client dependency root is not its owned canonical directory".into());
        }
        let mut physical = Vec::new();
        for copy in copies {
            copy.revalidate()?;
            if copy.file().path.parent() != Some(root.as_path()) {
                return Err("the genuine macro copies occupy different dependency views".into());
            }
            physical.push((copy.file().clone(), regular(copy.file())?));
        }
        let mut links = Vec::new();
        for name in CRATES.iter().filter(|name| name.ends_with(".rlib")) {
            let file = self.artifact(name)?;
            let origin = self.selected(sources, &file.path, file.sha256)?;
            let origin_id = regular(&file)?;
            let path = root.join(name);
            std::os::unix::fs::symlink(&file.path, &path).map_err(|e| e.to_string())?;
            let link_id = FileId::of(&std::fs::symlink_metadata(&path).map_err(|e| e.to_string())?);
            links.push(NonMacroLink {
                origin,
                path,
                link_id,
                origin_id,
            });
        }
        let root_id = FileId::of(&std::fs::symlink_metadata(&root).map_err(|e| e.to_string())?);
        let view = DependencyView {
            root,
            root_id,
            copies: physical,
            links,
        };
        view.revalidate()?;
        self.revalidate(sources)?;
        Ok(view)
    }
}

impl DependencyView {
    pub(in crate::reader::declaration_staging) fn revalidate(&self) -> Result<(), String> {
        let metadata = std::fs::symlink_metadata(&self.root).map_err(|e| e.to_string())?;
        if !metadata.is_dir()
            || FileId::of(&metadata) != self.root_id
            || self.root.canonicalize().map_err(|e| e.to_string())? != self.root
        {
            return Err("the owned client dependency directory was replaced".into());
        }
        let mut expected = BTreeSet::new();
        for (file, identity) in &self.copies {
            if regular(file)? != *identity {
                return Err("a physical macro copy was replaced".into());
            }
            expected.insert(
                file.path
                    .file_name()
                    .ok_or("macro copy has no filename")?
                    .to_os_string(),
            );
        }
        for link in &self.links {
            check_link(&link.path, link.origin.file(), link.link_id, link.origin_id)?;
            expected.insert(
                link.path
                    .file_name()
                    .ok_or("nonmacro link has no filename")?
                    .to_os_string(),
            );
        }
        check_inventory(&self.root, &expected)
    }

    pub(in crate::reader::declaration_staging) fn observation(
        &self,
    ) -> Result<serde_json::Value, String> {
        self.revalidate()?;
        Ok(
            serde_json::json!({"state": "ClosedClientDependencyView", "root": self.root,
            "physical_macros": self.copies.iter().map(|(file, _)|
                serde_json::json!({"path": file.path, "sha256": file.sha256}))
                .collect::<Vec<_>>(),
            "nonmacro_links": self.links.iter().map(|link|
                serde_json::json!({"path": link.path,
                    "target": link.origin.file().path, "origin": link.origin.observation()}))
                .collect::<Vec<_>>(),
            "import_authorized": false}),
        )
    }
}

#[cfg(test)]
mod tests;
