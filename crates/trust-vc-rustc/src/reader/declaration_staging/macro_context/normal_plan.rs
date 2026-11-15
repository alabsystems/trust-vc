// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Bind one normal invocation request to the real source and native owner.

use super::super::invocation::NormalNativeRequest;
use super::*;
use crate::shim::NormalInvocation;
use std::collections::BTreeSet;
use std::path::PathBuf;
use std::sync::Arc;

/// Opaque request identity only. It does not authorize an import or a body.
pub(crate) struct NormalPlanIdentity {
    _private: u8,
}

pub(crate) struct NormalClientPlan<'owner> {
    owner: &'owner standalone_client::StandaloneImported<'owner>,
    source: &'owner ClientSource,
    invocation: NormalInvocation,
    source_operand: PathBuf,
    identity: Arc<NormalPlanIdentity>,
    native: NormalNativeRequest,
}

impl<'owner> NormalClientPlan<'owner> {
    pub(in crate::reader::declaration_staging) fn closed(
        owner: &'owner standalone_client::StandaloneImported<'owner>,
        source: &'owner ClientSource,
        output: &Path,
        erase_output: &Path,
    ) -> Result<Self, String> {
        owner.check_retained_inputs()?;
        let macros = owner.macro_files().collect::<Vec<_>>();
        let args = normal_client_args(owner.library(), source, &macros, output, erase_output)?;
        Self::finish(owner, source, NormalInvocation::closed_standalone(args)?)
    }

    /// This represents the supplied CLI request; it never regenerates the
    /// closed vstd command and labels that different command as the caller's.
    pub(in crate::reader::declaration_staging) fn from_invocation(
        owner: &'owner standalone_client::StandaloneImported<'owner>,
        source: &'owner ClientSource,
        invocation: NormalInvocation,
    ) -> Result<Self, String> {
        owner.check_retained_inputs()?;
        let split = invocation
            .original()
            .ok_or("a closed standalone plan is not a CLI request")?;
        represented_options(split)?;
        invocation.source_matches(source.file())?;
        if invocation.source_operand()? != source.file().path.as_path() {
            return Err(
                "the owned CLI source operand must be its exact canonical source path".into(),
            );
        }
        represented_operands(owner, split, source)?;
        Self::finish(owner, source, invocation)
    }

    fn finish(
        owner: &'owner standalone_client::StandaloneImported<'owner>,
        source: &'owner ClientSource,
        invocation: NormalInvocation,
    ) -> Result<Self, String> {
        invocation.source_matches(source.file())?;
        let source_operand = invocation.source_operand()?.to_path_buf();
        let native = NormalNativeRequest::capture(invocation.verify())?;
        owner.check_retained_inputs()?;
        Ok(Self {
            owner,
            source,
            invocation,
            source_operand,
            identity: Arc::new(NormalPlanIdentity { _private: 0 }),
            native,
        })
    }

    pub(crate) fn verify(&self) -> &[String] {
        self.invocation.verify()
    }
    pub(crate) fn erase(&self) -> &[String] {
        self.invocation.erase()
    }
    pub(crate) fn invocation(&self) -> &NormalInvocation {
        &self.invocation
    }
    pub(crate) fn source_file(&self) -> &PinnedFile {
        self.source.file()
    }
    pub(crate) fn source_operand(&self) -> &Path {
        &self.source_operand
    }
    pub(crate) fn identity(&self) -> Arc<NormalPlanIdentity> {
        Arc::clone(&self.identity)
    }

    pub(crate) fn check_native_context(&self, tcx: TyCtxt<'_>) -> Result<(), String> {
        self.check_owner(self.owner, self.source)?;
        let images = self.owner.inspect(tcx, self.verify())?;
        images.current(tcx)?;
        self.owner
            .library()
            .prepared
            .erase
            .invocation
            .check_normal_client(tcx, &self.native)
    }

    pub(in crate::reader::declaration_staging) fn check_owner(
        &self,
        owner: &standalone_client::StandaloneImported<'_>,
        source: &ClientSource,
    ) -> Result<(), String> {
        if !std::ptr::eq(self.owner, owner) || !std::ptr::eq(self.source, source) {
            return Err(
                "the normal invocation plan belongs to another actual owner or source".into(),
            );
        }
        self.invocation.source_matches(source.file())?;
        owner.check_retained_inputs()
    }
}

fn represented_options(split: &crate::args::SplitArgs) -> Result<(), String> {
    for option in &split.verus {
        match option.name.as_str() {
            "no-external-by-default"
            | "no-verify"
            | "no-lifetime"
            | "no-erasure-check"
            | "no-auto-recommends-check"
            | "no-cheating"
            | "rlimit"
            | "multiple-errors"
            | "compile"
            | "no-vstd" => {}
            "V" if option.value.as_deref() == Some("new-mut-ref") => {}
            // Import/export descriptors and their replay worker are not yet
            // represented. Their spelling cannot supply a native permission.
            name => {
                return Err(format!(
                    "the owned normal request does not represent --{name}"
                ))
            }
        }
    }
    Ok(())
}

fn represented_operands(
    owner: &standalone_client::StandaloneImported<'_>,
    split: &crate::args::SplitArgs,
    source: &ClientSource,
) -> Result<(), String> {
    let library = owner.library();
    // Aliases are request operands, never authority. Bind the actual files;
    // the following compiler's CStore supplies their real native identities.
    let mut expected = BTreeSet::from([
        library.prepared.erase.file.path.clone(),
        library.inputs.builtin.path.clone(),
    ]);
    for file in owner.macro_files() {
        if !expected.insert(file.path.clone()) {
            return Err("the native owner duplicates an actual image".into());
        }
    }
    if expected.len() != 4 {
        return Err("the owned normal request lacks its exact four externs".into());
    }
    let directories = owner.native_dependency_directories()?;
    let args = &split.rustc;
    if args.iter().any(|argument| argument.starts_with('@')) {
        return Err("response files are not represented by the owned normal request".into());
    }
    let mut seen = BTreeSet::new();
    let mut selected = BTreeSet::new();
    let mut outputs = 0;
    let mut sources = 0;
    let mut emits = 0;
    let mut at = 0;
    while at < args.len() {
        let argument = &args[at];
        if argument.starts_with('@') {
            return Err("response files are not represented by the owned normal request".into());
        }
        let (kind, value, consumed) = if [
            "--extern",
            "-L",
            "--sysroot",
            "--target",
            "--cfg",
            "-Z",
            "-o",
            "--emit",
            "--edition",
            "--crate-name",
            "--crate-type",
            "--error-format",
            "--cap-lints",
            "-A",
            "-W",
            "-D",
            "-F",
            "--allow",
            "--warn",
            "--deny",
            "--forbid",
        ]
        .contains(&argument.as_str())
        {
            (
                argument.as_str(),
                args.get(at + 1)
                    .ok_or("an owned native operand is incomplete")?
                    .as_str(),
                2,
            )
        } else if let Some(value) = argument.strip_prefix("--extern=") {
            ("--extern", value, 1)
        } else if let Some(value) = argument.strip_prefix("--sysroot=") {
            ("--sysroot", value, 1)
        } else if let Some(value) = argument.strip_prefix("--target=") {
            ("--target", value, 1)
        } else if let Some(value) = argument.strip_prefix("--cfg=") {
            ("--cfg", value, 1)
        } else if let Some(value) = argument.strip_prefix("--emit=") {
            ("--emit", value, 1)
        } else if let Some(value) = argument.strip_prefix("--edition=") {
            ("--edition", value, 1)
        } else if let Some(value) = argument.strip_prefix("--crate-name=") {
            ("--crate-name", value, 1)
        } else if let Some(value) = argument.strip_prefix("--crate-type=") {
            ("--crate-type", value, 1)
        } else if let Some(value) = argument.strip_prefix("--error-format=") {
            ("--error-format", value, 1)
        } else if let Some(value) = argument.strip_prefix("--cap-lints=") {
            ("--cap-lints", value, 1)
        } else if let Some(value) = argument.strip_prefix("--allow=") {
            ("--allow", value, 1)
        } else if let Some(value) = argument.strip_prefix("--warn=") {
            ("--warn", value, 1)
        } else if let Some(value) = argument.strip_prefix("--deny=") {
            ("--deny", value, 1)
        } else if let Some(value) = argument.strip_prefix("--forbid=") {
            ("--forbid", value, 1)
        } else if let Some(value) = argument.strip_prefix("-L").filter(|s| !s.is_empty()) {
            ("-L", value, 1)
        } else if let Some(value) = argument.strip_prefix("-Z").filter(|s| !s.is_empty()) {
            ("-Z", value, 1)
        } else if let Some(value) = argument.strip_prefix("-o").filter(|s| !s.is_empty()) {
            ("-o", value, 1)
        } else if let Some(value) = argument.strip_prefix("-A").filter(|s| !s.is_empty()) {
            ("-A", value, 1)
        } else if let Some(value) = argument.strip_prefix("-W").filter(|s| !s.is_empty()) {
            ("-W", value, 1)
        } else if let Some(value) = argument.strip_prefix("-D").filter(|s| !s.is_empty()) {
            ("-D", value, 1)
        } else if let Some(value) = argument.strip_prefix("-F").filter(|s| !s.is_empty()) {
            ("-F", value, 1)
        } else if Path::new(argument) == source.file().path {
            ("source", argument.as_str(), 1)
        } else {
            return Err(format!(
                "the owned normal request does not represent rustc operand {argument}"
            ));
        };
        match kind {
            "--extern" => {
                let (name, path) = value
                    .split_once('=')
                    .ok_or("an owned extern is incomplete")?;
                let name = name.strip_prefix("force:").unwrap_or(name);
                if name.is_empty()
                    || !seen.insert(name.to_string())
                    || !expected.contains(Path::new(path))
                    || !selected.insert(PathBuf::from(path))
                {
                    return Err(
                        "the actual CLI extern is outside the exact owned image inventory".into(),
                    );
                }
            }
            "-L" => {
                let path = value.strip_prefix("dependency=").unwrap_or(value);
                if !directories.contains(Path::new(path)) {
                    return Err(
                        "the CLI search operand is outside the owned dependency view".into(),
                    );
                }
            }
            "--sysroot" if Path::new(value) == library.prepared.erase.invocation.sysroot() => {}
            "-Z" if ["unstable-options", "write_long_types_to_disk=no"].contains(&value) => {}
            "--sysroot" | "--target" | "-Z" => {
                return Err(
                    "the owned CLI target/sysroot or unstable option is not represented".into(),
                )
            }
            "--cfg"
                if ["verus_only", "verus_keep_ghost", "verus_keep_ghost_body"]
                    .contains(&value.split('=').next().unwrap_or(value)) =>
            {
                return Err(
                    "the caller cannot replace the normal verify/erase projection cfgs".into(),
                );
            }
            "--cfg" => {
                super::super::invocation::NormalNativeRequest::check_cfg(value)?;
            }
            "-o" => {
                outputs += 1;
                let output =
                    inputs::canonical_output(Path::new(value), library.inputs.sources.root())?;
                if output != Path::new(value) || output == source.file().path {
                    return Err("the normal output must be its exact fresh canonical path".into());
                }
            }
            "--emit" => {
                emits += 1;
                if !["metadata", "link"].contains(&value) {
                    return Err("explicit or multiple emit destinations are not represented by the owned normal request".into());
                }
            }
            "--edition" if ["2015", "2018", "2021", "2024"].contains(&value) => {}
            "--crate-type" if ["lib", "rlib"].contains(&value) => {}
            "--error-format" if value == "json" => {}
            "--crate-name" if !value.is_empty() && !value.starts_with('-') => {}
            "--cap-lints" if ["allow", "warn", "deny", "forbid"].contains(&value) => {}
            "-A" | "-W" | "-D" | "-F" | "--allow" | "--warn" | "--deny" | "--forbid"
                if !value.is_empty() && !value.starts_with('-') => {}
            "source" => {
                sources += 1;
            }
            _ => {
                return Err(
                    "the owned normal request contains an unrepresented native value".into(),
                )
            }
        }
        at += consumed;
    }
    if selected != expected {
        return Err(
            "the CLI request does not select the complete exact native owner inventory".into(),
        );
    }
    if outputs != 1 || sources != 1 || emits > 1 {
        return Err("the owned normal request has ambiguous source/output operands".into());
    }
    Ok(())
}
