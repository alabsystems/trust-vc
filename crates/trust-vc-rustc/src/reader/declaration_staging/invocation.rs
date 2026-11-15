//! Native invocation facts owned by one staging callback.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

extern crate rustc_session;
extern crate rustc_target;

use std::collections::BTreeSet;
use std::path::PathBuf;

use rustc_middle::ty::TyCtxt;
use rustc_session::config::Options;
use rustc_target::spec::Target;
use serde_json::{json, Value};
use sha2::{Digest as _, Sha256};

use crate::declaration_alignment::Digest;

mod normal_request;
pub(super) use normal_request::NormalNativeRequest;

pub(super) struct Invocation {
    // Retain native typed options/target. Debug output is never their identity.
    options: Options,
    target: Target,
    cfg: BTreeSet<(String, Option<String>)>,
    sysroot: PathBuf,
    argv: Vec<String>,
}

fn normalized_library_args(argv: &[String], keep: bool) -> Option<Vec<String>> {
    let mut normalized = Vec::new();
    let mut at = 0;
    let mut outputs = 0;
    let mut body_flags = 0;
    while at < argv.len() {
        if argv[at] == "-o" {
            let path = argv.get(at + 1)?;
            if !std::path::Path::new(path).is_absolute() {
                return None;
            }
            outputs += 1;
            normalized.extend(["-o".into(), "<owned-metadata-output>".into()]);
            at += 2;
        } else if argv[at] == "--cfg"
            && argv
                .get(at + 1)
                .is_some_and(|value| value == "verus_keep_ghost_body")
        {
            body_flags += 1;
            at += 2;
        } else {
            normalized.push(argv[at].clone());
            at += 1;
        }
    }
    (outputs == 1 && body_flags == usize::from(keep)).then_some(normalized)
}

impl Invocation {
    pub(super) fn capture(tcx: TyCtxt<'_>, argv: &[String]) -> Result<Self, String> {
        Self::capture_for(tcx, argv, "IsVstd")
    }

    /// Importing code has a different genuine macro expansion context from
    /// the vstd crate itself. This check does not reset a loaded macro's
    /// internal process state; the staging owner must establish that context
    /// before using an importing client, rather than relabel IsVstd as one.
    pub(super) fn capture_client(tcx: TyCtxt<'_>, argv: &[String]) -> Result<Self, String> {
        let invocation = Self::capture_for(tcx, argv, "Imported")?;
        if ["verus_keep_ghost", "verus_keep_ghost_body"]
            .into_iter()
            .any(|name| !invocation.cfg.contains(&(name.into(), None)))
        {
            return Err("the actual importing client must retain its original ghost bodies".into());
        }
        Ok(invocation)
    }

    fn capture_for(tcx: TyCtxt<'_>, argv: &[String], macro_context: &str) -> Result<Self, String> {
        let session = tcx.sess;
        if session.trust_verification_enabled()
            || session.trust_ir_lower_enabled()
            || session.opts.unstable_opts.trust_targo_test_monitor
            || session.opts.unstable_opts.trust_certified_test_monitors
            || session.opts.incremental.is_some()
        {
            return Err(
                "declaration staging requires its actual unverified, nonincremental Session".into(),
            );
        }
        let sysroot = session
            .opts
            .sysroot
            .path()
            .canonicalize()
            .map_err(|e| e.to_string())?;
        let expected = std::path::Path::new(env!("VC_SHIM_COMPILER_SYSROOT"))
            .canonicalize()
            .map_err(|e| e.to_string())?;
        if sysroot != expected || std::env::var("VSTD_KIND").as_deref() != Ok(macro_context) {
            return Err(
                "native sysroot or genuine macro environment differs from the staging recipe"
                    .into(),
            );
        }
        Ok(Self {
            options: session.opts.clone(),
            target: session.target.clone(),
            cfg: session
                .config
                .iter()
                .map(|(key, value)| (key.to_string(), value.map(|value| value.to_string())))
                .collect(),
            sysroot,
            argv: argv.to_vec(),
        })
    }

    pub(super) fn cfg_digest(&self) -> Result<Digest, String> {
        let bytes = serde_json::to_vec(&self.cfg).map_err(|e| e.to_string())?;
        Ok(Sha256::digest(bytes).into())
    }

    pub(super) fn same_target(&self, other: &Self) -> bool {
        self.target == other.target && self.sysroot == other.sysroot
    }

    pub(super) fn sysroot(&self) -> &std::path::Path {
        &self.sysroot
    }

    pub(super) fn keep_projection_of(&self, erase: &Self) -> bool {
        let mut erase_cfg = erase.cfg.clone();
        erase_cfg.insert(("verus_keep_ghost_body".into(), None));
        // Output file names are intentionally different. Every other native
        // tracked option and every constructed argument must remain identical,
        // except the one genuine Keep-body cfg. Sysroot/CStore checks cover
        // untracked search/extern selections separately.
        let mut keep_options = self.options.clone();
        keep_options.output_types = erase.options.output_types.clone();
        self.same_target(erase)
            && self.cfg == erase_cfg
            && self.options.unstable_opts.crate_attr == erase.options.unstable_opts.crate_attr
            && keep_options.dep_tracking_hash(false) == erase.options.dep_tracking_hash(false)
            && normalized_library_args(&self.argv, true).is_some_and(|keep| {
                normalized_library_args(&erase.argv, false).is_some_and(|erase| keep == erase)
            })
    }

    pub(super) fn observation(&self) -> Value {
        json!({"cfg": self.cfg, "sysroot": self.sysroot,
            "target_llvm": self.target.llvm_target.to_string(),
            "target_pointer_width": self.target.pointer_width,
            "native_options_tracking_hash": self.options.dep_tracking_hash(false).as_u64(),
            "argv_constructed_by_staging_owner": self.argv,
            "authority": "actual native Session facts, not a deserialized invocation receipt"})
    }
}

#[cfg(test)]
mod tests {
    use super::normalized_library_args;

    #[test]
    fn only_owned_output_and_the_single_keep_body_cfg_are_normalized() {
        let erase = [
            "compiler",
            "--crate-name=vstd",
            "-o",
            "/tmp/erase.rmeta",
            "library.rs",
        ]
        .map(String::from)
        .to_vec();
        let mut keep = erase.clone();
        keep[3] = "/tmp/keep.rmeta".into();
        keep.extend(["--cfg".into(), "verus_keep_ghost_body".into()]);
        assert_eq!(
            normalized_library_args(&keep, true),
            normalized_library_args(&erase, false)
        );
        keep.push("--cfg=altered_semantics".into());
        assert_ne!(
            normalized_library_args(&keep, true),
            normalized_library_args(&erase, false)
        );
        keep.extend(["--cfg".into(), "verus_keep_ghost_body".into()]);
        assert!(normalized_library_args(&keep, true).is_none());
        let mut erase = erase;
        erase[3] = "relative-output".into();
        assert!(normalized_library_args(&erase, false).is_none());
    }
}
