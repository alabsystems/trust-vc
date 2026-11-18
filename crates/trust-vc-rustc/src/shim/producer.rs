// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Producer bodies checked by the same original native/erase/AY pipeline.
//!
//! This is an in-process verification boundary, not an import decoder. It
//! retains the full checked bodies and clauses; a later client must still
//! establish its genuine Keep/Erase and CStore correspondence before consuming
//! any exported contract. No public CLI option is enabled here.

use super::*;
use crate::declaration_alignment::observation::ObservedAnchor;
use crate::declaration_alignment::source_bindings::{PinnedFile, SourceIdentity, Sources};
use crate::declaration_alignment::{AuthoredSpan, NativeKey};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_span::Pos;
use sha2::{Digest as _, Sha256};
use trust_vc_vcir::{Body, FnDecl, FnRole, Mode};

struct NativeInput {
    stable_crate_id: u64,
    svh: u128,
    file: PinnedFile,
}

/// Owned proof output, never constructed from a Record or a serialized claim.
/// The original body stays attached to its clauses until the future export
/// adapter has established a complete native producer/client mapping.
pub(crate) struct CheckedFunction {
    native: NativeKey,
    declaration: FnDecl,
}

pub(crate) struct CheckedProducer {
    source: SourceIdentity,
    source_files: Vec<PinnedFile>,
    native_inputs: Vec<NativeInput>,
    verify_argv: Vec<String>,
    erase_argv: Vec<String>,
    functions: Vec<CheckedFunction>,
    spans: Vec<AuthoredSpan>,
    pointer_width: u32,
    architecture: trust_vc_vcir::bitvector::Architecture,
}

impl CheckedProducer {
    pub(crate) fn source(&self) -> SourceIdentity {
        self.source
    }

    pub(crate) fn functions(&self) -> impl Iterator<Item = &CheckedFunction> {
        self.functions.iter()
    }

    pub(crate) fn revalidate(&self, sources: &Sources) -> Result<(), String> {
        let current = sources.source_files();
        if self.source != sources.identity()
            || self.source_files.len() != current.len()
            || self
                .source_files
                .iter()
                .zip(&current)
                .any(|(old, current)| old.path != current.path || old.sha256 != current.sha256)
        {
            return Err("the verified producer belongs to another complete source graph".into());
        }
        sources.revalidate()?;
        for file in &self.source_files {
            file.read()?;
        }
        for input in &self.native_inputs {
            input.file.read()?;
        }
        Ok(())
    }
}

impl CheckedFunction {
    pub(crate) fn native(&self) -> NativeKey {
        self.native
    }

    pub(crate) fn declaration(&self) -> &FnDecl {
        &self.declaration
    }
}

fn key(tcx: TyCtxt<'_>, owner: rustc_hir::def_id::LocalDefId) -> NativeKey {
    let (high, low) = tcx.def_path_hash(owner.to_def_id()).0.split();
    NativeKey {
        stable_crate_id: tcx.stable_crate_id(LOCAL_CRATE).as_u64(),
        def_path_hash: (u128::from(high.as_u64()) << 64) | u128::from(low.as_u64()),
    }
}

fn function_id(key: NativeKey) -> FnId {
    FnId(trust_vc_vcir::DefHash::new(
        (key.def_path_hash >> 64) as u64,
        key.def_path_hash as u64,
    ))
}

fn authored_span(tcx: TyCtxt<'_>, sources: &Sources, span: Span) -> Result<AuthoredSpan, String> {
    if span.is_dummy() {
        return Err("a verified producer span has no original authored identity".into());
    }
    let file = tcx.sess.source_map().lookup_source_file(span.lo());
    if !file.contains(span.hi()) {
        return Err("a verified producer span crosses native source files".into());
    }
    let FileName::Real(name) = &file.name else {
        return Err("a verified producer span belongs to a virtual source file".into());
    };
    let path = name
        .local_path()
        .and_then(|path| path.to_str())
        .ok_or("a verified producer source has no represented local path")?;
    sources.anchor(&ObservedAnchor {
        local_path: path.into(),
        compiler_source_hash: file.src_hash.to_string(),
        original_file_len: file.unnormalized_source_len,
        bytes: (
            file.original_relative_byte_pos(span.lo()).to_u32(),
            file.original_relative_byte_pos(span.hi()).to_u32(),
        ),
    })
}

fn native_inputs(tcx: TyCtxt<'_>) -> Result<Vec<NativeInput>, String> {
    let crates = tcx.crates(());
    if crates.len() > 16_384 {
        return Err("the verified producer dependency graph exceeds its bound".into());
    }
    let mut inputs = Vec::new();
    let mut seen = HashSet::new();
    for krate in crates {
        let source = tcx.used_crate_source(*krate);
        let selected = source
            .rmeta
            .as_ref()
            .or(source.rlib.as_ref())
            .or(source.dylib.as_ref())
            .ok_or("a producer native dependency has no selected image")?;
        let path = selected.canonicalize().map_err(|error| error.to_string())?;
        let metadata = std::fs::symlink_metadata(&path).map_err(|error| error.to_string())?;
        if !metadata.file_type().is_file() || !seen.insert(tcx.stable_crate_id(*krate).as_u64()) {
            return Err(
                "a producer dependency is nonregular or has duplicate native identity".into(),
            );
        }
        let bytes = std::fs::read(&path).map_err(|error| error.to_string())?;
        let file = PinnedFile {
            path,
            sha256: Sha256::digest(&bytes).into(),
        };
        file.read()?;
        inputs.push(NativeInput {
            stable_crate_id: tcx.stable_crate_id(*krate).as_u64(),
            svh: tcx.crate_hash(*krate).as_u128(),
            file,
        });
    }
    Ok(inputs)
}

fn full_checks(invocation: &NormalInvocation) -> Result<(), String> {
    let options = invocation.options();
    if options.no_verify
        || !options.lifetime_check
        || !options.erase_compile
        || options.erase_args.is_none()
        || !options.no_cheating
        || options.cargo
        || options.compiler_environment.is_some()
    {
        return Err("producer contract verification requires complete checking, native lifetime/erase checks and --no-cheating".into());
    }
    let split = invocation
        .original()
        .ok_or("producer verification requires its actual request split")?;
    if let Some((_, reason)) = ordinary_request_problem(split, false) {
        return Err(reason);
    }
    if split.has("no-erasure-check")
        || split.has("no-lifetime")
        || split.has("no-verify")
        || split.has("no-auto-recommends-check")
    {
        return Err(
            "a producer cannot export contracts after disabling a native or semantic check".into(),
        );
    }
    Ok(())
}

struct Producer<'plan, 'source> {
    invocation: &'plan NormalInvocation,
    sources: &'source Sources,
    run: VerifyRun,
    checked: Option<Result<CheckedProducer, String>>,
}

impl Producer<'_, '_> {
    fn read_and_verify<'tcx>(&mut self, tcx: TyCtxt<'tcx>) -> Result<CheckedProducer, String> {
        self.sources.revalidate()?;
        self.invocation.check_native_source(tcx)?;
        let actual_sysroot = tcx
            .sess
            .opts
            .sysroot
            .path()
            .canonicalize()
            .map_err(|error| error.to_string())?;
        let expected_sysroot = std::path::Path::new(env!("VC_SHIM_COMPILER_SYSROOT"))
            .canonicalize()
            .map_err(|error| error.to_string())?;
        if actual_sysroot != expected_sysroot
            || tcx.sess.opts.incremental.is_some()
            || tcx.sess.trust_verification_enabled()
            || tcx.sess.trust_ir_lower_enabled()
        {
            return Err("producer contracts require the genuine nonincremental native unverified compiler context".into());
        }
        let input = self
            .invocation
            .source_operand()?
            .canonicalize()
            .map_err(|error| error.to_string())?;
        let source = self
            .sources
            .source_files()
            .into_iter()
            .find(|file| file.path == input)
            .ok_or("the original producer input is outside its complete retained source graph")?;
        self.invocation.source_matches(&source)?;
        if !self.run.prepare_read(tcx) {
            return Err("the real producer native front end did not complete".into());
        }
        let read = reader::read_crate(tcx, self.run.opts.read);
        if read.fns.is_empty()
            || read.fns.len() > 16_384
            || read.spans.len() > 65_536
            || read.krate.fns.len() != read.fns.len()
            || read
                .krate
                .fns
                .iter()
                .any(|function| function.role != FnRole::Item)
        {
            return Err("the producer requires a complete owned local function graph; trait, instance and external contract exports need their native mapping".into());
        }
        let mut native_roots = HashSet::new();
        for function in &read.fns {
            let FnStatus::Read(id) = function.status else {
                return Err(
                    "every producer body must be read completely before contract verification"
                        .into(),
                );
            };
            let declaration = read
                .krate
                .fn_decl(id)
                .ok_or("a producer function is absent from its complete semantic read")?;
            if read.fn_defs.get(&id) != Some(&function.def_id)
                || function_id(key(tcx, function.def_id)) != id
                || matches!(declaration.body, Body::None | Body::Constant(_))
            {
                return Err(
                    "a producer function lost its actual native body/definition identity".into(),
                );
            }
            if matches!(declaration.mode, Mode::Exec | Mode::Proof) {
                tcx.ensure_ok().mir_borrowck(function.def_id);
                native_roots.insert(id);
            }
        }
        if native_roots.is_empty() || tcx.dcx().has_errors().is_some() {
            return Err("the original native producer ownership checks did not complete".into());
        }
        let inputs = native_inputs(tcx)?;
        self.run.decide(tcx, &read);
        let complete = match std::mem::replace(
            &mut self.run.native_capture,
            NativeVerificationCapture::Disabled,
        ) {
            NativeVerificationCapture::Complete(complete) => complete,
            _ => {
                return Err(if self.run.outcome == Some(Outcome::VerificationFailed) {
                    "the real AY producer body verification failed".to_owned()
                } else {
                    "the real producer native/erase/AY verification did not succeed".to_owned()
                });
            }
        };
        self.sources.revalidate()?;
        self.invocation.check_native_source(tcx)?;
        let current_inputs = native_inputs(tcx)?;
        if inputs.len() != current_inputs.len()
            || inputs.iter().zip(&current_inputs).any(|(old, current)| {
                old.stable_crate_id != current.stable_crate_id
                    || old.svh != current.svh
                    || old.file.path != current.file.path
                    || old.file.sha256 != current.file.sha256
            })
        {
            return Err(
                "the complete actual native dependency graph changed during producer verification"
                    .into(),
            );
        }
        if tcx.dcx().has_errors().is_some() {
            return Err("the native producer context has outstanding errors".into());
        }
        let mut functions = Vec::new();
        for declaration in &read.krate.fns {
            let owner = *read
                .fn_defs
                .get(&declaration.id)
                .ok_or("a checked producer declaration lost its original native owner")?;
            let result = complete
                .outcomes
                .get(&declaration.id)
                .ok_or("a producer declaration has no actual AY verification outcome")?;
            if result.verdict != Verdict::Verified || result.tag.is_some() {
                return Err(
                    "an unverified or trusted producer function cannot export a contract".into(),
                );
            }
            functions.push(CheckedFunction {
                native: key(tcx, owner),
                declaration: declaration.clone(),
            });
        }
        let spans = read
            .spans
            .iter()
            .map(|span| authored_span(tcx, self.sources, *span))
            .collect::<Result<Vec<_>, _>>()?;
        let checked = CheckedProducer {
            source: self.sources.identity(),
            source_files: self.sources.source_files(),
            native_inputs: inputs,
            verify_argv: self.invocation.verify().to_vec(),
            erase_argv: self.invocation.erase().to_vec(),
            functions,
            spans,
            pointer_width: read.krate.pointer_width,
            architecture: read.krate.architecture,
        };
        checked.revalidate(self.sources)?;
        Ok(checked)
    }
}

impl Callbacks for Producer<'_, '_> {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        self.run.config(config);
    }

    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        #[cfg(test)]
        let _native_erase = tests::NativeEraseDispatch::enter();
        let result = self.read_and_verify(tcx);
        if let Err(reason) = &result {
            tcx.dcx()
                .struct_err(format!("producer contract verification refused: {reason}"))
                .emit();
        }
        self.checked = Some(result);
        self.run.reading = false;
        Compilation::Stop
    }
}

/// Run a real producer compiler transaction. Its result is consumed in memory;
/// there is no JSON/Record loader, expected-outcome input or public import flag.
pub(crate) fn verify(
    invocation: &NormalInvocation,
    sources: &Sources,
) -> Result<CheckedProducer, String> {
    full_checks(invocation)?;
    sources.revalidate()?;
    if sources.file_count() > 65_536 {
        return Err("the complete producer source graph exceeds its retained-input bound".into());
    }
    let mut run = VerifyRun::new(invocation.options(), OutputSinks::default());
    run.native_capture = NativeVerificationCapture::Requested;
    let mut callback = Producer {
        invocation,
        sources,
        run,
        checked: None,
    };
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        rustc_driver::catch_fatal_errors(|| {
            rustc_driver::run_compiler(invocation.verify(), &mut callback)
        })
    }));
    match result {
        Ok(Ok(())) => {}
        Ok(Err(_)) => {
            return Err(match callback.checked.take() {
                Some(Err(reason)) => reason,
                _ => "the actual producer compiler returned an error".into(),
            });
        }
        Err(_) => return Err("the actual producer compiler did not complete normally".into()),
    }
    let checked = callback
        .checked
        .ok_or("the actual producer callback was not reached")??;
    checked.revalidate(sources)?;
    Ok(checked)
}

#[cfg(test)]
pub(super) mod tests;
