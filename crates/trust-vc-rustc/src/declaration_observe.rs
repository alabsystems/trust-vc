//! Analysis-only observation of genuine expanded Keep-body declarations.
//!
//! Ordinary HIR/type checks precede the projection, using the existing
//! verifier's compiler seam. The separate Erase artifact remains responsible
//! for ordinary compilation/ownership. Nothing from this tool authorizes
//! imports, body proofs, ownership, or private library semantics.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

extern crate rustc_driver;
extern crate rustc_hir_analysis;

use std::fs::OpenOptions;
use std::io::Write;
use std::path::PathBuf;
use std::process::ExitCode;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use serde_json::{json, Value};

const EXPECTED_COMPILER: &str = "82bb867eddb94599f68194f701c766f2b6f5a02f";

#[derive(Default)]
struct Observe {
    result: Option<Result<Value, String>>,
    identity_inputs: Option<crate::reader::function_identity_observer::Inputs>,
    configuration_error: Option<String>,
}

impl Callbacks for Observe {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        eprintln!(
            "vstd-function-identity-config: activation_input_present={}",
            self.identity_inputs.is_some()
        );
        if self.identity_inputs.is_some() {
            if let Err(error) = crate::reader::function_identity_observer::configure(config) {
                self.configuration_error = Some(error);
            }
        }
    }

    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let _identity_diagnostics = crate::reader::function_identity_observer::diagnostic_guard(
            tcx.sess,
            self.identity_inputs.is_some(),
        );
        if let Some(error) = self.configuration_error.take() {
            self.result = Some(Err(error));
            return Compilation::Stop;
        }
        if tcx.dcx().has_errors().is_some() {
            self.result = Some(Err("ordinary expansion rejected the Keep source".into()));
            return Compilation::Stop;
        }
        let identity_bootstrap = if let Some(inputs) = self.identity_inputs.take() {
            match crate::reader::function_identity_observer::arm(tcx, inputs) {
                Ok(report) => Some(report),
                Err(error) => {
                    self.result = Some(Err(error));
                    return Compilation::Stop;
                }
            }
        } else {
            None
        };
        rustc_hir_analysis::check_crate(tcx);
        if tcx.dcx().has_errors().is_some() {
            self.result = Some(Err(
                "ordinary HIR/type analysis rejected the Keep source".into()
            ));
            return Compilation::Stop;
        }
        let mut report = crate::reader::declaration_facts::observe(tcx);
        if tcx.dcx().has_errors().is_some() {
            self.result = Some(Err("declaration projection emitted compiler errors".into()));
            return Compilation::Stop;
        }
        if let Some(bootstrap) = identity_bootstrap {
            match crate::reader::function_identity_observer::complete(tcx) {
                Ok(identities) => {
                    report["function_identity_bootstrap"] = bootstrap;
                    report["function_identity_observations"] = identities;
                    report["analysis_input_view"] =
                        json!("ExplicitUnverifiedIdentityHelperProjection");
                    report["original_keep_helper_type_analysis"] =
                        json!("Not claimed; original graph retained separately");
                }
                Err(error) => {
                    self.result = Some(Err(error));
                    return Compilation::Stop;
                }
            }
        } else {
            report["analysis_input_view"] = json!("OriginalKeepGraph");
        }
        report["compiler_commit"] = json!(env!("VC_SHIM_COMPILER_COMMIT"));
        report["compiler_sysroot"] = json!(env!("VC_SHIM_COMPILER_SYSROOT"));
        report["crate_name"] = json!(tcx.crate_name(LOCAL_CRATE).to_string());
        report["keep_body_ownership_checked"] = json!(false);
        // Request foreign crate identities/sources only. The local Keep SVH
        // is intentionally not computed at this pre-MIR observation seam.
        report["loaded_crates"] = json!(tcx.crates(()).iter().map(|krate| {
            let source = tcx.used_crate_source(*krate);
            let path = |p: &Option<PathBuf>| p.as_ref().map(|p| p.display().to_string());
            json!({
                "name": tcx.crate_name(*krate).to_string(),
                "stable_crate_id": format!("{:016x}", tcx.stable_crate_id(*krate).as_u64()),
                "svh": tcx.crate_hash(*krate).to_string(),
                "sources": {"rmeta": path(&source.rmeta), "rlib": path(&source.rlib), "dylib": path(&source.dylib), "sdylib_interface": path(&source.sdylib_interface)},
            })
        }).collect::<Vec<_>>());
        // Projection requests typeck/normalization facts in addition to the
        // initial crate check. Their real diagnostics must also fail this run.
        if tcx.dcx().has_errors().is_some() {
            self.result = Some(Err(
                "loaded dependency observation emitted compiler errors".into()
            ));
            return Compilation::Stop;
        }
        report["ordinary_hir_type_analysis_completed"] = json!(true);
        self.result = Some(Ok(report));
        Compilation::Stop
    }
}

/// Run the declaration observer in the infrastructure-only unverified lane.
pub fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("vstd_declaration_observe: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    if env!("VC_SHIM_COMPILER_COMMIT") != EXPECTED_COMPILER {
        return Err("this prototype requires the recorded Trust82bb compiler".into());
    }
    let mut args = std::env::args();
    let program = args.next().ok_or("missing program name")?;
    let output = PathBuf::from(
        args.next()
            .ok_or("usage: vstd_declaration_observe REPORT -- RUSTC_ARGS")?,
    );
    if output.exists() {
        return Err("refusing to overwrite an existing observation".into());
    }
    if args.next().as_deref() != Some("--") {
        return Err("expected -- before compiler arguments".into());
    }
    let mut compiler_args = vec![program];
    compiler_args.extend(args);
    if compiler_args
        .iter()
        .any(|arg| arg == "--sysroot" || arg.starts_with("--sysroot="))
    {
        return Err("the compiler sysroot is pinned by the helper build".into());
    }
    for cfg in ["verus_keep_ghost", "verus_keep_ghost_body"] {
        if !compiler_args
            .windows(2)
            .any(|args| args[0] == "--cfg" && args[1] == cfg)
        {
            return Err(format!(
                "this producer requires the explicit genuine {cfg} cfg"
            ));
        }
    }
    if !compiler_args.iter().any(|arg| arg == "-Ztrust-verify=off") {
        return Err(
            "declaration observation requires the explicit unverified infrastructure lane".into(),
        );
    }
    compiler_args.extend(["--sysroot".into(), env!("VC_SHIM_COMPILER_SYSROOT").into()]);
    let mut callbacks = Observe {
        identity_inputs: crate::reader::function_identity_observer::Inputs::from_environment()?,
        ..Observe::default()
    };
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&compiler_args, &mut callbacks))
        .map_err(|_| "compiler rejected Keep-source analysis".to_string())?;
    let report = callbacks
        .result
        .ok_or("Keep-source analysis callback was not reached")??;
    let bytes = serde_json::to_vec_pretty(&report).map_err(|error| error.to_string())?;
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&output)
        .and_then(|mut file| file.write_all(&bytes))
        .map_err(|error| format!("{}: {error}", output.display()))
}
