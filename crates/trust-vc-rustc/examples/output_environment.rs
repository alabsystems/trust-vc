// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual compiler diagnostics for the closed three-variable SDK environment.
//! No Verus verification, SDK owner, imported body or official Trust evidence.

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;

#[path = "../src/compiler_environment.rs"]
mod compiler_environment;
#[path = "../src/output_environment.rs"]
mod output_environment;

use compiler_environment::CompilerEnvironment;
use rustc_session::{config::ErrorOutputType, EarlyDiagCtxt};
use std::ffi::OsString;
use std::io::Write;
use std::process::{Command, ExitCode, Stdio};

struct Callbacks {
    environment: Option<CompilerEnvironment>,
}

fn refuse(error: impl std::fmt::Display) -> ! {
    EarlyDiagCtxt::new(ErrorOutputType::default()).early_fatal(error.to_string())
}

impl rustc_driver::Callbacks for Callbacks {
    fn config(&mut self, config: &mut rustc_interface::Config) {
        if let Some(environment) = &self.environment {
            let before = config.opts.clone();
            environment
                .apply_to_options(&mut config.opts)
                .unwrap_or_else(|error| refuse(error));
            let mut accounted = config.opts.clone();
            accounted.logical_env = before.logical_env.clone();
            assert_eq!(
                before.dep_tracking_hash(false),
                accounted.dep_tracking_hash(false)
            );
        }
    }

    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        if let Some(environment) = &self.environment {
            environment
                .check_options(&tcx.sess.opts)
                .unwrap_or_else(|error| refuse(error));
            for (key, value) in tcx.sess.env_depinfo.lock().iter() {
                environment
                    .check_dependency(key.as_str(), value.as_ref().map(|value| value.as_str()))
                    .unwrap_or_else(|error| refuse(error));
            }
        }
        let doc_markers: usize = tcx
            .hir_body_owners()
            .map(|owner| {
                let attrs = tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner));
                format!("{attrs:?}")
                    .matches("verusdoc_special_attr")
                    .count()
            })
            .sum();
        eprintln!("COMPILER_ENV_DOC_MARKERS={doc_markers}");
        eprintln!("OUTPUT_ENV_ANALYSIS_RETURNED");
        rustc_driver::Compilation::Stop
    }
}

struct Request {
    environment: CompilerEnvironment,
    compiler: Vec<String>,
    child: bool,
}

fn request(args: &[OsString]) -> Result<Request, &'static str> {
    let split = args
        .iter()
        .position(|arg| arg == "--")
        .ok_or("missing compiler operands")?;
    let mut verdict = None;
    let mut dump = None;
    let mut verusdoc = None;
    let mut child = false;
    let mut index = 0;
    while index < split {
        match args[index].to_str() {
            Some("--verdict") if index + 1 < split && verdict.is_none() => {
                verdict = Some(args[index + 1].as_os_str());
                index += 2;
            }
            Some("--dump") if index + 1 < split && dump.is_none() => {
                dump = Some(args[index + 1].as_os_str());
                index += 2;
            }
            Some("--verusdoc") if index + 1 < split && verusdoc.is_none() => {
                verusdoc = Some(args[index + 1].as_os_str());
                index += 2;
            }
            Some("--erase-child") if !child => {
                child = true;
                index += 1;
            }
            _ => return Err("invalid diagnostic request"),
        }
    }
    let environment = CompilerEnvironment::from_raw(verdict, dump, verusdoc)
        .map_err(|_| "unrepresentable diagnostic output environment")?;
    let mut compiler = vec!["output-environment-diagnostic".into()];
    compiler.extend(
        args[split + 1..]
            .iter()
            .map(|arg| {
                arg.to_str()
                    .map(str::to_owned)
                    .ok_or("non-Unicode compiler operand")
            })
            .collect::<Result<Vec<_>, _>>()?,
    );
    Ok(Request {
        environment,
        compiler,
        child,
    })
}

fn compile(compiler: &[String], environment: Option<CompilerEnvironment>) -> u8 {
    if rustc_driver::catch_fatal_errors(|| {
        rustc_driver::run_compiler(compiler, &mut Callbacks { environment });
    })
    .is_ok()
    {
        0
    } else {
        1
    }
}

fn process_values() -> [Option<OsString>; 3] {
    [
        std::env::var_os("TRUST_VC_VERDICT_DIR"),
        std::env::var_os("TRUST_VC_DUMP_VCIR"),
        std::env::var_os("VERUSDOC"),
    ]
}

fn main() -> ExitCode {
    // SAFETY: first native entry operation, before file opens or callbacks.
    if let Err(code) = unsafe { trust_vc_rustc::native_entry::capture_inherited_resources() } {
        return code;
    }
    let args = std::env::args_os().skip(1).collect::<Vec<_>>();
    if args.first().is_some_and(|arg| arg == "--compiler-child") {
        if args.get(1).is_none_or(|arg| arg != "--") {
            return ExitCode::from(2);
        }
        let mut compiler = vec!["output-environment-child-diagnostic".to_owned()];
        for arg in &args[2..] {
            let Some(arg) = arg.to_str() else {
                return ExitCode::from(2);
            };
            compiler.push(arg.to_owned());
        }
        let before = process_values();
        let code = compile(&compiler, None);
        assert_eq!(process_values(), before);
        return ExitCode::from(code);
    }
    let requests = match args
        .split(|arg| arg == "--next-request")
        .map(request)
        .collect::<Result<Vec<_>, _>>()
    {
        Ok(requests) => requests,
        Err(error) => {
            eprintln!("output environment diagnostic refused: {error}");
            return ExitCode::from(65);
        }
    };
    // No producer/compiler or worker has run before this startup check. These
    // diagnostics load no user proc macro and perform no environment writes.
    // That closed source is essential; checks alone are not a no-writers proof.
    if requests.iter().any(|request| !request.child) {
        if let Err(error) = CompilerEnvironment::require_absent_process() {
            eprintln!("output environment diagnostic refused: {error}");
            return ExitCode::from(65);
        }
    }
    let before = process_values();
    let mut result = 0;
    for (index, request) in requests.into_iter().enumerate() {
        let code = if request.child {
            let mut command = Command::new(std::env::current_exe().unwrap());
            command
                .arg("--compiler-child")
                .arg("--")
                .args(&request.compiler[1..]);
            request.environment.configure_child(&mut command);
            let child = command
                .stdin(Stdio::null())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .unwrap();
            let pid = child.id();
            let output = child.wait_with_output().unwrap();
            std::io::stdout().write_all(&output.stdout).unwrap();
            std::io::stderr().write_all(&output.stderr).unwrap();
            eprintln!(
                "OUTPUT_ENV_CHILD pid={pid} exit={:?} directly_waited=true",
                output.status.code()
            );
            u8::try_from(output.status.code().unwrap_or(101)).unwrap_or(101)
        } else {
            compile(&request.compiler, Some(request.environment))
        };
        assert_eq!(
            process_values(),
            before,
            "diagnostic changed the process output environment"
        );
        eprintln!(
            "OUTPUT_ENV_REQUEST index={index} exit={code} process_environment_unchanged=true"
        );
        if code != 0 {
            result = code;
        }
    }
    ExitCode::from(result)
}
