// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The request callback borrows the actual producer and sealed SDK layout.
//! Native transport is data only; this module never decodes or recreates an owner.

use std::io::{self, Read};
use std::path::PathBuf;
use std::time::Duration;

use crate::native_requests::{Coordinator, Dispatch, Reply, Request};
use crate::shim::NormalInvocation;
use crate::verdict::OutputSinks;

use super::prepared_sdk::PreparedSdk;
use super::*;

mod capture;
mod entry;
mod runner;
pub use entry::main;

pub(super) struct Session<'owner> {
    owner: &'owner StandaloneImported<'owner>,
    sdk: &'owner PreparedSdk<'owner>,
    requests: usize,
}

impl<'owner> Session<'owner> {
    pub(super) fn new(
        owner: &'owner StandaloneImported<'owner>,
        sdk: &'owner PreparedSdk<'owner>,
    ) -> Result<Self, String> {
        sdk.check_owner(owner)?;
        Ok(Self {
            owner,
            sdk,
            requests: 0,
        })
    }

    /// # Safety
    /// The dedicated coordinator executes one callback at a time. All compiler,
    /// erase and solver children must join before it receives another request;
    /// no other same-process thread may exec or use process cwd/standard I/O.
    pub(super) unsafe fn serve(&mut self, channel: &Coordinator) -> io::Result<()> {
        loop {
            // SAFETY: this dedicated serial entry upholds the transport contract.
            match unsafe {
                channel.dispatch(Duration::from_secs(30), |request, reply| {
                    self.handle(request, reply)
                })
            } {
                Ok(Dispatch::Stopped) => break,
                Ok(Dispatch::Completed(_)) => {}
                Err(error)
                    if matches!(
                        error.kind(),
                        io::ErrorKind::TimedOut | io::ErrorKind::WouldBlock
                    ) => {}
                Err(error) => return Err(error),
            }
        }
        self.sdk.check_owner(self.owner).map_err(io::Error::other)
    }

    /// # Safety
    /// The same dedicated serial compiler/cwd/stdio contract as `serve`.
    /// The child is the data-only maintained runner, whose stdin lease owns
    /// its descendants; it performs no concurrent compiler work in this process.
    unsafe fn serve_runner(
        &mut self,
        channel: &Coordinator,
        runner: &mut runner::Runner,
    ) -> io::Result<()> {
        loop {
            if runner.try_wait()?.is_some() {
                break;
            }
            // SAFETY: the serial entry starts no concurrent exec/spawn here.
            let incoming = match unsafe { channel.receive(Some(Duration::from_millis(100))) } {
                Ok(Some(incoming)) => incoming,
                Ok(None) => {
                    return Err(io::Error::other(
                        "the runner stopped the request channel before its process completed",
                    ))
                }
                Err(error)
                    if matches!(
                        error.kind(),
                        io::ErrorKind::TimedOut | io::ErrorKind::WouldBlock
                    ) =>
                {
                    continue
                }
                Err(error) => return Err(error),
            };
            // Idle polling never shortens the established input admission
            // bound, and compiler execution still has no transport deadline.
            let (request, mut reply) = incoming.read(Duration::from_secs(30))?;
            let exit = unsafe { self.handle(request, &mut reply) }?;
            reply.finish(exit)?;
        }
        self.sdk.check_owner(self.owner).map_err(io::Error::other)
    }

    /// # Safety
    /// The caller supplies the same serial cwd/stdio and joined-worker contract
    /// as `serve`. The native compiler is executed here, never in the forwarder.
    pub(super) unsafe fn handle(&mut self, request: Request, reply: &mut Reply) -> io::Result<u8> {
        self.requests = self
            .requests
            .checked_add(1)
            .ok_or_else(|| io::Error::other("native request counter exhausted"))?;
        self.sdk.check_owner(self.owner).map_err(io::Error::other)?;
        let phase = format!("NativeRequest{}", self.requests);
        let outputs = OutputSinks::for_request(
            &request.cwd,
            request.outputs.verdict_dir.clone(),
            request.outputs.dump_vcir.clone(),
        )?;
        // SAFETY: forwarded from the dedicated serial coordinator contract.
        let (result, mut stdout, mut stderr) = unsafe {
            capture::run(
                &self.owner.library().inputs.output,
                &phase,
                &request.cwd,
                || self.verify(&request, &phase, &outputs),
            )
        }?;
        copy(&mut stdout, |bytes| reply.stdout(bytes))?;
        copy(&mut stderr, |bytes| reply.stderr(bytes))?;
        self.sdk.check_owner(self.owner).map_err(io::Error::other)?;
        match result {
            Ok(exit) => Ok(exit),
            Err(reason) => {
                let diagnostic = serde_json::json!({"$message_type": "diagnostic",
                    "message": format!("trust-vc refused: owned-native-request: {reason}"),
                    "code": null, "level": "error", "spans": [], "children": [],
                    "rendered": format!("error: trust-vc refused: owned-native-request: {reason}\n")});
                let mut bytes = serde_json::to_vec(&diagnostic).map_err(io::Error::other)?;
                bytes.push(b'\n');
                reply.stderr(&bytes)?;
                Ok(1)
            }
        }
    }

    fn verify(&self, request: &Request, phase: &str, outputs: &OutputSinks) -> Result<u8, String> {
        let environment = crate::compiler_environment::CompilerEnvironment::from_raw(
            request
                .outputs
                .verdict_dir
                .as_deref()
                .map(std::path::Path::as_os_str),
            request
                .outputs
                .dump_vcir
                .as_deref()
                .map(std::path::Path::as_os_str),
            request.verusdoc.as_deref(),
        )
        .map_err(|error| error.to_string())?;
        crate::compiler_environment::CompilerEnvironment::require_absent_process()
            .map_err(|error| error.to_string())?;
        let argv = request
            .argv
            .iter()
            .map(|arg| {
                arg.to_str()
                    .map(str::to_owned)
                    .ok_or("the native compiler requires UTF-8 arguments".to_owned())
            })
            .collect::<Result<Vec<_>, _>>()?;
        let (program, arguments) = argv
            .split_first()
            .ok_or("missing original executable operand")?;
        let split = crate::args::split(arguments).map_err(|e| e.to_string())?;
        if !split.verus.iter().any(|option| option.name == "import") {
            // A persistent compiler must represent its complete macro/Cargo
            // cohort before expansion. The ordinary public shim may load
            // plugins whose process-environment behavior this owner does not
            // govern. Do not run that larger cohort under the serial SDK
            // owner's more restrictive contract.
            return Err(
                "the coordinator does not yet represent an ordinary standalone compiler cohort"
                    .into(),
            );
        }
        let output = PathBuf::from(
            split
                .output_file()
                .ok_or("native request needs its original -o operand")?,
        );
        let invocation = NormalInvocation::derive(program.clone(), split)?;
        let source = ClientSource::read(invocation.source_operand()?)?;
        let plan = macro_context::NormalClientPlan::from_prepared_invocation(
            self.owner, self.sdk, &source, invocation,
        )?
        .with_compiler_environment(environment)?;
        super::normal::verify_plan_with_outputs(
            self.owner,
            &source,
            phase,
            &plan,
            output,
            outputs,
            Some(&argv),
        )
        .map(|succeeded| u8::from(!succeeded))
    }
}

fn copy(reader: &mut impl Read, mut write: impl FnMut(&[u8]) -> io::Result<()>) -> io::Result<()> {
    let mut bytes = [0; 65536];
    loop {
        let count = reader.read(&mut bytes)?;
        if count == 0 {
            return Ok(());
        }
        write(&bytes[..count])?;
    }
}
