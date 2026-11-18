// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A live-session-authenticated ordinary request, isolated from Imported
//! macro OnceLocks. It has no ClientImports or exported contract capability.

use super::*;
use crate::child_process::RetainedChild;
use crate::declaration_alignment::source_bindings::PinnedFile;
use crate::retained_bytes as storage;
use crate::shim::ordinary_protocol as protocol;
use crate::shim::{OrdinaryNativeInput, OrdinaryWorkerInput};
use std::io::Write;
use std::process::{Command, Stdio};

pub(super) struct OrdinaryWorkerPlan<'owner> {
    owner: &'owner StandaloneImported<'owner>,
    sdk: &'owner PreparedSdk<'owner>,
    input: OrdinaryWorkerInput,
    _scratch: Option<crate::cargo::Scratch>,
    output_file: Option<PathBuf>,
    entry_file: Option<PathBuf>,
}

impl<'owner> OrdinaryWorkerPlan<'owner> {
    pub(super) fn from_request(
        owner: &'owner StandaloneImported<'owner>,
        sdk: &'owner PreparedSdk<'owner>,
        request: Request,
    ) -> Result<Self, String> {
        sdk.check_owner(owner)?;
        if std::env::current_dir()
            .map_err(|e| e.to_string())?
            .canonicalize()
            .map_err(|e| e.to_string())?
            != request.cwd
        {
            return Err("ordinary request is outside its actual captured cwd".into());
        }
        request
            .cargo
            .check_macro_package(request.macro_package_name.as_deref())?;
        if request.macro_package_name.as_deref() == Some(std::ffi::OsStr::new("vstd")) {
            return Err("the Cargo vstd producer needs its genuine producer context".into());
        }
        let argv = request
            .argv
            .iter()
            .map(|a| {
                a.to_str()
                    .map(str::to_owned)
                    .ok_or("the native compiler requires UTF-8 arguments".to_owned())
            })
            .collect::<Result<Vec<_>, _>>()?;
        request.cargo.validate(&argv)?;
        let (arguments, via_cargo, cargo_inputs, compile_option) =
            match crate::cargo::prepare(&argv, |key| request.cargo.read(key))? {
                crate::cargo::Invocation::Standalone => (
                    argv.get(1..).unwrap_or(&[]).to_vec(),
                    false,
                    crate::cargo::Inputs::default(),
                    false,
                ),
                crate::cargo::Invocation::Verify {
                    args,
                    options,
                    inputs,
                } if options.import_deps.is_empty() => (args, true, inputs, options.compile),
                crate::cargo::Invocation::Verify { .. } => {
                    return Err(
                        "ordinary Cargo dependency imports need actual live library nodes".into(),
                    )
                }
                crate::cargo::Invocation::Direct { .. } => return Err(
                    "direct Cargo compiler cohorts need their separate ordinary native callback"
                        .into(),
                ),
            };
        let split = crate::args::split(&arguments).map_err(|e| e.to_string())?;
        if let Some((_, reason)) = crate::shim::ordinary_request_problem(&split, via_cargo) {
            return Err(reason);
        }
        if split
            .verus
            .iter()
            .any(|o| matches!(o.name.as_str(), "import" | "export" | "is-vstd" | "is-core"))
        {
            return Err("ordinary worker cannot import, export or produce a library owner".into());
        }
        let public_compile = via_cargo && (compile_option || split.has("compile"));
        let output_file = split.output_file().map(PathBuf::from);
        let entry_file = split.entry_file().map(PathBuf::from);
        let invocation = NormalInvocation::derive(
            argv.first().cloned().ok_or("missing ordinary argv0")?,
            split,
        )?;
        let source = ClientSource::read(invocation.source_operand()?)?;
        invocation.source_matches(source.file())?;
        macro_context::NormalClientPlan::ordinary_operands(
            owner,
            sdk,
            invocation
                .original()
                .ok_or("ordinary request lost its original options")?,
            &source,
        )?;
        let library = owner.library();
        let mut common = Vec::new();
        for row in library.prepared.common.native_input_observations() {
            let file = if let Some(file) = owner.common_files().get(&row.file.path) {
                file.clone()
            } else {
                let mut same = owner
                    .common_files()
                    .values()
                    .filter(|f| f.sha256 == row.file.sha256);
                let file = same
                    .next()
                    .ok_or("ordinary macro has no actual retained physical image")?
                    .clone();
                if same.next().is_some() {
                    return Err("ordinary macro physical selection is ambiguous".into());
                }
                file
            };
            common.push(OrdinaryNativeInput {
                stable_crate_id: row.stable_crate_id,
                svh: row.svh,
                file,
            });
        }
        // The executable is the CURRENT producer/coordinator image itself.
        // A caller-provided frontend path/hash is not verifier authority.
        let path = std::env::current_exe()
            .map_err(|e| e.to_string())?
            .canonicalize()
            .map_err(|e| e.to_string())?;
        let program = PinnedFile {
            path,
            sha256: library.inputs.producer_sha256,
        };
        program.read()?;
        let scratch = crate::cargo::Scratch::new().map_err(|e| e.to_string())?;
        let erase_plan = crate::shim::OrdinaryErasePlan {
            args: invocation.erase().to_vec(),
            cargo_inputs: cargo_inputs.0,
            verify_output: via_cargo.then(|| scratch.path().join("verify")),
            erase_output: scratch.path().join("erase"),
            expects_erase: invocation.expects_erase(),
            public_compile,
        };
        let input = OrdinaryWorkerInput {
            request,
            source: source.file().clone(),
            common,
            forbidden_library: library.prepared.erase.view.stable_crate_id,
            program,
            erase_plan,
        };
        let plan = Self {
            owner,
            sdk,
            input,
            _scratch: Some(scratch),
            output_file,
            entry_file,
        };
        plan.check()?;
        Ok(plan)
    }
    fn check(&self) -> Result<(), String> {
        self.sdk.check_owner(self.owner)?;
        self.input.source.read()?;
        self.input.program.read()?;
        for file in &self.input.common {
            file.file.read()?;
        }
        Ok(())
    }
    fn command(&self) -> Result<Command, String> {
        let request = &self.input.request;
        let mut command = Command::new(&self.input.program.path);
        command.current_dir(&request.cwd).env_clear().env(
            "DYLD_LIBRARY_PATH",
            PathBuf::from(env!("VC_SHIM_COMPILER_SYSROOT")).join("lib"),
        );
        crate::native_entry::configure_ordinary_child(&mut command)?;
        for (key, value) in &request.cargo.values {
            if let Some(value) = value {
                command.env(key, value);
            }
        }
        if let Some(value) = &request.macro_package_name {
            command.env("CARGO_PKG_NAME", value);
        }
        for (key, value) in [
            (
                "TRUST_VC_VERDICT_DIR",
                request.outputs.verdict_dir.as_ref().map(|p| p.as_os_str()),
            ),
            (
                "TRUST_VC_DUMP_VCIR",
                request.outputs.dump_vcir.as_ref().map(|p| p.as_os_str()),
            ),
            ("VERUSDOC", request.verusdoc.as_deref()),
        ] {
            if let Some(value) = value {
                command.env(key, value);
            }
        }
        Ok(command)
    }
    fn erase(&self, public: bool) -> Result<(i32, Vec<u8>), String> {
        self.check()?;
        let mut command = self.command()?;
        command
            .args(crate::shim::ordinary_erase_arguments(&self.input, public)?)
            .stdin(Stdio::piped())
            .stdout(Stdio::inherit())
            .stderr(Stdio::piped());
        // The guard exists before stream extraction, data writing or reading.
        let mut child = RetainedChild::spawn(&mut command).map_err(|e| e.to_string())?;
        child
            .write_input(&self.input.encode()?)
            .map_err(|e| e.to_string())?;
        let (status, stderr) = child.stderr_and_wait().map_err(|e| e.to_string())?;
        self.check()?;
        Ok((status.code().unwrap_or(101), stderr))
    }
    pub(super) fn execute(&self, outputs: &OutputSinks) -> Result<u8, String> {
        self.check()?;
        let mut command = self.command()?;
        command
            .arg(crate::shim::ORDINARY_WORKER_FLAG)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit());
        // Both workflow processes are direct children of THIS live owner.
        // During erase(), this worker guard remains owned on this stack.
        let mut worker = RetainedChild::spawn(&mut command).map_err(|e| e.to_string())?;
        let mut input = worker.take_stdin().map_err(|e| e.to_string())?;
        let mut channel = worker.take_stdout().map_err(|e| e.to_string())?;
        protocol::frame(&mut input, protocol::INITIAL, &self.input.encode()?)
            .map_err(|e| e.to_string())?;
        let (mut record, mut vcir, mut erased) = (Vec::new(), Vec::new(), None);
        let (code, public_compile) = loop {
            match protocol::receive_limited(&mut channel, |tag| match tag {
                protocol::RECORD => storage::remaining(record.len(), storage::MAX_RECORD_BYTES),
                protocol::VCIR => storage::remaining(vcir.len(), storage::MAX_VCIR_BYTES),
                _ => Ok(protocol::MAX_INPUT),
            })
            .map_err(|e| e.to_string())?
            {
                Some((protocol::ERASE, bytes))
                    if bytes.is_empty()
                        && erased.is_none()
                        && self.input.erase_plan.expects_erase
                        && record.is_empty() =>
                {
                    let (code, stderr) = self.erase(false)?;
                    erased = Some(code);
                    protocol::bytes(&mut input, protocol::ERASE_BYTES, &stderr)
                        .map_err(|e| e.to_string())?;
                    protocol::frame(&mut input, protocol::ERASE_END, &code.to_be_bytes())
                        .map_err(|e| e.to_string())?;
                }
                Some((protocol::STDOUT, bytes)) => std::io::stdout()
                    .write_all(&bytes)
                    .map_err(|e| e.to_string())?,
                Some((protocol::STDERR, bytes)) => std::io::stderr()
                    .write_all(&bytes)
                    .map_err(|e| e.to_string())?,
                Some((protocol::RECORD, bytes)) => {
                    storage::append(&mut record, &bytes, storage::MAX_RECORD_BYTES)
                        .map_err(|e| e.to_string())?
                }
                Some((protocol::VCIR, bytes)) => {
                    storage::append(&mut vcir, &bytes, storage::MAX_VCIR_BYTES)
                        .map_err(|e| e.to_string())?
                }
                Some((protocol::COMPLETE, bytes)) if bytes.len() == 2 && bytes[1] <= 1 => {
                    break (bytes[0], bytes[1] == 1)
                }
                _ => return Err("ordinary worker protocol is incomplete or out of order".into()),
            }
        };
        drop(input);
        protocol::expect_eof(&mut channel).map_err(|e| e.to_string())?;
        drop(channel);
        let status = worker.wait();
        if status.code() != Some(i32::from(code)) {
            return Err("ordinary worker status differs from its completion data".into());
        }
        self.check()?;
        let data: Value = serde_json::from_slice(&record).map_err(|e| e.to_string())?;
        let request_argv = self
            .input
            .request
            .argv
            .iter()
            .map(|a| a.to_str().map(str::to_owned).ok_or("nonUTF8 native argv"))
            .collect::<Result<Vec<_>, _>>()?;
        let expected_erase = erased.map(Value::from).unwrap_or(Value::Null);
        let expected_name = self
            .output_file
            .as_deref()
            .or(self.entry_file.as_deref())
            .and_then(std::path::Path::parent)
            .and_then(std::path::Path::file_name)
            .map(|p| p.to_string_lossy().into_owned());
        if data["schema"] != crate::verdict::SCHEMA
            || data["argv"] != json!(request_argv)
            || data["compiler_commit"] != env!("VC_SHIM_COMPILER_COMMIT")
            || data["entry_file"] != json!(self.entry_file)
            || data["output_file"] != json!(self.output_file)
            || data["test_dir"] != json!(expected_name)
            || data["exit_code"] != i32::from(code)
            || data["erase_exit"] != expected_erase
            || (code == 0 && self.input.erase_plan.expects_erase && erased != Some(0))
            || public_compile != (code == 0 && self.input.erase_plan.public_compile)
        {
            return Err(
                "ordinary worker result does not join its actual invocation and erase completion"
                    .into(),
            );
        }
        // This private value is constructed only after actual waits and all
        // current input checks. It is never deserialized from a report/ticket.
        let mut completion = JoinedOrdinaryCompletion { data, vcir, code };
        if public_compile {
            let (actual, stderr) = self.erase(true)?;
            let (lines, environment_refusal) =
                crate::shim::ordinary_erase_diagnostics(actual, &stderr);
            if environment_refusal {
                return Err("public erase read an unrepresented environment".into());
            }
            for line in lines {
                eprintln!("{line}");
            }
            if actual != 0 {
                completion.code = if actual == 101 { 101 } else { 1 };
                completion.data["outcome"] = json!("erase-rejected");
                completion.data["exit_code"] = json!(completion.code);
                completion.data["refused"] = json!(completion.data["crate_refusals"]
                    .as_array()
                    .is_some_and(|a| !a.is_empty()));
                for function in completion.data["functions"]
                    .as_array_mut()
                    .ok_or("missing native function data")?
                {
                    if function["verdict"] != "external" {
                        function["verdict"] = json!("rejected");
                        function["tag"] = Value::Null;
                        function["sites_proved"] = Value::Null;
                        function["sites_failed"] = Value::Null;
                    }
                }
            }
        }
        self.check()?;
        completion.commit(
            outputs,
            self.output_file.as_deref(),
            self.entry_file.as_deref(),
        )
    }
}

#[cfg(test)]
impl OrdinaryWorkerPlan<'_> {
    pub(super) fn private_worker_controls(&self) -> Result<(), String> {
        use std::io::Read;
        let output = self
            .output_file
            .as_ref()
            .ok_or("control needs original output")?;
        let local = output.parent().unwrap().join("trust-vc-verdict.jsonl");
        let before = std::fs::read(&local).ok();
        let verdicts = self.input.request.outputs.verdict_dir.as_ref().unwrap();
        for mode in ["forged-success", "duplicate-response", "cancel", "unwind"] {
            self.check()?;
            let mut command = self.command()?;
            command
                .arg(crate::shim::ORDINARY_WORKER_FLAG)
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::inherit());
            let mut worker = RetainedChild::spawn(&mut command).map_err(|e| e.to_string())?;
            let mut input = worker.take_stdin().map_err(|e| e.to_string())?;
            let mut channel = worker.take_stdout().map_err(|e| e.to_string())?;
            protocol::frame(&mut input, protocol::INITIAL, &self.input.encode()?)
                .map_err(|e| e.to_string())?;
            let event = protocol::receive(&mut channel).map_err(|e| e.to_string())?;
            assert!(
                matches!(event,Some((protocol::ERASE,ref bytes)) if bytes.is_empty()),
                "ordinary private control {mode}: expected empty ERASE; first event tag={:?}, payload={}",
                event.as_ref().map(|(tag, _)| *tag),
                event
                    .as_ref()
                    .map(|(_, bytes)| String::from_utf8_lossy(bytes))
                    .unwrap_or_default(),
            );
            if mode == "cancel" {
                drop(input);
                drop(channel);
                worker.cancel();
            } else if mode == "unwind" {
                let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
                    let (_worker, _input, _channel) = (worker, input, channel);
                    panic!("ordinary actual-worker unwind control");
                }));
                assert!(caught.is_err());
            } else {
                let forged = crate::shim::empty_erase_response_for_data_control();
                protocol::bytes(&mut input, protocol::ERASE_BYTES, &forged)
                    .map_err(|e| e.to_string())?;
                protocol::frame(&mut input, protocol::ERASE_END, &0i32.to_be_bytes())
                    .map_err(|e| e.to_string())?;
                if mode == "duplicate-response" {
                    protocol::frame(&mut input, protocol::ERASE_END, &0i32.to_be_bytes())
                        .map_err(|e| e.to_string())?;
                }
                let mut record = Vec::new();
                loop {
                    match protocol::receive_limited(&mut channel, |tag| match tag {
                        protocol::RECORD => {
                            storage::remaining(record.len(), storage::MAX_RECORD_BYTES)
                        }
                        _ => Ok(protocol::MAX_INPUT),
                    })
                    .map_err(|e| e.to_string())?
                    {
                        Some((protocol::COMPLETE, _)) => break,
                        Some((protocol::RECORD, bytes)) => {
                            storage::append(&mut record, &bytes, storage::MAX_RECORD_BYTES)
                                .map_err(|e| e.to_string())?
                        }
                        Some((protocol::STDOUT | protocol::STDERR | protocol::VCIR, _)) => {}
                        _ => return Err("private data control did not complete".into()),
                    }
                }
                drop(input);
                let mut extra = [0];
                assert_eq!(channel.read(&mut extra).map_err(|e| e.to_string())?, 0);
                drop(channel);
                let status = worker.wait();
                if mode == "forged-success" {
                    assert_eq!(status.code(), Some(0));
                    let data: Value = serde_json::from_slice(&record).unwrap();
                    assert_eq!(data["outcome"], "checked");
                } else {
                    assert_eq!(status.code(), Some(1));
                }
            }
            assert_eq!(std::fs::read(&local).ok(), before);
            assert!(!output.exists());
            assert!(!verdicts.exists());
            if let Some(path) = &self.input.request.outputs.dump_vcir {
                assert!(!path.exists());
            }
            self.check()?;
        }
        Ok(())
    }
}

struct JoinedOrdinaryCompletion {
    data: Value,
    vcir: Vec<u8>,
    code: u8,
}
impl JoinedOrdinaryCompletion {
    fn commit(
        self,
        outputs: &OutputSinks,
        output_file: Option<&std::path::Path>,
        entry_file: Option<&std::path::Path>,
    ) -> Result<u8, String> {
        let test_dir = output_file
            .or(entry_file)
            .and_then(std::path::Path::parent)
            .and_then(std::path::Path::file_name)
            .map(|p| p.to_string_lossy().into_owned());
        for problem in outputs.write_record_data(
            output_file,
            test_dir.as_deref(),
            &format!("{}\n", self.data),
        ) {
            eprintln!(
                "{}",
                crate::verdict::crate_refusal_json("record-output", &problem)
            );
        }
        if !self.vcir.is_empty() {
            let text = std::str::from_utf8(&self.vcir).map_err(|e| e.to_string())?;
            let _ = outputs.write_vcir(text);
        }
        Ok(self.code)
    }
}
