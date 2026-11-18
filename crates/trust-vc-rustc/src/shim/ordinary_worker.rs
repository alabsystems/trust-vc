// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! An isolated ordinary compiler. Every payload field is request/input data.
//! No decoder here constructs ClientImports, StandaloneImported or a library
//! contract. The actual native callback checks selections before read(None).

use super::ordinary_protocol as protocol;
use super::*;
use crate::declaration_alignment::source_bindings::PinnedFile;
use crate::native_requests::Request;
use serde_json::{json, Value};
use std::collections::BTreeSet;
use std::io::Read;
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::sync::{Arc, Mutex};

const MAX_PAYLOAD: usize = crate::native_requests::MAX_REQUEST_BYTES * 8;
pub(super) const ERASE_BINDING: &str = "--trust-vc-erase-ordinary-inputs";

#[derive(Clone)]
pub(crate) struct NativeInput {
    pub(crate) stable_crate_id: u64,
    pub(crate) svh: u128,
    pub(crate) file: PinnedFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ErasePlan {
    pub(crate) args: Vec<String>,
    pub(crate) cargo_inputs: std::collections::BTreeMap<String, Option<String>>,
    pub(crate) verify_output: Option<PathBuf>,
    pub(crate) erase_output: PathBuf,
    pub(crate) expects_erase: bool,
    pub(crate) public_compile: bool,
}

impl ErasePlan {
    fn json(&self) -> Value {
        json!({"args":self.args,"cargo_inputs":self.cargo_inputs,
            "verify_output":self.verify_output,"erase_output":self.erase_output,
            "expects_erase":self.expects_erase,"public_compile":self.public_compile})
    }
    fn parse(value: &Value) -> Result<Self, String> {
        let value = object(
            value,
            &[
                "args",
                "cargo_inputs",
                "verify_output",
                "erase_output",
                "expects_erase",
                "public_compile",
            ],
        )?;
        Ok(Self {
            args: serde_json::from_value(value["args"].clone()).map_err(|e| e.to_string())?,
            cargo_inputs: serde_json::from_value(value["cargo_inputs"].clone())
                .map_err(|e| e.to_string())?,
            verify_output: serde_json::from_value(value["verify_output"].clone())
                .map_err(|e| e.to_string())?,
            erase_output: serde_json::from_value(value["erase_output"].clone())
                .map_err(|e| e.to_string())?,
            expects_erase: value["expects_erase"]
                .as_bool()
                .ok_or("missing erase policy")?,
            public_compile: value["public_compile"]
                .as_bool()
                .ok_or("missing public compile policy")?,
        })
    }
}

pub(crate) struct WorkerInput {
    pub(crate) request: Request,
    pub(crate) source: PinnedFile,
    pub(crate) common: Vec<NativeInput>,
    pub(crate) forbidden_library: u64,
    pub(crate) program: PinnedFile,
    pub(crate) erase_plan: ErasePlan,
}

fn object<'a>(
    value: &'a Value,
    names: &[&str],
) -> Result<&'a serde_json::Map<String, Value>, String> {
    let map = value
        .as_object()
        .ok_or("ordinary worker requires an object")?;
    if map.len() != names.len() || map.keys().any(|key| !names.contains(&key.as_str())) {
        return Err("ordinary worker fields are missing or unrepresented".into());
    }
    Ok(map)
}
fn pinned(value: &Value) -> Result<PinnedFile, String> {
    let map = object(value, &["path", "sha256"])?;
    let bytes =
        serde_json::from_value::<Vec<u8>>(map["path"].clone()).map_err(|e| e.to_string())?;
    if bytes.contains(&0) {
        return Err("NUL in ordinary native input".into());
    }
    let path = PathBuf::from(std::ffi::OsString::from_vec(bytes));
    let sha256 = serde_json::from_value(map["sha256"].clone()).map_err(|e| e.to_string())?;
    if !path.is_absolute() || path.canonicalize().map_err(|e| e.to_string())? != path {
        return Err("ordinary native inputs require exact canonical paths".into());
    }
    let file = PinnedFile { path, sha256 };
    file.read()?;
    Ok(file)
}
fn pin_json(file: &PinnedFile) -> Value {
    json!({"path":file.path.as_os_str().as_bytes(),"sha256":file.sha256})
}
fn number(value: &Value, width: usize) -> Result<u128, String> {
    let text = value
        .as_str()
        .ok_or("missing native hexadecimal identity")?;
    if text.len() != width
        || !text
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err("invalid native hexadecimal identity".into());
    }
    u128::from_str_radix(text, 16).map_err(|e| e.to_string())
}
impl WorkerInput {
    pub(crate) fn encode(&self) -> Result<Vec<u8>, String> {
        let value = json!({"schema":"trust-vc.ordinary-worker-input@1",
            "request":self.request.encode_data().map_err(|e|e.to_string())?,
            "source":pin_json(&self.source),"program":pin_json(&self.program),"erase_plan":self.erase_plan.json(),
            "forbidden_library":format!("{:016x}",self.forbidden_library),
            "common":self.common.iter().map(|row|json!({"id":format!("{:016x}",row.stable_crate_id),
                "svh":format!("{:032x}",row.svh),"file":pin_json(&row.file)})).collect::<Vec<_>>()});
        let bytes = serde_json::to_vec(&value).map_err(|e| e.to_string())?;
        if bytes.len() > MAX_PAYLOAD {
            return Err("ordinary worker input exceeds its data bound".into());
        }
        Ok(bytes)
    }
    pub(crate) fn decode(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() > MAX_PAYLOAD {
            return Err("ordinary worker input exceeds its data bound".into());
        }
        let value: Value = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
        // This private writer uses one exact JSON representation. Reject
        // duplicate keys and trailing/alternative encodings, not just unknowns.
        if serde_json::to_vec(&value).map_err(|e| e.to_string())? != bytes {
            return Err("ordinary worker input is not its exact data encoding".into());
        }
        let map = object(
            &value,
            &[
                "schema",
                "request",
                "source",
                "program",
                "erase_plan",
                "forbidden_library",
                "common",
            ],
        )?;
        if map["schema"] != "trust-vc.ordinary-worker-input@1" {
            return Err("unknown ordinary worker data".into());
        }
        let raw: Vec<u8> =
            serde_json::from_value(map["request"].clone()).map_err(|e| e.to_string())?;
        let request = Request::decode_data(&raw).map_err(|e| e.to_string())?;
        let mut common = Vec::new();
        let (mut ids, mut files) = (BTreeSet::new(), BTreeSet::new());
        for row in map["common"]
            .as_array()
            .ok_or("missing ordinary native inputs")?
        {
            let row = object(row, &["id", "svh", "file"])?;
            let stable_crate_id =
                u64::try_from(number(&row["id"], 16)?).map_err(|e| e.to_string())?;
            let svh = number(&row["svh"], 32)?;
            let file = pinned(&row["file"])?;
            if !ids.insert(stable_crate_id) || !files.insert(file.path.clone()) {
                return Err("ordinary native input identities collide".into());
            }
            common.push(NativeInput {
                stable_crate_id,
                svh,
                file,
            });
        }
        let forbidden_library =
            u64::try_from(number(&map["forbidden_library"], 16)?).map_err(|e| e.to_string())?;
        if ids.contains(&forbidden_library) {
            return Err("ordinary input contains the paired SDK library".into());
        }
        Ok(Self {
            request,
            source: pinned(&map["source"])?,
            common,
            forbidden_library,
            program: pinned(&map["program"])?,
            erase_plan: ErasePlan::parse(&map["erase_plan"])?,
        })
    }
}

/// Extra negative constraints on an ordinary read. This contains no imported
/// declarations/equations or compiler lifetime and supplies no proof authority.
#[derive(Clone)]
pub(super) struct Binding {
    input: Arc<WorkerInput>,
    invocation: Arc<NormalInvocation>,
    prepared_options: Option<rustc_session::config::Options>,
    remote: Option<Arc<Mutex<Exchange>>>,
    data: Arc<Mutex<WorkerData>>,
}
impl Binding {
    fn new(input: WorkerInput) -> Result<(Self, Vec<String>), String> {
        let argv = input
            .request
            .argv
            .iter()
            .map(|arg| {
                arg.to_str()
                    .map(str::to_owned)
                    .ok_or("the native compiler requires UTF-8 arguments".to_owned())
            })
            .collect::<Result<Vec<_>, _>>()?;
        input.request.cargo.validate(&argv)?;
        input
            .request
            .cargo
            .check_macro_package(input.request.macro_package_name.as_deref())?;
        if std::env::var_os("CARGO_PKG_NAME") != input.request.macro_package_name
            || std::env::var_os("VSTD_KIND").is_some()
        {
            return Err(
                "ordinary worker did not receive its exact independent macro inputs".into(),
            );
        }
        if std::env::current_dir()
            .map_err(|e| e.to_string())?
            .canonicalize()
            .map_err(|e| e.to_string())?
            != input.request.cwd
        {
            return Err("ordinary worker cwd differs from its original request".into());
        }
        let (args, cargo_inputs, compile_option, via_cargo) = match crate::cargo::prepare(
            &argv,
            |key| input.request.cargo.read(key),
        )? {
            CargoInvocation::Standalone => (
                argv.get(1..).unwrap_or(&[]).to_vec(),
                CargoInputs::default(),
                false,
                false,
            ),
            CargoInvocation::Verify {
                args,
                options,
                inputs,
            } if options.import_deps.is_empty() => (args, inputs, options.compile, true),
            CargoInvocation::Verify { .. } => {
                return Err(
                    "ordinary dependency imports require retained live library nodes".into(),
                )
            }
            CargoInvocation::Direct { .. } => return Err(
                "direct Cargo compiler cohorts require their independent ordinary native callback"
                    .into(),
            ),
        };
        let split = args::split(&args).map_err(|e| e.to_string())?;
        if let Some((_, why)) = unsupported_request(&split, via_cargo) {
            return Err(why);
        }
        if split
            .verus
            .iter()
            .any(|o| matches!(o.name.as_str(), "import" | "export" | "is-vstd" | "is-core"))
        {
            return Err(
                "ordinary worker cannot import, export or construct a library owner".into(),
            );
        }
        let public_compile = via_cargo && (compile_option || split.has("compile"));
        let invocation = NormalInvocation::derive(
            argv.first().cloned().ok_or("missing ordinary argv0")?,
            split,
        )?;
        invocation.source_matches(&input.source)?;
        let expected = &input.erase_plan;
        if expected.args != invocation.erase()
            || expected.cargo_inputs != cargo_inputs.0
            || expected.expects_erase != invocation.expects_erase()
            || expected.public_compile != public_compile
            || expected.verify_output.is_some() != via_cargo
        {
            return Err("ordinary erase plan differs from the original invocation".into());
        }
        if !expected.erase_output.is_absolute()
            || expected.erase_output.file_name().and_then(|p| p.to_str()) != Some("erase")
            || expected
                .erase_output
                .canonicalize()
                .map_err(|e| e.to_string())?
                != expected.erase_output
        {
            return Err("ordinary erase output has no exact managed location".into());
        }
        if let Some(path) = &expected.verify_output {
            if !path.is_absolute()
                || path.file_name().and_then(|x| x.to_str()) != Some("verify")
                || path.canonicalize().map_err(|e| e.to_string())? != *path
            {
                return Err("ordinary private output has no exact managed location".into());
            }
        }
        Ok((
            Self {
                input: Arc::new(input),
                invocation: Arc::new(invocation),
                prepared_options: None,
                remote: None,
                data: Arc::new(Mutex::new(WorkerData::default())),
            },
            argv,
        ))
    }
    pub(super) fn configure(&mut self, config: &rustc_interface::interface::Config) {
        self.prepared_options = Some(config.opts.clone());
    }
    pub(super) fn read_input() -> Result<Self, String> {
        let mut bytes = Vec::new();
        std::io::stdin()
            .take((MAX_PAYLOAD + 1) as u64)
            .read_to_end(&mut bytes)
            .map_err(|e| e.to_string())?;
        Self::new(WorkerInput::decode(&bytes)?).map(|(binding, _)| binding)
    }
    pub(super) fn check(&self, tcx: TyCtxt<'_>) -> Result<(), String> {
        self.invocation.check_native_source(tcx)?;
        let expected = self
            .prepared_options
            .as_ref()
            .ok_or("ordinary native callback missed its original Config")?;
        crate::reader::declaration_staging::check_ordinary_native_options(
            expected,
            &tcx.sess.opts,
        )?;
        if std::env::var_os("VSTD_KIND").is_some()
            || std::env::var_os("CARGO_PKG_NAME") != self.input.request.macro_package_name
            || std::env::var("CARGO_PKG_NAME").as_deref() == Ok("vstd")
            || !tcx
                .sess
                .config
                .contains(&(rustc_span::Symbol::intern("verus_no_vstd"), None))
        {
            return Err(
                "ordinary worker requires its independent native no-vstd macro context".into(),
            );
        }
        let mut seen = BTreeSet::new();
        for krate in tcx.crates(()) {
            let id = tcx.stable_crate_id(*krate).as_u64();
            if id == self.input.forbidden_library {
                return Err("ordinary worker loaded the paired SDK target under an alias".into());
            }
            let svh = tcx.crate_hash(*krate).as_u128();
            let native = tcx.used_crate_source(*krate);
            let path = native
                .rmeta
                .as_ref()
                .or(native.rlib.as_ref())
                .or(native.dylib.as_ref())
                .ok_or("ordinary native dependency has no selected file")?
                .canonicalize()
                .map_err(|e| e.to_string())?;
            let row = self
                .input
                .common
                .iter()
                .find(|r| r.stable_crate_id == id)
                .ok_or("ordinary native dependency is outside the actual common cohort")?;
            if row.svh != svh || row.file.path != path || !seen.insert(id) {
                return Err("ordinary native dependency identity/path changed".into());
            }
            row.file.read()?;
        }
        // A subset is intentional: ordinary no-vstd code need not load every
        // library-producer dependency. Every actual selection above is joined.
        for (key, value) in tcx.sess.env_depinfo.lock().iter() {
            let key = key.as_str();
            let observed = value.as_ref().map(|v| v.as_str().to_owned());
            let expected = match key {
                "TRUST_VC_VERDICT_DIR" => self
                    .input
                    .request
                    .outputs
                    .verdict_dir
                    .as_ref()
                    .map(|p| p.as_os_str()),
                "TRUST_VC_DUMP_VCIR" => self
                    .input
                    .request
                    .outputs
                    .dump_vcir
                    .as_ref()
                    .map(|p| p.as_os_str()),
                "VERUSDOC" => self.input.request.verusdoc.as_deref(),
                "CARGO_PKG_NAME" => self.input.request.macro_package_name.as_deref(),
                _ => {
                    let expected = self.input.request.cargo.read(key)?;
                    if expected != observed {
                        return Err(
                            "ordinary Cargo dependency differs from its actual request".into()
                        );
                    }
                    continue;
                }
            }
            .map(|s| {
                s.to_str()
                    .map(str::to_owned)
                    .ok_or("ordinary native environment is not Unicode")
            })
            .transpose()?;
            if expected != observed {
                return Err("ordinary output/document dependency differs from its request".into());
            }
        }
        self.input.source.read()?;
        Ok(())
    }
}

#[derive(Default)]
struct WorkerData {
    record: Option<Value>,
    vcir: Option<String>,
    public_compile: bool,
}
struct Exchange {
    input: std::fs::File,
    output: std::fs::File,
    erase_requested: bool,
}

impl Binding {
    pub(super) fn private_output(&self) -> Option<&std::path::Path> {
        self.input.erase_plan.verify_output.as_deref()
    }
    pub(super) fn capture_record(&self, mut record: Record, code: u8) -> u8 {
        record.exit_code = Some(i32::from(code));
        let mut data = self.data.lock().unwrap();
        assert!(data.record.is_none(), "ordinary worker completed twice");
        data.record = Some(record.to_json());
        code
    }
    pub(super) fn capture_vcir(&self, text: String) {
        self.data.lock().unwrap().vcir = Some(text);
    }
    pub(super) fn defer_public_compile(&self) {
        self.data.lock().unwrap().public_compile = true;
    }
    pub(super) fn remote_erase(
        &self,
        args: &[String],
        inputs: &CargoInputs,
        private_output: Option<&std::path::Path>,
    ) -> Result<EraseChild, String> {
        let expected = &self.input.erase_plan;
        let erase_output = expected
            .verify_output
            .as_ref()
            .map(|p| p.with_file_name("erase"));
        if args != expected.args
            || inputs.0 != expected.cargo_inputs
            || private_output != erase_output.as_deref()
            || !expected.expects_erase
        {
            return Err(
                "ordinary erase operation differs from the independently prepared request".into(),
            );
        }
        let mut exchange = self
            .remote
            .as_ref()
            .ok_or("erase worker cannot request another erase")?
            .lock()
            .map_err(|_| "ordinary exchange poisoned")?;
        if exchange.erase_requested {
            return Err("duplicate ordinary erase operation".into());
        }
        exchange.erase_requested = true;
        protocol::frame(&mut exchange.output, protocol::ERASE, &[]).map_err(|e| e.to_string())?;
        let mut stderr = Vec::new();
        loop {
            match protocol::receive_limited(&mut exchange.input, |tag| match tag {
                protocol::ERASE_BYTES => crate::retained_bytes::remaining(
                    stderr.len(),
                    crate::retained_bytes::MAX_ERASE_STDERR_BYTES,
                ),
                protocol::ERASE_END => Ok(4),
                _ => Ok(0),
            })
            .map_err(|e| e.to_string())?
            {
                Some((protocol::ERASE_BYTES, bytes)) => crate::retained_bytes::append(
                    &mut stderr,
                    &bytes,
                    crate::retained_bytes::MAX_ERASE_STDERR_BYTES,
                )
                .map_err(|e| e.to_string())?,
                Some((protocol::ERASE_END, bytes)) if bytes.len() == 4 => {
                    let code = i32::from_be_bytes(bytes.try_into().unwrap());
                    return Ok(erase_child_result(code, &stderr));
                }
                _ => return Err("missing or malformed actual erase result".into()),
            }
        }
    }
}

pub fn main() -> ExitCode {
    let result = (|| -> Result<u8, String> {
        let (mut input_pipe, output_pipe) =
            crate::stdio_capture::standard_data_pipes().map_err(|e| e.to_string())?;
        let bytes = match protocol::receive(&mut input_pipe).map_err(|e| e.to_string())? {
            Some((protocol::INITIAL, bytes)) => bytes,
            _ => return Err("ordinary worker has no bounded initial input".into()),
        };
        let input = WorkerInput::decode(&bytes)?;
        let current = std::env::current_exe()
            .map_err(|e| e.to_string())?
            .canonicalize()
            .map_err(|e| e.to_string())?;
        if current != input.program.path
            || crate::reader::declaration_staging::ordinary_file_digest(&current)?
                != input.program.sha256
        {
            return Err(
                "ordinary worker executable differs from the actual retained producer".into(),
            );
        }
        let (mut binding, argv) = Binding::new(input)?;
        let exchange = Arc::new(Mutex::new(Exchange {
            input: input_pipe,
            output: output_pipe,
            erase_requested: false,
        }));
        binding.remote = Some(exchange.clone());
        let cwd = binding.input.request.cwd.clone();
        let outputs = OutputSinks::for_request(
            &cwd,
            binding.input.request.outputs.verdict_dir.clone(),
            binding.input.request.outputs.dump_vcir.clone(),
        )
        .map_err(|e| e.to_string())?;
        let cargo = binding.input.request.cargo.clone();
        let scratch = crate::cargo::Scratch::new().map_err(|e| e.to_string())?;
        // SAFETY: this dedicated process has no concurrent compiler/stdio/cwd
        // users; all erase work is requested on the separate owned DATA pipes.
        let (code, mut stdout, mut stderr) = unsafe {
            crate::stdio_capture::run(scratch.path(), "ordinary", &cwd, || {
                run_with_binding(argv, outputs, |key| cargo.read(key), Some(binding.clone()))
            })
        }
        .map_err(|e| e.to_string())?;
        let data = binding
            .data
            .lock()
            .map_err(|_| "ordinary output poisoned")?;
        let record = data
            .record
            .as_ref()
            .ok_or("ordinary worker produced no record data")?;
        let mut exchange = exchange.lock().map_err(|_| "ordinary exchange poisoned")?;
        protocol::stream(&mut exchange.output, protocol::STDOUT, &mut stdout)
            .map_err(|e| e.to_string())?;
        protocol::stream(&mut exchange.output, protocol::STDERR, &mut stderr)
            .map_err(|e| e.to_string())?;
        protocol::bytes(
            &mut exchange.output,
            protocol::RECORD,
            &serde_json::to_vec(record).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        if let Some(text) = &data.vcir {
            protocol::bytes(&mut exchange.output, protocol::VCIR, text.as_bytes())
                .map_err(|e| e.to_string())?;
        }
        protocol::frame(
            &mut exchange.output,
            protocol::COMPLETE,
            &[code, u8::from(data.public_compile)],
        )
        .map_err(|e| e.to_string())?;
        protocol::expect_eof(&mut exchange.input).map_err(|e| e.to_string())?;
        Ok(code)
    })();
    match result {
        Ok(code) => ExitCode::from(code),
        Err(why) => {
            eprintln!("{}", verdict::crate_refusal_json("ordinary-worker", &why));
            ExitCode::from(1)
        }
    }
}
