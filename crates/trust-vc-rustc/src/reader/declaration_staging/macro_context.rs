//! A standalone comparison of cached and separately loaded macro state.
//!
//! Both client analyses are observations. Even a distinct loaded image and
//! successful type analysis grant no declaration, ownership or proof authority.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::ffi::OsString;
use std::path::Path;

use super::*;
mod normal_plan;
mod search;
pub(crate) use normal_plan::{NormalClientPlan, NormalPlanIdentity};

pub(super) struct ClientSource {
    file: PinnedFile,
}

impl ClientSource {
    pub(super) fn read(path: &Path) -> Result<Self, String> {
        let path = path.canonicalize().map_err(|e| e.to_string())?;
        let file = PinnedFile {
            sha256: inputs::digest(&path)?,
            path,
        };
        file.read()?;
        Ok(Self { file })
    }

    pub(super) fn file(&self) -> &PinnedFile {
        &self.file
    }
}

/// Both argument vectors are constructed by the live owner. No command line,
/// receipt, caller-provided erase argv or success flag constructs this pair.
pub(crate) struct NormalClientArgs {
    verify: Vec<String>,
    erase: Vec<String>,
}

impl NormalClientArgs {
    pub(crate) fn verify(&self) -> &[String] {
        &self.verify
    }
    pub(crate) fn erase(&self) -> &[String] {
        &self.erase
    }
}

pub(super) fn normal_client_args(
    library: &StagedLibrary,
    source: &ClientSource,
    macros: &[&PinnedFile],
    output: &Path,
    erase_output: &Path,
) -> Result<NormalClientArgs, String> {
    let mut verify = client_args(library, source, macros, output)?;
    let mut erase = Vec::with_capacity(verify.len());
    let mut at = 0;
    let mut bodies = 0;
    let mut outputs = 0;
    while at < verify.len() {
        if verify[at] == "--cfg"
            && verify
                .get(at + 1)
                .is_some_and(|s| s == "verus_keep_ghost_body")
        {
            bodies += 1;
            at += 2;
        } else if verify[at] == "-o" {
            if verify.get(at + 1).map(String::as_str) != output.to_str() {
                return Err("the normal client output is not its owned metadata path".into());
            }
            outputs += 1;
            erase.extend(["-o".into(), erase_output.display().to_string()]);
            at += 2;
        } else {
            erase.push(verify[at].clone());
            at += 1;
        }
    }
    if bodies != 1 || outputs != 1 || output == erase_output {
        return Err("the normal verify/erase argument correspondence is ambiguous".into());
    }
    crate::shim::normal_client_lints(&mut verify, &mut erase);
    Ok(NormalClientArgs { verify, erase })
}

/// This guard is confined to the standalone driver after each preceding
/// compiler's scoped threads have joined. Engine callbacks must not change
/// process-wide macro environment to select a client expansion context.
struct ImportedEnvironment {
    previous: OsString,
}

impl ImportedEnvironment {
    /// # Safety
    /// No other thread may access the process environment until this guard
    /// is dropped, except the subsequently invoked, scoped compiler itself.
    unsafe fn enter() -> Result<Self, String> {
        let previous = std::env::var_os("VSTD_KIND")
            .filter(|value| value == "IsVstd")
            .ok_or("the standalone producer must begin in genuine IsVstd context")?;
        unsafe {
            std::env::set_var("VSTD_KIND", "Imported");
        }
        Ok(Self { previous })
    }
}

impl Drop for ImportedEnvironment {
    fn drop(&mut self) {
        // The standalone caller keeps the same environment exclusion until
        // every client compiler has returned and this guard is dropped.
        unsafe {
            std::env::set_var("VSTD_KIND", &self.previous);
        }
    }
}

pub(super) fn client_args(
    library: &StagedLibrary,
    source: &ClientSource,
    macros: &[&PinnedFile],
    output: &Path,
) -> Result<Vec<String>, String> {
    source.file.read()?;
    if macros.len() != 2 {
        return Err("the client requires the genuine two macro images".into());
    }
    let mut args = library
        .inputs
        .client_args(&library.prepared.erase.file.path, &source.file.path);
    let mut replaced = std::collections::BTreeSet::new();
    let mut at = 0;
    while at < args.len() {
        if args[at] == "--extern" {
            let value = args
                .get_mut(at + 1)
                .ok_or("incomplete closed extern argument")?;
            let (name, _) = value
                .split_once('=')
                .ok_or("unrepresented closed extern argument")?;
            let name = name.to_owned();
            if matches!(
                name.as_str(),
                "verus_builtin" | "verus_builtin_macros" | "verus_state_machines_macros"
            ) {
                if !replaced.insert(name.clone()) {
                    return Err("duplicate closed builtin extern".into());
                }
                let file = if name == "verus_builtin" {
                    &library.inputs.builtin
                } else {
                    macros
                        .iter()
                        .copied()
                        .find(|file| {
                            file.path
                                .file_name()
                                .is_some_and(|actual| actual == format!("lib{name}.dylib").as_str())
                        })
                        .ok_or("the client image does not belong to its actual macro crate")?
                };
                file.read()?;
                *value = format!("force:{name}={}", file.path.display());
            }
            at += 2;
        } else {
            at += 1;
        }
    }
    if replaced.len() != 3 {
        return Err("the closed client is missing a genuine builtin extern".into());
    }
    args.extend([
        "-Zunstable-options".into(),
        "--error-format=json".into(),
        "--cfg".into(),
        "verus_keep_ghost_body".into(),
        "-o".into(),
        output.display().to_string(),
    ]);
    let (original, selected) = macro_search_selection(library, macros)?;
    search::selected_search(args, &original, &selected)
}

fn macro_search_selection(
    library: &StagedLibrary,
    macros: &[&PinnedFile],
) -> Result<(BTreeSet<std::path::PathBuf>, BTreeSet<std::path::PathBuf>), String> {
    if macros.len() != 2 {
        return Err("the client requires the genuine two macro images".into());
    }
    let original = library
        .inputs
        .macros
        .iter()
        .filter_map(|file| file.path.parent())
        .map(Path::to_path_buf)
        .collect::<std::collections::BTreeSet<_>>();
    let selected = macros
        .iter()
        .filter_map(|file| file.path.parent())
        .map(Path::to_path_buf)
        .collect::<std::collections::BTreeSet<_>>();
    Ok((original, selected))
}

/// Use the production selection instead of the parents of explicit artifacts.
/// The original builtin's parent also contains the original macros, so it is
/// not an additional dependency lookup path for the copied native view.
pub(super) fn client_dependency_directories(
    library: &StagedLibrary,
    macros: &[&PinnedFile],
) -> Result<BTreeSet<std::path::PathBuf>, String> {
    let (original, selected) = macro_search_selection(library, macros)?;
    let mut directories = library
        .inputs
        .common_files
        .keys()
        .filter_map(|path| path.parent())
        .map(Path::to_path_buf)
        .collect::<BTreeSet<_>>();
    directories.insert(
        library
            .prepared
            .erase
            .file
            .path
            .parent()
            .ok_or("the owned target has no metadata parent")?
            .to_path_buf(),
    );
    search::selected_directories(directories, &original, &selected)
}

struct ObserveClient<'a> {
    library: &'a StagedLibrary,
    images: Option<&'a client_images::ClientImages<'a>>,
    source: &'a ClientSource,
    argv: &'a [String],
    result: Option<Result<Value, String>>,
}

impl Callbacks for ObserveClient<'_> {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        self.result = Some((|| {
            diagnostics(tcx)?;
            self.source.file.read()?;
            let invocation = Invocation::capture_client(tcx, self.argv)?;
            if !invocation.same_target(&self.library.prepared.erase.invocation) {
                return Err("the observed client changed the native library target/sysroot".into());
            }
            let images = if let Some(images) = self.images {
                images.observe(tcx)?.observation()
            } else {
                let _selected = collect::selections(
                    tcx,
                    &self.library.inputs,
                    Some(&self.library.prepared.erase.file),
                )?;
                json!({"state": "OriginalMacroImages", "context_authority": "Unknown"})
            };
            diagnostics(tcx)?;
            Ok(json!({"source_path": self.source.file.path,
                "source_sha256": self.source.file.sha256, "invocation": invocation.observation(),
                "images": images, "native_type_analysis": "ReturnedWithoutDiagnostics",
                "native_ownership_checked": false, "import_authorized": false,
                "verified_functions": null}))
        })());
        Compilation::Stop
    }
}

fn observe(
    library: &StagedLibrary,
    source: &ClientSource,
    images: Option<&client_images::ClientImages<'_>>,
    phase: &str,
) -> Result<Value, String> {
    let macros = images
        .map(|images| images.macro_files().collect::<Vec<_>>())
        .unwrap_or_else(|| library.inputs.macros.iter().collect());
    let args = client_args(
        library,
        source,
        &macros,
        &library.inputs.output.join(format!("{phase}.rmeta")),
    )?;
    let mut callback = ObserveClient {
        library,
        images,
        source,
        argv: &args,
        result: None,
    };
    // The markers delimit real, unsuppressed native JSON diagnostics so the
    // outer measurement can require E0433/prelude rather than any failure.
    eprintln!(
        "{}",
        json!({"macro_context_phase": phase, "event": "begin"})
    );
    let compiler = run_compiler(&args, &mut callback);
    eprintln!("{}", json!({"macro_context_phase": phase, "event": "end"}));
    record_phase(&library.inputs, phase, &compiler, callback.result.as_ref())?;
    library.inputs.revalidate()?;
    source.file.read()?;
    if let Some(images) = images {
        images.revalidate()?;
    }
    Ok(
        json!({"phase": phase, "argv": args, "compiler_returned": compiler.is_ok(),
        "compiler_error": compiler.err(),
        "callback": match callback.result {
            Some(Ok(value)) => json!({"state": "Observed", "value": value}),
            Some(Err(reason)) => json!({"state": "Rejected", "reason": reason}),
            None => json!({"state": "NotReached"}),
        },
        "diagnostic_classification": "Unknown; actual emitted code/message/spans must be checked",
        "import_authorized": false, "verified_functions": null}),
    )
}

fn save(
    library: &StagedLibrary,
    source: &ClientSource,
    original: &Value,
    copied: Option<&Value>,
) -> Result<(), String> {
    let report = json!({"schema": "trust-vc.macro-context-observation@1",
        "source_path": source.file.path, "source_sha256": source.file.sha256,
        "original": original, "copied": copied,
        "context_authority": "Unknown; actual discriminator diagnostics require qualification",
        "import_authorized": false, "verified_functions": null});
    std::fs::write(
        library.inputs.output.join("macro-context.json"),
        serde_json::to_vec_pretty(&report).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())
}

/// # Safety
/// This is a standalone command entry, not a host-engine callback. The caller
/// must have created no background threads and exclude other process-wide
/// compiler/environment users until it returns. Every run_compiler call must
/// return before the next environment transition or this function's return.
pub(super) unsafe fn run(request: &Path, client: &Path) -> Result<(), String> {
    if std::env::var("VSTD_KIND").as_deref() != Ok("IsVstd") {
        return Err("the standalone comparison must start with IsVstd".into());
    }
    let source = ClientSource::read(client)?;
    let library = produce(request)?;
    library.write_observation()?;
    let images = client_images::ClientImages::prepare(&library)?;
    let _environment = unsafe { ImportedEnvironment::enter()? };
    let original = observe(&library, &source, None, "CachedOriginalMacroImages")?;
    save(&library, &source, &original, None)?;
    if original["compiler_returned"] != false || original["callback"]["state"] == "Observed" {
        return Err(
            "the original macro image did not exhibit the expected cached-context refusal".into(),
        );
    }
    let copied = observe(&library, &source, Some(&images), "OwnedCopyMacroImages")?;
    save(&library, &source, &original, Some(&copied))?;
    if copied["compiler_returned"] != true || copied["callback"]["state"] != "Observed" {
        return Err(
            "the owned copied macro image did not complete the actual client observation".into(),
        );
    }
    Ok(())
}

/// Run the closed, observation-only macro-state comparison command.
///
/// # Safety
/// The caller must be the standalone process entry and satisfy `run`'s
/// process-environment exclusion for the entire command. This entry must not
/// be called by an embedding compiler or concurrent host engine.
pub unsafe fn main() -> ExitCode {
    let mut args = std::env::args_os().skip(1);
    let result = match (args.next(), args.next(), args.next()) {
        (Some(request), Some(client), None) => unsafe {
            run(Path::new(&request), Path::new(&client))
        },
        _ => Err(
            "expected staging request and unchanged client source; no compiler flag passthrough"
                .into(),
        ),
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("native macro context observation: {error}");
            ExitCode::FAILURE
        }
    }
}
