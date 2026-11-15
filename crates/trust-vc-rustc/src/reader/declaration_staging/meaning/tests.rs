//! Actual compiler selections and counterfeit diagnostic-item controls.
//! Fixture Inputs exercise refusal without a fresh build; they do not stand
//! for an approved vstd producer. The genuine fresh positive is an integration
//! gate owned by the staging process, never reconstructed in these tests.

extern crate rustc_driver;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use serde_json::{json, Value};

use crate::declaration_alignment::source_bindings::{MetadataInput, Sources};

use super::*;

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Temp(PathBuf);
impl Drop for Temp {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }
}

fn pin(path: PathBuf) -> PinnedFile {
    let path = path.canonicalize().unwrap();
    PinnedFile {
        sha256: super::super::inputs::digest(&path).unwrap(),
        path,
    }
}

fn selected_file(tcx: TyCtxt<'_>, definition: DefId) -> PinnedFile {
    let source = tcx.used_crate_source(definition.krate);
    pin(source
        .rmeta
        .as_ref()
        .or(source.rlib.as_ref())
        .or(source.dylib.as_ref())
        .unwrap()
        .to_path_buf())
}

fn arguments(path: &Path, output: &Path, name: &str) -> Vec<String> {
    vec![
        "native-meaning-control".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        env!("VC_SHIM_COMPILER_SYSROOT").into(),
        "--crate-type=lib".into(),
        format!("--crate-name={name}"),
        "--edition=2021".into(),
        "--emit=metadata".into(),
        "--out-dir".into(),
        output.to_str().unwrap().into(),
        path.to_str().unwrap().into(),
    ]
}

struct Emit;
impl Callbacks for Emit {}

struct Inspect {
    root: PathBuf,
    source: PathBuf,
    result: Option<Value>,
}
impl Callbacks for Inspect {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let box_def = tcx
            .lang_items()
            .owned_box()
            .expect("the fixture uses actual std Box");
        let driver = super::super::identity::loaded_driver().unwrap();
        let box_file = selected_file(tcx, box_def);
        let box_id = tcx.stable_crate_id(box_def.krate).as_u64();
        let box_svh = tcx.crate_hash(box_def.krate).as_u128();
        let make_metadata = |id, svh, file| {
            Metadata::load([MetadataInput {
                stable_crate_id: id,
                svh,
                file,
            }])
            .unwrap()
        };
        let actual = make_metadata(box_id, box_svh, box_file.clone());
        let binding = capture_box(tcx, &driver, &actual).unwrap().unwrap();
        assert_eq!(binding.key(), declaration_native::key(tcx, box_def));
        assert_eq!(binding.svh(), box_svh);
        assert_eq!(binding.artifact(), box_file.sha256);
        assert_eq!(binding.path(), box_file.path.as_path());
        let requirement = declaration_wf::BuiltinRequirement {
            role: declaration_wf::BuiltinRole::OwnedBox,
            definition: binding.key(),
            crate_svh: box_svh,
        };
        assert!(binding.covers(&requirement));
        for wrong in [
            declaration_wf::BuiltinRequirement {
                role: declaration_wf::BuiltinRole::NaturalNumber,
                ..requirement.clone()
            },
            declaration_wf::BuiltinRequirement {
                crate_svh: box_svh ^ 1,
                ..requirement.clone()
            },
            declaration_wf::BuiltinRequirement {
                definition: NativeKey {
                    def_path_hash: binding.key().def_path_hash ^ 1,
                    ..binding.key()
                },
                ..requirement.clone()
            },
        ] {
            assert!(!binding.covers(&wrong));
        }

        // Actual CStore lookup must use the native CID/SVH/path, not just the
        // genuine bytes of one approved file under a different identity.
        let wrong_id = make_metadata(box_id ^ 1, box_svh, box_file.clone());
        assert!(capture_box(tcx, &driver, &wrong_id).is_err());
        let wrong_svh = make_metadata(box_id, box_svh ^ 1, box_file.clone());
        assert!(capture_box(tcx, &driver, &wrong_svh).is_err());
        let copied = self.root.join("copied-native-metadata");
        std::fs::copy(&box_file.path, &copied).unwrap();
        let copied = pin(copied);
        assert_eq!(copied.sha256, box_file.sha256);
        let wrong_path = make_metadata(box_id, box_svh, copied);
        assert!(capture_box(tcx, &driver, &wrong_path).is_err());

        let natural_candidate = match scalar_definition(tcx, ScalarKind::Natural) {
            Ok(Some(_)) => "foreign-diagnostic-only",
            Ok(None) => "missing",
            Err(_) => "refused-local-or-shape",
        };
        let bytes = std::fs::read(&self.source).unwrap();
        let source_pin = pin(self.source.clone());
        let manifest = self.root.join("manifest.json");
        std::fs::write(&manifest, serde_json::to_vec(&json!({
            "git_commit": "native-meaning-negative-control", "archive_sha256": "00".repeat(32),
            "files_sha256": {"control.rs": source_pin.sha256.iter().map(|b|format!("{b:02x}")).collect::<String>()},
            "symlink_targets": {}
        })).unwrap()).unwrap();
        assert_eq!(source_pin.read().unwrap(), bytes);
        let sources = Sources::load(self.source.parent().unwrap(), pin(manifest), None).unwrap();
        let mut common_files = BTreeMap::new();
        let mut metadata_inputs = Vec::new();
        for krate in tcx.crates(()) {
            let source = tcx.used_crate_source(*krate);
            let file = pin(source
                .rmeta
                .as_ref()
                .or(source.rlib.as_ref())
                .or(source.dylib.as_ref())
                .unwrap()
                .to_path_buf());
            common_files.insert(file.path.clone(), file.clone());
            metadata_inputs.push(MetadataInput {
                stable_crate_id: tcx.stable_crate_id(*krate).as_u64(),
                svh: tcx.crate_hash(*krate).as_u128(),
                file,
            });
        }
        let metadata = Metadata::load(metadata_inputs).unwrap();
        let inputs = Inputs {
            sources,
            common_files,
            builtin: box_file,
            macros: vec![],
            output: self.root.join("unused-output"),
            producer_sha256: super::super::inputs::digest(&std::env::current_exe().unwrap())
                .unwrap(),
            compiler_driver: driver,
            build_origin: None,
        };
        let meanings = capture(tcx, &inputs, &metadata).unwrap();
        meanings.revalidate(tcx, &inputs, &metadata).unwrap();
        let matched = meanings.for_context(tcx, &inputs, &metadata).unwrap();
        assert!(matched.owned_box(tcx).is_some());
        assert!(
            meanings.scalars.is_empty(),
            "no fresh build can never mint scalar permission"
        );
        assert!(meanings.owned_box().is_some());
        if let Some(definition) =
            tcx.get_diagnostic_item(Symbol::intern(ScalarKind::Natural.diagnostic()))
        {
            assert!(meanings
                .get(declaration_native::key(tcx, definition))
                .is_none());
            assert!(matched
                .get(tcx, declaration_native::key(tcx, definition))
                .is_none());
        }
        let mut result = meanings.observation();
        result["candidate_status"] = json!(natural_candidate);
        result["actual_native_box_selection"] = json!(true);
        result["wrong_cid_svh_and_copied_path_refused"] = json!(true);
        self.result = Some(result);
        Compilation::Stop
    }
}

fn native(source: &str, foreign: bool) -> Value {
    let root = Temp(std::env::temp_dir().join(format!(
        "trust-vc-native-meaning-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&root.0).unwrap();
    let source_root = root.0.join("source");
    std::fs::create_dir(&source_root).unwrap();
    let path = source_root.join("control.rs");
    std::fs::write(
        &path,
        format!(
            r#"#![feature(rustc_attrs)]
#![allow(dead_code, non_camel_case_types, internal_features)]
pub fn uses_box(_value: Box<bool>) {{}}
{source}
"#
        ),
    )
    .unwrap();
    let mut argv = arguments(&path, &root.0, "native_meaning_control");
    if foreign {
        let fake = root.0.join("foreign.rs");
        std::fs::write(
            &fake,
            r#"#![feature(rustc_attrs)]
#![allow(internal_features)]
#[rustc_diagnostic_item = "verus::verus_builtin::nat"] pub struct Counterfeit;
"#,
        )
        .unwrap();
        let args = arguments(&fake, &root.0, "untrusted_math_fixture");
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&args, &mut Emit)).unwrap();
        argv.extend([
            "--extern".into(),
            format!(
                "untrusted_math_fixture={}",
                root.0.join("libuntrusted_math_fixture.rmeta").display()
            ),
        ]);
    }
    let mut capture = Inspect {
        root: root.0.clone(),
        source: path,
        result: None,
    };
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&argv, &mut capture)).unwrap();
    let result = capture.result.expect("actual native analysis callback ran");
    assert_eq!(result["scalars"], json!([]));
    assert_eq!(result["import_authorized"], false);
    assert_eq!(result["constructor_or_ownership_authority"], false);
    result
}

#[test]
fn same_spelling_never_selects_scalar_meaning() {
    let result = native("pub struct nat;", false);
    assert_eq!(result["candidate_status"], "missing");
}

#[test]
fn a_local_diagnostic_item_cannot_supply_foreign_scalar_meaning() {
    let result = native(
        r#"#[rustc_diagnostic_item = "verus::verus_builtin::nat"] pub struct Impostor;"#,
        false,
    );
    assert_eq!(result["candidate_status"], "refused-local-or-shape");
}

#[test]
fn foreign_diagnostic_metadata_without_a_fresh_build_cannot_supply_scalar_meaning() {
    let result = native(
        "pub fn use_foreign(_value: untrusted_math_fixture::Counterfeit) {}",
        true,
    );
    assert_eq!(result["candidate_status"], "foreign-diagnostic-only");
    assert_eq!(result["actual_native_box_selection"], true);
    assert_eq!(result["wrong_cid_svh_and_copied_path_refused"], true);
}
