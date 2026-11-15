//! Byte inputs and a closed compiler recipe for native declaration staging.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use serde_json::Value;
use sha2::{Digest as _, Sha256};

use crate::declaration_alignment::source_bindings::{
    CompatibilityInput, PinnedFile, SourceCompatibility, SourceIdentity, Sources,
};
use crate::declaration_alignment::Digest;

pub(super) struct Inputs {
    pub(super) sources: Sources,
    pub(super) common_files: BTreeMap<PathBuf, PinnedFile>,
    pub(super) builtin: PinnedFile,
    pub(super) macros: Vec<PinnedFile>,
    pub(super) output: PathBuf,
    pub(super) producer_sha256: Digest,
    pub(super) compiler_driver: PinnedFile,
    pub(super) build_origin: Option<super::build_origin::BuiltCohort>,
}

pub(super) fn canonical_output(requested: &Path, source: &Path) -> Result<PathBuf, String> {
    if !requested.is_absolute() {
        return Err("staging output must be absolute".into());
    }
    let name = requested
        .file_name()
        .ok_or("staging output needs a fresh basename")?;
    let parent = requested
        .parent()
        .ok_or("staging output has no parent")?
        .canonicalize()
        .map_err(|e| e.to_string())?;
    if !parent.is_dir() {
        return Err("staging output parent is not a directory".into());
    }
    let output = parent.join(name);
    match std::fs::symlink_metadata(&output) {
        Ok(_) => return Err("staging output already exists, including a dangling symlink".into()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(error.to_string()),
    }
    if output.starts_with(source) {
        return Err("staging output would modify the canonical approved source graph".into());
    }
    Ok(output)
}

pub(super) fn digest(path: &Path) -> Result<Digest, String> {
    Ok(Sha256::digest(std::fs::read(path).map_err(|e| e.to_string())?).into())
}

fn text<'a>(value: &'a Value, key: &str) -> Result<&'a str, String> {
    value[key].as_str().ok_or_else(|| format!("missing {key}"))
}

fn sha(value: &str) -> Result<Digest, String> {
    if value.len() != 64 || !value.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("invalid SHA256 pin".into());
    }
    let mut bytes = [0; 32];
    for (out, pair) in bytes.iter_mut().zip(value.as_bytes().as_chunks::<2>().0) {
        *out = u8::from_str_radix(std::str::from_utf8(pair).map_err(|e| e.to_string())?, 16)
            .map_err(|e| e.to_string())?;
    }
    Ok(bytes)
}

fn pinned(value: &Value) -> Result<PinnedFile, String> {
    let file = PinnedFile {
        path: PathBuf::from(text(value, "path")?),
        sha256: sha(text(value, "sha256")?)?,
    };
    file.read()?;
    Ok(PinnedFile {
        path: file.path.canonicalize().map_err(|e| e.to_string())?,
        ..file
    })
}

impl Inputs {
    pub(super) fn load(path: &Path) -> Result<Self, String> {
        let value: Value = serde_json::from_slice(&std::fs::read(path).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
        let object = value.as_object().ok_or("staging input must be an object")?;
        let fresh_build = value["schema"] == "trust-vc.native-declaration-staging-request@2";
        if (!fresh_build && value["schema"] != "trust-vc.native-declaration-staging-request@1")
            || object.keys().any(|key| {
                !matches!(
                    key.as_str(),
                    "schema"
                        | "source_root"
                        | "manifest"
                        | "compatibility"
                        | "common_metadata"
                        | "builtin"
                        | "macros"
                        | "registry_archives"
                        | "output"
                )
            })
            || (fresh_build && (object.contains_key("builtin") || object.contains_key("macros")))
            || (!fresh_build && object.contains_key("registry_archives"))
        {
            return Err("unsupported staging request or authority-bearing input fields".into());
        }
        let compatibility = &value["compatibility"];
        let sources = Sources::load(
            Path::new(text(&value, "source_root")?),
            pinned(&value["manifest"])?,
            Some(CompatibilityInput {
                recipe: pinned(&compatibility["recipe"])?,
                patch: pinned(&compatibility["patch"])?,
            }),
        )?;
        let identity = sources.identity();
        // This recipe admits the actual pinned source, with its reviewed
        // compatibility change. Paths and user-supplied source labels cannot
        // select another library while retaining this source identity.
        let expected_source = SourceIdentity {
            manifest_sha256: sha(
                "dab8d7c7732d498ce4fc80dce93cbd073488338c2b0e3e6d3a2c231634940187",
            )?,
            compatibility: SourceCompatibility::Applied {
                recipe_sha256: sha(
                    "8c76b07b40c8013f7f05db2966d239e9f9e99ee87092513881c4397b2b17fbb9",
                )?,
                patch_sha256: sha(
                    "67c3ec8d35127f98536fc0272109557b567405c0ad9ca0db90bdbb035b11b522",
                )?,
            },
        };
        if identity != expected_source {
            return Err(
                "the source/compatibility inputs are outside the native staging recipe".into(),
            );
        }
        let mut common_files = BTreeMap::new();
        for row in value["common_metadata"]
            .as_array()
            .ok_or("missing common metadata byte pins")?
        {
            let file = pinned(row)?;
            if common_files.insert(file.path.clone(), file).is_some() {
                return Err("duplicate canonical common metadata path".into());
            }
        }
        let output = canonical_output(Path::new(text(&value, "output")?), sources.root())?;
        let compiler_driver = super::identity::loaded_driver()?;
        let build_origin = if fresh_build {
            let sysroot = Path::new(env!("VC_SHIM_COMPILER_SYSROOT"))
                .canonicalize()
                .map_err(|e| e.to_string())?;
            if common_files
                .values()
                .any(|file| !file.path.starts_with(&sysroot))
            {
                return Err(
                    "fresh construction only accepts native sysroot metadata as common byte inputs"
                        .into(),
                );
            }
            let archives = value["registry_archives"]
                .as_array()
                .ok_or("fresh construction needs the exact locked registry archives")?
                .iter()
                .map(pinned)
                .collect::<Result<Vec<_>, _>>()?;
            let basename = output
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or("fresh staging output has no represented basename")?;
            let builtins = output.with_file_name(format!("{basename}-builtins"));
            Some(super::build_origin::build(
                &sources,
                &archives,
                &builtins,
                &compiler_driver,
            )?)
        } else {
            None
        };
        let (builtin, macros) = if let Some(cohort) = &build_origin {
            let builtin = cohort.artifact("libverus_builtin.rlib")?;
            let macros = [
                "libverus_builtin_macros.dylib",
                "libverus_state_machines_macros.dylib",
            ]
            .into_iter()
            .map(|name| cohort.artifact(name))
            .collect::<Result<Vec<_>, _>>()?;
            for file in [&builtin].into_iter().chain(&macros) {
                if common_files
                    .insert(file.path.clone(), file.clone())
                    .is_some()
                {
                    return Err(
                        "fresh builtin output duplicates a common metadata selection".into(),
                    );
                }
            }
            (builtin, macros)
        } else {
            let builtin = pinned(&value["builtin"])?;
            let macros = value["macros"]
                .as_array()
                .ok_or("missing genuine macro byte pins")?
                .iter()
                .map(pinned)
                .collect::<Result<Vec<_>, _>>()?;
            (builtin, macros)
        };
        let macro_names = macros
            .iter()
            .filter_map(|file| file.path.file_name().and_then(|name| name.to_str()))
            .collect::<BTreeSet<_>>();
        if common_files.is_empty()
            || macros.len() != 2
            || macro_names
                != BTreeSet::from([
                    "libverus_builtin_macros.dylib",
                    "libverus_state_machines_macros.dylib",
                ])
            || builtin.path.file_name().and_then(|name| name.to_str())
                != Some("libverus_builtin.rlib")
            || [&builtin].into_iter().chain(&macros).any(|file| {
                common_files
                    .get(&file.path)
                    .is_none_or(|pin| pin.sha256 != file.sha256)
            })
        {
            return Err(
                "the closed recipe requires the exact three selected builtin artifacts".into(),
            );
        }
        let producer_sha256 = digest(&std::env::current_exe().map_err(|e| e.to_string())?)?;
        Ok(Self {
            sources,
            common_files,
            builtin,
            macros,
            output,
            producer_sha256,
            compiler_driver,
            build_origin,
        })
    }

    pub(super) fn revalidate(&self) -> Result<(), String> {
        self.sources.revalidate()?;
        if let Some(cohort) = &self.build_origin {
            cohort.revalidate(&self.sources)?;
        }
        self.compiler_driver.read()?;
        if super::identity::loaded_driver_path()? != self.compiler_driver.path {
            return Err("the loaded native compiler driver changed".into());
        }
        for file in self.common_files.values() {
            file.read()?;
        }
        if digest(&std::env::current_exe().map_err(|e| e.to_string())?)? != self.producer_sha256 {
            return Err("the staging executable bytes changed".into());
        }
        Ok(())
    }

    pub(super) fn library_args(&self, keep: bool) -> Vec<String> {
        let mut args = self.base("vstd");
        if keep {
            args.extend(["--cfg".into(), "verus_keep_ghost_body".into()]);
        }
        args.push(
            self.sources
                .root()
                .join("source/vstd/vstd.rs")
                .display()
                .to_string(),
        );
        args
    }

    pub(super) fn client_args(&self, metadata: &Path, client: &Path) -> Vec<String> {
        let mut args = self.base("trust_vc_staged_metadata_client");
        args.extend([
            "--extern".into(),
            format!("vstd={}", metadata.display()),
            client.display().to_string(),
        ]);
        args
    }

    fn base(&self, name: &str) -> Vec<String> {
        let mut args = vec![
            "trust-vc-native-declaration-stage".into(),
            "-Ztrust-verify=off".into(),
            "-Cdebuginfo=0".into(),
            "--edition=2021".into(),
            "--crate-type=rlib".into(),
            format!("--crate-name={name}"),
            "--emit=metadata".into(),
            "--sysroot".into(),
            env!("VC_SHIM_COMPILER_SYSROOT").into(),
        ];
        let directories = self
            .common_files
            .keys()
            .filter_map(|file| file.parent())
            .collect::<BTreeSet<_>>();
        for directory in directories {
            args.extend(["-L".into(), format!("dependency={}", directory.display())]);
        }
        for cfg in [
            "proc_macro_span",
            "verus_keep_ghost",
            "span_locations",
            "procmacro2_semver_exempt",
            "verus_only",
            "feature=\"std\"",
            "feature=\"alloc\"",
        ] {
            args.extend(["--cfg".into(), cfg.into()]);
        }
        for attr in [
            "allow(internal_features)",
            "feature(stmt_expr_attributes)",
            "feature(negative_impls)",
            "feature(rustc_attrs)",
            "feature(unboxed_closures)",
            "feature(register_tool)",
            "feature(tuple_trait)",
            "feature(custom_inner_attributes)",
            "feature(try_trait_v2)",
            "register_tool(verus)",
            "register_tool(verifier)",
            "register_tool(verusfmt)",
        ] {
            args.push(format!("-Zcrate-attr={attr}"));
        }
        args.extend([
            "--extern".into(),
            format!("verus_builtin={}", self.builtin.path.display()),
        ]);
        for file in &self.macros {
            let name = if file.path.file_name().and_then(|name| name.to_str())
                == Some("libverus_builtin_macros.dylib")
            {
                "verus_builtin_macros"
            } else {
                "verus_state_machines_macros"
            };
            args.extend(["--extern".into(), format!("{name}={}", file.path.display())]);
        }
        args
    }
}
