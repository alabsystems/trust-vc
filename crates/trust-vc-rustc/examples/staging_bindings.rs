//! Check an explicitly pinned staging input cohort using the library API.
//! This example reports byte bindings only, never import or proof authority.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

// The native hash implementation links the compiler through this binary.
#![feature(rustc_private)]

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::path::{Path, PathBuf};

use serde_json::{json, Value};
use trust_vc_rustc::declaration_alignment::observation::ObservedAnchor;
use trust_vc_rustc::declaration_alignment::source_bindings::{
    CompatibilityInput, Metadata, MetadataInput, PinnedFile, Sources,
};

type Result<T> = std::result::Result<T, Box<dyn Error>>;

fn string<'a>(value: &'a Value, field: &str) -> Result<&'a str> {
    value[field]
        .as_str()
        .ok_or_else(|| format!("missing {field}").into())
}

fn hexadecimal(value: &str, width: usize) -> Result<u128> {
    if value.len() != width || !value.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("invalid native hexadecimal identity".into());
    }
    Ok(u128::from_str_radix(value, 16)?)
}

fn pinned(value: &Value) -> Result<PinnedFile> {
    let text = string(value, "sha256")?;
    if text.len() != 64 || !text.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("invalid SHA256 pin".into());
    }
    let bytes = text
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|part| u8::from_str_radix(std::str::from_utf8(part)?, 16).map_err(Into::into))
        .collect::<Result<Vec<_>>>()?;
    Ok(PinnedFile {
        path: PathBuf::from(string(value, "path")?),
        sha256: bytes.try_into().map_err(|_| "wrong digest length")?,
    })
}

fn anchors(value: &Value, output: &mut BTreeSet<ObservedAnchor>, depth: usize) -> Result<()> {
    if depth > 256 {
        return Err("observation nesting exceeded its bound".into());
    }
    match value {
        Value::Object(fields) => {
            if value["state"] == "ObservedRealSourceAnchor" {
                let index = |name: &str| -> Result<u32> {
                    Ok(u32::try_from(
                        value[name].as_u64().ok_or("missing source coordinate")?,
                    )?)
                };
                output.insert(ObservedAnchor {
                    local_path: string(value, "local_path")?.into(),
                    compiler_source_hash: string(value, "compiler_source_hash")?.into(),
                    original_file_len: index("original_file_len")?,
                    bytes: (index("original_lo")?, index("original_hi")?),
                });
            }
            for child in fields.values() {
                anchors(child, output, depth + 1)?;
            }
        }
        Value::Array(values) => {
            for child in values {
                anchors(child, output, depth + 1)?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn main() -> Result<()> {
    let path = std::env::args_os()
        .nth(1)
        .ok_or("expected staging input JSON path")?;
    let input: Value = serde_json::from_slice(&std::fs::read(path)?)?;
    if input["schema"] != "trust-vc.byte-binding-input@1" {
        return Err("unsupported input schema".into());
    }
    let compatibility = input
        .get("compatibility")
        .map(|v| -> Result<_> {
            Ok(CompatibilityInput {
                recipe: pinned(&v["recipe"])?,
                patch: pinned(&v["patch"])?,
            })
        })
        .transpose()?;
    let sources = Sources::load(
        Path::new(string(&input, "source_root")?),
        pinned(&input["manifest"])?,
        compatibility,
    )?;
    let emitted = input
        .get("emitted_manifest")
        .map(|value| -> Result<Sources> {
            Ok(Sources::load(
                Path::new(string(&input, "source_root")?),
                pinned(value)?,
                None,
            )?)
        })
        .transpose()?;
    let target = input
        .get("target_metadata")
        .map(|row| -> Result<_> {
            let id = u64::try_from(hexadecimal(string(row, "stable_crate_id")?, 16)?)?;
            let svh = hexadecimal(string(row, "svh")?, 32)?;
            Ok((
                id,
                Metadata::load([MetadataInput {
                    stable_crate_id: id,
                    svh,
                    file: pinned(&row["file"])?,
                }])?,
            ))
        })
        .transpose()?;
    let selected = input["metadata"]
        .as_array()
        .ok_or("missing selected metadata")?
        .iter()
        .map(|row| -> Result<_> {
            Ok(MetadataInput {
                stable_crate_id: u64::try_from(hexadecimal(string(row, "stable_crate_id")?, 16)?)?,
                svh: hexadecimal(string(row, "svh")?, 32)?,
                file: pinned(&row["file"])?,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    let metadata_files = selected.len();
    let expected_ids = selected
        .iter()
        .map(|row| row.stable_crate_id)
        .collect::<BTreeSet<_>>();
    if expected_ids.is_empty()
        || target
            .as_ref()
            .is_some_and(|(id, _)| expected_ids.contains(id))
    {
        return Err("common metadata must be nonempty and exclude the target".into());
    }
    let metadata = Metadata::load(selected)?;
    let mut coordinates = BTreeSet::new();
    let mut metadata_selections = 0;
    let mut target_selections = 0;
    let observations = input["observations"]
        .as_array()
        .filter(|rows| !rows.is_empty())
        .ok_or("missing observations")?;
    for observation in observations {
        let value: Value = serde_json::from_slice(&pinned(&observation["file"])?.read()?)?;
        anchors(&value, &mut coordinates, 0)?;
        let skip = observation
            .get("target_crate_id")
            .map(|id| -> Result<_> {
                Ok(u64::try_from(hexadecimal(
                    id.as_str().ok_or("invalid target ID")?,
                    16,
                )?)?)
            })
            .transpose()?;
        let mut seen = BTreeSet::new();
        for row in value["loaded_crates"]
            .as_array()
            .ok_or("missing actual loaded metadata")?
        {
            let id = u64::try_from(hexadecimal(string(row, "stable_crate_id")?, 16)?)?;
            if !seen.insert(id) {
                return Err("duplicate actual loaded metadata identity".into());
            }
            // The native CStore reports the selected metadata-bearing source;
            // prefer separate metadata, then an archive or dynamic artifact.
            let path = ["rmeta", "rlib", "dylib", "sdylib_interface"]
                .iter()
                .find_map(|kind| row["sources"][*kind].as_str())
                .ok_or("loaded crate has no metadata source")?;
            let svh = hexadecimal(string(row, "svh")?, 32)?;
            if Some(id) == skip {
                let (target_id, target_metadata) =
                    target.as_ref().ok_or("unbound target metadata exclusion")?;
                if *target_id != id {
                    return Err("target metadata identity differs".into());
                }
                target_metadata.selected(id, svh, Path::new(path))?;
                target_selections += 1;
                continue;
            }
            metadata.selected(id, svh, Path::new(path))?;
            metadata_selections += 1;
        }
        if let Some(id) = skip {
            if !seen.remove(&id) {
                return Err("declared target is absent from actual loaded metadata".into());
            }
        }
        if seen != expected_ids {
            return Err("actual common metadata inventory differs from the approved cohort".into());
        }
    }
    if target.is_some() && target_selections == 0 {
        return Err("target metadata was not selected by any observation".into());
    }
    let mut bound = 0;
    let mut unknown = 0;
    let mut unknown_reasons = BTreeMap::new();
    for anchor in &coordinates {
        match sources.anchor(anchor) {
            Ok(value) => {
                if let Some(emitted) = &emitted {
                    if emitted.anchor(anchor)? != value {
                        return Err("original and emitted source views differ".into());
                    }
                }
                bound += 1;
            }
            Err(reason) => {
                unknown += 1;
                *unknown_reasons.entry(reason).or_insert(0_usize) += 1;
            }
        }
    }
    if bound == 0 {
        return Err("no observed source anchor bound to the approved source graph".into());
    }
    sources.revalidate()?;
    metadata.revalidate()?;
    if let Some(emitted) = &emitted {
        emitted.revalidate()?;
    }
    if let Some((_, target)) = &target {
        target.revalidate()?;
    }
    println!(
        "{}",
        json!({"schema": "trust-vc.byte-binding-report@1",
        "source_files": sources.file_count(), "unique_source_anchors": coordinates.len(),
        "bound_source_anchors": bound, "unbound_source_anchors": unknown,
        "unbound_source_anchors_by_reason": unknown_reasons,
        "selected_metadata_files": metadata_files, "actual_metadata_selections_checked": metadata_selections,
        "actual_target_metadata_selections_checked": target_selections,
        "authority": "checked byte bindings only; native identities remain observations",
        "import_authorized": false, "verified_functions": null})
    );
    Ok(())
}
