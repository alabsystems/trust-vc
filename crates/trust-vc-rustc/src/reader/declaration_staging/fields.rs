//! Bind conditional field-language facts to the same nominal WF/source cohort.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

enum MappingOrigin {
    NativeCompiler(alignment::Digest),
    FreshBuiltin(super::build_origin::BuiltArtifact),
    Unknown,
}

pub(super) struct MappingSelection {
    proxy: NativeKey,
    target: NativeKey,
    svh: u128,
    artifact: alignment::Digest,
    origin: MappingOrigin,
}

impl MappingSelection {
    pub(super) fn observation(&self) -> Value {
        json!({"proxy": self.proxy.def_path_hash.to_string(),
            "target": self.target.def_path_hash.to_string(), "svh": self.svh.to_string(),
            "selected_artifact_sha256": self.artifact,
            "selected_build_origin": match &self.origin {
                MappingOrigin::NativeCompiler(driver) => json!({"state": "NativeCompilerSysroot",
                    "compiler_driver_sha256": driver}),
                MappingOrigin::FreshBuiltin(artifact) => artifact.observation(),
                MappingOrigin::Unknown => json!({"state": "Unknown"}),
            }, "import_authorized": false})
    }
}

fn exact_inventory(owner: NativeKey, wf: &[NativeKey], fields: &[NativeKey]) -> Result<(), String> {
    let expected = wf.iter().copied().collect::<BTreeSet<_>>();
    let actual = fields.iter().copied().collect::<BTreeSet<_>>();
    if expected.len() != wf.len()
        || actual.len() != fields.len()
        || !expected.contains(&owner)
        || actual != expected
    {
        return Err(
            "field and WF checked-local inventories differ, duplicate or omit the owner".into(),
        );
    }
    Ok(())
}

pub(super) fn bind<'tcx>(
    tcx: TyCtxt<'tcx>,
    policy: &declaration_policy::OwnedPolicy,
    wf: &declaration_wf::OwnedWf,
    fields: &declaration_fields::OwnedFields,
    owners: &BTreeMap<NativeKey, rustc_hir::def_id::LocalDefId>,
    inputs: &Inputs,
    metadata: &Metadata,
) -> Result<Vec<MappingSelection>, String> {
    if policy.owner() != wf.owner() || fields.owner() != wf.owner() || policy.nominal().is_none() {
        return Err(
            "native policy, field and WF facts do not belong to the same nominal owner".into(),
        );
    }
    exact_inventory(
        wf.owner(),
        wf.local_declarations(),
        fields.local_declarations(),
    )?;
    for local in fields.local_declarations().iter().copied().chain(
        fields
            .external_mappings()
            .iter()
            .map(|mapping| mapping.proxy),
    ) {
        let owner = owners
            .get(&local)
            .ok_or("a field dependency/proxy has no original local owner")?;
        let native = declaration_native::capture(
            tcx,
            owner.to_def_id(),
            LOCAL_CRATE,
            &inputs.sources,
            metadata,
        );
        if native.key != local || !matches!(native.source, Observation::Observed(_)) {
            return Err("a field dependency/proxy has a different native key or lacks approved source-byte anchors".into());
        }
    }
    let mut selections = Vec::new();
    let mut seen = BTreeSet::new();
    for mapping in fields.external_mappings() {
        if !seen.insert((mapping.proxy, mapping.target)) {
            return Err("external type mapping is duplicated".into());
        }
        let mut matching =
            tcx.crates(()).iter().copied().filter(|krate| {
                tcx.stable_crate_id(*krate).as_u64() == mapping.target.stable_crate_id
            });
        let krate = matching
            .next()
            .ok_or("an external type mapping target is not loaded")?;
        if matching.next().is_some() || tcx.crate_hash(krate).as_u128() != mapping.target_svh {
            return Err(
                "an external type mapping target has ambiguous or changed native metadata".into(),
            );
        }
        let native = tcx.used_crate_source(krate);
        let path = native
            .rmeta
            .as_ref()
            .or(native.rlib.as_ref())
            .or(native.dylib.as_ref())
            .ok_or("an external mapping target has no actual selected metadata")?
            .canonicalize()
            .map_err(|e| e.to_string())?;
        let artifact =
            metadata.selected(mapping.target.stable_crate_id, mapping.target_svh, &path)?;
        let sysroot = Path::new(env!("VC_SHIM_COMPILER_SYSROOT"))
            .canonicalize()
            .map_err(|e| e.to_string())?;
        let origin = if path.starts_with(sysroot) {
            inputs.compiler_driver.read()?;
            if identity::loaded_driver_path()? != inputs.compiler_driver.path {
                return Err("external mapping uses a different actual compiler image".into());
            }
            MappingOrigin::NativeCompiler(inputs.compiler_driver.sha256)
        } else if let Some(cohort) = &inputs.build_origin {
            MappingOrigin::FreshBuiltin(cohort.selected(&inputs.sources, &path, artifact)?)
        } else {
            MappingOrigin::Unknown
        };
        selections.push(MappingSelection {
            proxy: mapping.proxy,
            target: mapping.target,
            svh: mapping.target_svh,
            artifact,
            origin,
        });
    }
    Ok(selections)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn key(index: u128) -> NativeKey {
        NativeKey {
            stable_crate_id: 1,
            def_path_hash: index,
        }
    }
    #[test]
    fn nominal_field_join_requires_complete_unique_checked_local_inventory() {
        let a = key(1);
        let b = key(2);
        let c = key(3);
        assert!(exact_inventory(a, &[a, b], &[b, a]).is_ok());
        for other in [vec![a], vec![a, c], vec![a, b, b], vec![b]] {
            assert!(exact_inventory(a, &[a, b], &other).is_err());
        }
        assert!(exact_inventory(a, &[a, a], &[a]).is_err());
        assert!(exact_inventory(a, &[b], &[b]).is_err());
    }
}
