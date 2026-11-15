//! Match conditional WF language requirements to actual selected metadata.
//!
//! This is a byte/definition binding, not proof of how a macro was built.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;
use serde_json::{json, Value};

use super::super::{declaration_native, declaration_wf};
use super::inputs::Inputs;
use crate::declaration_alignment::source_bindings::Metadata;
use crate::declaration_alignment::{Digest, NativeKey};

pub(super) struct Selection {
    role: declaration_wf::BuiltinRole,
    key: NativeKey,
    svh: u128,
    artifact: Digest,
    build: Option<super::build_origin::BuiltArtifact>,
}

pub(super) enum WfMeaning<'facts> {
    FreshBuiltin(&'facts super::build_origin::BuiltArtifact),
    NativeCompiler(&'facts super::meaning::OwnedBoxBinding),
}

impl Selection {
    pub(super) fn for_requirement<'facts, 'tcx>(
        &'facts self,
        requirement: &declaration_wf::BuiltinRequirement,
        tcx: TyCtxt<'tcx>,
        meanings: &'facts super::meaning::MatchedBindings<'_, 'tcx>,
    ) -> Result<WfMeaning<'facts>, String> {
        if self.role != requirement.role
            || self.key != requirement.definition
            || self.svh != requirement.crate_svh
        {
            return Err("the retained builtin selection belongs to another WF requirement".into());
        }
        if self.role == declaration_wf::BuiltinRole::OwnedBox {
            let native = meanings
                .owned_box(tcx)
                .filter(|native| native.covers(requirement) && native.artifact() == self.artifact)
                .ok_or("the WF Box selection lacks its actual native compiler meaning token")?;
            Ok(WfMeaning::NativeCompiler(native))
        } else {
            self.build
                .as_ref()
                .map(WfMeaning::FreshBuiltin)
                .ok_or_else(|| "the WF builtin selection lacks its fresh construction token".into())
        }
    }

    pub(super) fn observation(&self) -> Value {
        json!({"role": format!("{:?}", self.role),
            "native_key": self.key.def_path_hash.to_string(), "svh": self.svh.to_string(),
            "artifact_sha256": self.artifact,
            "build_authentication": self.build.as_ref().map(|built| built.observation())
                .unwrap_or_else(|| json!({"state": "Unknown", "reason":
                    "this selection has no fresh builtin construction token"}))})
    }
}

pub(super) fn bind(
    tcx: TyCtxt<'_>,
    inputs: &Inputs,
    metadata: &Metadata,
    requirements: &[declaration_wf::BuiltinRequirement],
) -> Result<Vec<Selection>, String> {
    let mut selections = Vec::new();
    for requirement in requirements {
        let def = match requirement.role {
            declaration_wf::BuiltinRole::OwnedBox => tcx.lang_items().owned_box(),
            role => {
                let name = match role {
                    declaration_wf::BuiltinRole::SpecFunction => "verus::verus_builtin::FnSpec",
                    declaration_wf::BuiltinRole::MathematicalInteger => "verus::verus_builtin::int",
                    declaration_wf::BuiltinRole::NaturalNumber => "verus::verus_builtin::nat",
                    declaration_wf::BuiltinRole::OwnedBox => {
                        return Err("unexpected builtin role".into())
                    }
                };
                tcx.get_diagnostic_item(Symbol::intern(name))
            }
        }
        .ok_or("the WF requirement has no current native language definition")?;
        if def.is_local()
            || declaration_native::key(tcx, def) != requirement.definition
            || tcx.crate_hash(def.krate).as_u128() != requirement.crate_svh
        {
            return Err("the WF builtin native definition/SVH changed".into());
        }
        let source = tcx.used_crate_source(def.krate);
        let path = source
            .rmeta
            .as_ref()
            .or(source.rlib.as_ref())
            .or(source.dylib.as_ref())
            .ok_or("a WF builtin has no represented metadata selection")?
            .canonicalize()
            .map_err(|e| e.to_string())?;
        let artifact = metadata.selected(
            requirement.definition.stable_crate_id,
            requirement.crate_svh,
            &path,
        )?;
        match requirement.role {
            declaration_wf::BuiltinRole::OwnedBox => {
                let sysroot = std::path::Path::new(env!("VC_SHIM_COMPILER_SYSROOT"))
                    .canonicalize()
                    .map_err(|e| e.to_string())?;
                if !path.starts_with(sysroot) {
                    return Err(
                        "the actual Box language item is outside the native compiler sysroot"
                            .into(),
                    );
                }
            }
            _ if path != inputs.builtin.path || artifact != inputs.builtin.sha256 => {
                return Err(
                    "the WF language item is not in the exact selected builtin artifact".into(),
                )
            }
            _ => {}
        }
        let build = if requirement.role == declaration_wf::BuiltinRole::OwnedBox {
            None // The actual sysroot language item is a distinct native origin.
        } else {
            inputs
                .build_origin
                .as_ref()
                .map(|cohort| cohort.selected(&inputs.sources, &path, artifact))
                .transpose()?
        };
        selections.push(Selection {
            role: requirement.role,
            key: requirement.definition,
            svh: requirement.crate_svh,
            artifact,
            build,
        });
    }
    Ok(selections)
}
