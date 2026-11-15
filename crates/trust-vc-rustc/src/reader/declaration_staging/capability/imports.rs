//! Client-scoped declarations constructed from the complete native handoff.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;

use rustc_hir::def_id::DefId;
use trust_vc_vcir::{AdtDecl, AdtId, AdtKind, DefHash, FnDecl, FnId, FnRole, Mode, SpanId, Ty};

use super::*;

mod normal;
mod verification;
pub(crate) use normal::LiveNormalClientRead;
pub(in crate::reader::declaration_staging) use verification::PendingVerification;

pub(in crate::reader) struct ImportedNominal<'library> {
    definition: DefId,
    id: AdtId,
    name: String,
    parameters: Vec<u32>,
    policy: &'library declaration_policy::OwnedPolicy,
}

impl ImportedNominal<'_> {
    pub(in crate::reader) fn id(&self) -> AdtId {
        self.id
    }
    pub(in crate::reader) fn declaration(&self, span: SpanId) -> AdtDecl {
        AdtDecl {
            id: self.id,
            name: self.name.clone(),
            type_params: parameter_names(&self.parameters),
            span,
            kind: AdtKind::Opaque,
            variants: Vec::new(),
        }
    }
    /// Retained for native wrapper checking. It does not license construction,
    /// projection or base cases inferred from the absence of exported fields.
    pub(in crate::reader) fn recursion(&self) -> &[declaration_policy::ParameterRecursion] {
        self.policy
            .nominal()
            .map(|nominal| nominal.recursion())
            .unwrap_or(&[])
    }
    pub(in crate::reader) fn definition(&self) -> DefId {
        self.definition
    }
    pub(in crate::reader) fn policy(&self) -> &declaration_policy::OwnedPolicy {
        self.policy
    }
}

pub(in crate::reader) struct ImportedFunction {
    definition: DefId,
    id: FnId,
    name: String,
    parameters: Vec<u32>,
    inputs: Vec<Ty>,
    output: Ty,
    modes: super::super::super::modes::CallModes,
}

impl ImportedFunction {
    pub(in crate::reader) fn id(&self) -> FnId {
        self.id
    }
    pub(in crate::reader) fn definition(&self) -> DefId {
        self.definition
    }
    pub(in crate::reader) fn arity(&self) -> usize {
        self.parameters.len()
    }
    pub(in crate::reader) fn call_modes(&self) -> super::super::super::modes::CallModes {
        self.modes.clone()
    }
    pub(in crate::reader) fn declaration(&self, span: SpanId) -> FnDecl {
        use trust_vc_vcir::{Body, FnAttrs, FnKind, LocalDecl, LocalId, LocalKind};
        let mut locals = self
            .inputs
            .iter()
            .enumerate()
            .map(|(index, ty)| LocalDecl {
                name: format!("arg{index}"),
                ty: ty.clone(),
                mode: Mode::Spec,
                mutable: false,
                kind: LocalKind::Param,
                span,
            })
            .collect::<Vec<_>>();
        let ret = LocalId(self.inputs.len() as u32);
        locals.push(LocalDecl {
            name: "result".into(),
            ty: self.output.clone(),
            mode: Mode::Spec,
            mutable: false,
            kind: LocalKind::Return,
            span,
        });
        FnDecl {
            id: self.id,
            name: self.name.clone(),
            span,
            mode: Mode::Spec,
            role: FnRole::Imported,
            kind: FnKind::Function,
            type_params: parameter_names(&self.parameters),
            locals,
            params: (0..ret.0).map(LocalId).collect(),
            ret,
            requires: Vec::new(),
            ensures: Vec::new(),
            recommends: Vec::new(),
            decreases: Vec::new(),
            decreases_when: None,
            decreases_by: None,
            attrs: FnAttrs::default(),
            body: Body::None,
        }
    }
}

/// No JSON or user declaration constructs this registry. Native identities
/// are scoped to this fresh client GCTx and the actual producer is borrowed
/// until the read/verification handoff has revalidated its retained bytes.
pub(in crate::reader) struct ClientImports<'library, 'tcx> {
    frame: client::ClientFrame<'library, 'tcx>,
    library: &'library StagedLibrary,
    nominals: HashMap<DefId, ImportedNominal<'library>>,
    functions: HashMap<DefId, ImportedFunction>,
    wf_requirements: Vec<declaration_wf::BuiltinRequirement>,
    refused: Vec<(NativeKey, String)>,
}

fn hash(key: NativeKey) -> DefHash {
    DefHash::new((key.def_path_hash >> 64) as u64, key.def_path_hash as u64)
}

fn parameter_names(indices: &[u32]) -> Vec<String> {
    indices.iter().map(|index| format!("T{index}")).collect()
}

impl<'library, 'tcx> ClientImports<'library, 'tcx> {
    /// The default reader cannot mint a registry. The explicitly owned
    /// library path validates the same packet again after all reader queries.
    pub(in crate::reader) fn read(
        &self,
        tcx: TyCtxt<'tcx>,
        options: super::super::super::ReadOptions,
    ) -> Result<super::super::super::CrateRead, String> {
        let registry = super::super::super::imports::Registry::capture(tcx, self)?;
        let read = super::super::super::read_with_imports(tcx, options, Some(registry));
        self.revalidate(tcx)?;
        Ok(read)
    }

    pub(in crate::reader::declaration_staging) fn new(
        tcx: TyCtxt<'tcx>,
        argv: &[String],
        owner: &'library standalone_client::StandaloneImported<'library>,
    ) -> Result<Self, String> {
        let frame = client::ClientFrame::capture(tcx, argv, owner)?;
        let library = frame.library();
        let meanings =
            library
                .prepared
                .meanings
                .for_context(tcx, &library.inputs, frame.common())?;
        let cohort = library
            .inputs
            .build_origin
            .as_ref()
            .ok_or("declaration imports require the actual fresh builtin construction")?;
        // Revalidate each actual proc macro and builtin selection through its
        // private construction token, rather than a crate-name allowlist.
        for file in [&library.inputs.builtin]
            .into_iter()
            .chain(&library.inputs.macros)
        {
            let _origin = cohort.selected(&library.inputs.sources, &file.path, file.sha256)?;
        }
        let mut nominals = HashMap::new();
        let mut nominal_ids = BTreeMap::new();
        let mut refused = Vec::new();
        let mut wf_requirements = Vec::new();
        for key in library.prepared.nominal_policies.keys().copied() {
            let result: Result<
                (
                    ImportedNominal<'library>,
                    Vec<declaration_wf::BuiltinRequirement>,
                ),
                String,
            > = (|| {
                let facts = facts::nominal(library, key)?;
                let wf = library
                    .prepared
                    .nominal_wf
                    .get(&key)
                    .ok_or("missing nominal WF")?;
                let selections = builtins::bind(
                    tcx,
                    &library.inputs,
                    frame.common(),
                    wf.builtin_requirements(),
                )?;
                if selections.len() != wf.builtin_requirements().len() {
                    return Err("the current native WF selection inventory changed".into());
                }
                for (selection, requirement) in selections.iter().zip(wf.builtin_requirements()) {
                    let _meaning = selection.for_requirement(requirement, tcx, &meanings)?;
                }
                let fields = library
                    .prepared
                    .nominal_fields
                    .get(&key)
                    .ok_or("missing field admission")?;
                // External proxy targets require a separate current native
                // mapping join before those broader carriers are admitted.
                if !fields.external_mappings().is_empty() {
                    return Err(
                        "the current client external-type mapping join is not implemented".into(),
                    );
                }
                let (definition, _) = frame.declaration(facts.erase.key)?;
                Ok((
                    ImportedNominal {
                        definition,
                        id: AdtId(hash(facts.erase.key)),
                        name: tcx.def_path_str(definition),
                        parameters: facts.parameters,
                        policy: facts.policy,
                    },
                    wf.builtin_requirements().to_vec(),
                ))
            })();
            match result {
                Ok((nominal, requirements)) => {
                    let erase = declaration_native::key(tcx, nominal.definition);
                    if nominal_ids
                        .insert(erase, (nominal.id, nominal.parameters.len()))
                        .is_some()
                        || nominals.insert(nominal.definition, nominal).is_some()
                    {
                        return Err("licensed nominal native identities collide".into());
                    }
                    for requirement in requirements {
                        if !wf_requirements.contains(&requirement) {
                            wf_requirements.push(requirement);
                        }
                    }
                }
                Err(reason) => refused.push((key, reason)),
            }
        }
        let mut functions = HashMap::new();
        for packet in &library.prepared.functions {
            let native = &packet.native;
            let result: Result<ImportedFunction, String> = (|| {
                let (keep, erase) = facts::correspondence(library, native.keep_key())?;
                let parameters = facts::parameters(keep, &packet.policy)?;
                let (definition, actual) = frame.declaration(native.erase_key())?;
                if erase.key != actual.key
                    || native
                        .parameter_modes()
                        .iter()
                        .any(|mode| *mode != Mode::Spec)
                    || native.return_mode() != Mode::Spec
                {
                    return Err(
                        "the retained declaration has a different native key or modes".into(),
                    );
                }
                let Observation::Observed(alignment::DeclarationShape::Function {
                    origin,
                    inputs,
                    output,
                }) = &actual.shape
                else {
                    return Err("the actual function signature is Unknown".into());
                };
                if inputs.len() > 256 || native.parameter_modes().len() != inputs.len() {
                    return Err("the actual signature and checked parameter modes differ".into());
                }
                let types = lower::Types {
                    tcx,
                    meanings: &meanings,
                    nominals: &nominal_ids,
                    parameters: &parameters,
                };
                if let alignment::FunctionOrigin::Inherent { self_type } = origin {
                    let _self_type = types.lower(self_type)?;
                }
                let inputs = inputs
                    .iter()
                    .map(|ty| types.lower(ty))
                    .collect::<Result<Vec<_>, _>>()?;
                let output = types.lower(output)?;
                let modes = super::super::super::modes::CallModes {
                    mode: Mode::Spec,
                    params: native
                        .parameter_modes()
                        .iter()
                        .map(|mode| super::super::super::modes::CallParameter {
                            mode: *mode,
                            mutable_reference: false,
                        })
                        .collect(),
                    ret: native.return_mode(),
                };
                Ok(ImportedFunction {
                    definition,
                    id: FnId(hash(actual.key)),
                    name: tcx.def_path_str(definition),
                    parameters,
                    inputs,
                    output,
                    modes,
                })
            })();
            match result {
                Ok(function) => {
                    if functions.insert(function.definition, function).is_some() {
                        return Err("licensed function native identities collide".into());
                    }
                }
                Err(reason) => refused.push((native.keep_key(), reason)),
            }
        }
        diagnostics(tcx)?;
        Ok(Self {
            frame,
            library,
            nominals,
            functions,
            wf_requirements,
            refused,
        })
    }

    pub(in crate::reader) fn revalidate(&self, tcx: TyCtxt<'tcx>) -> Result<(), String> {
        self.frame.revalidate(tcx)?;
        self.library.inputs.revalidate()?;
        self.library.prepared.erase.target_metadata.revalidate()?;
        self.frame.common().revalidate()?;
        self.library.prepared.meanings.for_context(
            tcx,
            &self.library.inputs,
            self.frame.common(),
        )?;
        diagnostics(tcx)
    }

    /// A diagnostic of the actual current client match, never an input
    /// capable of reconstructing the private declaration registry.
    pub(in crate::reader::declaration_staging) fn matched_meaning_observation(
        &self,
        tcx: TyCtxt<'tcx>,
    ) -> Result<Value, String> {
        self.revalidate(tcx)?;
        let _matched = self.library.prepared.meanings.for_context(
            tcx,
            &self.library.inputs,
            self.frame.common(),
        )?;
        Ok(json!({"state": "CurrentClientNativeMeaningsMatched",
            "facts": self.library.prepared.meanings.observation(),
            "permission_from_observation": false}))
    }

    pub(in crate::reader) fn function(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: DefId,
    ) -> Option<&ImportedFunction> {
        self.frame.current(tcx).ok()?;
        self.functions.get(&definition)
    }

    pub(in crate::reader) fn nominal(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: DefId,
    ) -> Option<&ImportedNominal<'library>> {
        self.frame.current(tcx).ok()?;
        self.nominals.get(&definition)
    }

    pub(in crate::reader) fn declarations(
        &self,
        tcx: TyCtxt<'tcx>,
    ) -> Result<(Vec<&ImportedNominal<'library>>, Vec<&ImportedFunction>), String> {
        self.revalidate(tcx)?;
        let mut nominals = self.nominals.values().collect::<Vec<_>>();
        let mut functions = self.functions.values().collect::<Vec<_>>();
        nominals.sort_by_key(|nominal| nominal.id);
        functions.sort_by_key(|function| function.id);
        Ok((nominals, functions))
    }

    /// The union comes only from successfully admitted nominals whose
    /// complete requirements were matched to actual current native meanings.
    pub(in crate::reader) fn wf_requirements(
        &self,
        tcx: TyCtxt<'tcx>,
    ) -> Result<&[declaration_wf::BuiltinRequirement], String> {
        self.frame.current(tcx)?;
        Ok(&self.wf_requirements)
    }

    pub(in crate::reader::declaration_staging) fn observation(&self) -> Value {
        json!({"state": "ClientScopedDeclarationCandidates", "nominals": self.nominals.len(),
            "functions": self.functions.len(), "refused": self.refused.iter().map(|(key, reason)|
                json!({"keep_hash": key.def_path_hash.to_string(), "reason": reason})).collect::<Vec<_>>(),
            "product_import_activated": false, "body_or_private_axiom_authority": false,
            "ownership_authority": false, "imported_verified_functions": 0})
    }
}
