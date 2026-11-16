//! Reader registrations derived only from a current native library packet.
//!
//! This module has no receipt decoder or public registration constructor.
//! The ordinary reader is unchanged unless its caller owns ClientImports.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use trust_vc_vcir::{
    AdtDecl, AdtId, AdtKind, Body, FnDecl, FnId, FnRole, Mode, SpanId, Ty, VcCrate,
};

use super::declaration_staging::ClientImports;
use super::{modes, Cx, FnInfo};

pub(super) mod wrappers;

struct Nominal {
    definition: DefId,
    declaration: AdtDecl,
    policy: super::declaration_policy::OwnedPolicy,
}

struct Function {
    definition: DefId,
    declaration: FnDecl,
    modes: modes::CallModes,
    source_recommendations: bool,
}

/// This view exists only for a nominal that passed the sealed original
/// Sized, positivity/base-case and field-language checks with authenticated
/// builtin meanings. It exports policy, never foreign representation. The
/// empty Opaque variants are not evidence for any of these prerequisites.
pub(super) struct NominalPolicy<'registry> {
    nominal: &'registry Nominal,
}

impl NominalPolicy<'_> {
    pub(super) fn id(&self) -> AdtId {
        self.nominal.declaration.id
    }
    pub(super) fn definition(&self) -> DefId {
        self.nominal.definition
    }
    pub(super) fn arity(&self) -> usize {
        self.nominal.declaration.type_params.len()
    }
    /// The owner/scoped parameter keys are from the actual Keep check;
    /// definition() is its uniquely matched actual client Erase declaration.
    pub(super) fn policy(&self) -> &super::declaration_policy::OwnedPolicy {
        &self.nominal.policy
    }
    pub(super) fn recursion(&self) -> &[super::declaration_policy::ParameterRecursion] {
        self.nominal
            .policy
            .nominal()
            .map(|nominal| nominal.recursion())
            .unwrap_or(&[])
    }
}

/// No source name, DefId or structural view can construct this value. The
/// staging packet must first rematch the actual current client metadata.
pub(super) struct Registry<'tcx> {
    tcx: TyCtxt<'tcx>,
    nominals: Vec<Nominal>,
    functions: Vec<Function>,
    spec_definitions: super::declaration_staging::ClientDefinitions,
    wf_requirements: Vec<super::declaration_wf::BuiltinRequirement>,
}

impl<'tcx> Registry<'tcx> {
    pub(super) fn capture(
        tcx: TyCtxt<'tcx>,
        imports: &ClientImports<'_, 'tcx>,
    ) -> Result<Self, String> {
        let (nominals, functions) = imports.declarations(tcx)?;
        // Spans are assigned from the actual native declarations only when
        // installing into the reader's own span table.
        let nominals = nominals
            .into_iter()
            .map(|nominal| Nominal {
                definition: nominal.definition(),
                declaration: nominal.declaration(SpanId(0)),
                policy: nominal.policy().clone(),
            })
            .collect();
        let functions = functions
            .into_iter()
            .map(|function| Function {
                definition: function.definition(),
                declaration: function.declaration(SpanId(0)),
                modes: function.call_modes(),
                source_recommendations: function.source_recommendations(),
            })
            .collect();
        let wf_requirements = imports.wf_requirements(tcx)?.to_vec();
        let spec_definitions = imports.definition_packet(tcx)?;
        Ok(Self {
            tcx,
            nominals,
            functions,
            spec_definitions,
            wf_requirements,
        })
    }

    fn current(&self, tcx: TyCtxt<'tcx>) -> bool {
        std::ptr::eq(*self.tcx, *tcx) && tcx.dcx().has_errors().is_none()
    }

    /// Cost bound for a linear call-mode lookup, not declaration permission.
    pub(super) fn call_mode_lookup_work(&self) -> usize {
        self.functions.len()
    }

    pub(super) fn call_modes(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: DefId,
    ) -> Option<modes::CallModes> {
        if !self.current(tcx) {
            return None;
        }
        self.functions
            .iter()
            .find(|entry| entry.definition == definition)
            .map(|entry| entry.modes.clone())
    }

    pub(super) fn function(&self, tcx: TyCtxt<'tcx>, definition: DefId) -> Option<(FnId, usize)> {
        if !self.current(tcx) {
            return None;
        }
        self.functions
            .iter()
            .find(|entry| entry.definition == definition)
            .map(|entry| (entry.declaration.id, entry.declaration.type_params.len()))
    }

    /// A diagnostic item is only a candidate. The existing owned packet must
    /// supply this exact native definition and its entire pure signature.
    /// No sequence equations or representation follow from this projection.
    pub(super) fn seq_len(&self, tcx: TyCtxt<'tcx>, definition: DefId) -> bool {
        if !self.current(tcx) || definition.is_local() {
            return false;
        }
        let Some(entry) = self
            .functions
            .iter()
            .find(|entry| entry.definition == definition)
        else {
            return false;
        };
        let declaration = &entry.declaration;
        let ([parameter], Some(result)) = (
            declaration.params.as_slice(),
            declaration.locals.get(declaration.ret.index()),
        ) else {
            return false;
        };
        let Some(parameter) = declaration.locals.get(parameter.index()) else {
            return false;
        };
        let Ty::Adt(nominal, arguments) = &parameter.ty else {
            return false;
        };
        declaration.role == FnRole::Imported
            && declaration.mode == Mode::Spec
            && declaration.type_params.len() == 1
            && parameter.mode == Mode::Spec
            && arguments.as_slice() == [Ty::Param(0)]
            && result.mode == Mode::Spec
            && result.ty == Ty::nat()
            && matches!(declaration.body, Body::None)
            && entry.modes.mode == Mode::Spec
            && entry.modes.ret == Mode::Spec
            && !entry.modes.prophetic
            && matches!(entry.modes.params.as_slice(), [parameter] if parameter.mode == Mode::Spec && !parameter.mutable_reference)
            && self.nominals.iter().any(|entry| {
                entry.declaration.id == *nominal
                    && entry.declaration.kind == AdtKind::Opaque
                    && entry.declaration.type_params.len() == 1
            })
    }

    /// Require this exact current foreign member of the complete source
    /// family, including its separate checked recommendation packet. It
    /// remains bodyless; no sequence value or representation is supplied.
    pub(super) fn seq_index(&self, tcx: TyCtxt<'tcx>, definition: DefId) -> bool {
        if !self.current(tcx) || definition.is_local() {
            return false;
        }
        let Some(entry) = self
            .functions
            .iter()
            .find(|entry| entry.definition == definition)
        else {
            return false;
        };
        let declaration = &entry.declaration;
        let ([receiver, index], Some(result)) = (
            declaration.params.as_slice(),
            declaration.local(declaration.ret),
        ) else {
            return false;
        };
        let (Some(receiver), Some(index)) =
            (declaration.local(*receiver), declaration.local(*index))
        else {
            return false;
        };
        let Ty::Adt(nominal, arguments) = &receiver.ty else {
            return false;
        };
        entry.source_recommendations
            && self
                .spec_definitions
                .bodyless_recommendation_owner(declaration.id)
            && declaration.role == FnRole::Imported
            && declaration.mode == Mode::Spec
            && declaration.type_params.len() == 1
            && matches!(declaration.body, Body::None)
            && receiver.mode == Mode::Spec
            && arguments.as_slice() == [Ty::Param(0)]
            && index.mode == Mode::Spec
            && index.ty == Ty::int()
            && result.mode == Mode::Spec
            && result.ty == Ty::Param(0)
            && entry.modes.mode == Mode::Spec
            && entry.modes.ret == Mode::Spec
            && !entry.modes.prophetic
            && matches!(entry.modes.params.as_slice(), [receiver,index] if [receiver,index].iter().all(|parameter| parameter.mode == Mode::Spec && !parameter.mutable_reference))
            && self.nominals.iter().any(|entry| {
                entry.declaration.id == *nominal
                    && entry.declaration.kind == AdtKind::Opaque
                    && entry.declaration.type_params.len() == 1
            })
    }

    pub(super) fn nominal(&self, tcx: TyCtxt<'tcx>, definition: DefId) -> Option<AdtId> {
        if !self.current(tcx) {
            return None;
        }
        self.nominals
            .iter()
            .find(|entry| entry.definition == definition)
            .map(|entry| entry.declaration.id)
    }

    pub(super) fn nominal_policy(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: DefId,
    ) -> Option<NominalPolicy<'_>> {
        if !self.current(tcx) {
            return None;
        }
        self.nominals
            .iter()
            .find(|entry| entry.definition == definition)
            .map(|nominal| NominalPolicy { nominal })
    }

    pub(super) fn covers_wf_requirement(
        &self,
        tcx: TyCtxt<'tcx>,
        requirement: &super::declaration_wf::BuiltinRequirement,
    ) -> bool {
        self.current(tcx) && self.wf_requirements.contains(requirement)
    }

    pub(super) fn install(&self, cx: &mut Cx<'tcx>, krate: &mut VcCrate) -> Result<(), String> {
        if !self.current(cx.tcx) {
            return Err("the native import registry lost its client context".into());
        }
        // Preflight the entire insertion before touching either index. A
        // foreign declaration can never replace a local item or another ID.
        for nominal in &self.nominals {
            if nominal.definition.is_local()
                || cx.adts.contains_key(&nominal.definition)
                || cx.adts.values().any(|id| *id == nominal.declaration.id)
                || krate
                    .adts
                    .iter()
                    .any(|decl| decl.id == nominal.declaration.id)
                || nominal.policy.nominal().is_none_or(|policy| {
                    policy.recursion().len() != nominal.declaration.type_params.len()
                })
            {
                return Err(
                    "an imported nominal identity collides or lacks its recursion policy".into(),
                );
            }
        }
        for function in &self.functions {
            if function.definition.is_local()
                || cx.fns.contains_key(&function.definition)
                || cx
                    .fns
                    .values()
                    .any(|info| info.id == function.declaration.id)
                || krate
                    .fns
                    .iter()
                    .any(|decl| decl.id == function.declaration.id)
            {
                return Err(
                    "an imported function identity collides with an existing declaration".into(),
                );
            }
        }
        let definitions = self.spec_definitions.install(cx)?;
        // Definition admission is part of the same all-or-nothing preflight.
        // Validate against the complete prospective signature view before
        // either native lookup index or the caller's crate is changed.
        if !definitions.is_empty() {
            let mut prospective = krate.clone();
            prospective.adts.extend(
                self.nominals
                    .iter()
                    .map(|nominal| nominal.declaration.clone()),
            );
            prospective.fns.extend(
                self.functions
                    .iter()
                    .map(|function| function.declaration.clone()),
            );
            definitions.validate_for_crate(&prospective)
                .map_err(|errors| format!("the checked Spec definitions differ from the prospective native signatures: {errors:?}"))?;
        }
        for nominal in &self.nominals {
            let span = cx.span_id(cx.tcx.def_span(nominal.definition));
            let mut declaration = nominal.declaration.clone();
            declaration.span = span;
            cx.adts.insert(nominal.definition, declaration.id);
            krate.adts.push(declaration);
        }
        for function in &self.functions {
            let span = cx.span_id(cx.tcx.def_span(function.definition));
            let mut declaration = function.declaration.clone();
            declaration.span = span;
            for local in &mut declaration.locals {
                local.span = span;
            }
            cx.fns.insert(
                function.definition,
                FnInfo {
                    id: declaration.id,
                    mode: Mode::Spec,
                },
            );
            krate.fns.push(declaration);
        }
        cx.spec_definitions = definitions;
        Ok(())
    }
}
