//! Borrow original opaque carriers while their checked Keep context is live.
//!
//! This is a source-reader capability, not a foreign import registry or an
//! owned declaration constructor. It exports no fields or representation.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use rustc_hir::{self as hir, OwnerNode};
use trust_vc_vcir::{AdtDecl, AdtId, AdtKind, VcCrate};

use super::capability::facts::{self, NominalInputs};
use super::nominal_helpers::ClosedScope;
use super::*;

struct Original<'tcx> {
    owner: LocalDefId,
    item: &'tcx hir::Item<'tcx>,
}

impl<'tcx> Original<'tcx> {
    fn current(&self, tcx: TyCtxt<'tcx>) -> bool {
        let Some(original) = tcx.lower_to_hir(self.owner).as_owner() else {
            return false;
        };
        matches!(
            (original.node(), tcx.hir_node_by_def_id(self.owner)),
            (OwnerNode::Item(a), hir::Node::Item(b))
                if std::ptr::eq(a, self.item) && std::ptr::eq(b, self.item)
        )
    }
}

struct Nominal<'facts, 'tcx> {
    owner: LocalDefId,
    key: NativeKey,
    policy: &'facts declaration_policy::OwnedPolicy,
    parameters: Vec<u32>,
    originals: Vec<Original<'tcx>>,
}

/// The only constructor requires a successful transaction's borrowed native
/// scope. Neither an OwnedHelpers map nor copied keys can recreate this value.
pub(in crate::reader) struct SourceNominals<'facts, 'tcx> {
    tcx: TyCtxt<'tcx>,
    scope: &'facts ClosedScope<'facts, 'tcx>,
    facts: NominalInputs<'facts>,
    meanings: &'facts meaning::ScalarBindings,
    selections: &'facts BTreeMap<NativeKey, Vec<builtins::Selection>>,
    nominal: Nominal<'facts, 'tcx>,
}

impl<'facts, 'tcx> SourceNominals<'facts, 'tcx> {
    pub(super) fn native_pair(&self, tcx: TyCtxt<'tcx>) -> Result<(NativeKey, NativeKey), String> {
        self.revalidate(tcx)?;
        let (_, erase) = self.facts.correspondence(self.nominal.key)?;
        Ok((self.nominal.key, erase.key))
    }

    pub(super) fn capture(
        tcx: TyCtxt<'tcx>,
        scope: &'facts ClosedScope<'facts, 'tcx>,
        facts: NominalInputs<'facts>,
        meanings: &'facts meaning::ScalarBindings,
        selections: &'facts BTreeMap<NativeKey, Vec<builtins::Selection>>,
        owners: &BTreeMap<NativeKey, LocalDefId>,
        key: NativeKey,
    ) -> Result<Self, String> {
        scope.revalidate(tcx, facts.inputs, facts.common, facts.helpers)?;
        facts.erase.file.read()?;
        facts.erase.target_metadata.revalidate()?;
        let joined = facts::nominal_from(facts, key)?;
        let (keep, _) = facts.correspondence(key)?;
        let owner = owners
            .get(&key)
            .copied()
            .ok_or("the source opaque carrier has no original local owner")?;
        let native = declaration_native::capture(
            tcx,
            owner.to_def_id(),
            LOCAL_CRATE,
            &facts.inputs.sources,
            facts.common,
        );
        // This finite path is for a public, one-parameter opaque source
        // struct. Broader datatype modes and external mappings need their
        // own source consumers before this boundary can be extended.
        if native != *keep
            || tcx.def_kind(owner) != DefKind::Struct
            || !tcx.visibility(owner).is_public()
            || joined.parameters != [0]
            || !joined.policy.nominal().is_some_and(|nominal| {
                nominal.mode() == trust_vc_vcir::Mode::Exec && nominal.external_body()
            })
        {
            return Err(
                "the original source opaque owner, binder or native policy is unsupported".into(),
            );
        }
        let policy = declaration_policy::check(tcx, owner.to_def_id());
        let wf = declaration_wf::check(tcx, owner.to_def_id(), &policy);
        let fields = declaration_fields::check(tcx, owner.to_def_id(), &policy, &wf);
        let expected_wf = facts.wf.get(&key).ok_or("missing source opaque WF facts")?;
        let expected_fields = facts
            .fields
            .get(&key)
            .ok_or("missing source opaque field-language facts")?;
        if policy.for_owner(tcx, owner.to_def_id()) != Some(joined.policy)
            || wf.for_owner(tcx, owner.to_def_id()) != Some(expected_wf)
            || fields.for_owner(tcx, owner.to_def_id()) != Some(expected_fields)
            || !expected_fields.external_mappings().is_empty()
        {
            return Err("the current original policy, WF or field-language facts differ".into());
        }
        let matched = meanings.for_context(tcx, facts.inputs, facts.common)?;
        let selected = selections
            .get(&key)
            .ok_or("missing original source opaque builtin selections")?;
        if selected.len() != expected_wf.builtin_requirements().len() {
            return Err("the source opaque WF builtin inventory changed".into());
        }
        for (selection, requirement) in selected.iter().zip(expected_wf.builtin_requirements()) {
            let _meaning = selection.for_requirement(requirement, tcx, &matched)?;
        }
        let mut originals = Vec::new();
        for definition in wf
            .local_owners(tcx, owner.to_def_id())
            .ok_or("the source opaque WF lost its original local owners")?
        {
            let local = definition
                .as_local()
                .ok_or("a source opaque WF dependency is foreign")?;
            let key = declaration_native::key(tcx, *definition);
            if owners.get(&key) != Some(&local) {
                return Err("the source opaque dependency has another native owner".into());
            }
            let native = declaration_native::capture(
                tcx,
                *definition,
                LOCAL_CRATE,
                &facts.inputs.sources,
                facts.common,
            );
            if !matches!(native.source, Observation::Observed(_)) {
                return Err("a source opaque dependency lacks its approved original source".into());
            }
            let Some(original) = tcx.lower_to_hir(local).as_owner() else {
                return Err("a source opaque dependency has no original HIR owner".into());
            };
            let OwnerNode::Item(item) = original.node() else {
                return Err("a source opaque dependency is not an original nominal item".into());
            };
            originals.push(Original { owner: local, item });
        }
        let result = Self {
            tcx,
            scope,
            facts,
            meanings,
            selections,
            nominal: Nominal {
                owner,
                key,
                policy: joined.policy,
                parameters: joined.parameters,
                originals,
            },
        };
        result.revalidate(tcx)?;
        Ok(result)
    }

    fn current(&self, tcx: TyCtxt<'tcx>) -> Result<(), String> {
        if !std::ptr::eq(*tcx, *self.tcx) {
            return Err("the source opaque packet belongs to another compiler context".into());
        }
        self.scope.current(
            tcx,
            self.facts.inputs,
            self.facts.common,
            self.facts.helpers,
        )?;
        if declaration_native::key(tcx, self.nominal.owner.to_def_id()) != self.nominal.key
            || self.facts.policies.get(&self.nominal.key) != Some(self.nominal.policy)
            || !self
                .nominal
                .originals
                .iter()
                .all(|original| original.current(tcx))
        {
            return Err("the source opaque original owner or retained policy changed".into());
        }
        Ok(())
    }

    pub(in crate::reader) fn revalidate(&self, tcx: TyCtxt<'tcx>) -> Result<(), String> {
        self.current(tcx)?;
        self.scope.revalidate(
            tcx,
            self.facts.inputs,
            self.facts.common,
            self.facts.helpers,
        )?;
        self.facts.erase.file.read()?;
        self.facts.erase.target_metadata.revalidate()?;
        let matched = self
            .meanings
            .for_context(tcx, self.facts.inputs, self.facts.common)?;
        let expected = self
            .facts
            .wf
            .get(&self.nominal.key)
            .ok_or("the source opaque WF owner disappeared")?
            .builtin_requirements();
        let selected = self
            .selections
            .get(&self.nominal.key)
            .ok_or("the source opaque builtin selection owner disappeared")?;
        if selected.len() != expected.len() {
            return Err("the source opaque WF builtin inventory changed".into());
        }
        for (selection, requirement) in selected.iter().zip(expected) {
            let _meaning = selection.for_requirement(requirement, tcx, &matched)?;
        }
        self.current(tcx)
    }

    /// Install only into the same reader's native context, with no fields or
    /// constructors. No owned return value can seed a later context.
    pub(in crate::reader) fn install(
        &self,
        cx: &mut crate::reader::Cx<'tcx>,
        krate: &mut VcCrate,
    ) -> Result<(), String> {
        self.revalidate(cx.tcx)?;
        let definition = self.nominal.owner.to_def_id();
        let id = AdtId(cx.def_hash(definition));
        if cx.imports.is_some()
            || !cx.fns.is_empty()
            || !cx.adts.is_empty()
            || !cx.source_opaque_nominals.is_empty()
            || !krate.adts.is_empty()
        {
            return Err(
                "an opaque source packet requires an unused source reader without foreign registrations"
                    .into(),
            );
        }
        let declaration = AdtDecl {
            id,
            name: cx.tcx.def_path_str(definition),
            type_params: self
                .nominal
                .parameters
                .iter()
                .map(|index| format!("T{index}"))
                .collect(),
            span: cx.span_id(cx.tcx.def_span(definition)),
            kind: AdtKind::Opaque,
            variants: Vec::new(),
        };
        self.current(cx.tcx)?;
        cx.adts.insert(definition, id);
        cx.source_opaque_nominals.insert(definition);
        krate.adts.push(declaration);
        Ok(())
    }
}
