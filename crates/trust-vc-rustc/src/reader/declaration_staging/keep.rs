//! Consume sealed Erase facts in the actual Keep compiler callback.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

pub(super) struct ConsumeKeep<'a> {
    inputs: &'a Inputs,
    erase: Option<OwnedErase>,
    argv: &'a [String],
    adapter: Option<function_identity_observer::Inputs>,
    config_error: Option<String>,
    result: Option<Result<KeepInputs, String>>,
    #[cfg(test)]
    transaction_probe: Option<nominal_helpers::TransactionProbe>,
}

pub(super) struct CheckedFunctionInputs {
    pub(super) native: factory::OwnedFunction,
    pub(super) policy: declaration_policy::OwnedPolicy,
}

/// Owned native inputs retained independently of their diagnostic JSON. They
/// are not imported until the remaining producer/type/WF facts are checked.
pub(super) struct KeepInputs {
    pub(super) report: Value,
    pub(super) functions: Vec<CheckedFunctionInputs>,
    pub(super) nominal_policies: BTreeMap<NativeKey, declaration_policy::OwnedPolicy>,
    pub(super) nominal_wf: BTreeMap<NativeKey, declaration_wf::OwnedWf>,
    pub(super) wf_builtin_selections: BTreeMap<NativeKey, Vec<builtins::Selection>>,
    pub(super) nominal_fields: BTreeMap<NativeKey, declaration_fields::OwnedFields>,
    pub(super) nominal_helpers: BTreeMap<NativeKey, nominal_helpers::OwnedHelpers>,
    pub(super) external_mapping_selections: BTreeMap<NativeKey, Vec<fields::MappingSelection>>,
    pub(super) keep_view: View,
    pub(super) erase: OwnedErase,
    pub(super) common: Metadata,
    pub(super) candidates: alignment::Candidates,
    pub(super) meanings: meaning::ScalarBindings,
    pub(super) spec_inputs: BTreeMap<NativeKey, spec_graph::OwnedInputs>,
    pub(super) spec_pairs: spec_graph::Pairs,
    pub(super) spec_view: spec_graph::View,
}

impl<'a> ConsumeKeep<'a> {
    pub(super) fn new(
        inputs: &'a Inputs,
        erase: OwnedErase,
        argv: &'a [String],
        adapter: function_identity_observer::Inputs,
    ) -> Self {
        Self {
            inputs,
            erase: Some(erase),
            argv,
            adapter: Some(adapter),
            config_error: None,
            result: None,
            #[cfg(test)]
            transaction_probe: None,
        }
    }

    #[cfg(test)]
    pub(super) fn set_transaction_probe(
        &mut self,
        probe: Option<nominal_helpers::TransactionProbe>,
    ) {
        self.transaction_probe = probe;
    }

    pub(super) fn result(&self) -> Option<&Result<KeepInputs, String>> {
        self.result.as_ref()
    }

    pub(super) fn finish(self) -> Result<KeepInputs, String> {
        let mut prepared = self
            .result
            .ok_or("the Keep native callback was not reached")??;
        if prepared
            .functions
            .iter()
            .any(|function| function.native.keep_key() != function.policy.owner())
        {
            return Err("the owned native function/policy handoff changed owner".into());
        }
        prepared.report["retained_owned_function_inputs"] = json!(prepared.functions.len());
        prepared.report["retained_owned_nominal_policies"] = json!(prepared.nominal_policies.len());
        prepared.report["retained_conditional_nominal_wf"] = json!(prepared.nominal_wf.len());
        prepared.report["retained_wf_selection_groups"] =
            json!(prepared.wf_builtin_selections.len());
        for (key, fields) in &prepared.nominal_fields {
            if fields.owner() != *key
                || prepared
                    .nominal_wf
                    .get(key)
                    .is_none_or(|wf| wf.owner() != *key)
                || !prepared.external_mapping_selections.contains_key(key)
            {
                return Err("the owned field/WF/mapping handoff changed nominal owner".into());
            }
        }
        prepared.report["retained_conditional_field_admissions"] =
            json!(prepared.nominal_fields.len());
        for (key, helpers) in &prepared.nominal_helpers {
            if helpers.owner() != *key
                || !prepared.nominal_fields.contains_key(key)
                || prepared
                    .nominal_wf
                    .get(key)
                    .is_none_or(|wf| wf.local_declarations() != helpers.local_declarations())
            {
                return Err("the original nominal helper handoff changed its owner closure".into());
            }
        }
        nominal_helpers::revalidate_all(
            self.inputs,
            &prepared.common,
            prepared.nominal_helpers.values(),
        )?;
        spec_graph::revalidate_all(
            self.inputs,
            &prepared.spec_pairs,
            prepared.spec_inputs.values(),
        )?;
        prepared.report["retained_original_helper_closures"] =
            json!(prepared.nominal_helpers.len());
        Ok(prepared)
    }
}

impl Callbacks for ConsumeKeep<'_> {
    fn config(&mut self, config: &mut Config) {
        self.config_error = function_identity_observer::configure(config).err();
    }

    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let _guard = function_identity_observer::diagnostic_guard(tcx.sess, true);
        self.result = Some((|| {
            if let Some(error) = self.config_error.take() {
                return Err(error);
            }
            diagnostics(tcx)?;
            let adapter = self
                .adapter
                .take()
                .ok_or("the native adapter input was already consumed")?;
            function_identity_observer::arm(tcx, adapter)?;
            rustc_hir_analysis::check_crate(tcx);
            diagnostics(tcx)?;
            let erase = self
                .erase
                .take()
                .ok_or("the sealed Erase handoff was already consumed")?;
            let invocation = Invocation::capture(tcx, self.argv)?;
            if !invocation.keep_projection_of(&erase.invocation) {
                return Err(
                    "the actual Keep Session is not the intended projection of the Erase recipe"
                        .into(),
                );
            }
            let (common, _) = collect::selections(tcx, self.inputs, None)?;
            let meanings = meaning::capture(tcx, self.inputs, &common)?;
            let keep = collect::view(tcx, LOCAL_CRATE, self.inputs, &common, &invocation, None)?;
            let compared = factory::ComparedViews::compare(&keep, &erase.view)?;
            let candidates = compared.candidates();
            let spec_view = spec_graph::View::capture(tcx, LOCAL_CRATE, self.inputs, &common)?;
            let nominal_pairs = spec_graph::nominal_pairs(&keep, candidates);
            let spec_pairs = spec_graph::Pairs::compare(
                &spec_view,
                &erase.spec_view,
                &erase.spec_roundtrip_unknown,
                nominal_pairs,
            )?;
            let owners = tcx
                .hir_crate_items(())
                .owners()
                .map(|owner| {
                    (
                        declaration_native::key(tcx, owner.def_id.to_def_id()),
                        owner.def_id,
                    )
                })
                .collect::<BTreeMap<_, _>>();
            let modes = declaration_modes::DeclarationModes::new(tcx);
            let mut helper_work = nominal_helpers::Work::new();
            let helper_cohort =
                nominal_helpers::Cohort::capture(tcx, self.inputs, &common, &mut helper_work);
            let bytes = factory::ByteInputs {
                sources: &self.inputs.sources,
                dependencies: &common,
                erase_artifact: &erase.target_metadata,
                erase_svh: erase.target_svh,
                erase_path: &erase.file.path,
            };
            let mut rows = Vec::new();
            let mut functions = Vec::new();
            let mut nominal_policies = BTreeMap::new();
            let mut nominal_rows = Vec::new();
            let mut nominal_wf = BTreeMap::new();
            let mut wf_builtin_selections = BTreeMap::new();
            let mut nominal_fields = BTreeMap::new();
            let mut nominal_helpers = BTreeMap::new();
            let mut external_mapping_selections = BTreeMap::new();
            let mut spec_inputs = BTreeMap::new();
            let mut spec_rows = Vec::new();
            for declaration in &keep.declarations {
                if !matches!(
                    declaration.shape,
                    Observation::Observed(alignment::DeclarationShape::Nominal { .. })
                ) {
                    continue;
                }
                let owner = owners
                    .get(&declaration.key)
                    .copied()
                    .ok_or("no native nominal owner")?;
                let checked = declaration_policy::check(tcx, owner.to_def_id());
                if let Some(policy) = checked.owned_for(tcx, owner.to_def_id()) {
                    if policy.owner() != declaration.key {
                        return Err("native nominal policy owner changed".into());
                    }
                    nominal_policies.insert(declaration.key, policy);
                }
                let mut observed = checked.observation();
                let wf = declaration_wf::check(tcx, owner.to_def_id(), &checked);
                observed["conditional_nominal_wf"] = wf.observation();
                let checked_fields =
                    declaration_fields::check(tcx, owner.to_def_id(), &checked, &wf);
                observed["conditional_field_language"] = checked_fields.observation();
                if let Some(owned) = wf.owned_for(tcx, owner.to_def_id()) {
                    let binding = (|| {
                        if owned.owner() != declaration.key {
                            return Err("native nominal WF belongs to another owner".into());
                        }
                        for local in owned.local_declarations() {
                            let owner = owners
                                .get(local)
                                .ok_or("a WF dependency has no original local owner")?;
                            let native = declaration_native::capture(
                                tcx,
                                owner.to_def_id(),
                                LOCAL_CRATE,
                                &self.inputs.sources,
                                &common,
                            );
                            if native.key != *local
                                || !matches!(native.source, Observation::Observed(_))
                            {
                                return Err(
                                    "a local WF dependency has a different native key or lacks approved source-byte anchors"
                                        .into(),
                                );
                            }
                        }
                        builtins::bind(tcx, self.inputs, &common, owned.builtin_requirements())
                    })();
                    match binding {
                        Ok(selections) => {
                            observed["selected_wf_builtin_requirements"] = json!(selections
                                .iter()
                                .map(builtins::Selection::observation)
                                .collect::<Vec<_>>());
                            nominal_wf.insert(declaration.key, owned);
                            wf_builtin_selections.insert(declaration.key, selections);
                        }
                        Err(reason) => {
                            observed["wf_selection_or_source_binding"] = json!({
                            "state": "Unknown", "reason": reason})
                        }
                    }
                }
                if let (Some(policy), Some(wf), Some(owned_fields)) = (
                    nominal_policies.get(&declaration.key),
                    nominal_wf.get(&declaration.key),
                    checked_fields.owned_for(tcx, owner.to_def_id()),
                ) {
                    match fields::bind(
                        tcx,
                        policy,
                        wf,
                        &owned_fields,
                        &owners,
                        self.inputs,
                        &common,
                    ) {
                        Ok(selections) => {
                            observed["selected_external_type_mappings"] = json!(selections
                                .iter()
                                .map(fields::MappingSelection::observation)
                                .collect::<Vec<_>>());
                            nominal_fields.insert(declaration.key, owned_fields);
                            external_mapping_selections.insert(declaration.key, selections);
                        }
                        Err(reason) => {
                            observed["field_selection_or_source_binding"] =
                                json!({"state": "Unknown", "reason": reason})
                        }
                    }
                }
                if nominal_fields.contains_key(&declaration.key)
                    && nominal_wf.contains_key(&declaration.key)
                {
                    match &helper_cohort {
                        Ok(cohort) => {
                            let helpers = nominal_helpers::check(
                                tcx,
                                owner.to_def_id(),
                                nominal_helpers::Required {
                                    policy: &checked,
                                    wf: &wf,
                                    fields: &checked_fields,
                                    cohort,
                                    modes: &modes,
                                    inputs: self.inputs,
                                    metadata: &common,
                                },
                                &mut helper_work,
                            );
                            observed["original_nominal_helpers"] = helpers.observation();
                            if let Ok(pending) = helpers.into_pending() {
                                nominal_helpers.insert(declaration.key, pending);
                            }
                        }
                        Err(reason) => observed["original_nominal_helpers"] = reason.observation(),
                    }
                }
                nominal_rows.push(observed);
            }
            for candidate in &candidates.matches {
                let result = (|| {
                    if let Some(reason) = erase.roundtrip_unknown.get(&candidate.erase) {
                        return Err(reason.clone());
                    }
                    let owner = owners
                        .get(&candidate.keep)
                        .copied()
                        .ok_or("no current native Keep owner")?;
                    let checked_policy = declaration_policy::check(tcx, owner.to_def_id());
                    let policy = checked_policy
                        .owned_for(tcx, owner.to_def_id())
                        .ok_or_else(|| {
                            format!(
                                "native generic policy Unknown: {}",
                                checked_policy.observation()
                            )
                        })?;
                    if policy.owner() != candidate.keep {
                        return Err("native function policy belongs to a different owner".into());
                    }
                    let headers = declaration_headers::check(tcx, owner);
                    let correspondence =
                        factory::prepare_correspondence(&bytes, &compared, candidate)?;
                    let native =
                        factory::prepare_function(tcx, owner, &modes, &headers, correspondence)
                            .map_err(|error| match error {
                                factory::PreparationError::Refused(reason) => reason,
                                factory::PreparationError::ModeRejected(error) => {
                                    format!("native mode rejection: {}", error.message)
                                }
                                factory::PreparationError::ModeUnknown(reason) => {
                                    format!("native mode Unknown: {}", reason.detail)
                                }
                            })?
                            .into_owned(tcx)?;
                    let mut observed = native.observation();
                    observed["native_policy"] = checked_policy.observation();
                    observed["unresolved_import_prerequisites"] = json!([
                        "matching nominal policy/WF closure",
                        "typed generic value representation",
                        "builtin/proc-macro build-owner provenance"
                    ]);
                    functions.push(CheckedFunctionInputs { native, policy });
                    Ok(observed)
                })();
                rows.push(match result {
                    Ok(facts) => facts,
                    Err(reason) => json!({"state": "Unknown", "keep_key": candidate.keep.def_path_hash.to_string(),
                        "erase_key": candidate.erase.def_path_hash.to_string(), "reason": reason,
                        "import_authorized": false}),
                });
            }
            // This new path captures nonempty original Spec dependency inputs
            // without changing the old empty-header/signature-only factory.
            // No result enters ClientImports or supplies a body definition.
            match spec_graph::Intrinsics::capture(tcx, self.inputs, &common) {
                Ok(scope) => {
                    let mut work = spec_graph::Work::new();
                    for owner in owners.values().copied() {
                        if !matches!(
                            tcx.def_kind(owner),
                            rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
                        ) || !tcx.visibility(owner).is_public()
                            || super::super::attrs::item_attrs(
                                tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner)),
                            )
                            .mode
                                != Some(trust_vc_vcir::Mode::Spec)
                        {
                            continue;
                        }
                        let key = declaration_native::key(tcx, owner.to_def_id());
                        let result = (|| {
                            let graph =
                                spec_graph::capture(tcx, owner, &scope, &spec_pairs, &mut work)?;
                            let observation = graph.observation()?;
                            spec_inputs.insert(key, graph.into_inputs()?);
                            Ok::<_, String>(observation)
                        })();
                        spec_rows.push(match result {
                            Ok(row) => row,
                            Err(reason) => json!({"state": "Unknown", "root_hash": key.def_path_hash.to_string(),
                                "reason": reason, "body_import_authorized": false}),
                        });
                    }
                    scope.revalidate()?;
                }
                Err(reason) => spec_rows.push(json!({"state": "Unknown", "reason": reason,
                    "body_import_authorized": false})),
            }
            let identities = function_identity_observer::complete(tcx)?;
            diagnostics(tcx)?;
            self.inputs.revalidate()?;
            let report = json!({"schema": "trust-vc.native-declaration-staging@2",
                "erase_invocation": erase.invocation.observation(),
                "metadata_loader_invocation": erase.loader_observation,
                "keep_invocation": invocation.observation(),
                "erase_metadata_sha256": erase.file.sha256,
                "producer_executable_sha256": self.inputs.producer_sha256,
                "compiler_driver_path": self.inputs.compiler_driver.path,
                "compiler_driver_sha256": self.inputs.compiler_driver.sha256,
                "keep_inventory": keep.declarations.len(), "erase_inventory": erase.view.declarations.len(),
                "structural_candidates": candidates.matches.len(),
                "structural_refusals": candidates.refused.iter().map(|r| json!({
                    "key": r.keep.def_path_hash.to_string(), "reason": r.reason})).collect::<Vec<_>>(),
                "metadata_roundtrip_unknown": erase.roundtrip_unknown.iter().map(|(key, reason)|
                    json!({"key": key.def_path_hash.to_string(), "reason": reason})).collect::<Vec<_>>(),
                "declarations": rows, "nominal_policy_observations": nominal_rows,
                "original_spec_dependency_inputs": spec_rows,
                "function_identity_observations": identities,
                "foreign_private_fields_read": false,
                "original_local_field_types_validated": {"successful_nominals": nominal_wf.len(),
                    "scope": "original local reachable source types only; builtin meanings remain conditional"},
                "private_representation_exported": false, "representation_axioms_exported": false,
                "builtin_macro_build_provenance": self.inputs.build_origin.as_ref()
                    .map(|origin| origin.observation()).unwrap_or_else(|| json!({
                        "state": "Unknown", "reason": "prebuilt byte pins are not a build-owner receipt"})),
                "captured_native_meanings": meanings.observation(),
                "import_authorized": false, "verified_functions": null,
                "keep_body_ownership_checked": false});
            let nominal_helpers = match helper_cohort {
                Ok(cohort) => {
                    #[cfg(test)]
                    let cohort = cohort.with_transaction_probe(self.transaction_probe.take());
                    cohort.finish(nominal_helpers)?
                }
                Err(_) if nominal_helpers.is_empty() => BTreeMap::new(),
                Err(_) => return Err("helper results escaped an unavailable native scope".into()),
            };
            let candidates = compared.into_candidates();
            Ok(KeepInputs {
                report,
                functions,
                nominal_policies,
                nominal_wf,
                wf_builtin_selections,
                nominal_fields,
                nominal_helpers,
                external_mapping_selections,
                keep_view: keep,
                erase,
                common,
                candidates,
                meanings,
                spec_inputs,
                spec_pairs,
                spec_view,
            })
        })());
        Compilation::Stop
    }
}
