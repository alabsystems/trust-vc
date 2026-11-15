// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Recapture actual native prerequisites; never manufacture a test permission.

use super::*;

pub(super) fn scope<'scope, 'tcx>(
    original: &Cohort<'scope, 'tcx>,
) -> Result<Cohort<'scope, 'tcx>, String> {
    Cohort::capture(
        original.tcx,
        original.inputs,
        original.metadata,
        &mut Work::new(),
    )
    .map_err(|failure| format!("the actual auxiliary cohort failed: {failure:?}"))
}

pub(super) fn pending(
    scope: &Cohort<'_, '_>,
    seed: &PendingHelpers,
) -> Result<PendingHelpers, String> {
    let tcx = scope.tcx;
    let mut owners = BTreeMap::new();
    for owner in tcx.hir_crate_items(()).owners() {
        if owners.len() >= 65_536 {
            return Err("the native test owner inventory exceeds its bound".into());
        }
        let key = declaration_native::key(tcx, owner.def_id.to_def_id());
        if owners.insert(key, owner.def_id).is_some() {
            return Err("the native test owner inventory has duplicate keys".into());
        }
    }
    let owner = owners
        .get(&seed.owner)
        .copied()
        .ok_or("the actual pending owner is absent from the current native inventory")?;
    if !inventory::original(tcx, owner) {
        return Err("the test owner no longer has its actual original HIR".into());
    }
    let owner = owner.to_def_id();
    let policy = declaration_policy::check(tcx, owner);
    let wf = declaration_wf::check(tcx, owner, &policy);
    let fields = declaration_fields::check(tcx, owner, &policy, &wf);
    let owned_policy = policy
        .owned_for(tcx, owner)
        .ok_or("the actual recaptured policy is unavailable")?;
    let owned_wf = wf
        .owned_for(tcx, owner)
        .ok_or("the actual recaptured nominal WF is unavailable")?;
    let owned_fields = fields
        .owned_for(tcx, owner)
        .ok_or("the actual recaptured field admission is unavailable")?;
    if owned_policy.owner() != seed.owner
        || owned_wf.owner() != seed.owner
        || owned_fields.owner() != seed.owner
        || owned_wf.local_declarations() != seed.local_declarations.as_slice()
        || owned_fields.local_declarations() != seed.local_declarations.as_slice()
    {
        return Err("the real recaptured prerequisites changed owner closure".into());
    }
    for local in owned_wf.local_declarations() {
        let native_owner = owners
            .get(local)
            .ok_or("a real WF dependency has no current original owner")?;
        let native = declaration_native::capture(
            tcx,
            native_owner.to_def_id(),
            LOCAL_CRATE,
            &scope.inputs.sources,
            scope.metadata,
        );
        if native.key != *local || !matches!(native.source, Observation::Observed(_)) {
            return Err("a recaptured local dependency lacks its actual source binding".into());
        }
    }
    // These are the same genuine conditional-meaning joins used by Keep before
    // admitting a nominal to the real pending inventory.
    builtins::bind(
        tcx,
        scope.inputs,
        scope.metadata,
        owned_wf.builtin_requirements(),
    )?;
    fields::bind(
        tcx,
        &owned_policy,
        &owned_wf,
        &owned_fields,
        &owners,
        scope.inputs,
        scope.metadata,
    )?;
    let modes = declaration_modes::DeclarationModes::new(tcx);
    let checked = check(
        tcx,
        owner,
        Required {
            policy: &policy,
            wf: &wf,
            fields: &fields,
            cohort: scope,
            modes: &modes,
            inputs: scope.inputs,
            metadata: scope.metadata,
        },
        &mut Work::new(),
    );
    let pending = checked
        .into_pending()
        .map_err(|failure| format!("the actual auxiliary helper check failed: {failure:?}"))?;
    if pending.owner != seed.owner
        || pending.local_declarations != seed.local_declarations
        || pending.helpers != seed.helpers
    {
        return Err("the actual auxiliary helper closure differs from its genuine seed".into());
    }
    Ok(pending)
}

pub(super) fn one(
    scope: &Cohort<'_, '_>,
    seed: &PendingHelpers,
) -> Result<BTreeMap<NativeKey, PendingHelpers>, String> {
    let fact = pending(scope, seed)?;
    Ok(BTreeMap::from([(fact.owner, fact)]))
}
