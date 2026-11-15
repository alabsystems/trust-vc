// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native complete-binder and Self-type correspondence for synthesis candidates.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};

use super::*;

fn parameters(tcx: TyCtxt<'_>, owner: DefId, work: &mut Work) -> Result<usize, Failure> {
    let native = tcx.generics_of(owner);
    work.charge(tcx, native.own_params.len())?;
    if native.parent.is_some()
        || native.parent_count != 0
        || native.has_self
        || native.has_arg_pos_consts
        || native.has_late_bound_regions.is_some()
        || native.own_params.len() > 256
        || native
            .own_params
            .iter()
            .enumerate()
            .any(|(index, parameter)| {
                parameter.index as usize != index
                    || parameter.pure_wrt_drop
                    || !matches!(
                        parameter.kind,
                        ty::GenericParamDefKind::Type {
                            has_default: false,
                            synthetic: false
                        }
                    )
            })
    {
        return Err(Failure::Unknown(
            "the helper nominal/impl binder is not a complete simple type binder".into(),
        ));
    }
    Ok(native.own_params.len())
}

pub(super) fn implementation(
    tcx: TyCtxt<'_>,
    nominal: DefId,
    implementation: DefId,
    work: &mut Work,
) -> Result<(), Failure> {
    if parameters(tcx, nominal, work)? != parameters(tcx, implementation, work)? {
        return Err(Failure::Unknown(
            "the helper impl and nominal have different complete binders".into(),
        ));
    }
    let arguments = ty::GenericArgs::identity_for_item(tcx, nominal);
    let declared = tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::non_body_analysis(tcx, nominal),
            tcx.type_of(nominal).instantiate_identity(),
        )
        .map_err(|_| Failure::Unknown("nominal native Self type cannot be normalized".into()))?;
    let actual = tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::non_body_analysis(tcx, implementation),
            tcx.type_of(implementation).instantiate(tcx, arguments),
        )
        .map_err(|_| Failure::Unknown("impl native Self type cannot be normalized".into()))?;
    if declared != actual {
        return Err(Failure::Unknown(
            "the helper impl does not preserve the native nominal type substitution".into(),
        ));
    }
    diagnostics(tcx)?;
    Ok(())
}

pub(super) fn member(
    tcx: TyCtxt<'_>,
    nominal: DefId,
    implementation: DefId,
    member: DefId,
    work: &mut Work,
) -> Result<(), Failure> {
    let native = tcx.generics_of(member);
    work.charge(tcx, native.own_params.len() + 1)?;
    if native.parent != Some(implementation)
        || !native.own_params.is_empty()
        || native.parent_count != tcx.generics_of(implementation).own_params.len()
        || native.has_arg_pos_consts
        || native.has_late_bound_regions.is_some()
    {
        return Err(Failure::Unknown(
            "the helper does not retain its exact complete impl binder".into(),
        ));
    }
    work.charge(
        tcx,
        tcx.clauses_of(nominal)
            .clauses
            .len()
            .checked_add(tcx.clauses_of(implementation).clauses.len())
            .and_then(|count| count.checked_add(tcx.clauses_of(member).clauses.len()))
            .ok_or_else(|| Failure::Unknown("helper native clause count overflowed".into()))?,
    )?;
    let nominal_policy = declaration_policy::check(tcx, nominal);
    let nominal_policy = nominal_policy
        .for_owner(tcx, nominal)
        .ok_or_else(|| Failure::Unknown("the helper nominal policy is Unknown".into()))?;
    // The function producer checks its full inherited original impl scope,
    // including raw generic inventories, attributes and native clauses.
    // Standalone impls deliberately have no declaration-policy constructor.
    let helper_policy = declaration_policy::check(tcx, member);
    let helper_policy = helper_policy.for_owner(tcx, member).ok_or_else(|| {
        Failure::Unknown("the helper inherited implementation policy is Unknown".into())
    })?;
    let impl_key = declaration_native::key(tcx, implementation);
    let nominal_key = declaration_native::key(tcx, nominal);
    if nominal_policy.parameters().len() != helper_policy.parameters().len()
        || helper_policy
            .parameters()
            .iter()
            .zip(&tcx.generics_of(implementation).own_params)
            .any(|(checked, actual)| {
                checked.scope != impl_key
                    || checked.definition != declaration_native::key(tcx, actual.def_id)
                    || checked.index != actual.index
                    || checked.has_default
            })
        || nominal_policy.clauses().len() != helper_policy.clauses().len()
        || nominal_policy
            .clauses()
            .iter()
            .zip(helper_policy.clauses())
            .any(|(expected, actual)| {
                expected.scope != nominal_key
                    || actual.scope != impl_key
                    || expected.parameter != actual.parameter
                    || expected.kind != actual.kind
                    || expected.trait_definition != actual.trait_definition
            })
    {
        return Err(Failure::Unknown(
            "the helper impl has different native declaration clauses".into(),
        ));
    }
    diagnostics(tcx)?;
    Ok(())
}

#[cfg(test)]
mod tests;
