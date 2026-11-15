//! Consume only actual recursion-directive occurrences in a checked nominal.
//!
//! This view supplies policy inputs, not datatype well-foundedness. A reader
//! that consumes any directive must validate that owner and its affected local
//! closure with the native positivity/base-case checker before verification,
//! including when the declaration mentions no imported datatype.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_attr_ir::Attribute;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::AttrId;

use super::{attributes, CheckedPolicy};
use attributes::Context;

const MAX_TOTAL_ATTRIBUTES: usize = 16_384;

#[cfg(test)]
mod tests;

struct Occurrence {
    index: usize,
    id: AttrId,
}

struct Scope<'tcx> {
    definition: DefId,
    original: &'tcx [Attribute],
    recursion: Vec<Occurrence>,
}

/// This token cannot authorize attributes from another owner, a cloned list,
/// a same-span macro expansion, or a later compiler context. It never consumes
/// ext_equal, mode, external_body or any other unrelated directive.
pub(in crate::reader) struct CheckedDirectives<'policy, 'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    policy: &'policy CheckedPolicy<'tcx>,
    scopes: Vec<Scope<'tcx>>,
}

fn native_attrs<'tcx>(tcx: TyCtxt<'tcx>, definition: DefId) -> Option<&'tcx [Attribute]> {
    let local = definition.as_local()?;
    Some(tcx.hir_attrs(tcx.local_def_id_to_hir_id(local)))
}

impl<'tcx> CheckedDirectives<'_, 'tcx> {
    fn current(&self, tcx: TyCtxt<'tcx>) -> bool {
        std::ptr::eq(*self.tcx, *tcx)
            && self.policy.for_owner(tcx, self.owner).is_some()
            && self.scopes.iter().all(|scope| {
                native_attrs(tcx, scope.definition)
                    .is_some_and(|actual| std::ptr::eq(actual, scope.original))
            })
    }

    /// True means a mandatory native WF obligation must be scheduled. Policy
    /// parsing alone is never permission to use the old Param-is-founded rule.
    pub(in crate::reader) fn has_directives(&self, tcx: TyCtxt<'tcx>) -> bool {
        self.current(tcx) && self.scopes.iter().any(|scope| !scope.recursion.is_empty())
    }

    pub(in crate::reader) fn permits(
        &self,
        tcx: TyCtxt<'tcx>,
        scope: DefId,
        attribute: &Attribute,
    ) -> bool {
        if !self.current(tcx) {
            return false;
        }
        let Attribute::Unparsed(item) = attribute else {
            return false;
        };
        self.scopes
            .iter()
            .find(|entry| entry.definition == scope)
            .is_some_and(|entry| {
                entry.recursion.iter().any(|occurrence| {
                    occurrence.id == item.id.attr_id
                        && entry
                            .original
                            .get(occurrence.index)
                            .is_some_and(|actual| std::ptr::eq(actual, attribute))
                })
            })
    }

    /// The attributes of this exact item or one of its checked native type
    /// parameters, with only covered recursion occurrences removed. All other
    /// original attributes survive, even when they share the same source span.
    pub(in crate::reader) fn remaining(
        &self,
        tcx: TyCtxt<'tcx>,
        scope: DefId,
    ) -> Option<Vec<Attribute>> {
        if !self.current(tcx) {
            return None;
        }
        let scope = self.scopes.iter().find(|entry| entry.definition == scope)?;
        Some(
            scope
                .original
                .iter()
                .enumerate()
                .filter(|(index, _)| {
                    scope
                        .recursion
                        .binary_search_by_key(index, |occurrence| occurrence.index)
                        .is_err()
                })
                .map(|(_, attribute)| attribute.clone())
                .collect(),
        )
    }
}

fn scope<'tcx>(
    tcx: TyCtxt<'tcx>,
    definition: DefId,
    context: Context,
    remaining: &mut usize,
) -> Result<Scope<'tcx>, String> {
    let original =
        native_attrs(tcx, definition).ok_or("recursion directives require a local native scope")?;
    *remaining = remaining
        .checked_sub(original.len())
        .ok_or("local recursion attribute inventory exceeds its bound")?;
    // The narrow policy parser intentionally represents only policy facts.
    // Keep the ordinary full language parser first: in particular an internal
    // spelling it rejects cannot be laundered by filtering its occurrence.
    super::super::attrs::verus_parse(original).map_err(|problem| {
        format!("the original attribute language parse is unavailable: {problem:?}")
    })?;
    let mut recursion = Vec::new();
    for (index, attribute) in original.iter().enumerate() {
        let directives = attributes::read(std::slice::from_ref(attribute), context)?;
        if directives.has_recursion() {
            let Attribute::Unparsed(item) = attribute else {
                return Err(
                    "a recursion directive is not an actual unparsed native attribute".into(),
                );
            };
            recursion.push(Occurrence {
                index,
                id: item.id.attr_id,
            });
        }
    }
    Ok(Scope {
        definition,
        original,
        recursion,
    })
}

/// A bounded syntax-only hint for scheduling the real policy check. Neither
/// true nor false supplies attribute permission. On false or unavailable
/// syntax the caller must retain its ordinary, unfiltered attribute handling.
/// This performs no native sizedness, generics_of or clause queries.
pub(in crate::reader) fn has_candidate(tcx: TyCtxt<'_>, owner: DefId) -> Result<bool, String> {
    use rustc_hir::def::DefKind;
    let local = owner
        .as_local()
        .ok_or("a recursion candidate must be local")?;
    if !matches!(tcx.def_kind(owner), DefKind::Struct | DefKind::Enum)
        || !super::original_owner_available(tcx, owner)
        || tcx.dcx().has_errors().is_some()
    {
        return Err("recursion candidate discovery needs an original error-free nominal".into());
    }
    let mut budget = MAX_TOTAL_ATTRIBUTES;
    let mut read = |definition, context| -> Result<bool, String> {
        let attrs = native_attrs(tcx, definition).ok_or("the candidate scope is not local")?;
        budget = budget
            .checked_sub(attrs.len())
            .ok_or("local recursion candidate attributes exceed their bound")?;
        Ok(attributes::read(attrs, context)?.has_recursion())
    };
    let mut found = read(owner, Context::Nominal)?;
    let generics = tcx
        .hir_node_by_def_id(local)
        .generics()
        .ok_or("the nominal candidate has no original generic declaration")?;
    if generics.params.len() > 256 {
        return Err("local recursion candidate parameters exceed their bound".into());
    }
    for parameter in generics.params {
        found |= read(parameter.def_id.to_def_id(), Context::Parameter)?;
    }
    Ok(found)
}

pub(in crate::reader) fn capture<'policy, 'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    checked: &'policy CheckedPolicy<'tcx>,
) -> Result<CheckedDirectives<'policy, 'tcx>, String> {
    let policy = checked
        .for_owner(tcx, owner)
        .ok_or("the nominal has no current original checked policy")?;
    if policy.nominal().is_none() {
        return Err("local recursion directive consumption requires a nominal policy".into());
    }
    let generics = tcx.generics_of(owner);
    if generics.parent.is_some()
        || generics.own_params.len() != policy.parameters().len()
        || policy
            .parameters()
            .iter()
            .zip(&generics.own_params)
            .any(|(checked, native)| {
                checked.definition != super::key(tcx, native.def_id)
                    || checked.scope != policy.owner()
                    || checked.index != native.index
            })
    {
        return Err(
            "the recursion directive owner and actual complete native parameters differ".into(),
        );
    }
    let mut budget = MAX_TOTAL_ATTRIBUTES;
    let mut scopes = vec![scope(tcx, owner, Context::Nominal, &mut budget)?];
    for parameter in &generics.own_params {
        scopes.push(scope(
            tcx,
            parameter.def_id,
            Context::Parameter,
            &mut budget,
        )?);
    }
    let result = CheckedDirectives {
        tcx,
        owner,
        policy: checked,
        scopes,
    };
    if !result.current(tcx) {
        return Err("the recursion directive view lost its original native context".into());
    }
    Ok(result)
}
