//! Observe actual instantiated field types before rustc's typeck result
//! hides a closed projection's spelling. No source-text RHS inference.

use super::*;
use crate::reader::Refusal;
use std::collections::HashSet;

pub(in crate::reader) fn observe_fields<'tcx>(
    cx: &Cx<'tcx>,
    definition: LocalDefId,
    owner: LocalDefId,
    typeck: &'tcx TypeckResults<'tcx>,
    checked: Option<&Rc<super::super::modes::CheckedModes<'tcx>>>,
    root: ty::Ty<'tcx>,
    work: &std::cell::Cell<usize>,
) -> Result<Vec<LocalDefId>, Refusal> {
    // Negative-only eligibility: no field projection was represented during
    // this reader's actual declaration pass. This grants no new type/form.
    if cx.projections.borrow().is_empty() {
        return Ok(Vec::new());
    }
    let tcx = cx.tcx;
    let fail = |detail| Refusal::new("projection-field", detail, tcx.def_span(definition));
    let charge = |n: usize| -> Result<(), Refusal> {
        match work.get().checked_sub(n) {
            Some(left) => {
                work.set(left);
                Ok(())
            }
            None => {
                work.set(0);
                Err(fail(
                    "the existing type-dependency traversal grant was exhausted",
                ))
            }
        }
    };
    // This negative eligibility observation uses the same whole-reader work
    // account as the positive field walk. Pay before creating/advancing it.
    let eligible = {
        charge(1)?;
        let mut arguments = root.walk();
        loop {
            charge(1)?;
            let Some(argument) = arguments.next() else {
                break false;
            };
            let Some(ty) = argument.as_type() else {
                continue;
            };
            if matches!(ty.kind(), ty::Adt(definition, _) if definition.did().is_local() && cx.adt_id(definition.did()).is_some())
            {
                break true;
            }
        }
    };
    if !eligible {
        return Ok(Vec::new());
    }
    charge(1)?;
    let mut pending = vec![root];
    let mut seen = HashSet::new();
    let mut used = Vec::new();
    while let Some(root) = pending.pop() {
        for native in root.walk().filter_map(|argument| argument.as_type()) {
            charge(1)?;
            let ty::Adt(datatype, args) = native.kind() else {
                continue;
            };
            let Some(local) = datatype.did().as_local() else {
                continue;
            };
            // This route never examines foreign/unrepresented fields or
            // gains layout authority merely from an opaque nominal identity.
            if cx.adt_id(datatype.did()).is_none() || cx.mentions_source_opaque(native) {
                continue;
            }
            if !seen.insert(native) {
                continue;
            }
            if !ready(tcx, local) {
                return Err(fail("the native field owner is unavailable"));
            }
            for field in datatype.all_fields() {
                charge(1)?;
                let parent = tcx.parent(field.did);
                if field.did.as_local().is_none()
                    || !(parent == datatype.did()
                        || tcx.def_kind(parent) == DefKind::Variant
                            && tcx.parent(parent) == datatype.did())
                {
                    return Err(fail("the native field has a different owner"));
                }
                let instantiated = tcx
                    .type_of(field.did)
                    .instantiate(tcx, args)
                    .skip_normalization();
                charge(1)?;
                pending.push(instantiated);
                for alias_ty in instantiated
                    .walk()
                    .filter_map(|argument| argument.as_type())
                {
                    charge(1)?;
                    let ty::Alias(_, alias) = alias_ty.kind() else {
                        continue;
                    };
                    let ty::AliasTyKind::Projection { def_id: member } = alias.kind else {
                        continue;
                    };
                    if alias_ty.has_param() {
                        continue;
                    }
                    let Some(checked) = checked else {
                        return Err(fail(
                            "closed field normalization needs completed body modes",
                        ));
                    };
                    if !current(cx, definition, owner, typeck, checked) {
                        return Err(fail(
                            "closed field normalization lost its current body/typeck/mode context",
                        ));
                    }
                    let observed =
                        observe_instance(cx, definition, owner, typeck, Some(checked), alias_ty);
                    let Some(declaration) = member.as_local() else {
                        return Err(fail("a closed field projection has no local declaration"));
                    };
                    let parent = tcx.local_parent(declaration);
                    let environment = ty::TypingEnv::fully_monomorphized();
                    let arguments = tcx
                        .try_normalize_erasing_regions(
                            environment,
                            ty::Unnormalized::new(alias.args),
                        )
                        .map_err(|_| fail("the actual field arguments cannot be normalized"))?;
                    let reference = ty::TraitRef::new(tcx, parent.to_def_id(), arguments.iter());
                    let Ok(rustc_middle::traits::ImplSource::UserDefined(selection)) =
                        tcx.codegen_select_candidate(environment.as_query_input(reference))
                    else {
                        return Err(fail(
                            "the actual field has no selected native implementation",
                        ));
                    };
                    let Some(implementation) = selection.impl_def_id.as_local() else {
                        return Err(fail(
                            "the selected field implementation is not source-owned",
                        ));
                    };
                    let mut members = tcx
                        .associated_items(implementation)
                        .in_definition_order()
                        .filter(|item| item.trait_item_def_id() == Some(member));
                    let Some(actual_member) = members.next() else {
                        return Err(fail(
                            "the selected field has no implementing associated definition",
                        ));
                    };
                    let Some(actual_member_owner) = actual_member.def_id.as_local() else {
                        return Err(fail(
                            "the implementing field definition is not source-owned",
                        ));
                    };
                    if members.next().is_some()
                        || tcx.local_parent(actual_member_owner) != implementation
                        || !ready(tcx, actual_member_owner)
                    {
                        return Err(fail(
                            "the field has no unique current implementing definition",
                        ));
                    }
                    let mut represented = Vec::new();
                    charge(arguments.len())?;
                    for argument in arguments.iter() {
                        let ty::GenericArgKind::Type(native) = argument.kind() else {
                            return Err(fail("the field discarded a non-type argument"));
                        };
                        represented.push(cx.vc_ty_with(native, &|_| None).ok_or_else(|| {
                            fail("a field implementation argument is unrepresented")
                        })?);
                    }
                    let rhs = tcx
                        .try_normalize_erasing_regions(environment, ty::Unnormalized::new(alias_ty))
                        .map_err(|_| fail("the actual field projection cannot be normalized"))?;
                    let represented_rhs = cx
                        .vc_ty_with(rhs, &|_| None)
                        .ok_or_else(|| fail("the actual normalized field type is unrepresented"))?;
                    let definitions = cx.projection_impls.borrow();
                    let matched = definitions
                        .get(&selection.impl_def_id)
                        .is_some_and(|actual| {
                            actual.id == cx.def_hash(selection.impl_def_id)
                                && actual.trait_id == cx.def_hash(parent.to_def_id())
                                && actual.arguments == represented
                                && actual.values.iter().any(|value| {
                                    value.declaration == ProjectionId(cx.def_hash(member))
                                        && value.definition == cx.def_hash(actual_member.def_id)
                                        && value.ty == represented_rhs
                                })
                        });
                    drop(definitions);
                    if !matched
                        || !observed.contains(&implementation)
                        || !ready(tcx, local)
                        || !ready(tcx, declaration)
                        || !ready(tcx, parent)
                        || !ready(tcx, implementation)
                        || !current(cx, definition, owner, typeck, checked)
                        || !ready(tcx, actual_member_owner)
                    {
                        return Err(fail("the field's actual selection/definition/normalized RHS does not match its semantic declaration"));
                    }
                    for implementation in observed {
                        if !used.contains(&implementation) {
                            charge(used.len() + 1)?;
                            used.push(implementation);
                        }
                    }
                }
            }
            if !ready(tcx, local) {
                return Err(fail("the native field owner became unavailable"));
            }
        }
    }
    Ok(used)
}
