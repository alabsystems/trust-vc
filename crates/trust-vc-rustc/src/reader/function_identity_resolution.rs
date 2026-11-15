//! Native declaration lookup for uninstantiated function identities.
//!
//! Lookup names are compiler Idents in the actual value namespace, scoped by
//! the native receiver/container DefId. No printed path or arbitrary generic
//! instantiation selects an implementation. This is declaration observation,
//! not Rust call selection, reveal permission or import/proof authority.
//! Receiver/member references are borrowed only from the canonical ORIGINAL
//! lower_to_hir graph. No saved original HirId is looked up through projected
//! nodes or typeck tables; unavailable type-dependent information is Unknown.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;

use rustc_hir::def::{DefKind, Namespace, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{self as hir};
use rustc_middle::ty::{self, TyCtxt};
use serde_json::{json, Value};

use super::declaration_facts::definition;
use super::function_identity::{ReceiverSyntax, Target};

fn associated_origin(tcx: TyCtxt<'_>, target: DefId) -> Result<Value, String> {
    let item = tcx.associated_item(target);
    if !item.is_fn() {
        return Err("the selected associated declaration is not a function".into());
    }
    let parent = tcx.parent(target);
    let native_relations = json!({
        "parent": definition(tcx, parent),
        "associated_kind_debug": format!("{:?}", item.kind),
        "container_debug": format!("{:?}", item.container),
        "trait_of_assoc": tcx.trait_of_assoc(target).map(|def| definition(tcx, def)),
        "impl_of_assoc": tcx.impl_of_assoc(target).map(|def| definition(tcx, def)),
    });
    Ok(match item.container {
        ty::AssocContainer::InherentImpl => json!({
            "kind": "InherentDeclaration", "implementation": definition(tcx, parent),
            "native_relations": native_relations,
            "self_type_unnormalized_debug": format!("{:?}", tcx.type_of(parent).instantiate_identity()),
            "implementation_generics_debug": format!("{:?}", tcx.generics_of(parent)),
        }),
        ty::AssocContainer::Trait => json!({
            "kind": "TraitDeclaration", "trait": definition(tcx, parent),
            "native_relations": native_relations,
            "defaultness_debug": format!("{:?}", item.defaultness(tcx)),
            "concrete_implementation": {"state": "Unknown", "reason": "a trait declaration is not a selected implementation"},
        }),
        ty::AssocContainer::TraitImpl(trait_item) => {
            if !matches!(tcx.def_kind(parent), DefKind::Impl { of_trait: true })
                || tcx.impl_of_assoc(target) != Some(parent)
            {
                return Err(
                    "the native trait implementation container has an unexpected kind".into(),
                );
            }
            let trait_item =
                trait_item.map_err(|_| "the native trait declaration relation was rejected")?;
            json!({"kind": "TraitImplementationDeclaration", "implementation": definition(tcx, parent),
                "native_relations": native_relations,
                "trait_declaration": definition(tcx, trait_item),
                "defaultness_debug": format!("{:?}", item.defaultness(tcx)),
                "self_type_unnormalized_debug": format!("{:?}", tcx.type_of(parent).instantiate_identity()),
                "trait_reference_unnormalized_debug": format!("{:?}", tcx.impl_trait_ref(parent).instantiate_identity()),
                "implementation_generics_debug": format!("{:?}", tcx.generics_of(parent)),
                "generic_application": "Uninstantiated"})
        }
    })
}

fn receiver_arguments(
    tcx: TyCtxt<'_>,
    carrier: DefId,
    receiver: &ReceiverSyntax<'_>,
) -> Result<Value, String> {
    let generics = tcx.generics_of(carrier);
    let parameters = generics
        .own_params
        .iter()
        .map(|parameter| {
            json!({
                "definition": definition(tcx, parameter.def_id), "index": parameter.index,
                "kind": match parameter.kind {
                    ty::GenericParamDefKind::Type { .. } => "Type",
                    ty::GenericParamDefKind::Lifetime => "Lifetime",
                    ty::GenericParamDefKind::Const { .. } => "Const",
                },
                "native_kind_debug": format!("{:?}", parameter.kind),
            })
        })
        .collect::<Vec<_>>();
    let mut bindings = Vec::new();
    let syntax = if let Some(arguments) = &receiver.explicit_arguments {
        if generics.parent_count != 0 || arguments.segment + 1 != receiver.path.segments.len() {
            return Err(
                "explicit receiver slots require a direct nominal declaration binder".into(),
            );
        }
        if arguments.placeholders.len() != generics.own_params.len() {
            return Err(
                "receiver placeholder count differs from the actual native declaration binder"
                    .into(),
            );
        }
        for (argument, parameter) in arguments.placeholders.iter().zip(&generics.own_params) {
            if argument.syntax_kind != hir::InferArgKind::TypeOrConst
                || !matches!(parameter.kind, ty::GenericParamDefKind::Type { .. })
            {
                return Err(
                    "a receiver placeholder is not bound to an actual native type-parameter slot"
                        .into(),
                );
            }
            bindings.push(json!({"syntax_kind": "TypeOrConstInferencePlaceholder",
                "original_argument_anchor": super::declaration_facts::source_anchor(tcx, argument.span),
                "native_parameter_definition": definition(tcx, parameter.def_id),
                "native_binder_definition": definition(tcx, carrier),
                "native_parameter_index": parameter.index, "native_parameter_kind": "Type",
                "chosen_type": {"state": "Unknown", "reason": "declaration identity does not instantiate inference placeholders"}}));
        }
        json!({"kind": "ExplicitInferenceArguments", "segment": arguments.segment,
            "original_list_anchor": super::declaration_facts::source_anchor(tcx, arguments.span)})
    } else {
        json!({"kind": "ElidedArguments", "substitution": "Uninstantiated"})
    };
    Ok(
        json!({"state": "ObservedUninstantiatedNominalReceiver", "definition": definition(tcx, carrier),
        "native_binder": {"definition": definition(tcx, carrier), "parent_count": generics.parent_count,
            "parent": generics.parent.map(|def| definition(tcx, def)), "parameters": parameters},
        "syntax": syntax, "explicit_slot_bindings": bindings, "substitution": "Uninstantiated",
        "applicability": {"state": "Unknown", "reason": "a nominal carrier and hygienic declaration lookup do not prove Rust call obligations"}}),
    )
}

fn receiver_adt(tcx: TyCtxt<'_>, receiver: &ReceiverSyntax<'_>) -> Result<(DefId, Value), String> {
    match receiver.path.res {
        Res::Def(DefKind::Struct | DefKind::Enum, def) => Ok((def, receiver_arguments(tcx, def, receiver)?)),
        Res::SelfTyAlias { alias_to, is_trait_impl: false } => {
            if receiver.explicit_arguments.is_some() {
                return Err("explicit receiver slots cannot be attached to a Self alias".into());
            }
            if !matches!(tcx.def_kind(alias_to), DefKind::Impl { of_trait: false }) {
                return Err("the native Self alias is not an inherent implementation".into());
            }
            let value = tcx.try_normalize_erasing_regions(
                ty::TypingEnv::non_body_analysis(tcx, alias_to),
                tcx.type_of(alias_to).instantiate_identity(),
            ).map_err(|error| format!("native inherent Self normalization failed: {error:?}"))?;
            match value.kind() {
                ty::Adt(adt, _) => Ok((adt.did(), receiver_arguments(tcx, adt.did(), receiver)?)),
                _ => Err("the native inherent Self alias is not an ADT declaration".into()),
            }
        }
        _ => Err("type aliases, primitive/trait Self and parameter receivers still need canonical identity support".into()),
    }
}

fn inherent_declaration(
    tcx: TyCtxt<'_>,
    receiver: &ReceiverSyntax<'_>,
    member: &hir::PathSegment<'_>,
) -> Result<(DefId, Value), String> {
    if member.args.is_some() {
        return Err(
            "explicit associated generic arguments are not discarded by identity lookup".into(),
        );
    }
    let (carrier, receiver_observation) = receiver_adt(tcx, receiver)?;
    if !matches!(member.res, Res::Err | Res::Def(DefKind::AssocFn, _)) {
        return Err("the original associated segment has an unsupported native resolution".into());
    }
    let mut candidates = Vec::new();
    for &implementation in tcx.inherent_impls(carrier) {
        let items = tcx.associated_items(implementation);
        if let Some(item) =
            items.find_by_ident_and_namespace(tcx, member.ident, Namespace::ValueNS, implementation)
        {
            if !item.is_fn()
                || item.container != ty::AssocContainer::InherentImpl
                || tcx.parent(item.def_id) != implementation
            {
                return Err(
                    "the native associated name resolves outside the inherent function namespace"
                        .into(),
                );
            }
            // The actual impl self type must name this carrier. This does not
            // unify or instantiate its generic arguments or satisfy predicates.
            let self_ty = tcx
                .try_normalize_erasing_regions(
                    ty::TypingEnv::non_body_analysis(tcx, implementation),
                    tcx.type_of(implementation).instantiate_identity(),
                )
                .map_err(|error| format!("native impl self normalization failed: {error:?}"))?;
            if !matches!(self_ty.kind(), ty::Adt(adt, _) if adt.did() == carrier) {
                return Err(
                    "the native associated container does not match its receiver carrier".into(),
                );
            }
            candidates.push(item.def_id);
        }
    }
    let mut seen = HashSet::new();
    candidates.retain(|candidate| seen.insert(*candidate));
    match candidates.as_slice() {
        [target] => {
            if let Res::Def(DefKind::AssocFn, original) = member.res {
                if original != *target {
                    return Err("the hygienic candidate differs from the original native associated declaration".into());
                }
            }
            Ok((*target, receiver_observation))
        }
        [] => Err(
            "no native inherent function declaration matches this receiver/member identity".into(),
        ),
        _ => Err("the native receiver/member identity has multiple inherent declarations".into()),
    }
}

/// Run only after ordinary HIR/type analysis, outside any Session-state lock.
/// This does not turn a trait/qualified identity into a concrete call instance.
pub(super) fn resolve_declaration(
    tcx: TyCtxt<'_>,
    helper: LocalDefId,
    target: &Target<'_>,
) -> Result<Value, String> {
    let (target, receiver_observation) = match target {
        Target::Declaration(definition) if tcx.def_kind(*definition) == DefKind::Fn => {
            (*definition, None)
        }
        Target::AssociatedDeclaration(definition)
            if tcx.def_kind(*definition) == DefKind::AssocFn =>
        {
            (*definition, None)
        }
        Target::TypeRelative { receiver, member } => {
            let (target, receiver) = inherent_declaration(tcx, receiver, member)?;
            (target, Some(receiver))
        }
        Target::Qualified { .. } => return Err(
            "qualified Self/trait argument validation remains an open native resolver requirement"
                .into(),
        ),
        _ => return Err("the native function declaration has an unexpected kind".into()),
    };
    if !tcx
        .visibility(target)
        .is_accessible_from(helper.to_def_id(), tcx)
    {
        return Err(
            "the native declaration is not visible from the identity helper's scope".into(),
        );
    }
    let origin = match tcx.def_kind(target) {
        DefKind::Fn => json!({"kind": "FreeDeclaration"}),
        DefKind::AssocFn => associated_origin(tcx, target)?,
        _ => return Err("identity lookup did not return a function declaration".into()),
    };
    Ok(json!({
        "state": "ObservedNativeDeclarationIdentity",
        "definition": definition(tcx, target), "origin": origin,
        "receiver": receiver_observation,
        "structural_signature": super::declaration_types::signature(tcx, target),
        "generic_arguments": "Uninstantiated", "visibility_checked": true,
        "concrete_call_selection": {"state": "Unknown", "reason": "declaration lookup does not instantiate a Rust call"},
        "reveal_permission": {"state": "Unknown", "reason": "declaration identity alone grants no body visibility or reveal authority"},
        "import_authorized": false,
    }))
}
