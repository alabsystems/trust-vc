//! Bounded structural declaration types for Keep/Erase comparison.
//!
//! Debug displays are never type identities. This initial codec preserves
//! actual ADT declaration keys and generic argument indices, and returns
//! Unknown for types/binders it cannot describe. Keys remain pass-local until
//! an authenticated source/signature alignment explicitly relates them.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

extern crate rustc_abi;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Ty, TyCtxt};
use serde_json::{json, Value};

use super::declaration_facts::definition;

fn encode_type<'tcx>(tcx: TyCtxt<'tcx>, value: Ty<'tcx>, depth: usize) -> Result<Value, String> {
    if depth > 64 {
        return Err("structural type nesting exceeded its bound".into());
    }
    Ok(match value.kind() {
        ty::Bool => json!({"kind": "Bool"}),
        ty::Int(kind) => json!({"kind": "Int", "width": match kind {
            ty::IntTy::I8 => "8", ty::IntTy::I16 => "16", ty::IntTy::I32 => "32",
            ty::IntTy::I64 => "64", ty::IntTy::I128 => "128", ty::IntTy::Isize => "pointer",
        }}),
        ty::Uint(kind) => json!({"kind": "Uint", "width": match kind {
            ty::UintTy::U8 => "8", ty::UintTy::U16 => "16", ty::UintTy::U32 => "32",
            ty::UintTy::U64 => "64", ty::UintTy::U128 => "128", ty::UintTy::Usize => "pointer",
        }}),
        ty::Param(parameter) => json!({"kind": "TypeParameter", "index": parameter.index}),
        ty::Tuple(values) => json!({"kind": "Tuple", "elements": values.iter()
            .map(|value| encode_type(tcx, value, depth + 1)).collect::<Result<Vec<_>, _>>()?}),
        ty::Adt(adt, args) => {
            let generics = tcx.generics_of(adt.did());
            if generics.parent.is_some()
                || generics.own_params.iter().any(|parameter| {
                    !matches!(parameter.kind, ty::GenericParamDefKind::Type { .. })
                })
            {
                return Err(
                    "a nominal declaration has unsupported parent/lifetime/const binders".into(),
                );
            }
            let mut arguments = Vec::new();
            for argument in args.iter() {
                let ty::GenericArgKind::Type(argument) = argument.kind() else {
                    return Err(
                        "lifetime/const generic arguments are outside the first structural codec"
                            .into(),
                    );
                };
                arguments.push(encode_type(tcx, argument, depth + 1)?);
            }
            if generics.own_params.len() != arguments.len() {
                return Err(
                    "nominal identity arguments do not match the native declaration arity".into(),
                );
            }
            json!({"kind": "Adt", "definition": definition(tcx, adt.did()),
                "native_type_parameter_count": generics.own_params.len(), "type_arguments": arguments})
        }
        _ => return Err("the signature contains an unsupported structural type".into()),
    })
}

fn encode_generics(tcx: TyCtxt<'_>, def: DefId) -> Result<Value, String> {
    let generics = tcx.generics_of(def);
    let mut parameters = Vec::new();
    for parameter in &generics.own_params {
        let ty::GenericParamDefKind::Type {
            has_default,
            synthetic,
        } = parameter.kind
        else {
            return Err(
                "lifetime/const generic declarations are outside the first structural codec".into(),
            );
        };
        if has_default || synthetic {
            return Err("default type expressions and synthetic generic parameters require another structural codec".into());
        }
        parameters.push(json!({
            "index": parameter.index, "kind": "Type", "has_default": has_default,
            "synthetic": synthetic, "pure_wrt_drop": parameter.pure_wrt_drop,
        }));
    }
    Ok(json!({
        "parent_count": generics.parent_count,
        "has_self": generics.has_self,
        "own_parameters": parameters,
        "parent": generics.parent.map(|parent| definition(tcx, parent)),
    }))
}

fn encode_generic_scopes(tcx: TyCtxt<'_>, def: DefId) -> Result<Vec<Value>, String> {
    let mut scopes = Vec::new();
    let mut current = Some(def);
    while let Some(scope) = current {
        if scopes.len() > 64 {
            return Err("generic parent nesting exceeded its bound".into());
        }
        scopes.push(
            json!({"definition": definition(tcx, scope), "generics": encode_generics(tcx, scope)?}),
        );
        current = tcx.generics_of(scope).parent;
    }
    Ok(scopes)
}

fn encode_signature(tcx: TyCtxt<'_>, def: DefId) -> Result<Value, String> {
    // Identity arguments are generic. A fully-monomorphized environment would
    // drop their where-clauses and use codegen normalization incorrectly.
    let environment = ty::TypingEnv::non_body_analysis(tcx, def);
    let normalized = tcx
        .try_normalize_erasing_regions(environment, tcx.fn_sig(def).instantiate_identity())
        .map_err(|error| format!("generic signature normalization failed: {error:?}"))?;
    let signature = normalized
        .no_bound_vars()
        .ok_or("higher-ranked signature binders are outside the first structural codec")?;
    if signature.abi() != rustc_abi::ExternAbi::Rust
        || !signature.safety().is_safe()
        || signature.c_variadic()
        || signature.splatted().is_some()
    {
        return Err("only safe nonvariadic unsplatted Rust signatures are represented".into());
    }
    Ok(json!({
        "state": "ObservedStructuralSignature",
        "typing_environment": "non_body_analysis with the original generic declaration param_env",
        "normalization_erases_regions": true,
        "generic_scopes": encode_generic_scopes(tcx, def)?,
        "inputs": signature.inputs().iter().map(|value| encode_type(tcx, *value, 0)).collect::<Result<Vec<_>, _>>()?,
        "output": encode_type(tcx, signature.output(), 0)?,
        "abi": "Rust", "safety": "Safe", "c_variadic": false, "splatted": false,
        "predicate_authority": {"state": "Unknown", "reason": "generic clauses are not encoded or imported by this observation codec"},
    }))
}

pub(super) fn signature(tcx: TyCtxt<'_>, def: DefId) -> Value {
    encode_signature(tcx, def)
        .unwrap_or_else(|reason| json!({"state": "Unknown", "reason": reason}))
}

/// The same generic codec in both projections. No field/layout query is
/// needed to describe a nominal declaration or an inherent impl's Self.
pub(super) fn nominal(tcx: TyCtxt<'_>, def: DefId) -> Value {
    let observed = || -> Result<Value, String> {
        let environment = ty::TypingEnv::non_body_analysis(tcx, def);
        let normalized = tcx
            .try_normalize_erasing_regions(environment, tcx.type_of(def).instantiate_identity())
            .map_err(|error| format!("generic nominal type normalization failed: {error:?}"))?;
        Ok(json!({
            "state": "ObservedStructuralNominalType",
            "generic_scopes": encode_generic_scopes(tcx, def)?,
            "type": encode_type(tcx, normalized, 0)?,
            "predicate_authority": {"state": "Unknown", "reason": "generic clauses are not encoded or imported by this observation codec"},
            "private_representation_read": false,
        }))
    };
    observed().unwrap_or_else(|reason| json!({"state": "Unknown", "reason": reason}))
}
