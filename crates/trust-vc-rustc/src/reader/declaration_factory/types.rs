//! Direct comparison with native generic identities and selected metadata.
//!
//! Predicate/WF, mode and producer authority are separate from this bounded
//! structural check. Unsupported forms fail rather than using Debug strings.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

extern crate rustc_abi;

use std::collections::BTreeSet;

use rustc_hir::def_id::{CrateNum, DefId, LocalDefId, LOCAL_CRATE};
use rustc_middle::ty::{self, Ty, TyCtxt};

use crate::declaration_alignment::source_bindings::Metadata;
use crate::declaration_alignment::{
    Declaration, DeclarationShape, DeclarationType, Digest, FunctionOrigin, GenericScope,
    IntegerWidth, NativeKey, Observation,
};

fn key(tcx: TyCtxt<'_>, def: DefId) -> NativeKey {
    let (high, low) = tcx.def_path_hash(def).0.split();
    NativeKey {
        stable_crate_id: tcx.stable_crate_id(def.krate).as_u64(),
        def_path_hash: (u128::from(high.as_u64()) << 64) | u128::from(low.as_u64()),
    }
}

fn selected(tcx: TyCtxt<'_>, krate: CrateNum, metadata: &Metadata) -> Result<Digest, String> {
    let source = tcx.used_crate_source(krate);
    let path = source
        .rmeta
        .as_ref()
        .or(source.rlib.as_ref())
        .or(source.dylib.as_ref())
        .ok_or("a native dependency has no represented selected metadata path")?;
    let svh = tcx.crate_hash(krate).as_u128();
    metadata.selected(tcx.stable_crate_id(krate).as_u64(), svh, path)
}

struct Matcher<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    dependencies: &'a Metadata,
}

impl<'tcx> Matcher<'tcx, '_> {
    fn ty(&self, native: Ty<'tcx>, candidate: &DeclarationType, depth: usize) -> bool {
        if depth > 64 {
            return false;
        }
        match (native.kind(), candidate) {
            (ty::Bool, DeclarationType::Bool) => true,
            (
                ty::Int(kind),
                DeclarationType::Integer {
                    signed: true,
                    width,
                },
            ) => {
                *width
                    == match kind {
                        ty::IntTy::I8 => IntegerWidth::Fixed(8),
                        ty::IntTy::I16 => IntegerWidth::Fixed(16),
                        ty::IntTy::I32 => IntegerWidth::Fixed(32),
                        ty::IntTy::I64 => IntegerWidth::Fixed(64),
                        ty::IntTy::I128 => IntegerWidth::Fixed(128),
                        ty::IntTy::Isize => IntegerWidth::Pointer,
                    }
            }
            (
                ty::Uint(kind),
                DeclarationType::Integer {
                    signed: false,
                    width,
                },
            ) => {
                *width
                    == match kind {
                        ty::UintTy::U8 => IntegerWidth::Fixed(8),
                        ty::UintTy::U16 => IntegerWidth::Fixed(16),
                        ty::UintTy::U32 => IntegerWidth::Fixed(32),
                        ty::UintTy::U64 => IntegerWidth::Fixed(64),
                        ty::UintTy::U128 => IntegerWidth::Fixed(128),
                        ty::UintTy::Usize => IntegerWidth::Pointer,
                    }
            }
            (ty::Param(parameter), DeclarationType::Parameter(index)) => parameter.index == *index,
            (ty::Tuple(types), DeclarationType::Tuple(values)) => {
                types.len() == values.len()
                    && types
                        .iter()
                        .zip(values)
                        .all(|(native, value)| self.ty(native, value, depth + 1))
            }
            (
                ty::Adt(adt, args),
                DeclarationType::LocalNominal {
                    declaration,
                    arguments,
                },
            ) => {
                adt.did().krate == LOCAL_CRATE
                    && key(self.tcx, adt.did()) == *declaration
                    && self.adt_args(adt.did(), *args, arguments, depth)
            }
            (
                ty::Adt(adt, args),
                DeclarationType::ExternalNominal {
                    declaration,
                    arguments,
                },
            ) => {
                adt.did().krate != LOCAL_CRATE
                    && key(self.tcx, adt.did()) == declaration.key
                    && self.tcx.generics_of(adt.did()).own_params.len()
                        == declaration.type_parameters as usize
                    && selected(self.tcx, adt.did().krate, self.dependencies).ok()
                        == Some(declaration.artifact_sha256)
                    && self.adt_args(adt.did(), *args, arguments, depth)
            }
            _ => false,
        }
    }

    fn adt_args(
        &self,
        def: DefId,
        native: ty::GenericArgs<'tcx>,
        arguments: &[DeclarationType],
        depth: usize,
    ) -> bool {
        let generics = self.tcx.generics_of(def);
        generics.parent.is_none()
            && generics.own_params.len() == arguments.len()
            && native.len() == arguments.len()
            && generics
                .own_params
                .iter()
                .all(|parameter| matches!(parameter.kind, ty::GenericParamDefKind::Type { .. }))
            && native
                .iter()
                .zip(arguments)
                .all(|(native, candidate)| match native.kind() {
                    ty::GenericArgKind::Type(native) => self.ty(native, candidate, depth + 1),
                    _ => false,
                })
    }

    fn scopes(&self, def: DefId, scopes: &[GenericScope]) -> bool {
        if scopes.len() > 64 {
            return false;
        }
        let mut current = Some(def);
        for candidate in scopes {
            let Some(def) = current else {
                return false;
            };
            let native = self.tcx.generics_of(def);
            if native.parent_count != candidate.parent_count as usize
                || native.has_self != candidate.has_self
                || native.own_params.len() != candidate.own_type_parameters.len()
            {
                return false;
            }
            for (native, candidate) in native.own_params.iter().zip(&candidate.own_type_parameters)
            {
                let ty::GenericParamDefKind::Type {
                    has_default,
                    synthetic,
                } = native.kind
                else {
                    return false;
                };
                if native.index != candidate.index
                    || has_default != candidate.has_default
                    || synthetic != candidate.synthetic
                    || native.pure_wrt_drop != candidate.pure_wrt_drop
                {
                    return false;
                }
            }
            current = native.parent;
        }
        current.is_none()
    }
}

pub(super) fn check(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    declaration: &Declaration,
    dependencies: &Metadata,
) -> Result<(), String> {
    let loaded = tcx
        .crates(())
        .iter()
        .map(|krate| tcx.stable_crate_id(*krate).as_u64())
        .collect::<BTreeSet<_>>();
    if loaded != dependencies.crate_ids() {
        return Err("the native dependency inventory differs from the checked byte cohort".into());
    }
    for krate in tcx.crates(()) {
        selected(tcx, *krate, dependencies)?;
    }
    let def = owner.to_def_id();
    let matcher = Matcher { tcx, dependencies };
    let Observation::Observed(scopes) = &declaration.generics else {
        return Err("candidate generic scopes are Unknown".into());
    };
    if !matcher.scopes(def, scopes) {
        return Err("native generic binder identities differ from the candidate".into());
    }
    let Observation::Observed(DeclarationShape::Function {
        origin,
        inputs,
        output,
    }) = &declaration.shape
    else {
        return Err("candidate function shape is Unknown".into());
    };
    let environment = ty::TypingEnv::non_body_analysis(tcx, def);
    let normalized = tcx
        .try_normalize_erasing_regions(environment, tcx.fn_sig(def).instantiate_identity())
        .map_err(|_| "native generic signature normalization failed")?;
    let signature = normalized
        .no_bound_vars()
        .ok_or("unsupported native signature binders")?;
    if signature.abi() != rustc_abi::ExternAbi::Rust
        || !signature.safety().is_safe()
        || signature.c_variadic()
        || signature.splatted().is_some()
        || signature.inputs().len() != inputs.len()
        || !signature
            .inputs()
            .iter()
            .zip(inputs)
            .all(|(native, value)| matcher.ty(*native, value, 0))
        || !matcher.ty(signature.output(), output, 0)
    {
        return Err("native signature types or ABI differ from the structural candidate".into());
    }
    if let FunctionOrigin::Inherent { self_type } = origin {
        let parent = tcx.parent(def);
        let native = tcx
            .try_normalize_erasing_regions(
                ty::TypingEnv::non_body_analysis(tcx, parent),
                tcx.type_of(parent).instantiate_identity(),
            )
            .map_err(|_| "native inherent Self type normalization failed")?;
        if !matcher.ty(native, self_type, 0) {
            return Err("native inherent Self type differs from the candidate".into());
        }
    }
    Ok(())
}
