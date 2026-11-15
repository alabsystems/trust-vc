//! Owned structural declarations read directly from one native compiler view.
//!
//! No observation JSON is accepted by this codec. Unsupported facts remain
//! Unknown, and no private fields, layouts, MIR or library axioms are read.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

extern crate rustc_abi;

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{CrateNum, DefId};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::{FileName, Pos, Span};

use crate::declaration_alignment::observation::ObservedAnchor;
use crate::declaration_alignment::source_bindings::{Metadata, Sources};
use crate::declaration_alignment::{
    AuthoredSpan, Declaration, DeclarationShape, DeclarationType, Digest, ExternalType,
    FunctionOrigin, GenericScope, IntegerWidth, NativeKey, NominalKind, Observation, SourceAnchor,
    TypeParameter,
};

pub(super) fn key(tcx: TyCtxt<'_>, def: DefId) -> NativeKey {
    let (high, low) = tcx.def_path_hash(def).0.split();
    NativeKey {
        stable_crate_id: tcx.stable_crate_id(def.krate).as_u64(),
        def_path_hash: (u128::from(high.as_u64()) << 64) | u128::from(low.as_u64()),
    }
}

pub(super) fn selected(
    tcx: TyCtxt<'_>,
    krate: CrateNum,
    metadata: &Metadata,
) -> Result<Digest, String> {
    let source = tcx.used_crate_source(krate);
    let path = source
        .rmeta
        .as_ref()
        .or(source.rlib.as_ref())
        .or(source.dylib.as_ref())
        .ok_or("a selected dependency has no represented native metadata path")?;
    metadata.selected(
        tcx.stable_crate_id(krate).as_u64(),
        tcx.crate_hash(krate).as_u128(),
        path,
    )
}

pub(super) fn span(tcx: TyCtxt<'_>, sources: &Sources, span: Span) -> Result<AuthoredSpan, String> {
    if span.is_dummy() {
        return Err("a dummy span has no authored source identity".into());
    }
    let file = tcx.sess.source_map().lookup_source_file(span.lo());
    if !file.contains(span.hi()) {
        return Err("an authored span crosses source files".into());
    }
    let FileName::Real(name) = &file.name else {
        return Err("a virtual source file is not an authored declaration".into());
    };
    let path = name
        .local_path()
        .and_then(|path| path.to_str())
        .ok_or("an authored source file has no represented local path")?;
    sources.anchor(&ObservedAnchor {
        local_path: path.into(),
        compiler_source_hash: file.src_hash.to_string(),
        original_file_len: file.unnormalized_source_len,
        bytes: (
            file.original_relative_byte_pos(span.lo()).to_u32(),
            file.original_relative_byte_pos(span.hi()).to_u32(),
        ),
    })
}

pub(super) fn source(
    tcx: TyCtxt<'_>,
    def: DefId,
    sources: &Sources,
) -> Result<SourceAnchor, String> {
    let identifier = tcx
        .def_ident_span(def)
        .ok_or("no native declaration identifier span")?;
    let mut enclosing = Vec::new();
    let mut current = tcx.opt_parent(def);
    while let Some(parent) = current {
        if enclosing.len() >= 64 {
            return Err("authored declaration nesting exceeds its bound".into());
        }
        if tcx.opt_parent(parent).is_none() {
            break;
        }
        enclosing.push(span(tcx, sources, tcx.def_span(parent))?);
        current = tcx.opt_parent(parent);
    }
    enclosing.reverse();
    Ok(SourceAnchor {
        identifier: span(tcx, sources, identifier)?,
        enclosing_declarations: enclosing,
    })
}

pub(super) fn scopes(tcx: TyCtxt<'_>, def: DefId) -> Result<Vec<GenericScope>, String> {
    let mut scopes = Vec::new();
    let mut current = Some(def);
    while let Some(def) = current {
        if scopes.len() >= 64 {
            return Err("native generic scope nesting exceeds its bound".into());
        }
        let native = tcx.generics_of(def);
        let mut parameters = Vec::new();
        for parameter in &native.own_params {
            let ty::GenericParamDefKind::Type {
                has_default,
                synthetic,
            } = parameter.kind
            else {
                return Err("lifetime or const declaration binders are not represented".into());
            };
            if has_default || synthetic {
                return Err("default or synthetic generic declarations are not represented".into());
            }
            parameters.push(TypeParameter {
                index: parameter.index,
                has_default,
                synthetic,
                pure_wrt_drop: parameter.pure_wrt_drop,
            });
        }
        scopes.push(GenericScope {
            parent_count: u32::try_from(native.parent_count)
                .map_err(|_| "native generic parent count exceeds the structural codec")?,
            own_type_parameters: parameters,
            has_self: native.has_self,
        });
        current = native.parent;
    }
    Ok(scopes)
}

pub(super) struct Types<'tcx, 'a> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) library: CrateNum,
    pub(super) dependencies: &'a Metadata,
}

impl<'tcx> Types<'tcx, '_> {
    pub(super) fn encode(&self, value: Ty<'tcx>, depth: usize) -> Result<DeclarationType, String> {
        if depth > 64 {
            return Err("native declaration type depth exceeds its bound".into());
        }
        Ok(match value.kind() {
            ty::Bool => DeclarationType::Bool,
            ty::Int(kind) => DeclarationType::Integer {
                signed: true,
                width: match kind {
                    ty::IntTy::I8 => IntegerWidth::Fixed(8),
                    ty::IntTy::I16 => IntegerWidth::Fixed(16),
                    ty::IntTy::I32 => IntegerWidth::Fixed(32),
                    ty::IntTy::I64 => IntegerWidth::Fixed(64),
                    ty::IntTy::I128 => IntegerWidth::Fixed(128),
                    ty::IntTy::Isize => IntegerWidth::Pointer,
                },
            },
            ty::Uint(kind) => DeclarationType::Integer {
                signed: false,
                width: match kind {
                    ty::UintTy::U8 => IntegerWidth::Fixed(8),
                    ty::UintTy::U16 => IntegerWidth::Fixed(16),
                    ty::UintTy::U32 => IntegerWidth::Fixed(32),
                    ty::UintTy::U64 => IntegerWidth::Fixed(64),
                    ty::UintTy::U128 => IntegerWidth::Fixed(128),
                    ty::UintTy::Usize => IntegerWidth::Pointer,
                },
            },
            ty::Param(parameter) => DeclarationType::Parameter(parameter.index),
            ty::Tuple(values) => DeclarationType::Tuple(
                values
                    .iter()
                    .map(|value| self.encode(value, depth + 1))
                    .collect::<Result<_, _>>()?,
            ),
            ty::Adt(adt, args) => {
                let generics = self.tcx.generics_of(adt.did());
                if generics.parent.is_some()
                    || generics.own_params.len() != args.len()
                    || generics.own_params.iter().any(|parameter| {
                        !matches!(parameter.kind, ty::GenericParamDefKind::Type { .. })
                    })
                {
                    return Err("unsupported native nominal declaration binder".into());
                }
                let arguments = args
                    .iter()
                    .map(|arg| match arg.kind() {
                        ty::GenericArgKind::Type(value) => self.encode(value, depth + 1),
                        _ => Err("lifetime/const nominal arguments are not represented".into()),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let key = key(self.tcx, adt.did());
                if adt.did().krate == self.library {
                    DeclarationType::LocalNominal {
                        declaration: key,
                        arguments,
                    }
                } else {
                    DeclarationType::ExternalNominal {
                        declaration: ExternalType {
                            key,
                            artifact_sha256: selected(
                                self.tcx,
                                adt.did().krate,
                                self.dependencies,
                            )?,
                            type_parameters: u32::try_from(generics.own_params.len()).map_err(
                                |_| "external nominal arity exceeds the structural codec",
                            )?,
                        },
                        arguments,
                    }
                }
            }
            _ => return Err("the native declaration contains an unsupported type".into()),
        })
    }

    fn shape(&self, def: DefId) -> Result<DeclarationShape, String> {
        let nominal = match self.tcx.def_kind(def) {
            DefKind::Struct => Some(NominalKind::Struct),
            DefKind::Enum => Some(NominalKind::Enum),
            DefKind::Union => Some(NominalKind::Union),
            DefKind::Fn | DefKind::AssocFn => None,
            _ => return Err("unsupported native declaration kind".into()),
        };
        if let Some(kind) = nominal {
            return Ok(DeclarationShape::Nominal { kind });
        }
        let parent = self
            .tcx
            .opt_parent(def)
            .ok_or("native function has no declaration parent")?;
        let origin = match self.tcx.def_kind(parent) {
            DefKind::Mod => FunctionOrigin::Free,
            DefKind::Impl { of_trait: false } => {
                let native = self
                    .tcx
                    .try_normalize_erasing_regions(
                        ty::TypingEnv::non_body_analysis(self.tcx, parent),
                        self.tcx.type_of(parent).instantiate_identity(),
                    )
                    .map_err(|_| "native inherent Self normalization failed")?;
                FunctionOrigin::Inherent {
                    self_type: self.encode(native, 0)?,
                }
            }
            _ => {
                return Err(
                    "trait/default/inherited function correspondence is not represented".into(),
                )
            }
        };
        let native = self
            .tcx
            .try_normalize_erasing_regions(
                ty::TypingEnv::non_body_analysis(self.tcx, def),
                self.tcx.fn_sig(def).instantiate_identity(),
            )
            .map_err(|_| "native generic signature normalization failed")?;
        let signature = native
            .no_bound_vars()
            .ok_or("higher-ranked native signature binder")?;
        if signature.abi() != rustc_abi::ExternAbi::Rust
            || !signature.safety().is_safe()
            || signature.c_variadic()
            || signature.splatted().is_some()
        {
            return Err("unsupported native function ABI".into());
        }
        Ok(DeclarationShape::Function {
            origin,
            inputs: signature
                .inputs()
                .iter()
                .map(|ty| self.encode(*ty, 0))
                .collect::<Result<_, _>>()?,
            output: Box::new(self.encode(signature.output(), 0)?),
        })
    }
}

fn observed<T>(value: Result<T, String>) -> Observation<T> {
    match value {
        Ok(value) => Observation::Observed(value),
        Err(reason) => Observation::Unknown(reason),
    }
}

pub(super) fn capture(
    tcx: TyCtxt<'_>,
    def: DefId,
    library: CrateNum,
    sources: &Sources,
    dependencies: &Metadata,
) -> Declaration {
    let types = Types {
        tcx,
        library,
        dependencies,
    };
    Declaration {
        key: key(tcx, def),
        source: observed(source(tcx, def, sources)),
        generics: observed(scopes(tcx, def)),
        shape: observed(types.shape(def)),
    }
}
