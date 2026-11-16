//! Native local datatype layouts and compiler-resolved variant identities.
//!
//! Foreign carriers still require their separate retained representation owner.
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use rustc_hir::def::Res;

/// A field's mode comes only from its original local declaration. Opaque or
/// foreign carriers have no field-layout authority in the native reader.
pub(super) fn field_mode(
    tcx: TyCtxt<'_>,
    field: &mty::FieldDef,
    span: Span,
) -> Result<Mode, Refusal> {
    let Some(local) = field.did.as_local() else {
        return Err(Refusal::new(
            "field-mode",
            "a field without its original local declaration",
            span,
        ));
    };
    let mut mode = None;
    for (attribute, at) in attrs::verus_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(local))) {
        match attribute {
            VerusAttr::Mode(value) => {
                mode.get_or_insert(value);
            }
            VerusAttr::VerusMacro => {}
            other => {
                return Err(Refusal::new(
                    "attribute",
                    format!("{other:?} on field `{}`", field.name),
                    at,
                ))
            }
        }
    }
    Ok(mode.unwrap_or(Mode::Exec))
}

/// Resolve through actual native constructor/variant IDs, never a display name.
/// This lookup grants no datatype access or imported representation permission.
pub(super) fn constructor_variant<'tcx>(
    adt: mty::AdtDef<'tcx>,
    resolution: Res,
) -> Option<(u32, &'tcx mty::VariantDef)> {
    if !adt.is_struct() && !adt.is_enum() {
        return None;
    }
    adt.variants()
        .iter()
        .enumerate()
        .find_map(|(index, variant)| {
            let matches = match resolution {
                Res::Def(DefKind::Ctor(..), constructor) => {
                    variant.ctor_def_id() == Some(constructor)
                }
                Res::Def(DefKind::Variant, definition) => variant.def_id == definition,
                Res::Def(DefKind::Struct, definition) => adt.is_struct() && adt.did() == definition,
                _ => false,
            };
            matches
                .then(|| u32::try_from(index).ok().map(|index| (index, variant)))
                .flatten()
        })
}

/// A source-typed local struct or enum with the complete native field inventory.
pub(super) fn lower<'tcx>(
    cx: &Cx<'tcx>,
    def_id: LocalDefId,
    id: AdtId,
    wrappers: &imports::wrappers::Checks<'_, 'tcx>,
) -> Result<AdtDecl, Refusal> {
    let tcx = cx.tcx;
    let span = tcx.def_span(def_id);
    let noun = if tcx.def_kind(def_id) == DefKind::Enum {
        "enum"
    } else {
        "struct"
    };
    if !wrappers.belongs_to(cx) {
        return Err(Refusal::new(
            "import-binding",
            "the wrapper policy belongs to another reader context",
            span,
        ));
    }
    // `#[verifier::external_body]` makes a datatype opaque: Verus rejects
    // any use of its fields. The reader does not check those uses.
    let hir_id = tcx.local_def_id_to_hir_id(def_id);
    let native_policy = wrappers
        .checked_policy(def_id)
        .then(|| declaration_policy::check(tcx, def_id.to_def_id()));
    let native_directives = native_policy.as_ref().and_then(|policy| {
        declaration_policy::local_directives::capture(tcx, def_id.to_def_id(), policy).ok()
    });
    let ordinary_attributes = native_directives
        .as_ref()
        .and_then(|directives| directives.remaining(tcx, def_id.to_def_id()))
        .unwrap_or_else(|| tcx.hir_attrs(hir_id).to_vec());
    let struct_attrs = attrs::item_attrs(&ordinary_attributes);
    if struct_attrs.external_body {
        return Err(Refusal::new(
            "opaque-datatype",
            format!("a {noun} marked external_body"),
            span,
        ));
    }
    // `tracked struct` / `ghost struct` give the datatype a mode; VcIR data
    // types have none.
    if let Some(mode) = struct_attrs.mode {
        return Err(Refusal::new(
            if noun == "enum" {
                "enum-mode"
            } else {
                "struct-mode"
            },
            format!("a {noun} with mode {mode:?}"),
            span,
        ));
    }
    if let Some((name, attr_span)) = struct_attrs.unsupported.first() {
        return Err(Refusal::new(
            "attribute",
            format!("{name} on a {noun}"),
            *attr_span,
        ));
    }
    if let Some(refusal) =
        where_refusal(cx, def_id.to_def_id()).or_else(|| trait_check_bound_refusal(cx, def_id))
    {
        return Err(refusal);
    }
    let adt = tcx.adt_def(def_id);
    if !adt.is_struct() && !adt.is_enum() {
        return Err(Refusal::new(
            "adt",
            "a datatype that is not a struct or enum",
            span,
        ));
    }
    // Type parameters, in order; lifetimes do not matter to VcIR.
    let mut type_params = Vec::new();
    let mut param_index: HashMap<u32, u32> = HashMap::new();
    for param in &tcx.generics_of(def_id).own_params {
        if let mty::GenericParamDefKind::Type { .. } = param.kind {
            param_index.insert(
                param.index,
                u32::try_from(type_params.len()).unwrap_or(u32::MAX),
            );
            type_params.push(param.name.to_string());
        }
    }
    let mut variants = Vec::new();
    for variant in adt.variants().iter() {
        if adt.is_enum() {
            let local = variant.def_id.as_local().ok_or_else(|| {
                Refusal::new(
                    "adt",
                    "an enum variant without its original local owner",
                    span,
                )
            })?;
            for (attribute, attribute_span) in
                attrs::verus_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(local)))
            {
                if attribute != VerusAttr::VerusMacro {
                    return Err(Refusal::new(
                        "attribute",
                        format!("{attribute:?} on an enum variant"),
                        attribute_span,
                    ));
                }
            }
        }
        let mut fields = Vec::new();
        for field in &variant.fields {
            let mode = field_mode(tcx, field, tcx.def_span(field.did))?;
            if mode != Mode::Exec {
                return Err(Refusal::new(
                    "field-mode",
                    "mixed native field modes await coherent consumers",
                    tcx.def_span(field.did),
                ));
            }
            let ty = tcx
                .try_normalize_erasing_regions(
                    mty::TypingEnv::non_body_analysis(tcx, def_id.to_def_id()),
                    tcx.type_of(field.did).instantiate_identity(),
                )
                .map_err(|_| {
                    Refusal::new(
                        "type",
                        "a native datatype field type that cannot be normalized",
                        tcx.def_span(field.did),
                    )
                })?;
            // The declaration registry retains imported parameter recursion
            // policy, but the local recursive-type pass does not consume it yet.
            // Do not infer local wrapper WF from an opaque carrier's empty IR.
            if !wrappers.checked_policy(def_id)
                && ty.walk().any(|argument| {
                    argument.as_type().is_some_and(|value|
                matches!(value.kind(), mty::Adt(adt, _) if cx.imported_nominal(adt.did()).is_some()))
                })
            {
                return Err(Refusal::new(
                    "foreign-field-policy",
                    "a local field using an imported carrier needs the native recursion-policy join",
                    tcx.def_span(field.did),
                ));
            }
            // VcIR models `&mut` only as a function parameter's whole type.
            if ty.walk().any(|arg| {
                arg.as_type()
                    .is_some_and(|t| matches!(t.kind(), mty::Ref(_, _, m) if m.is_mut()))
            }) {
                return Err(Refusal::new(
                    "type",
                    format!("field `{}` holds `&mut`", field.name),
                    tcx.def_span(field.did),
                ));
            }
            let mut vc = cx.vc_ty_with(ty, &|p: mty::ParamTy| param_index.get(&p.index).copied());
            if vc.is_some()
                && cx
                    .verus_ty_problem_allowing_mut(ty, def_id.to_def_id())?
                    .is_some()
            {
                vc = None;
            }
            let Some(vc) = vc else {
                return Err(Refusal::new(
                    "type",
                    format!("field `{}` has type `{ty}`", field.name),
                    tcx.def_span(field.did),
                ));
            };
            fields.push(FieldDecl {
                name: field.name.to_string(),
                ty: vc,
                mode,
            });
        }
        variants.push(VariantDecl {
            name: variant.name.to_string(),
            fields,
        });
    }
    Ok(AdtDecl {
        id,
        name: format!(
            "{}::{}",
            tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE),
            tcx.def_path_str(def_id.to_def_id())
        ),
        type_params,
        span: cx.span_id(span),
        kind: if adt.is_enum() {
            AdtKind::Enum
        } else {
            AdtKind::Struct
        },
        variants,
    })
}
