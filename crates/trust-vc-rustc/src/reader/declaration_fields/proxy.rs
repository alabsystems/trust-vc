//! Narrow authored opaque external mapping used for a Box allocator type.
//!
//! This never reads the external type's fields. Its exact native identity and
//! the original local proxy become obligations for the staging producer.

use rustc_attr_ir::Attribute;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Ty, TyCtxt};
use trust_vc_vcir::Mode;

use super::super::attrs::{self, VerusAttr};
use super::{attributes, declaration_wf, key, ExternalMapping};

const MAX_LOCAL_OWNERS: usize = 65_536;
const MAX_PROXY_FIELDS: usize = 4_096;

fn attributes_supported(attributes: &[Attribute]) -> Result<(), String> {
    // Bound token work before the shared recursive attribute parser runs.
    if attributes::mode(attributes)? != Mode::Exec {
        return Err("an allocator proxy must be an exec declaration".into());
    }
    let parsed = attrs::verus_parse(attributes)
        .map_err(|_| "allocator proxy attributes do not parse without an error")?;
    if parsed.rustc.is_some() || parsed.deprecated.is_some() {
        return Err("allocator proxy has unsupported rustc or deprecated directives".into());
    }
    let mut marker = false;
    let mut external = false;
    let mut opaque = false;
    for attribute in attributes {
        for (value, _) in attrs::verus_attrs(std::slice::from_ref(attribute)) {
            match value {
                VerusAttr::VerusMacro => marker = true,
                VerusAttr::ExternalBody => opaque = true,
                VerusAttr::Mode(Mode::Exec) => {}
                _ if attributes::empty_verifier(attribute, "external_type_specification") => {
                    external = true;
                }
                _ => return Err("an allocator proxy has an unsupported verifier directive".into()),
            }
        }
    }
    if !marker || !external || !opaque {
        return Err(
            "an allocator proxy needs original Verus, external-type and opaque declarations".into(),
        );
    }
    Ok(())
}

fn zero_parameters_and_clauses(tcx: TyCtxt<'_>, owner: DefId) -> bool {
    let generics = tcx.generics_of(owner);
    let clauses = tcx.clauses_of(owner);
    generics.parent.is_none()
        && generics.own_params.is_empty()
        && clauses.parent.is_none()
        && clauses.clauses.is_empty()
}

pub(super) fn find<'tcx>(
    tcx: TyCtxt<'tcx>,
    target: Ty<'tcx>,
) -> Result<(DefId, ExternalMapping), String> {
    let ty::Adt(adt, arguments) = target.kind() else {
        return Err(
            "the native default allocator has no supported external nominal mapping".into(),
        );
    };
    let target_id = adt.did();
    if target_id.is_local()
        || !adt.is_struct()
        || !arguments.is_empty()
        || !tcx.visibility(target_id).is_public()
        || !zero_parameters_and_clauses(tcx, target_id)
    {
        return Err(
            "allocator mapping currently requires a public foreign zero-parameter struct".into(),
        );
    }
    let mut matched = None;
    let mut count = 0usize;
    let mut field_work = MAX_PROXY_FIELDS;
    for owner in tcx.hir_crate_items(()).owners() {
        count += 1;
        if count > MAX_LOCAL_OWNERS {
            return Err("allocator mapping local-owner inventory exceeds its bound".into());
        }
        let proxy = owner.def_id.to_def_id();
        let attrs = tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner.def_id));
        if attrs.len() > 2_048 {
            return Err("allocator mapping attribute inventory exceeds its bound".into());
        }
        if !attrs
            .iter()
            .any(|attribute| attributes::verifier_named(attribute, "external_type_specification"))
        {
            continue;
        }
        if !matches!(
            tcx.def_kind(proxy),
            DefKind::Struct | DefKind::Enum | DefKind::Union
        ) || !declaration_wf::original(tcx, proxy)
        {
            continue;
        }
        // Check the authored target before interpreting the proxy as a mapping.
        // One invalid or duplicate proxy for this exact target cannot be hidden
        // by selecting another candidate with more convenient attributes.
        let definition = tcx.adt_def(proxy);
        let mut points_to_target = false;
        for field in definition.all_fields() {
            field_work = field_work
                .checked_sub(1)
                .ok_or("allocator proxy field work exceeds its bound")?;
            points_to_target |= tcx
                .type_of(field.did)
                .instantiate_identity()
                .skip_normalization()
                == target;
        }
        if !points_to_target {
            continue;
        }
        attributes_supported(attrs)?;
        if !definition.is_struct() {
            return Err("an allocator external-type proxy must be a struct".into());
        }
        let fields = &definition.non_enum_variant().fields;
        let hir = tcx.hir_node_by_def_id(owner.def_id);
        let rustc_hir::Node::Item(item) = hir else {
            return Err("allocator proxy has no original native item".into());
        };
        let Some(generics) = item.kind.generics() else {
            return Err("allocator proxy has no original generic inventory".into());
        };
        if fields.len() != 1
            || !tcx.visibility(proxy).is_public()
            || !generics.params.is_empty()
            || !zero_parameters_and_clauses(tcx, proxy)
            || tcx.def_kind(tcx.local_parent(owner.def_id)) != DefKind::Mod
        {
            return Err("allocator proxy shape, visibility or generic bounds do not match".into());
        }
        if matched.replace(proxy).is_some() {
            return Err("multiple authored allocator mappings have the same native target".into());
        }
    }
    let proxy = matched
        .ok_or("native Box allocator has no checked original external-type specification")?;
    Ok((
        proxy,
        ExternalMapping {
            proxy: key(tcx, proxy),
            target: key(tcx, target_id),
            target_svh: tcx.crate_hash(target_id.krate).as_u128(),
        },
    ))
}
