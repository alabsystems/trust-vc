//! Native validation of the macro's uncallable ambiguous-field diagnostic.
//!
//! This never defines a getter, assumes a result, or makes an external body
//! verifiable. Every call remains the upstream RustToVir error.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

extern crate rustc_abi;

use std::collections::{HashMap, HashSet};

use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{self as hir};
use rustc_middle::ty::{self, TyCtxt};
use rustc_session::config::ExternLocation;
use rustc_span::{ExpnId, Symbol};
use sha2::{Digest as _, Sha256};
use trust_vc_vcir::Mode;

use super::{attrs, declaration_modes, Cx};
use crate::declaration_alignment::source_bindings::PinnedFile;
use attrs::VerusAttr;

pub(super) struct Pending<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    nominal: DefId,
    nominal_item: &'tcx hir::Item<'tcx>,
    body: &'tcx hir::Body<'tcx>,
    macro_file: PinnedFile,
    attributes: &'tcx [rustc_attr_ir::Attribute],
}

pub(super) struct Checked<'tcx> {
    pending: Pending<'tcx>,
}

fn events(
    tcx: TyCtxt<'_>,
    definition: DefId,
    path: &std::path::Path,
) -> Result<HashSet<ExpnId>, String> {
    let mut pending = vec![tcx.expn_that_defined(definition)];
    let mut seen = HashSet::new();
    let mut result = HashSet::new();
    while let Some(event) = pending.pop() {
        if event == ExpnId::root() || !seen.insert(event) {
            continue;
        }
        if seen.len() > 128 {
            return Err("enum diagnostic expansion graph exceeds its bound".into());
        }
        let data = event.expn_data();
        if let Some(macro_id) = data.macro_def_id.filter(|def| !def.is_local()) {
            let source = tcx.used_crate_source(macro_id.krate);
            if let Some(selected) = source.dylib.as_ref() {
                if selected.canonicalize().map_err(|error| error.to_string())? == path {
                    result.insert(event);
                }
            }
        }
        pending.extend([data.parent, data.call_site.ctxt().outer_expn()]);
    }
    Ok(result)
}

fn diverging_stub(tcx: TyCtxt<'_>, owner: LocalDefId, body: &hir::Body<'_>) -> Result<(), String> {
    if body.params.len() != 1 || body.contract.is_some() {
        return Err("the enum diagnostic stub has another original body schema".into());
    }
    let mut tail = body.value;
    for _ in 0..8 {
        match tail.kind {
            hir::ExprKind::Block(block, None) if block.stmts.is_empty() => {
                tail = block.expr.ok_or("the enum diagnostic stub has no tail")?;
            }
            hir::ExprKind::DropTemps(inner) => tail = inner,
            _ => break,
        }
    }
    let hir::ExprKind::Call(callee, []) = tail.kind else {
        return Err("the enum diagnostic stub is not its original diverging call".into());
    };
    let hir::ExprKind::Path(ref path) = callee.kind else {
        return Err("the enum diagnostic stub has an indirect tail".into());
    };
    let types = tcx.typeck(owner);
    let Res::Def(DefKind::Fn, function) = types.qpath_res(path, callee.hir_id) else {
        return Err("the enum diagnostic stub tail has no native function".into());
    };
    let core = tcx
        .lang_items()
        .sized_trait()
        .ok_or("the enum diagnostic has no native core identity")?
        .krate;
    if function.is_local()
        || function.krate != core
        || !types.node_args(callee.hir_id).is_empty()
        || !types.expr_ty(tail).is_never()
    {
        return Err(
            "the enum diagnostic stub does not diverge through the actual native core".into(),
        );
    }
    // The installed core's zero-argument unimplemented! expansion calls a
    // zero-argument panic helper. Bind the actual macro definition as well
    // as the native function/signature; a spelling or an arbitrary ! result
    // does not identify this original stub.
    let macro_id = tcx
        .get_diagnostic_item(Symbol::intern("unimplemented_macro"))
        .filter(|definition| definition.krate == core && !definition.is_local())
        .ok_or("the enum diagnostic has no actual native unimplemented macro")?;
    let mut pending = vec![
        tail.span.ctxt().outer_expn(),
        callee.span.ctxt().outer_expn(),
    ];
    let mut seen = HashSet::new();
    let mut found = false;
    while let Some(event) = pending.pop() {
        if event == ExpnId::root() || !seen.insert(event) {
            continue;
        }
        if seen.len() > 128 {
            return Err("the enum diagnostic stub expansion exceeds its bound".into());
        }
        let data = event.expn_data();
        found |= data.macro_def_id == Some(macro_id);
        pending.extend([data.parent, data.call_site.ctxt().outer_expn()]);
    }
    let signature = tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::non_body_analysis(tcx, owner.to_def_id()),
            tcx.fn_sig(function).instantiate_identity(),
        )
        .map_err(|_| "the enum diagnostic panic signature cannot be normalized")?
        .no_bound_vars()
        .ok_or("the enum diagnostic panic signature has bound variables")?;
    if !found
        || !signature.inputs().is_empty()
        || !signature.output().is_never()
        || signature.abi() != rustc_abi::ExternAbi::Rust
        || !signature.safety().is_safe()
        || signature.c_variadic()
        || signature.splatted().is_some()
    {
        return Err("the enum diagnostic stub is not its actual native macro/schema".into());
    }
    Ok(())
}

pub(super) fn prepare<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId) -> Result<Pending<'tcx>, String> {
    if tcx.def_kind(owner) != DefKind::AssocFn
        || !declaration_modes::original_body_available(tcx, owner)
    {
        return Err("an enum diagnostic needs an original local associated function".into());
    }
    let attributes = tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner));
    let raw = tcx
        .lower_to_hir(owner)
        .as_owner()
        .ok_or("the enum diagnostic has no canonical owner")?;
    if !std::ptr::eq(
        raw.attrs.get(tcx.local_def_id_to_hir_id(owner).local_id),
        attributes,
    ) {
        return Err("the enum diagnostic attributes differ from their canonical owner".into());
    }
    let parsed =
        attrs::verus_parse(attributes).map_err(|_| "enum diagnostic attributes do not parse")?;
    if parsed.rustc.is_some() || parsed.deprecated.is_some() {
        return Err("unsupported enum diagnostic directives".into());
    }
    let mut marker = 0;
    let mut external = 0;
    let mut mode = 0;
    let mut origin = 0;
    for (attribute, _) in attrs::verus_attrs(attributes) {
        match attribute {
            VerusAttr::VerusMacro => origin += 1,
            VerusAttr::Mode(Mode::Spec) => mode += 1,
            VerusAttr::External => external += 1,
            VerusAttr::GetFieldManyVariants => marker += 1,
            VerusAttr::Visibility { open: true } => {}
            _ => return Err("an enum diagnostic has an unsupported directive".into()),
        }
    }
    if [marker, external, mode, origin] != [1, 1, 1, 1] {
        return Err("the enum diagnostic markers are not exact".into());
    }
    let implementation = tcx.local_parent(owner);
    if tcx.def_kind(implementation) != (DefKind::Impl { of_trait: false }) {
        return Err("the enum diagnostic is not an inherent member".into());
    }
    let env = ty::TypingEnv::non_body_analysis(tcx, implementation.to_def_id());
    let self_type = tcx
        .try_normalize_erasing_regions(env, tcx.type_of(implementation).instantiate_identity())
        .map_err(|_| "the enum diagnostic Self type cannot be normalized")?;
    let ty::Adt(adt, args) = self_type.kind() else {
        return Err("the enum diagnostic has no native nominal Self".into());
    };
    if !adt.did().is_local()
        || !adt.is_enum()
        || tcx.visibility(owner) != tcx.visibility(adt.did())
        || tcx.generics_of(owner).own_params.len() != 0
        || !tcx.clauses_of(owner).clauses.is_empty()
        || tcx.generics_of(owner).parent != Some(implementation.to_def_id())
        || tcx.generics_of(owner).parent_count != args.len()
        || *args != ty::GenericArgs::identity_for_item(tcx, adt.did())
    {
        return Err(
            "the enum diagnostic binder/Self/visibility differs from its native enum".into(),
        );
    }
    let signature = tcx
        .try_normalize_erasing_regions(env, tcx.fn_sig(owner).instantiate_identity())
        .map_err(|_| "the enum diagnostic signature cannot be normalized")?;
    let signature = signature
        .no_bound_vars()
        .ok_or("the enum diagnostic has an unsupported signature binder")?;
    if signature.inputs() != [self_type]
        || !signature.safety().is_safe()
        || signature.abi() != rustc_abi::ExternAbi::Rust
        || signature.c_variadic()
        || signature.splatted().is_some()
    {
        return Err("the enum diagnostic signature has another receiver or ABI".into());
    }
    let mut fields: HashMap<Symbol, Vec<ty::Ty<'tcx>>> = HashMap::new();
    let mut work = 4096usize;
    for variant in adt.variants() {
        for field in &variant.fields {
            work = work
                .checked_sub(1)
                .ok_or("the enum diagnostic field inventory exceeds its bound")?;
            let value = tcx
                .try_normalize_erasing_regions(env, field.ty(tcx, args))
                .map_err(|_| "an enum diagnostic field type cannot be normalized")?;
            fields.entry(field.ident(tcx).name).or_default().push(value);
        }
    }
    if !fields
        .values()
        .any(|types| types.len() > 1 && types.iter().all(|value| *value == signature.output()))
    {
        return Err("the enum diagnostic has no actual repeated field/result type".into());
    }
    let entry = tcx
        .sess
        .opts
        .externs
        .get("verus_builtin_macros")
        .ok_or("the enum diagnostic lacks the ordinary reader's explicit macro cohort")?;
    let ExternLocation::ExactPaths(paths) = &entry.location else {
        return Err("the enum diagnostic macro cohort needs an exact selected path".into());
    };
    if paths.len() != 1 {
        return Err("the enum diagnostic macro cohort has multiple paths".into());
    }
    let path = paths
        .iter()
        .next()
        .ok_or("missing macro path")?
        .canonicalized()
        .canonicalize()
        .map_err(|error| error.to_string())?;
    let a = events(tcx, owner.to_def_id(), &path)?;
    let b = events(tcx, adt.did(), &path)?;
    let local = adt.did().expect_local();
    let nominal_raw = tcx
        .lower_to_hir(local)
        .as_owner()
        .ok_or("the enum diagnostic has no canonical nominal owner")?;
    let hir::OwnerNode::Item(nominal_item) = nominal_raw.node() else {
        return Err("the enum diagnostic nominal owner is not an original item".into());
    };
    if nominal_item.owner_id.def_id != local
        || !matches!(nominal_item.kind, hir::ItemKind::Enum(..))
        || !matches!(tcx.hir_node_by_def_id(local), hir::Node::Item(current)
            if std::ptr::eq(nominal_item, current))
    {
        return Err("the enum diagnostic nominal differs from its canonical enum".into());
    }
    // A nominal's def_span describes its header, while the macro gives the
    // synthesized function the complete enum span. Use the actual original
    // item, never a span inferred from a generated member or its attributes.
    let nominal_span = nominal_item.span.source_callsite();
    let owner_span = tcx.def_span(owner).source_callsite();
    if a.is_disjoint(&b)
        || nominal_span.lo() != owner_span.lo()
        || nominal_span.hi() != owner_span.hi()
    {
        return Err(
            "the enum diagnostic lacks the same actual macro event and original enum extent".into(),
        );
    }
    let body = tcx
        .hir_maybe_body_owned_by(owner)
        .ok_or("the enum diagnostic has no original body")?;
    diverging_stub(tcx, owner, body)?;
    let bytes = std::fs::read(&path).map_err(|error| error.to_string())?;
    let macro_file = PinnedFile {
        path,
        sha256: Sha256::digest(bytes).into(),
    };
    macro_file.read()?;
    Ok(Pending {
        tcx,
        owner,
        nominal: adt.did(),
        nominal_item,
        body,
        macro_file,
        attributes,
    })
}

impl<'tcx> Pending<'tcx> {
    pub(super) fn finish(self, cx: &Cx<'tcx>) -> Result<Checked<'tcx>, String> {
        let result = Checked { pending: self };
        result.revalidate(cx)?;
        Ok(result)
    }
}

impl<'tcx> Checked<'tcx> {
    pub(super) fn definition(&self) -> DefId {
        self.pending.owner.to_def_id()
    }
    pub(super) fn revalidate(&self, cx: &Cx<'tcx>) -> Result<(), String> {
        let pending = &self.pending;
        if !std::ptr::eq(*cx.tcx, *pending.tcx)
            || cx.tcx.dcx().has_errors().is_some()
            || !declaration_modes::original_body_available(cx.tcx, pending.owner)
            || cx
                .tcx
                .hir_maybe_body_owned_by(pending.owner)
                .is_none_or(|body| !std::ptr::eq(body, pending.body))
            || !std::ptr::eq(
                cx.tcx
                    .hir_attrs(cx.tcx.local_def_id_to_hir_id(pending.owner)),
                pending.attributes,
            )
            || cx.adt_id(pending.nominal).is_none()
            || cx.imported_nominal(pending.nominal).is_some()
            || !matches!(cx.tcx.hir_node_by_def_id(pending.nominal.expect_local()),
                hir::Node::Item(current) if std::ptr::eq(pending.nominal_item, current))
            || cx
                .local_variant_fields
                .as_ref()
                .is_none_or(|scope| !scope.permits(cx.tcx, pending.nominal))
        {
            return Err(
                "the enum diagnostic left its exact original local representation scope".into(),
            );
        }
        pending.macro_file.read()?;
        Ok(())
    }
}
