//! Constant declarations and their real compiler-owned erased counterparts.
//!
//! The generated name only locates a possible pair. Native item kinds, lexical
//! ownership, marker roles, signatures and original source boundaries decide
//! whether the pair is usable. A real Rust initializer is never a spec body.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;

use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use rustc_hir::{self as hir, Node};
use rustc_middle::ty::{self, TyCtxt};

use super::attrs::{self, ItemAttrs, VerusAttr};
use trust_vc_vcir::{ConstMode, FnKind, Mode};

const PROXY_PREFIX: &str = "VERUS_UNERASED_PROXY__";
const PROXY: &str = "verus::internal(unerased_proxy)";
const REAL: &str = "verus::internal(uses_unerased_proxy)";
const CONSTANT: &str = "verus::internal(encoded_const)";

/// Exact local definitions; displayed names are never call identities.
#[derive(Default)]
pub(super) struct Registry {
    proxy_to_real: HashMap<LocalDefId, LocalDefId>,
    real_to_proxy: HashMap<LocalDefId, LocalDefId>,
    modes: HashMap<LocalDefId, ConstMode>,
}

fn marker_count(tcx: TyCtxt<'_>, def: LocalDefId, keyword: &str) -> usize {
    attrs::verus_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(def)))
        .iter()
        .filter(|(attr, _)| matches!(attr, VerusAttr::Unknown(name) if name == keyword))
        .count()
}

impl Registry {
    pub(super) fn collect(tcx: TyCtxt<'_>) -> Self {
        let owners: Vec<_> = tcx
            .hir_crate_items(())
            .owners()
            .map(|owner| owner.def_id)
            .collect();
        let mut real_candidates = HashMap::<_, Vec<_>>::new();
        for &def in &owners {
            if matches!(tcx.def_kind(def), DefKind::Const | DefKind::AssocConst)
                && marker_count(tcx, def, REAL) == 1
            {
                real_candidates
                    .entry((tcx.local_parent(def), tcx.item_name(def.to_def_id())))
                    .or_default()
                    .push(def);
            }
        }
        let mut registry = Self::default();
        for &proxy in &owners {
            if !matches!(tcx.def_kind(proxy), DefKind::Fn | DefKind::AssocFn)
                || marker_count(tcx, proxy, PROXY) != 1
                || marker_count(tcx, proxy, CONSTANT) != 1
            {
                continue;
            }
            let parent = tcx.local_parent(proxy);
            // A generated associated proxy and its erased native constant
            // must have the SAME lexical impl owner. Generic arguments are
            // consequently the same inherited native parameter indices.
            if !matches!(
                tcx.def_kind(parent),
                DefKind::Mod | DefKind::Impl { of_trait: false }
            ) || !tcx.generics_of(proxy).own_params.is_empty()
            {
                continue;
            }
            let proxy_attrs = attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(proxy)));
            let mode = match proxy_attrs.mode {
                Some(Mode::Spec) => ConstMode::Spec,
                None => ConstMode::Dual,
                _ => continue, // exec/proof consts need different read semantics
            };
            if !proxy_attrs.verus_macro || proxy_attrs.external {
                continue;
            }
            let name = tcx.item_name(proxy.to_def_id());
            let Some(real_name) = name.as_str().strip_prefix(PROXY_PREFIX) else {
                continue;
            };
            let real_name = rustc_span::Symbol::intern(real_name);
            let Some(candidates) = real_candidates.get(&(parent, real_name)) else {
                continue;
            };
            let [real] = candidates.as_slice() else {
                continue;
            };
            let real = *real;
            let real_attrs = attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(real)));
            if !real_attrs.external
                || marker_count(tcx, real, PROXY) != 0
                || marker_count(tcx, real, CONSTANT) != 0
                || !tcx.generics_of(real).own_params.is_empty()
                || tcx.generics_of(real).parent != tcx.generics_of(proxy).parent
                || tcx.explicit_clauses_of(real).clauses != tcx.explicit_clauses_of(proxy).clauses
                || tcx.visibility(real) != tcx.visibility(proxy)
            {
                continue;
            }
            let (sig, proxy_span) = match tcx.hir_node_by_def_id(proxy) {
                Node::Item(item) => match item.kind {
                    hir::ItemKind::Fn { sig, .. } => (sig, item.span),
                    _ => continue,
                },
                Node::ImplItem(item) => match item.kind {
                    hir::ImplItemKind::Fn(sig, _) => (sig, item.span),
                    _ => continue,
                },
                _ => continue,
            };
            let hir::FnRetTy::Return(output) = sig.decl.output else {
                continue;
            };
            let (real_ty, real_span) = match tcx.hir_node_by_def_id(real) {
                Node::Item(item) => match item.kind {
                    hir::ItemKind::Const(_, _, ty, _) => (ty, item.span),
                    _ => continue,
                },
                Node::ImplItem(item) => match item.kind {
                    hir::ImplItemKind::Const(ty, _) => (ty, item.span),
                    _ => continue,
                },
                _ => continue,
            };
            let Ok(real_type) = tcx.try_normalize_erasing_regions(
                ty::TypingEnv::non_body_analysis(tcx, real.to_def_id()),
                tcx.type_of(real).instantiate_identity(),
            ) else {
                continue;
            };
            if !sig.decl.inputs.is_empty()
                || !sig.header.is_safe()
                || sig.header.is_async()
                || !matches!(sig.header.constness, hir::Constness::NotConst)
                || output.span != real_ty.span
                || proxy_span.lo() != real_span.lo()
                || tcx
                    .fn_sig(proxy)
                    .instantiate_identity()
                    .skip_binder()
                    .output()
                    != real_type
            {
                continue;
            }
            let Some(proxy_body) = tcx.hir_maybe_body_owned_by(proxy) else {
                continue;
            };
            let Some(real_body) = tcx.hir_maybe_body_owned_by(real) else {
                continue;
            };
            if proxy_body.value.span != real_body.value.span
                || registry.real_to_proxy.contains_key(&real)
            {
                continue;
            }
            registry.proxy_to_real.insert(proxy, real);
            registry.real_to_proxy.insert(real, proxy);
            registry.modes.insert(proxy, mode);
        }
        // Trait constants have native HIR initializers instead of generated
        // functions. Only original verus-owned non-external declarations are
        // indexed. No spelling, evaluated host value or caller bit grants a
        // value definition.
        for def in owners {
            if tcx.def_kind(def) != DefKind::AssocConst {
                continue;
            }
            let parent = tcx.local_parent(def);
            if !matches!(
                tcx.def_kind(parent),
                DefKind::Trait | DefKind::Impl { of_trait: true }
            ) || super::is_external(tcx, def)
            {
                continue;
            }
            let attributes = attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(def)));
            // Pinned Verus marks the native Trait owner, but does not add an
            // item marker to required/default TraitItem::Const declarations.
            // Use that exact lexical native owner, never an unrelated marker
            // or displayed path. Trait impl constants have their own marker.
            let owned_trait_declaration = tcx.def_kind(parent) == DefKind::Trait
                && attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(parent))).verus_macro;
            if (attributes.verus_macro || owned_trait_declaration)
                && attributes.mode.is_none()
                && attributes.ret_mode.is_none()
                && attributes.unsupported.is_empty()
                && tcx.generics_of(def).own_params.is_empty()
            {
                registry.modes.insert(def, ConstMode::Dual);
            }
        }
        registry
    }

    pub(super) fn proxy(&self, real: LocalDefId) -> Option<LocalDefId> {
        self.real_to_proxy.get(&real).copied()
    }

    pub(super) fn real(&self, proxy: LocalDefId) -> Option<LocalDefId> {
        self.proxy_to_real.get(&proxy).copied()
    }

    pub(super) fn kind(&self, proxy: LocalDefId) -> FnKind {
        self.mode(proxy).map_or(FnKind::Function, FnKind::Constant)
    }

    pub(super) fn mode(&self, declaration: LocalDefId) -> Option<ConstMode> {
        self.modes.get(&declaration).copied()
    }

    pub(super) fn declaration(&self, native: LocalDefId) -> Option<LocalDefId> {
        self.proxy(native)
            .or_else(|| self.mode(native).map(|_| native))
    }

    pub(super) fn accepts_attribute(&self, def: LocalDefId, attr: &VerusAttr) -> bool {
        matches!(attr, VerusAttr::Unknown(name) if
            self.real(def).is_some() && (name == PROXY || name == CONSTANT)
            || self.proxy(def).is_some() && name == REAL)
    }

    pub(super) fn item_attrs(&self, tcx: TyCtxt<'_>, def: LocalDefId) -> ItemAttrs {
        let mut result = attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(def)));
        result
            .unsupported
            .retain(|(name, _)| !self.accepts_attribute(def, &VerusAttr::Unknown(name.clone())));
        result
    }
}
