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
const STATIC: &str = "verus::internal(encoded_static)";

mod pairs;
pub(super) use pairs::Use;

/// Exact local definitions; displayed names are never call identities.
#[derive(Default)]
pub(super) struct Registry<'tcx> {
    pairs: pairs::Pairs<'tcx>,
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

impl<'tcx> Registry<'tcx> {
    pub(super) fn collect(tcx: TyCtxt<'tcx>) -> Self {
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
        registry.pairs = pairs::Pairs::collect(tcx, &owners);
        for (proxy, real, kind) in registry.pairs.items() {
            if registry.proxy_to_real.contains_key(&proxy)
                || registry.real_to_proxy.contains_key(&real)
            {
                continue;
            }
            registry.proxy_to_real.insert(proxy, real);
            registry.real_to_proxy.insert(real, proxy);
            if let FnKind::Constant(mode) = kind {
                registry.modes.insert(proxy, mode);
            }
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
        self.pairs
            .kind(proxy)
            .unwrap_or_else(|| self.mode(proxy).map_or(FnKind::Function, FnKind::Constant))
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
            self.real(def).is_some() && (name == PROXY || name == CONSTANT || name == STATIC && self.kind(def) == FnKind::Static)
            || self.proxy(def).is_some() && name == REAL)
    }

    /// Only diagnostic ownership of an actual macro-copied request. The
    /// canonical declaration must still be visited by the whole autospec
    /// validator; this supplies no target, signature, mode or body permission.
    pub(super) fn copied_autospec_owner(
        &self,
        tcx: TyCtxt<'tcx>,
        real: LocalDefId,
        attribute: &VerusAttr,
        span: rustc_span::Span,
    ) -> Option<LocalDefId> {
        if !matches!(attribute, VerusAttr::WhenUsedAsSpec(_)) {
            return None;
        }
        let proxy = self.proxy(real)?;
        if self.real(proxy) != Some(real)
            || self.kind(proxy) != FnKind::ConstFunction
            || !self.current_pair(tcx, proxy)
        {
            return None;
        }
        let requests = |owner| {
            attrs::verus_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner)))
                .into_iter()
                .filter(|(attr, _)| matches!(attr, VerusAttr::WhenUsedAsSpec(_)))
                .collect::<Vec<_>>()
        };
        let original = requests(real);
        let canonical = requests(proxy);
        // Preserve every request's identity and order, including A40's
        // existing last-request semantics. A target need not be valid here.
        (!original.is_empty()
            && original == canonical
            && original
                .iter()
                .any(|(attr, actual_span)| attr == attribute && *actual_span == span))
        .then_some(proxy)
    }

    pub(super) fn select(
        &self,
        tcx: TyCtxt<'tcx>,
        caller: LocalDefId,
        typeck: &'tcx ty::TypeckResults<'tcx>,
        expression: &'tcx hir::Expr<'tcx>,
    ) -> Result<Option<Use<'tcx>>, String> {
        self.pairs.select(tcx, caller, typeck, expression)
    }

    pub(super) fn current_pair(&self, tcx: TyCtxt<'tcx>, proxy: LocalDefId) -> bool {
        self.pairs.current(tcx, proxy)
    }

    pub(super) fn value_kind(&self, native: LocalDefId) -> Option<FnKind> {
        let declaration = self.proxy(native).unwrap_or(native);
        match self.kind(declaration) {
            kind @ (FnKind::Constant(_) | FnKind::Static) => Some(kind),
            _ => None,
        }
    }

    pub(super) fn item_attrs(&self, tcx: TyCtxt<'_>, def: LocalDefId) -> ItemAttrs {
        let mut result = attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(def)));
        result
            .unsupported
            .retain(|(name, _)| !self.accepts_attribute(def, &VerusAttr::Unknown(name.clone())));
        result
    }

    pub(super) fn item_attrs_with_work(
        &self,
        tcx: TyCtxt<'_>,
        def: LocalDefId,
        remaining: &mut usize,
    ) -> Result<ItemAttrs, String> {
        let mut result =
            attrs::item_attrs_with_work(tcx.hir_attrs(tcx.local_def_id_to_hir_id(def)), remaining)?;
        // Retain the exact proxy/role filtering, including its owned Unknown
        // name copy. No attr spelling can establish a constant role.
        for (name, _) in &result.unsupported {
            *remaining = remaining
                .checked_sub(1)
                .and_then(|left| left.checked_sub(name.len()))
                .ok_or("constant attribute filtering exceeds the caller's shared work bound")?;
        }
        result
            .unsupported
            .retain(|(name, _)| !self.accepts_attribute(def, &VerusAttr::Unknown(name.clone())));
        Ok(result)
    }
}
