//! Native declaration index for the shared body mode checker.
//!
//! This index exports no representation, clauses, proof or ownership facts.
//! Trait/default correspondence and ADT field-mode reads remain Unknown in
//! this first producer slice; the product retains its existing full context.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{HashMap, HashSet};

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{self as hir, OwnerNode};
use rustc_middle::ty::TyCtxt;
use trust_vc_vcir::Mode;

use super::attrs::ItemAttrs;
use super::constants;
use super::modes::{self, ModeCheck, ModeContext};
use crate::verus_items::VerusItem;

pub(super) struct DeclarationModes<'tcx> {
    tcx: TyCtxt<'tcx>,
    functions: HashMap<DefId, Mode>,
    legacy: HashSet<LocalDefId>,
    items: HashMap<DefId, VerusItem>,
    constants: constants::Registry<'tcx>,
}

impl<'tcx> DeclarationModes<'tcx> {
    pub(super) fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self::with_legacy_policy(tcx, false)
    }

    /// An explicit declaration policy, never a default Exec/ownership fact.
    pub(super) fn with_legacy_policy(tcx: TyCtxt<'tcx>, no_external_by_default: bool) -> Self {
        let constants = constants::Registry::collect(tcx);
        let mut legacy = HashSet::new();
        let mut functions = HashMap::new();
        for owner in tcx.hir_crate_items(()).owners() {
            let def = owner.def_id;
            if !matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
                && constants.mode(def).is_none()
            {
                continue;
            }
            let attrs = constants.item_attrs(tcx, def);
            let is_legacy = super::legacy::eligible(tcx, def, no_external_by_default)
                && constants.real(def).is_none()
                && constants.proxy(def).is_none();
            if is_legacy {
                legacy.insert(def);
            }
            if attrs.verus_macro || constants.mode(def).is_some() || is_legacy {
                functions.insert(
                    def.to_def_id(),
                    if let Some(constant) = constants.mode(def) {
                        if constant == trust_vc_vcir::ConstMode::Exec {
                            Mode::Exec
                        } else {
                            Mode::Spec
                        }
                    } else {
                        attrs.mode.unwrap_or(Mode::Exec)
                    },
                );
            }
        }
        Self {
            tcx,
            functions,
            legacy,
            items: super::verus_item_table(tcx),
            constants,
        }
    }

    pub(super) fn check(&self, def: LocalDefId) -> ModeCheck<'tcx> {
        modes::check_with_context(self, def)
    }

    pub(super) fn belongs_to(&self, tcx: TyCtxt<'tcx>) -> bool {
        std::ptr::eq(*self.tcx, *tcx)
    }

    /// Require the body the checker actually sees to be the canonical
    /// unprojected body. Original local IDs are looked up only in the raw
    /// lowering's own map, never through projected node/typeck queries.
    pub(super) fn has_original_body(&self, def: LocalDefId) -> bool {
        original_body_available(self.tcx, def)
    }
}

pub(super) fn original_body_available(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    let Some(raw) = tcx.lower_to_hir(def).as_owner() else {
        return false;
    };
    let body_id = match raw.node() {
        OwnerNode::Item(hir::Item {
            kind: hir::ItemKind::Fn { body, .. },
            ..
        }) => *body,
        OwnerNode::ImplItem(hir::ImplItem {
            kind: hir::ImplItemKind::Fn(_, body),
            ..
        }) => *body,
        _ => return false,
    };
    let Some(original) = raw.nodes.bodies.get(&body_id.hir_id.local_id).copied() else {
        return false;
    };
    // This evaluates any active owner projection before inspecting its
    // state. There is no compiler query inside the state-lock closure.
    let current = tcx.hir_maybe_body_owned_by(def);
    let quarantined = super::function_identity_observer::body_is_quarantined(tcx.sess, def);
    !quarantined && current.is_some_and(|body| std::ptr::eq(body, original))
}

impl<'tcx> ModeContext<'tcx> for DeclarationModes<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn legacy_function(&self, definition: LocalDefId) -> bool {
        self.legacy.contains(&definition)
    }

    fn function_mode(&self, def: DefId) -> Option<Mode> {
        self.functions.get(&def).copied()
    }

    fn body_owner(&self, def: LocalDefId) -> Option<LocalDefId> {
        let parent = self.tcx.local_parent(def);
        if self.tcx.def_kind(parent) == DefKind::Trait
            || self.tcx.trait_impl_of_assoc(def.to_def_id()).is_some()
            || !self.has_original_body(def)
        {
            None
        } else {
            Some(def)
        }
    }

    fn declaration_attrs(&self, def: LocalDefId) -> ItemAttrs {
        self.constants.item_attrs(self.tcx, def)
    }

    fn declaration_attrs_with_work(
        &self,
        def: LocalDefId,
        remaining: &mut usize,
    ) -> Result<ItemAttrs, String> {
        self.constants
            .item_attrs_with_work(self.tcx, def, remaining)
    }

    fn verus_item(&self, def: DefId) -> Option<VerusItem> {
        self.items.get(&def).copied()
    }

    fn constant_proxy(&self, def: LocalDefId) -> Option<LocalDefId> {
        self.constants.proxy(def)
    }

    fn constant_mode(&self, def: LocalDefId) -> Option<trust_vc_vcir::ConstMode> {
        self.constants
            .declaration(def)
            .and_then(|d| self.constants.mode(d))
    }

    fn friendly_fn_path(&self, def: DefId) -> String {
        let display = def
            .as_local()
            .and_then(|local| self.constants.real(local))
            .map_or(def, LocalDefId::to_def_id);
        self.tcx.def_path_str(display)
    }

    fn read_adt_field_modes(&self) -> bool {
        false
    }
}
