// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The exact scoped field permission consumed only by original helper modes.

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
use trust_vc_vcir::Mode;

use super::*;
use crate::reader::attrs::ItemAttrs;
use crate::reader::declaration_modes::DeclarationModes;
use crate::reader::modes::ModeContext;
use crate::verus_items::VerusItem;

pub(super) struct Context<'a, 'tcx> {
    modes: &'a DeclarationModes<'tcx>,
    allowed: &'a HashSet<DefId>,
    intrinsic: DefId,
    owner: LocalDefId,
    inline: &'a inline::Checked<'tcx>,
}

impl<'a, 'tcx> Context<'a, 'tcx> {
    pub(super) fn new(
        modes: &'a DeclarationModes<'tcx>,
        allowed: &'a HashSet<DefId>,
        intrinsic: DefId,
        owner: LocalDefId,
        inline: &'a inline::Checked<'tcx>,
    ) -> Self {
        Self {
            modes,
            allowed,
            intrinsic,
            owner,
            inline,
        }
    }
}

impl<'tcx> ModeContext<'tcx> for Context<'_, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.modes.tcx()
    }
    fn function_mode(&self, def: DefId) -> Option<Mode> {
        self.modes.function_mode(def)
    }
    fn body_owner(&self, def: LocalDefId) -> Option<LocalDefId> {
        self.modes.body_owner(def)
    }
    fn declaration_attrs(&self, def: LocalDefId) -> ItemAttrs {
        if def == self.owner {
            if let Some(attributes) = self.inline.mode_attrs(self.tcx(), def) {
                return attributes;
            }
        }
        self.modes.declaration_attrs(def)
    }
    fn verus_item(&self, def: DefId) -> Option<VerusItem> {
        self.modes.verus_item(def)
    }
    fn constant_proxy(&self, def: LocalDefId) -> Option<LocalDefId> {
        self.modes.constant_proxy(def)
    }
    fn constant_mode(&self, def: LocalDefId) -> Option<trust_vc_vcir::ConstMode> {
        self.modes.constant_mode(def)
    }
    fn friendly_fn_path(&self, def: DefId) -> String {
        self.modes.friendly_fn_path(def)
    }
    fn read_adt_field_modes(&self) -> bool {
        false
    }
    fn permits_adt_fields(&self, def: DefId) -> bool {
        def.is_local() && self.allowed.contains(&def)
    }
    fn variant_field_intrinsic(&self) -> Option<DefId> {
        Some(self.intrinsic)
    }
}
