// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Early refusals only. The factory retains every positive-path byte, mode,
//! origin and sealed-header check before creating an owned function.

use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;
use trust_vc_vcir::Mode;

use crate::reader::declaration_headers::{self, CheckedHeaders};
use crate::reader::declaration_modes::DeclarationModes;
use crate::reader::modes::ModeContext;

pub(super) fn check<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    modes: &DeclarationModes<'tcx>,
) -> Result<CheckedHeaders<'tcx>, String> {
    if !modes.belongs_to(tcx)
        || tcx.dcx().has_errors().is_some()
        || !tcx.visibility(owner).is_public()
    {
        return Err(
            "native owner preflight: the public native Keep owner/body is not established".into(),
        );
    }
    if !matches!(tcx.def_kind(owner), DefKind::Fn | DefKind::AssocFn)
        || modes.body_owner(owner) != Some(owner)
    {
        return Err(
            "native origin preflight: the native function origin differs from the candidate".into(),
        );
    }
    let declared = modes.function_mode(owner.to_def_id());
    if declared != Some(Mode::Spec) {
        return Err(format!(
            "native declared-mode preflight {declared:?}: the checked native signature is not the corresponding all-Spec declaration",
        ));
    }
    let headers = declaration_headers::check(tcx, owner);
    if headers.empty_for(tcx, owner).is_none() {
        return Err("no sealed empty-header fact for this original native owner".into());
    }
    Ok(headers)
}
