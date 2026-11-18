//! Legacy declarations use the native language context without ghost blocks.
//!
//! Classification alone grants no completed modes, erasure or ownership.

use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;

use super::attrs;

/// The initial native legacy declaration scope is a real local free function.
/// Trait/default owners and generated/native constant roles keep their own
/// correspondence rules. Every ordinary attribute/WF/body gate still runs.
pub(super) fn eligible(
    tcx: TyCtxt<'_>,
    definition: LocalDefId,
    no_external_by_default: bool,
) -> bool {
    eligible_using(tcx, definition, no_external_by_default, None)
        .expect("unmetered eligibility has no work failure")
}

pub(super) fn eligible_with_work(
    tcx: TyCtxt<'_>,
    definition: LocalDefId,
    no_external_by_default: bool,
    remaining: &mut usize,
) -> Result<bool, String> {
    eligible_using(tcx, definition, no_external_by_default, Some(remaining))
}

fn eligible_using(
    tcx: TyCtxt<'_>,
    definition: LocalDefId,
    no_external_by_default: bool,
    mut remaining: Option<&mut usize>,
) -> Result<bool, String> {
    if let Some(work) = remaining.as_deref_mut() {
        *work = work
            .checked_sub(1)
            .ok_or("legacy eligibility exceeds the caller's shared work bound")?;
    }
    if tcx.def_kind(definition) != DefKind::Fn
        || tcx.def_kind(tcx.local_parent(definition)) != DefKind::Mod
        || tcx.is_typeck_child(definition.to_def_id())
        || match remaining.as_deref_mut() {
            Some(work) => super::is_external_with_work(tcx, definition, work)?,
            None => super::is_external(tcx, definition),
        }
    {
        return Ok(false);
    }
    let attributes = match remaining {
        Some(work) => attrs::item_attrs_with_work(
            tcx.hir_attrs(tcx.local_def_id_to_hir_id(definition)),
            work,
        )?,
        None => attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(definition))),
    };
    Ok(!attributes.verus_macro
        && !attributes.external
        && !attributes.external_body
        && (no_external_by_default || attributes.mode.is_some()))
}
