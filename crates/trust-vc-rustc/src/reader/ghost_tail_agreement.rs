//! Exact physical occurrence agreement with compiler-owned raw tail modes.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::{Cx, Refusal};
use trust_vc_vcir::VcCrate;

pub(super) fn check(cx: &Cx<'_>, krate: &VcCrate) -> Result<(), Refusal> {
    let observed = trust_vc_vcir::wf::ghost_tail_modes(krate);
    let expected = cx.ghost_tail_occurrences.borrow();
    let failure = |message| {
        Refusal::new(
            "ghost-tail-modes",
            message,
            cx.tcx.def_span(rustc_hir::def_id::CRATE_DEF_ID),
        )
    };
    if expected.len() != observed.len() {
        return Err(failure(
            "the original native and IR ghost-tail occurrence counts differ",
        ));
    }
    let checked = cx.checked_modes.borrow();
    for (native, ir) in expected.iter().zip(observed) {
        if native.function != ir.function || native.span != ir.span {
            return Err(failure(
                "the physical native and IR ghost-tail occurrence order differs",
            ));
        }
        let fact = checked
            .get(&native.definition())
            .ok_or_else(|| failure("a lowered ghost tail has no completed native mode walk"))?;
        let mode = fact
            .ghost_tails
            .mode_for(cx.tcx, native)
            .map_err(|message| {
                Refusal::new(
                    "ghost-tail-modes",
                    message,
                    cx.span_of(native.span).unwrap_or(rustc_span::DUMMY_SP),
                )
            })?;
        if ir.class != Some(trust_vc_vcir::wf::GhostTailModeClass::from(mode)) {
            return Err(Refusal::new(
                "ghost-tail-modes",
                format!(
                    "the raw IR ghost-tail mode differs from its original native expression: native={mode:?}, raw={:?}, function={:?}, span={:?}",
                    ir.class, native.function, native.span,
                ),
                cx.span_of(native.span).unwrap_or(rustc_span::DUMMY_SP),
            ));
        }
    }
    Ok(())
}
