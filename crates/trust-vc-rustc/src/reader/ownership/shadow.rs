//! First-class source-to-native ownership-shadow translation.
//!
//! Preparation is deliberately distinct from native materialization and
//! borrow checking. A source inventory, type requirement, completed mode
//! observation or successful eligibility predicate never admits a tracked
//! value. The normal verifier will consume an actually transformed native
//! graph and execute its canonical borrow check before AY.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

mod native;
mod program;
mod source;

use source::SourceInventory;

pub(in crate::reader) fn retained_values<'tcx>(
    cx: &super::Cx<'tcx>,
    definition: rustc_hir::def_id::LocalDefId,
    remaining: &mut usize,
) -> Option<super::NativeOwnership> {
    source::retained::classify(cx, definition, remaining)
}
