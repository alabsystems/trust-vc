//! Native mode observations, without borrow-check or import authority.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_hir::HirId;
use trust_vc_vcir::Mode;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum AccessKind {
    Read,
    Assign,
    MutBorrow,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum VarErasure {
    Keep,
    Erase,
    Shadow,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PlaceUse {
    pub(crate) place: HirId,
    pub(crate) local_use: HirId,
    pub(crate) binding: HirId,
    pub(crate) binding_mode: Mode,
    pub(crate) place_mode: Mode,
    pub(crate) mode: Mode,
    pub(crate) access: AccessKind,
    pub(crate) shadow_check: bool,
    pub(crate) erasure: VarErasure,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ArgumentUse {
    pub(crate) call: HirId,
    pub(crate) argument: HirId,
    pub(crate) position: usize,
    /// The actual formal parameter or constructor field's declared mode.
    pub(crate) mode: Mode,
    /// Only this parameter/field erasure rule, not erasure of a whole tree.
    pub(crate) erased: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Operation {
    pub(crate) expression: HirId,
    pub(crate) place: HirId,
    pub(crate) kind: AccessKind,
    pub(crate) place_mode: Mode,
    pub(crate) mode: Mode,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AdjustmentKind {
    BuiltinDeref,
    SharedBorrow,
    MutableBorrow,
    SpecReborrow,
    NeverToAny,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AdjustmentUse {
    pub(crate) expression: HirId,
    pub(crate) kinds: Vec<AdjustmentKind>,
    pub(crate) reborrow: Option<ReborrowUse>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReborrowPhase {
    Immediate,
    TwoPhase,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReborrowDisposition {
    SpecRead,
    KeptPlace,
    KeptTemporary,
}

/// Derived by the completed mode walk from this expression's actual typeck
/// adjustments. The pointee is a role of the adjustment, never a fabricated HIR place.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ReborrowUse {
    pub(crate) deref_index: usize,
    pub(crate) borrow_index: usize,
    pub(crate) phase: ReborrowPhase,
    pub(crate) disposition: ReborrowDisposition,
    pub(crate) carrier_mode: Mode,
    pub(crate) pointee_mode: Option<Mode>,
    pub(crate) result_mode: Mode,
}
