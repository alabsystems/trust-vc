#![cfg(feature = "trust-integration")]
// Capability #2 — compiler-fact frame/alias VC tests.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// These tests drive `compiler_facts::lower_frame` through trust-vc-core's REAL
// encoder + ay solver. They establish the capability end to end:
//   1. a frame condition over a compiler-resolved write footprint VERIFIES when
//      the body relation truly preserves the unmodified location, and
//   2. a frame VIOLATION is REFUTED with a counterexample when a location the
//      body actually writes is (falsely) claimed unmodified — the seam is sound,
//      not a rubber stamp.
//
// This is the framing power Verus lacks: it reasons from surface `ensures`,
// while here the modified set is the compiler's resolved borrow/ownership write
// footprint (a `trust_ir::NativeCompilerFactRef` lineage), and the preservation
// of everything outside it is discharged as a checked VC.

use trust_ir::request::{NativeCompilerFactId, NativeCompilerFactRef};
use trust_vc_core::ir::ArithOp;
use trust_vc_driver::compiler_facts::{
    assume_preserved, assume_written, lower_frame, FrameFact, FrameLoc,
};
use trust_vc_driver::lower::{uint, Outcome};

fn u32t() -> trust_vc_core::ir::TrustVcType {
    uint(32)
}

/// `<loc>_post == <loc>_pre + 1` — a concrete write the body performs.
fn pre_plus_one(loc: &FrameLoc) -> trust_vc_core::ir::TrustVcExpr {
    trust_vc_core::ir::TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(loc.pre().as_var()),
        right: Box::new(trust_vc_core::ir::TrustVcExpr::IntLit {
            value: 1,
            ty: u32t(),
        }),
        ty: u32t(),
    }
}

/// Frame condition VERIFIES: the call modifies `x` (an AdtLayout-resolved field
/// write) and the body preserves `y`; the VC `y_post == y_pre` holds.
#[test]
fn frame_condition_for_unmodified_location_verifies() {
    let x = FrameLoc::new("x", u32t());
    let y = FrameLoc::new("y", u32t());

    // Modified set = {x}, justified by a real resolved compiler fact reference.
    let fact = FrameFact::default().from_fact_ref(
        "x",
        NativeCompilerFactRef::AdtLayout(NativeCompilerFactId(7)),
    );

    let df = lower_frame(
        "frame_preserves_y",
        &[x.clone(), y.clone()],
        &fact,
        vec![
            // Body writes x and leaves y untouched (the compiler-justified relation).
            assume_written(&x, pre_plus_one(&x)),
            assume_preserved(&y),
        ],
    );

    let (outcome, raw) = df.verify();
    assert_eq!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
    // The traceability lineage is recorded.
    assert_eq!(fact.justifications.len(), 1);
    assert!(fact.modifies("x"));
}

/// Frame VIOLATION is REFUTED: `y` is (falsely) claimed unmodified — outside the
/// modified set {x} — but the body actually writes `y_post == y_pre + 1`. The
/// asserted frame condition `y_post == y_pre` must be refuted, not stamped.
#[test]
fn frame_violation_is_refuted() {
    let x = FrameLoc::new("x", u32t());
    let y = FrameLoc::new("y", u32t());

    // Compiler claims only {x} is modified...
    let fact = FrameFact::new(["x"]);

    let df = lower_frame(
        "frame_violation",
        &[x.clone(), y.clone()],
        &fact,
        vec![
            assume_written(&x, pre_plus_one(&x)),
            // ...but the body relation actually writes y too. The frame VC for y
            // (y_post == y_pre) is therefore false and must be refuted.
            assume_written(&y, pre_plus_one(&y)),
        ],
    );

    let (outcome, raw) = df.verify();
    assert_eq!(outcome, Outcome::Refuted, "raw verdict: {raw:?}");
}

/// With nothing modified, every location is framed; preserving all of them
/// VERIFIES (all-preserved degenerate case).
#[test]
fn empty_modified_set_preserves_everything() {
    let a = FrameLoc::new("a", u32t());
    let b = FrameLoc::new("b", u32t());
    let fact = FrameFact::default();

    let df = lower_frame(
        "frame_all_preserved",
        &[a.clone(), b.clone()],
        &fact,
        vec![assume_preserved(&a), assume_preserved(&b)],
    );

    // Both locations are framed.
    assert_eq!(df.ensures.len(), 2);

    let (outcome, raw) = df.verify();
    assert_eq!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
}

/// A Monomorphization fact reference also populates the modified set — exercises
/// a second real `NativeCompilerFactRef` variant binding.
#[test]
fn monomorphization_fact_ref_modifies_location() {
    use trust_ir::request::NativeMonomorphizationId;
    let fact = FrameFact::default().from_fact_ref(
        "instance_slot",
        NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId(3)),
    );
    assert!(fact.modifies("instance_slot"));
    assert_eq!(fact.justifications.len(), 1);
}
