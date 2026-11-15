// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Permanent sentinels for source-file lanes that are deliberately quarantined.
//!
//! These surfaces must remain fail closed until their scoping, identity, and
//! well-foundedness models are sound.  An extraction error, counterexample, or
//! unknown result is acceptable; `Verified` is never acceptable.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fixture(name: &str) -> String {
    format!("{}/tests/data/{name}", env!("CARGO_MANIFEST_DIR"))
}

fn assert_not_verified(file: &str, function: &str) {
    if let Ok(VerifyResult::Verified) = verify_function_from_file(&fixture(file), function) {
        panic!("QUARANTINE BREACH: `{function}` from `{file}` must remain fail closed")
    }
}

/// A surface whose quarantine has been SOUNDLY lifted: it must now positively
/// verify. Used only for the reinstated closure def-side lane, whose isolated
/// child-context check verifies a def-side-valid spec while the poison probe
/// below still fails closed.
fn assert_verified(file: &str, function: &str) {
    match verify_function_from_file(&fixture(file), function) {
        Ok(VerifyResult::Verified) => {}
        other => panic!(
            "REINSTATEMENT REGRESSION: `{function}` from `{file}` should now verify \
             through the isolated def-side check, got {other:?}"
        ),
    }
}

#[test]
fn loop_decreases_file_path_is_sound() {
    // REINSTATED (un-quarantine #3, well-founded-measure invariant): a
    // genuinely terminating loop now VERIFIES through the measure lane — WF1
    // (`Inv && G |= M >= 0`, a direct single-state floor in the measure's own
    // sort) and WF2 (`Inv && G && s'=f(s) |= M(s') < M(s)`, a frame-condition
    // inductive step).
    assert_verified("loop_decreases_soundness_repro.rs", "terminating_countdown");
    // PERMANENT NEGATIVE (must NEVER verify): a strictly-decreasing but
    // unbounded-below `int` measure. WF2 (descent) holds, so ONLY the
    // well-foundedness floor can reject it. A `Verified` here is the cardinal
    // false-verify the lane was quarantined for. (The WF1 floor is exercised
    // directly on `int_floor_probe` in `loop_decreases_soundness.rs`; this
    // divergent loop is additionally intercepted by the vacuous-truth precheck.)
    assert_not_verified(
        "loop_decreases_soundness_repro.rs",
        "unbounded_negative_measure",
    );
}

#[test]
fn closure_def_side_specs_cannot_poison_the_parent_context() {
    // REINSTATED (isolated child-context def-side check): a def-side-valid,
    // never-called closure spec now soundly VERIFIES — its `R`, `res == BODY`,
    // and `E` are discharged in a discarded child context, contributing nothing
    // to the parent.
    assert_verified("closure_spec_soundness_repro.rs", "def_side_valid_verified");
    // POISON PROBE (unchanged, must NEVER verify): a never-called
    // `requires(false)` closure alongside a parent `assert!(false)`. The
    // closure's contradictory precondition is discharged VACUOUSLY in the
    // discarded child context and never enters the parent's assumption set, so
    // the parent still Counterexamples on its own `assert!(false)`. A parent
    // that VERIFIES here is the cardinal false-verify the lane was quarantined
    // for.
    assert_not_verified(
        "closure_spec_soundness_repro.rs",
        "requires_false_cannot_poison_parent",
    );
}

#[test]
fn broadcast_use_file_path_is_sound() {
    // REINSTATED (un-quarantine #4, forward-only monotone activation): a grouped
    // broadcast lemma activated by a `broadcast_use!(g)` that PRECEDES the
    // assertion now soundly VERIFIES — each use lowers to a body-ordered
    // `BroadcastUse` marker and the encoder gate admits the grouped axiom only
    // for obligations at or after the marker (position-aware, not a
    // function-global set). Full positive/adversarial coverage lives in
    // `broadcast_use_soundness.rs`.
    assert_verified(
        "broadcast_use_soundness_repro.rs",
        "grouped_broadcast_activated",
    );
    // PERMANENT NEGATIVE (must NEVER verify): the `assert bcg(5) > 0` PRECEDES
    // the `broadcast_use!(bc_guarded_group)`, so at the assert's body position
    // the group is not yet active and `bcg` is opaque. A `Verified` here is the
    // cardinal RETROACTIVE false-verify the lane was quarantined for — a
    // function-global positionless set would produce exactly that. (Also
    // asserted, as a Counterexample, in `broadcast_use_soundness.rs`.)
    assert_not_verified(
        "broadcast_use_soundness_repro.rs",
        "broadcast_use_cannot_activate_retroactively",
    );
}

#[test]
fn generic_inherent_method_monomorphization_is_sound() {
    // REINSTATED (un-quarantine #2, per-instantiation monomorphization): a
    // generic inherent method (`impl<A> AWrapper<A> { fn take(self) -> A }`)
    // called on a CONCRETE receiver (`AWrapper::<u64>`) is now monomorphized
    // (`A -> u64`) and its conformance-checked contract applied at the call
    // site, so `w.take() == value` soundly VERIFIES. (Full positive/adversarial
    // coverage lives in `a2_generic_soundness.rs`.)
    assert_verified("a2_generic_soundness_repro.rs", "take_pos");
    // PERMANENT NEGATIVE (must NEVER verify): two same-leaf `Wrapper<A>` impls in
    // modules collision_a/collision_b declare the same `pick` (`self.first` vs
    // `self.second`). The registry collision guard drops BOTH — no concrete
    // `Wrapper_u64__pick` symbol is defined by either body — so a caller of
    // `collision_b::Wrapper::<u64>` asserting `w.pick() == first` fails closed. A
    // Verified here is the cardinal cross-contamination false-verify the guard
    // exists to prevent. (Also asserted permanently in `a2_generic_soundness.rs`.)
    assert_not_verified(
        "a2_generic_soundness_repro.rs",
        "same_leaf_method_names_cannot_cross_contaminate",
    );
}
