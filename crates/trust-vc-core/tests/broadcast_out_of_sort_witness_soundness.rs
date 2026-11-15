// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CARDINAL FALSE-VERIFY REGRESSION: an out-of-sort broadcast-lemma ground
//! instance poisons the consumer query.
//!
//! A broadcast `forall` is instantiated at ground witnesses drawn from three
//! sources — fixed type boundaries, literal constants in the premise text, and
//! scalars harvested from a candidate SAT model
//! (`build_premise_ground_instances`). Each instance is asserted into the query
//! and is sound ONLY because it is a universal instantiation of the lemma.
//!
//! That argument silently required the substituted value to be a value of the
//! bound variable's sort, and nothing enforced it. A model witness harvested
//! from an unrelated `u64` term (`2^64-1`) was substituted for a `u8` bound
//! variable. `encode_int_lit` deliberately does NOT wrap an out-of-range literal
//! (wrapping would silently redefine the constant — the casts-bitvec cluster);
//! it WIDENS. So the trivially-true `x <= 255u8` was asserted as the 64-bit
//! comparison `2^64-1 <= 255` — a FALSE ground fact. A false premise entails
//! everything, so the negated goal went UNSAT and the obligation was reported
//! `Verified`.
//!
//! The fixture makes that visible the only way that admits no argument: three
//! MUTUALLY CONTRADICTORY postconditions on the same body, over an `#[opaque]`
//! spec fn that is never revealed. At most one of them can be true; all three
//! verified. `no_lemma_control` is the control — remove the lemma and the same
//! three goals are refuted, so the lemma (not the opacity, not the goal shape)
//! is what turned them.
//!
//! NARROWNESS. The fix filters candidate witnesses to those that inhabit the
//! bound variable's sort — it does not disable broadcast lemmas, drop
//! interpreted-op triggers, or stop instantiating. `pin_*` below are a
//! narrow-typed (`u8`) lemma with an interpreted-op trigger that must still
//! fire and prove its goals, plus a discriminator that must still fail. If a
//! future "fix" buys soundness by rejecting more, the pins go red.

use trust_vc_core::{verify_function_from_file, VerifyResult};

const REPRO: &str = "broadcast_out_of_sort_witness_repro.rs";
const CONTROL: &str = "broadcast_out_of_sort_witness_control.rs";

fn fixture(name: &str) -> String {
    format!("{}/tests/data/{name}", env!("CARGO_MANIFEST_DIR"))
}

/// The on-disk VC cache stores only `Verified` results and survives
/// `cargo clean -p`. A soundness probe asserting a NON-verified verdict must
/// never trust it: one stale `Verified` written by a pre-fix binary would mask
/// the regression forever.
fn verify_in(file: &str, function: &str) -> VerifyResult {
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(&fixture(file), function)
            .unwrap_or_else(|err| panic!("`{function}` failed to extract: {err:?}"))
    })
}

fn verify(function: &str) -> VerifyResult {
    verify_in(REPRO, function)
}

fn assert_not_verified(function: &str) {
    if let VerifyResult::Verified = verify(function) {
        panic!("SOUNDNESS BREACH: `{function}` must NOT verify — `h` is opaque and never revealed");
    }
}

fn assert_verified(function: &str) {
    match verify(function) {
        VerifyResult::Verified => {}
        other => panic!("NARROWNESS PIN BROKEN: `{function}` should VERIFY, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// The defect. Each of these alone is unprovable; the trio is contradictory.
// ---------------------------------------------------------------------------

#[test]
fn opaque_result_is_not_forty_two() {
    assert_not_verified("fv_forty_two");
}

#[test]
fn opaque_result_is_not_forty_three() {
    assert_not_verified("fv_forty_three");
}

#[test]
fn opaque_result_is_not_zero() {
    assert_not_verified("fv_zero");
}

/// The three goals above are pairwise contradictory, so this is the statement
/// the defect actually violated: whatever `h(0)` is, at most ONE of
/// `== 42`, `== 43`, `== 0` can hold. Asserted jointly so a partial regression
/// (say, only `fv_zero` flipping back) still reads as what it is.
#[test]
fn at_most_one_contradictory_goal_verifies() {
    let verified: Vec<&str> = ["fv_forty_two", "fv_forty_three", "fv_zero"]
        .into_iter()
        .filter(|function| matches!(verify(function), VerifyResult::Verified))
        .collect();
    assert!(
        verified.len() <= 1,
        "SOUNDNESS BREACH: mutually contradictory goals both verified: {verified:?} \
         — the assumption context is inconsistent"
    );
}

/// THE CONTROL. Same three goals, same opaque `h`, lemma removed. They were
/// refuted before the fix and are refuted after it — so the lemma, not the goal
/// shape and not `h`'s opacity, is what turned them. Without this the suite
/// could not distinguish "the fix works" from "these goals never verified".
#[test]
fn control_without_the_lemma_refutes_all_three() {
    for function in ["fv_forty_two", "fv_forty_three", "fv_zero"] {
        if verify_in(CONTROL, function) == VerifyResult::Verified {
            panic!(
                "CONTROL BROKEN: `{function}` verified with NO lemma in scope — the repro no \
             longer isolates the broadcast lemma"
            )
        }
    }
}

// ---------------------------------------------------------------------------
// NARROWNESS PINS — the lemma must still work.
// ---------------------------------------------------------------------------

#[test]
fn narrow_lemma_still_fires_at_type_boundaries() {
    // `hh` is opaque; these are provable ONLY through the broadcast lemma's
    // ground instantiation at the u8 boundary witnesses 0, 1 and 255 — the very
    // witness battery the fix filters.
    assert_verified("pin_boundary_zero");
    assert_verified("pin_boundary_one");
    assert_verified("pin_boundary_max");
}

#[test]
fn narrow_lemma_does_not_prove_a_false_goal() {
    // Discriminator for the pins above: the lemma fires, but `hh(0) == 1` is
    // false. If this ever verifies, the pins are passing on a contradiction
    // rather than on the lemma.
    assert_not_verified("pin_discriminator_wrong_value");
}
