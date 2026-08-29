// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pins for the DENOTATIONAL static-length fold
//! `AstExpressionParser::finite_seq_literal_len`, and specifically for its
//! EMPTY-CONSTRUCTOR arm.
//!
//! The fold answers "what is this Seq's length, in EVERY model?" for a chain
//! whose length is fixed by construction. It is a HINT: `encode_seq_contains`
//! uses it to pick a ground fixed-array unroll over a quantified
//! `int2bv`/`bv2int` existential, `encode_push` uses it to keep a length
//! literal, and the F3 point-interval pin `finite_len_pin_binding` consumes it.
//! It never replaces an obligation — `encode_subrange` still pushes
//! `0 <= start`, `start <= end` and `end <= len` into `overflow_checks`
//! regardless of what the fold answers.
//!
//! WHAT IS PINNED. The constructor arm's gate is the `Seq(_)` RETURN TYPE, not
//! the symbol's spelling. A `name.contains("Seq_")` substring conjunct used to
//! stand in for it and rejected the most common exec root there is:
//! `ir_lowering/dispatch/collections/constructors.rs` renders the SOURCE PATH,
//! so `Vec::<u32>::new` mints `__trust_vc_collection_ctor_Vec_u32_new` with no
//! "Seq" in it, while `control_flow.rs` renders the TARGET type and would have
//! produced `..._ctor_Vec_Seq_u32_new`. An exec
//! `let mut v: Vec<u32> = Vec::new();` is turbofished from its annotation
//! before lowering, so it lands in the first renderer. Rejected, the root
//! reports "length unknown" and every downstream fold falls back to a
//! quantified encoding.
//!
//! Both directions are pinned. The verifying direction shows the fold is
//! reached; the CARDINAL refusing direction shows the ground unroll it enables
//! still refutes false claims — a widened length fold that made a false
//! `contains` or a wrong `len()` verify would be caught here.
//!
//! Measured at trust-vc 7eb96392 / ay f1f93ed25, prebuilt binaries,
//! `--test-threads=1`, arms interleaved, 3 reps, on a heavily loaded box
//! (1-minute average 24-74): with the substring gate restored
//! `tests/vec_pop_capability.rs` costs 213.90 / 276.20 / 253.05 s with 32
//! published-but-unvalidated models per rep; without it, 3.49 / 3.21 / 3.16 s
//! with 0. This suite itself goes 83.72 / 84.69 / 87.52 s (6 passed, 1 failed)
//! to 0.09 / 0.09 / 0.10 s (7 passed).

use std::time::{Duration, Instant};
use trust_vc_core::{verify_function_from_file, VerifyResult};

/// House pattern (see `vec_pop_capability.rs`): a pid-qualified fixture in the
/// system temp dir, removed afterwards, so the suite is CWD-independent and
/// two concurrent runs cannot collide.
fn verify(code: &str, name: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_seqfold_{}_{}.rs", std::process::id(), name));
    std::fs::write(&p, code).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), name).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

fn assert_verified(code: &str, name: &str) {
    let r = verify(code, name);
    assert!(
        matches!(r, VerifyResult::Verified),
        "{name}: a claim entailed by the static length fold must VERIFY, got {r:?}"
    );
}

/// CARDINAL direction: never a false `Verified`. `Counterexample`, `NotProved`
/// and `Unknown` are all acceptable refusals; only `Verified` is a bug.
fn assert_not_verified(code: &str, name: &str) {
    let r = verify(code, name);
    assert!(
        !matches!(r, VerifyResult::Verified),
        "{name}: a FALSE claim must never verify, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// The constructor arm's gate is `return_ty`, not the symbol's spelling.
// ---------------------------------------------------------------------------

/// The turbofish `Vec::<u32>::new()` mints `..._ctor_Vec_u32_new` — a name with
/// no "Seq" in it — while denoting the empty `Seq<u32>`. With a
/// `name.contains("Seq_")` gate the root's length is unknown, so
/// `encode_seq_contains` falls to its QUANTIFIED `int2bv`/`bv2int` existential
/// instead of the ground fixed-array unroll.
#[test]
fn turbofish_vec_new_push_chain_contains_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn turbofish_vec_new_push_chain_contains_verifies() {
    trust_vc::assert!(
        Vec::<u32>::new().push(1u32).push(2u32).push(3u32).push(4u32).push(5u32).contains(3u32)
    );
}
"#,
        "turbofish_vec_new_push_chain_contains_verifies",
    );
}

/// CARDINAL companion: the ground unroll the widened gate enables must still
/// REFUTE a value that is not in the chain.
#[test]
fn turbofish_vec_new_absent_element_does_not_verify() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn turbofish_vec_new_absent_element_does_not_verify() {
    trust_vc::assert!(Vec::<u32>::new().push(7u32).contains(8u32));
}
"#,
        "turbofish_vec_new_absent_element_does_not_verify",
    );
}

#[test]
fn turbofish_vec_new_push_chain_length_verifies() {
    assert_verified(
        r#"
#[trust_vc::ensures(true)]
fn turbofish_vec_new_push_chain_length_verifies() {
    trust_vc::assert!(Vec::<u32>::new().push(1u32).push(2u32).len() == 2int);
}
"#,
        "turbofish_vec_new_push_chain_length_verifies",
    );
}

/// CARDINAL: the fold answers 0 for the root, so the chain's length is exactly
/// 2. A claim of 3 must refuse.
#[test]
fn turbofish_vec_new_wrong_length_does_not_verify() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn turbofish_vec_new_wrong_length_does_not_verify() {
    trust_vc::assert!(Vec::<u32>::new().push(1u32).push(2u32).len() == 3int);
}
"#,
        "turbofish_vec_new_wrong_length_does_not_verify",
    );
}

/// CARDINAL: the widened gate must not fold the EMPTY constructor's length to
/// anything but 0.
#[test]
fn turbofish_vec_new_empty_nonzero_length_does_not_verify() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn turbofish_vec_new_empty_nonzero_length_does_not_verify() {
    trust_vc::assert!(Vec::<u32>::new().len() == 1int);
}
"#,
        "turbofish_vec_new_empty_nonzero_length_does_not_verify",
    );
}

/// CARDINAL / VACUITY probe: a true folded fact conjoined with a plain
/// falsehood must still refuse. A fold that poisoned the context (rather than
/// supplying a hint) would verify this.
#[test]
fn turbofish_vec_new_fold_does_not_poison_the_context() {
    assert_not_verified(
        r#"
#[trust_vc::ensures(true)]
fn turbofish_vec_new_fold_does_not_poison_the_context() {
    trust_vc::assert!(Vec::<u32>::new().push(1u32).len() == 1int && 0int == 1int);
}
"#,
        "turbofish_vec_new_fold_does_not_poison_the_context",
    );
}

/// COST PIN, and the pre/post DISCRIMINATOR for this change.
/// `Vec::<T>::new()` and `Seq::<T>::empty()` denote the same empty sequence, so
/// the IDENTICAL claim must not cost wildly different amounts of wall clock.
/// With the `name.contains("Seq_")` substring gate restored this test FAILS:
/// measured at trust-vc 7eb96392 / ay f1f93ed25, the turbofish spelling took
/// 17.73s against 87.8ms for the ghost spelling — a ~200x spread bought by
/// nothing but the symbol's spelling — and it failed on all three interleaved
/// reps at a 1-minute load average of 61 to 74.
///
/// The bar is a RATIO against the ghost spelling measured in this same process,
/// plus a 1s floor, so it self-scales with machine contention instead of
/// asserting a bare wall clock that a loaded box can trip. That self-scaling
/// is not theoretical: in the measured failing reps the ghost spelling took
/// 87.8ms, so the bar rose to 9.78s, and the 17.73s regression was still
/// caught. With the gate
/// removed both spellings land in the same tens of milliseconds.
#[test]
fn turbofish_spelling_costs_the_same_as_the_ghost_spelling() {
    const GHOST: &str = r#"
#[trust_vc::ensures(true)]
fn ghost_spelling_contains() {
    trust_vc::assert!(
        Seq::<u32>::empty().push(1u32).push(2u32).push(3u32).push(4u32).push(5u32).contains(3u32)
    );
}
"#;
    const TURBOFISH: &str = r#"
#[trust_vc::ensures(true)]
fn turbofish_spelling_contains() {
    trust_vc::assert!(
        Vec::<u32>::new().push(1u32).push(2u32).push(3u32).push(4u32).push(5u32).contains(3u32)
    );
}
"#;
    let t0 = Instant::now();
    let ghost = verify(GHOST, "ghost_spelling_contains");
    let ghost_elapsed = t0.elapsed();

    let t1 = Instant::now();
    let turbofish = verify(TURBOFISH, "turbofish_spelling_contains");
    let turbofish_elapsed = t1.elapsed();

    assert!(
        matches!(ghost, VerifyResult::Verified),
        "ghost spelling must verify, got {ghost:?}"
    );
    assert!(
        matches!(turbofish, VerifyResult::Verified),
        "turbofish spelling must verify, got {turbofish:?}"
    );

    let bar = ghost_elapsed * 100 + Duration::from_secs(1);
    assert!(
        turbofish_elapsed < bar,
        "the turbofish spelling fell off the static-length fold: {turbofish_elapsed:?} \
         (ghost spelling of the same claim: {ghost_elapsed:?}; bar: {bar:?})"
    );
}
