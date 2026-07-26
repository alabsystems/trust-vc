// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! End-to-end (source-catalog path, via `verify_function_from_file`) coverage
//! for USER-DEFINED self-recursive datatypes as spec-fn parameters/types —
//! Peano `Nat`, a cons-`IntList`, and a binary `IntTree`, all declared with the
//! recursion threaded through `Box<Self>`.
//!
//! The source→IR bridge (see `vc_extraction.rs::is_self_reference` /
//! `to_datatype_type_inner` and the `from_item_enum` self-reference guard
//! removal) materialises a self-referential variant field as a
//! `TrustVcType::RecursiveRef` to the owning carrier — exactly the IR shape the
//! builtin `List`/`Tree` already use. The encoder's native datatype theory plus
//! the `dt_size` acyclicity invariant then apply unchanged.
//!
//! This file is FIRST a soundness battery. Recursive datatypes are a prime
//! false-`Verified` risk (cyclic models: `n == Succ(n)`), so every adversarial
//! direction is pinned:
//!   * TRUE structural claims verify (selector/constructor/match/disjointness,
//!     and `n != Succ(n)` — the positive `dt_size` acyclicity witness);
//!   * FALSE claims are NEVER `Verified` (Counterexample or fail-closed Unknown);
//!   * a CYCLIC claim (`n == Succ(n)`, or assuming it then proving `0 == 1`) is
//!     NEVER `Verified` — `dt_size` refutes the finite cycle;
//!   * a no-base-case enum, mutual recursion, and a negative-position
//!     (`fn(Self)`) field all stay FAIL-CLOSED (extraction/encoding Error);
//!   * an ill-founded recursive spec fn (no `#[decreases]`) stays uninterpreted
//!     (no unsound defining axiom — `0 == 1` is not provable through it).
//!
//! KNOWN pre-existing gap (NOT a regression, NOT unsoundness): a recursive spec
//! fn WITH `#[decreases]` over a datatype param (`depth(Zero) == 0`) returns
//! `Unknown`. The decreases termination gate / measure shaper is not yet
//! `dt_size`-aware for structural datatype measures, and the same goal over the
//! BUILTIN `List`/`Tree` is `Unknown` too. It is pinned here as a non-`Verified`
//! witness so a future fix is observable and so it can never silently become a
//! false `Verified`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn path() -> String {
    format!(
        "{}/tests/data/user_recursive_datatypes.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> Result<VerifyResult, trust_vc_core::TrustVcError> {
    verify_function_from_file(&path(), func)
}

fn ok(func: &str) -> VerifyResult {
    verdict(func).unwrap_or_else(|e| panic!("extract/verify {func} failed: {e:?}"))
}

// ───────────────────────────── TRUE → Verified ─────────────────────────────

#[test]
fn true_structural_claims_verify() {
    for func in [
        "t_is_zero_zero",      // is_zero(Zero) == true
        "t_is_zero_succ",      // is_zero(Succ(Zero)) == false (Box::new transparent)
        "t_head_or_cons",      // head_or(Cons(5, Nil), 0) == 5 (selector)
        "t_head_or_nil",       // head_or(Nil, 7) == 7
        "t_variants_disjoint", // Succ(Zero) != Zero (native disjointness)
        "t_tree_disjoint",     // Branch(..) != Leaf(..)
    ] {
        assert!(
            matches!(ok(func), VerifyResult::Verified),
            "TRUE structural claim {func} over a user recursive datatype must Verify, got {:?}",
            ok(func)
        );
    }
}

/// The positive `dt_size` acyclicity witness: `n != Succ(n)` is VALID for every
/// `Nat` (size strictly increases under `Succ`), so it must Verify. If this ever
/// regresses to non-`Verified`, the acyclicity belt has been weakened.
#[test]
fn acyclicity_is_provable() {
    assert!(
        matches!(ok("t_acyclic"), VerifyResult::Verified),
        "n != Succ(n) must Verify via dt_size acyclicity, got {:?}",
        ok("t_acyclic")
    );
}

// ───────────────────── FALSE → never Verified (sound) ──────────────────────

#[test]
fn false_claims_are_never_verified() {
    for func in ["f_is_zero_wrong", "f_head_or_wrong", "f_variants_equal"] {
        let result = ok(func);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "UNSOUND: false claim {func} must NOT Verify, got {result:?}"
        );
    }
    // The directly-refutable one (disjoint variants) is a definite Counterexample.
    assert!(
        matches!(ok("f_variants_equal"), VerifyResult::Counterexample { .. }),
        "Succ(Zero) == Zero must be a Counterexample, got {:?}",
        ok("f_variants_equal")
    );
}

// ─────────── CYCLIC → never Verified (dt_size refutes finite cycles) ────────

#[test]
fn cyclic_claims_are_never_verified() {
    // Asserting the cyclic structure directly.
    let asserted = ok("c_assert_cycle");
    assert!(
        !matches!(asserted, VerifyResult::Verified),
        "UNSOUND: asserting n == Succ(n) must NOT Verify (no Nat is its own \
         successor), got {asserted:?}"
    );

    // Assuming the cycle then trying to prove `0 == 1` about an unrelated value.
    // The engine must not build a cyclic model and prove arithmetic falsehoods;
    // it detects the contradictory assumption (dt_size) and returns a
    // non-`Verified` verdict.
    let assumed = ok("c_cycle_assume_then_false");
    assert!(
        !matches!(assumed, VerifyResult::Verified),
        "UNSOUND: assuming n == Succ(n) must NOT yield a real Verified for 0 == 1, \
         got {assumed:?}"
    );
}

// ───── ill-founded recursive spec fn (no #[decreases]) → no unsound axiom ────

#[test]
fn ill_founded_recursion_proves_no_false() {
    let result = ok("g_bad_depth_no_false");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "UNSOUND: bad_depth (recursive spec fn with NO #[decreases]) must stay \
         uninterpreted; 0 == 1 must NOT verify through it, got {result:?}"
    );
}

// ───────────────────────── fail-closed datatypes ───────────────────────────

/// A no-base-case enum (`Stream { More(Box<Stream>) }`), mutual recursion
/// (`EvenNat`/`OddNat`), and a negative-position field (`Fn(fn(NegPos) -> i32)`)
/// must all stay fail-closed: the datatype is never registered, so a spec fn
/// taking one as a parameter fails extraction/encoding rather than verifying.
#[test]
fn unsupported_recursion_stays_fail_closed() {
    for func in ["use_stream", "use_even", "use_negpos"] {
        let result = verdict(func);
        let is_fail_closed = match &result {
            Err(_) => true,
            Ok(VerifyResult::Error { .. }) => true,
            _ => false,
        };
        assert!(
            is_fail_closed,
            "{func} must fail closed (no-base-case / mutual / negative-position \
             recursion is unsupported), got {result:?}"
        );
        assert!(
            !matches!(result, Ok(VerifyResult::Verified)),
            "UNSOUND: {func} must never Verify, got {result:?}"
        );
    }
}

// ───────────── recursive #[decreases]: pinned non-Verified witness ──────────

/// Structural-descent `#[decreases]` is now `dt_size`-aware: a recursive spec fn
/// whose measure is its recursive-datatype parameter earns its defining
/// (unfolding) axiom once the termination gate proves the matched structural
/// child strictly shrinks `dt_size`. `depth(Zero) == 0` therefore VERIFIES (it
/// was previously a pinned `Unknown` completeness gap). The broader
/// structural-descent battery — deeper goals, false goals, and the
/// self/non-child/no-base axiom-suppression cases (#50) — lives in
/// `recursive_structural_decreases.rs`.
#[test]
fn recursive_decreases_over_datatype_verifies_base_case() {
    let result = ok("depth_zero_is_zero");
    assert!(
        matches!(result, VerifyResult::Verified),
        "depth(Zero) == 0 must Verify now that structural decreases is dt_size-aware, \
         got {result:?}"
    );
}
