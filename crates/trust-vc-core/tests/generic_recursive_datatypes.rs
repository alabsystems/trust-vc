// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! End-to-end (source-catalog path, via `verify_function_from_file`) coverage
//! for GENERIC self-recursive datatypes as spec-fn parameters/types — a
//! user-defined `enum GList<T>` / `enum GTree<T>`, plus the builtin `List<i32>` /
//! `Tree<i32>` consumed as source-parsed spec-fn parameters.
//!
//! This is the generic companion to `user_recursive_datatypes.rs` (monomorphic
//! Nat / IntList / IntTree). A generic recursive datatype is monomorphized at
//! the USE SITE to a per-instantiation carrier with CONCRETE field sorts
//! (`GList<i32>`: `GCons(head: i32, tail: RecursiveRef("GList<i32>"))`), exactly
//! how the builtin `List<i32>` already substitutes a concrete element sort. The
//! self-recursion edge stays a SELF-only `RecursiveRef` to that per-instantiation
//! carrier, so the `dt_size` acyclicity invariant and the structural-decreases
//! termination gate (#99 / #100) apply to each instantiation verbatim.
//!
//! This file is FIRST a soundness battery — generic recursive datatypes are a
//! prime false-`Verified` risk:
//!   * TRUE structural claims verify, including structural-descent over a generic
//!     recursive datatype (`glen` firing its unfolding axiom twice) and the
//!     positive `dt_size` acyclicity witness (`xs != GCons(h, xs)`);
//!   * FALSE claims are NEVER `Verified` (Counterexample or fail-closed Unknown);
//!   * a CYCLIC claim (`xs == GCons(h, xs)`, or assuming it then proving `0 == 1`)
//!     is NEVER `Verified` — `dt_size` refutes the finite cycle;
//!   * an ill-founded generic recursive spec fn (no `#[decreases]`) stays
//!     uninterpreted — `0 == 1` is not provable through it;
//!   * DISTINCT instantiations (`GList<i32>` vs `GList<bool>`) are DISTINCT
//!     carriers — they verify independently and are never collapsed; using one
//!     generic spec fn at two instantiations in a single function stays
//!     fail-closed (no false `Verified`);
//!   * a generic no-base-case enum, generic mutual recursion, and a generic
//!     negative-position (`fn(Self)`) field all stay FAIL-CLOSED.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn path() -> String {
    format!(
        "{}/tests/data/generic_recursive_datatypes.rs",
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
fn true_generic_structural_claims_verify() {
    for func in [
        "t_glen_zero",      // glen::<i32>(GNil) == 0
        "t_glen_one",       // glen(GCons(5i32, GNil)) == 1 (generic + structural decreases)
        "t_glen_two",       // glen(GCons(5, GCons(6, GNil))) == 2 (axiom fires twice)
        "t_glen_bool_one",  // glen(GCons(true, GNil)) == 1 (distinct GList<bool> carrier)
        "t_gis_empty_nil",  // gis_empty::<i32>(GNil) == true
        "t_gis_empty_cons", // gis_empty(GCons(9i32, GNil)) == false (selector)
        "t_gtree_disjoint", // GBranch(..) != GLeaf(..) (native disjointness)
        "t_blen_one",       // builtin List<i32>: blen(Cons(5, Nil)) == 1
        "t_troot_leaf",     // builtin Tree<i32>: troot(Leaf(7)) == 7
    ] {
        assert!(
            matches!(ok(func), VerifyResult::Verified),
            "TRUE generic structural claim {func} must Verify, got {:?}",
            ok(func)
        );
    }
}

/// The positive `dt_size` acyclicity witness over a GENERIC datatype: no
/// `GList<i32>` equals its own `GCons`, so `xs != GCons(h, xs)` is VALID and must
/// Verify. If this regresses, the acyclicity belt failed to transfer to the
/// per-instantiation carrier.
#[test]
fn generic_acyclicity_is_provable() {
    assert!(
        matches!(ok("t_gacyclic"), VerifyResult::Verified),
        "xs != GCons(h, xs) over GList<i32> must Verify via dt_size acyclicity, got {:?}",
        ok("t_gacyclic")
    );
}

// ───────────────────── FALSE → never Verified (sound) ──────────────────────

#[test]
fn false_generic_claims_are_never_verified() {
    for func in ["f_glen_one_wrong", "f_glen_zero_wrong", "f_gis_empty_wrong"] {
        let result = ok(func);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "UNSOUND: false generic claim {func} must NOT Verify, got {result:?}"
        );
    }
}

// ─────────── CYCLIC → never Verified (dt_size refutes finite cycles) ────────

#[test]
fn generic_cyclic_claims_are_never_verified() {
    let asserted = ok("c_gassert_cycle");
    assert!(
        !matches!(asserted, VerifyResult::Verified),
        "UNSOUND: asserting xs == GCons(h, xs) must NOT Verify (no GList is its own \
         GCons), got {asserted:?}"
    );

    // Assuming the cycle then trying to prove `0 == 1`: the engine must detect the
    // contradictory (dt_size-impossible) assumption rather than build a cyclic
    // model and prove an arithmetic falsehood.
    let assumed = ok("c_gcycle_assume_then_false");
    assert!(
        !matches!(assumed, VerifyResult::Verified),
        "UNSOUND: assuming xs == GCons(h, xs) must NOT yield a real Verified for 0 == 1, \
         got {assumed:?}"
    );
}

// ───── ill-founded generic recursive spec fn (no #[decreases]) → no axiom ────

#[test]
fn ill_founded_generic_recursion_proves_no_false() {
    let result = ok("g_glen_bad_no_false");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "UNSOUND: glen_bad (generic recursive spec fn with NO #[decreases]) must stay \
         uninterpreted; 0 == 1 must NOT verify through it, got {result:?}"
    );
}

// ─── DISTINCT instantiations stay distinct carriers (never collapsed) ────────

/// `GList<i32>` and `GList<bool>` are DISTINCT per-instantiation carriers: each
/// verifies independently (covered by `true_generic_structural_claims_verify`'s
/// `t_glen_one` + `t_glen_bool_one`). Using the SAME generic spec fn at BOTH
/// instantiations within a single function cannot be monomorphized to one helper
/// symbol, so it stays fail-closed — `0 == 1` must NOT verify through it.
///
/// The conflict is detected EARLY (the function builds a self-recursive generic
/// datatype at two distinct instantiations) and surfaced as a CLEAN
/// `VerifyResult::Error` before any obligation is encoded. Previously the
/// per-instantiation carrier mismatch leaked all the way into the backend as an
/// `apply` sort mismatch that was swallowed and mis-reported as
/// `Unknown { category: SolverPanic }`; assert it is now a clean fail-close with
/// no swallowed panic.
#[test]
fn distinct_instantiations_do_not_collapse() {
    use trust_vc_core::UnknownCategory;
    let result = ok("t_conflict_no_false");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "UNSOUND: a generic spec fn used at two instantiations in one function must \
         stay fail-closed; 0 == 1 must NOT verify, got {result:?}"
    );
    // Clean fail-close: a `VerifyResult::Error`, never a swallowed `SolverPanic`.
    assert!(
        matches!(result, VerifyResult::Error { .. }),
        "two-instantiation conflict must fail closed as a clean Error, got {result:?}"
    );
    assert!(
        !matches!(
            result,
            VerifyResult::Unknown {
                category: UnknownCategory::SolverPanic,
                ..
            }
        ),
        "two-instantiation conflict must NOT surface a swallowed SolverPanic, got {result:?}"
    );
}

// ───────────────────────── fail-closed generic datatypes ───────────────────

/// A generic no-base-case enum (`GStream<T> { GMore(T, Box<GStream<T>>) }`),
/// generic mutual recursion (`GEven<T>` / `GOdd<T>`), and a generic
/// negative-position field (`GFn(fn(GNegPos<T>) -> T)`) must all stay
/// fail-closed: the datatype is never registered, so a spec fn taking one as a
/// parameter fails extraction/encoding rather than verifying.
#[test]
fn unsupported_generic_recursion_stays_fail_closed() {
    for func in ["use_gstream", "use_geven", "use_gnegpos"] {
        let result = verdict(func);
        let is_fail_closed = match &result {
            Err(_) => true,
            Ok(VerifyResult::Error { .. }) => true,
            _ => false,
        };
        assert!(
            is_fail_closed,
            "{func} must fail closed (generic no-base-case / mutual / negative-position \
             recursion is unsupported), got {result:?}"
        );
        assert!(
            !matches!(result, Ok(VerifyResult::Verified)),
            "UNSOUND: {func} must never Verify, got {result:?}"
        );
    }
}
