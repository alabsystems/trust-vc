// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Fixture for the extensionality bridge regression test
// (`tests/extensionality_bridge.rs`). Parsed and verified through
// `verify_function_from_file`, exactly like the upstream `maps.rs`/`sets.rs`
// strict-eq ports — these functions are NOT compiled as a test target.
//
// The bridge: a discharged extensional equality (`=~=`/`ext_eq!`) makes the
// raw/strict equality (`===`/`strict_eq!`) of the same operands available to
// later obligations, mirroring Verus's auto-`ext_equal`. The strict `===`
// surface stays strict — it discharges ONLY once the extensional formula is
// independently entailed (a verified earlier `=~=`, or a genuine hypothesis).

use trust_vc_types::Set;

// ── POSITIVE: the upstream sets.rs test1 shape ──────────────────────────────
// Two symbolic sets with equal membership: prove `=~=`, then `===`. Before the
// bridge the trailing strict-eq was Unknown; the proven `=~=` is now carried
// forward and the bridge turns it into raw equality.
#[trust_vc::requires(forall(|e: i32| s.contains(e) == t.contains(e)))]
#[trust_vc::ensures(true)]
fn proven_exteq_then_strict(s: Set<i32>, t: Set<i32>) {
    trust_vc::assert!(trust_vc::ext_eq!(s, t));
    trust_vc::assert!(trust_vc::strict_eq!(s, t));
}

// POSITIVE: strict `===` discharged directly from a genuine extensional-
// equality hypothesis (membership equality), without an intermediate `=~=`.
#[trust_vc::requires(forall(|e: i32| s.contains(e) == t.contains(e)))]
#[trust_vc::ensures(true)]
fn strict_from_membership_hypothesis(s: Set<i32>, t: Set<i32>) {
    trust_vc::assert!(trust_vc::strict_eq!(s, t));
}

// POSITIVE (task's literal `==` shape): two concrete sets built two ways. Both
// asserts verify. (NOTE: plain collection `==` is already extensional, so this
// shape verified pre-bridge too; included for completeness.)
#[trust_vc::ensures(true)]
fn concrete_exteq_then_eq() {
    trust_vc::assert!(trust_vc::ext_eq!(
        Set::<u32>::empty().insert(0u32).insert(1u32),
        Set::<u32>::empty().insert(1u32).insert(0u32)
    ));
    trust_vc::assert!(
        Set::<u32>::empty().insert(0u32).insert(1u32)
            == Set::<u32>::empty().insert(1u32).insert(0u32)
    );
}

// ── SOUNDNESS #1: no established `=~=`, provably-distinct sets ───────────────
// `s` contains 5, `t` does not, so they are NOT equal. The bridge must NOT
// fabricate equality: strict `===` must fail closed (no `=~=` was established,
// and the implication's premise is false).
#[trust_vc::requires(s.contains(5i32))]
#[trust_vc::requires(!t.contains(5i32))]
#[trust_vc::ensures(true)]
fn strict_distinct_no_exteq(s: Set<i32>, t: Set<i32>) {
    trust_vc::assert!(trust_vc::strict_eq!(s, t));
}

// SOUNDNESS #1b: strict `===` over unconstrained symbolic sets, no hypothesis
// at all. Must fail closed.
#[trust_vc::ensures(true)]
fn strict_no_hypothesis(s: Set<i32>, t: Set<i32>) {
    trust_vc::assert!(trust_vc::strict_eq!(s, t));
}

// ── SOUNDNESS #2: `=~=` over not-extensionally-equal sets must FAIL at `=~=` ─
// `s` contains 5, `t` does not, so `s =~= t` is false and must be rejected; the
// following strict `===` must therefore never become available.
#[trust_vc::requires(s.contains(5i32))]
#[trust_vc::requires(!t.contains(5i32))]
#[trust_vc::ensures(true)]
fn false_exteq_then_strict(s: Set<i32>, t: Set<i32>) {
    trust_vc::assert!(trust_vc::ext_eq!(s, t));
    trust_vc::assert!(trust_vc::strict_eq!(s, t));
}

// Control: the strict-eq assert in isolation over the distinct sets, so the
// soundness test can attribute a failure to the strict-eq obligation itself
// rather than to a preceding step.
#[trust_vc::requires(s.contains(5i32))]
#[trust_vc::requires(!t.contains(5i32))]
#[trust_vc::ensures(true)]
fn false_exteq_only(s: Set<i32>, t: Set<i32>) {
    trust_vc::assert!(trust_vc::ext_eq!(s, t));
}
