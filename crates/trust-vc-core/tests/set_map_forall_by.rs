// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! End-to-end guards for the upstream `rust_verify_test/tests/sets.rs` `test1`
//! map-over-comprehension `assert ... by` step (#2778).
//!
//! `pos2 = nonneg.map(|i| i + 1)` for `nonneg = Set::new(|i| i >= 0)`. Proving
//! `forall|i| pos2.contains(i) == (i > 0)` needs the per-`i` hint
//! `pos2.contains(i) == nonneg.contains(i - 1)`, which in turn requires the
//! mapped set's forward/reverse image axioms to fire on the *source* set's
//! membership. That only connects when the two occurrences of `nonneg`
//! (standalone and as the map receiver) share ONE backend term — which the pure
//! spec-collection memoization (`AstExpressionParser::pure_collection_cache`)
//! provides.
//!
//! SOUNDNESS is the priority: the wrong-goal / wrong-hint cases below MUST fail
//! closed (never a false `Verified`).

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    let dir = Path::new("target/set_map_forall_by");
    fs::create_dir_all(dir).unwrap();
    let f = dir.join(format!("{name}.rs"));
    fs::write(&f, code).unwrap();
    trust_vc_core::verify_function_from_file(f.to_str().unwrap(), name)
}

fn verified(r: &TrustVcResult<VerifyResult>) -> bool {
    matches!(r, Ok(VerifyResult::Verified))
}

// ───────────────────────── POSITIVE ─────────────────────────

/// The `assert ... by` map step in isolation (the historic blocker): the outer
/// `forall|i| pos2.contains(i) == (i > 0)` discharged via the per-`i` hint.
#[test]
fn pos2_membership_forall_via_hint_verifies() {
    let code = r#"
#[trust_vc::ensures(true)]
fn pos2_membership_forall_via_hint() {
    let nonneg = Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int)));
    let pos2 = nonneg.map(SpecFn::new(|i: int| i + (1 as int)));
    trust_vc::assert_forall_by!(|i: int| pos2.contains(i) == (i > (0 as int)), {
        trust_vc::assert!(pos2.contains(i) == nonneg.contains(i - (1 as int)));
    });
}
"#;
    let r = verify(code, "pos2_membership_forall_via_hint");
    assert!(verified(&r), "test1 map step must verify, got {:?}", r);
}

/// The inner hint alone, for symbolic `i`: `pos2.contains(i) == nonneg.contains(i-1)`.
/// Exercises both image directions: forward (`nonneg[i-1] ⇒ pos2[i]`, needs
/// `(i-1)+1 == i` index congruence) and reverse (`pos2[i] ⇒ nonneg[i-1]`).
#[test]
fn inner_hint_membership_equivalence_verifies() {
    let code = r#"
#[trust_vc::ensures(true)]
fn inner_hint_membership_equivalence() {
    let nonneg = Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int)));
    let pos2 = nonneg.map(SpecFn::new(|i: int| i + (1 as int)));
    trust_vc::assert_forall_by!(|i: int| pos2.contains(i) == nonneg.contains(i - (1 as int)), {
    });
}
"#;
    let r = verify(code, "inner_hint_membership_equivalence");
    assert!(verified(&r), "inner hint must verify, got {:?}", r);
}

/// Upstream `test1` preamble THROUGH the map step: comprehension membership
/// forall, `filter` membership forall, then the `assert ... by` map step. (The
/// trailing bare re-assert of the just-proven forall and the `pos1 =~= pos2` /
/// `pos1 === pos2` extensional/strict-eq steps depend on separate, pre-existing
/// gaps — verified-`assert_by`-fact forwarding and set extensionality — and are
/// not exercised here.)
#[test]
fn test1_preamble_through_map_step_verifies() {
    let code = r#"
#[trust_vc::ensures(true)]
fn test1_preamble_through_map_step() {
    let nonneg = Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int)));
    trust_vc::assert!(forall|i: int| nonneg.contains(i) == (i >= (0 as int)));
    let pos1 = nonneg.filter(SpecFn::new(|i: int| i > (0 as int)));
    trust_vc::assert!(forall|i: int| pos1.contains(i) == (i > (0 as int)));
    let pos2 = nonneg.map(SpecFn::new(|i: int| i + (1 as int)));
    trust_vc::assert_forall_by!(|i: int| pos2.contains(i) == (i > (0 as int)), {
        trust_vc::assert!(pos2.contains(i) == nonneg.contains(i - (1 as int)));
    });
}
"#;
    let r = verify(code, "test1_preamble_through_map_step");
    assert!(
        verified(&r),
        "test1 preamble through map step must verify, got {:?}",
        r
    );
}

// ───────────────────────── SOUNDNESS (must fail closed) ─────────────────────────

/// WRONG outer goal with the TRUE inner hint: `pos2.contains(i) == (i > 1)` is
/// false at `i = 1` (1 is in pos2). Must NOT verify even though the hint is true.
#[test]
fn wrong_goal_with_true_hint_does_not_verify() {
    let code = r#"
#[trust_vc::ensures(true)]
fn wrong_goal_with_true_hint() {
    let nonneg = Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int)));
    let pos2 = nonneg.map(SpecFn::new(|i: int| i + (1 as int)));
    trust_vc::assert_forall_by!(|i: int| pos2.contains(i) == (i > (1 as int)), {
        trust_vc::assert!(pos2.contains(i) == nonneg.contains(i - (1 as int)));
    });
}
"#;
    let r = verify(code, "wrong_goal_with_true_hint");
    assert!(
        !verified(&r),
        "FALSE forall (i>1) must NOT verify, got {:?}",
        r
    );
}

/// WRONG outer goal with NO hint. Must NOT verify (fail closed).
#[test]
fn wrong_goal_no_hint_does_not_verify() {
    let code = r#"
#[trust_vc::ensures(true)]
fn wrong_goal_no_hint() {
    let nonneg = Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int)));
    let pos2 = nonneg.map(SpecFn::new(|i: int| i + (1 as int)));
    trust_vc::assert_forall_by!(|i: int| pos2.contains(i) == (i > (1 as int)), {
    });
}
"#;
    let r = verify(code, "wrong_goal_no_hint");
    assert!(
        !verified(&r),
        "FALSE forall (i>1), no hint, must NOT verify, got {:?}",
        r
    );
}

/// WRONG inner hint: `pos2.contains(i) == nonneg.contains(i + 1)` is false at
/// `i = 0` (0 not in pos2, but nonneg.contains(1) holds). The scoped hint
/// assertion must itself fail closed.
#[test]
fn wrong_inner_hint_does_not_verify() {
    let code = r#"
#[trust_vc::ensures(true)]
fn wrong_inner_hint() {
    let nonneg = Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int)));
    let pos2 = nonneg.map(SpecFn::new(|i: int| i + (1 as int)));
    trust_vc::assert_forall_by!(|i: int| pos2.contains(i) == nonneg.contains(i + (1 as int)), {
    });
}
"#;
    let r = verify(code, "wrong_inner_hint");
    assert!(
        !verified(&r),
        "FALSE inner hint (i+1) must NOT verify, got {:?}",
        r
    );
}

/// Ground soundness: `0` is NOT in `pos2 = { i+1 : i >= 0 } = { y : y >= 1 }`.
/// Asserting membership of an excluded element must fail closed — a direct guard
/// that memoization did not collapse the image set into something over-permissive.
#[test]
fn excluded_ground_member_does_not_verify() {
    let code = r#"
#[trust_vc::ensures(true)]
fn excluded_ground_member() {
    let nonneg = Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int)));
    let pos2 = nonneg.map(SpecFn::new(|i: int| i + (1 as int)));
    trust_vc::assert!(pos2.contains(0 as int));
}
"#;
    let r = verify(code, "excluded_ground_member");
    assert!(
        !verified(&r),
        "0 is not in pos2; membership must NOT verify, got {:?}",
        r
    );
}

// ─────────────────── VERIFIED-assert_by FORWARDING (#2778) ───────────────────

/// The remaining `test1` gap: a `assert ... by` that proves
/// `forall|i| pos2.contains(i) == (i > 0)` followed by a BARE re-assert of the
/// very same forall. The bare re-assert carries no `by`-block, so it can only
/// discharge if the PROVEN `assert_forall_by` conclusion is forwarded as a
/// quantified assumption. With pure-collection memoization the forwarded
/// `forall i. pos2.contains(i) == (i > 0)` shares pos2's backend term with the
/// goal and closes trivially.
#[test]
fn forwarded_forall_reassert_verifies() {
    let code = r#"
#[trust_vc::ensures(true)]
fn forwarded_forall_reassert() {
    let nonneg = Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int)));
    let pos2 = nonneg.map(SpecFn::new(|i: int| i + (1 as int)));
    trust_vc::assert_forall_by!(|i: int| pos2.contains(i) == (i > (0 as int)), {
        trust_vc::assert!(pos2.contains(i) == nonneg.contains(i - (1 as int)));
    });
    trust_vc::assert!(forall|i: int| pos2.contains(i) == (i > (0 as int)));
}
"#;
    let r = verify(code, "forwarded_forall_reassert");
    assert!(
        verified(&r),
        "bare re-assert of the proven forall must verify via forwarding, got {:?}",
        r
    );
}

/// Full upstream `test1` preamble THROUGH the bare re-assert: comprehension
/// membership forall, `filter` membership forall, the `assert ... by` map step,
/// and then the bare `assert(forall|i| pos2.contains(i) == (i > 0))`. (The
/// trailing `pos1 =~= pos2` / `pos1 === pos2` extensional/strict-eq steps still
/// depend on the separate set-extensionality gap and are not exercised here.)
#[test]
fn test1_through_bare_reassert_verifies() {
    let code = r#"
#[trust_vc::ensures(true)]
fn test1_through_bare_reassert() {
    let nonneg = Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int)));
    trust_vc::assert!(forall|i: int| nonneg.contains(i) == (i >= (0 as int)));
    let pos1 = nonneg.filter(SpecFn::new(|i: int| i > (0 as int)));
    trust_vc::assert!(forall|i: int| pos1.contains(i) == (i > (0 as int)));
    let pos2 = nonneg.map(SpecFn::new(|i: int| i + (1 as int)));
    trust_vc::assert_forall_by!(|i: int| pos2.contains(i) == (i > (0 as int)), {
        trust_vc::assert!(pos2.contains(i) == nonneg.contains(i - (1 as int)));
    });
    trust_vc::assert!(forall|i: int| pos2.contains(i) == (i > (0 as int)));
}
"#;
    let r = verify(code, "test1_through_bare_reassert");
    assert!(
        verified(&r),
        "test1 preamble through bare re-assert must verify, got {:?}",
        r
    );
}

// ─────────────── SOUNDNESS of forwarding (must fail closed) ───────────────

/// The forwarded fact is the PROVEN one (`i > 0`), NOT the goal. A bare
/// re-assert of a DIFFERENT forall (`i > 1`) must NOT verify just because a
/// related-but-distinct forall was proven and forwarded. `i = 1` is the
/// witness: `pos2.contains(1)` holds (proven `1 > 0`) but the goal claims it
/// equals `1 > 1 == false`.
#[test]
fn forwarded_proven_forall_does_not_prove_wrong_reassert() {
    let code = r#"
#[trust_vc::ensures(true)]
fn forwarded_proven_forall_wrong_reassert() {
    let nonneg = Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int)));
    let pos2 = nonneg.map(SpecFn::new(|i: int| i + (1 as int)));
    trust_vc::assert_forall_by!(|i: int| pos2.contains(i) == (i > (0 as int)), {
        trust_vc::assert!(pos2.contains(i) == nonneg.contains(i - (1 as int)));
    });
    trust_vc::assert!(forall|i: int| pos2.contains(i) == (i > (1 as int)));
}
"#;
    let r = verify(code, "forwarded_proven_forall_wrong_reassert");
    assert!(
        !verified(&r),
        "wrong re-assert (i>1) must NOT verify from the proven (i>0) forall, got {:?}",
        r
    );
}

/// An `assert ... by` whose `by`-block does NOT discharge the goal must never
/// forward anything: the conclusion is unproven, so it is never pushed to the
/// verified-`assert_by` lane and cannot leak to the bare re-assert. The TRUE
/// forall `i > 0` needs the per-`i` hint; with an EMPTY `by`-block the
/// `assert_forall_by` fails its own obligation, and the function must fail
/// closed (the later bare re-assert never sees a forwarded fact).
#[test]
fn unproven_forall_by_does_not_forward() {
    let code = r#"
#[trust_vc::ensures(true)]
fn unproven_forall_by_no_leak() {
    let nonneg = Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int)));
    let pos2 = nonneg.map(SpecFn::new(|i: int| i + (1 as int)));
    trust_vc::assert_forall_by!(|i: int| pos2.contains(i) == (i > (0 as int)), {
    });
    trust_vc::assert!(forall|i: int| pos2.contains(i) == (i > (0 as int)));
}
"#;
    let r = verify(code, "unproven_forall_by_no_leak");
    assert!(
        !verified(&r),
        "undischarged by-block must not forward; function must fail closed, got {:?}",
        r
    );
}

/// The COMPLETE upstream `test1`, end to end: comprehension/filter membership
/// foralls, the `assert ... by` map step, the bare re-assert of the proven
/// forall (the gap this change closes), AND the trailing `pos1 =~= pos2`
/// (extensional) / `pos1 === pos2` (strict) equalities. `pos1 = { i : i > 0 }`
/// and `pos2 = { i + 1 : i >= 0 } = { y : y >= 1 } = { y : y > 0 }` are equal
/// int-sets, so all steps are genuinely true. With the proven bare re-assert
/// now forwarded, memoized pure-collection terms close the equalities too.
#[test]
fn full_test1_through_extensional_and_strict_eq_verifies() {
    let code = r#"
#[trust_vc::ensures(true)]
fn full_test1() {
    let nonneg = Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int)));
    trust_vc::assert!(forall|i: int| nonneg.contains(i) == (i >= (0 as int)));
    let pos1 = nonneg.filter(SpecFn::new(|i: int| i > (0 as int)));
    trust_vc::assert!(forall|i: int| pos1.contains(i) == (i > (0 as int)));
    let pos2 = nonneg.map(SpecFn::new(|i: int| i + (1 as int)));
    trust_vc::assert_forall_by!(|i: int| pos2.contains(i) == (i > (0 as int)), {
        trust_vc::assert!(pos2.contains(i) == nonneg.contains(i - (1 as int)));
    });
    trust_vc::assert!(forall|i: int| pos2.contains(i) == (i > (0 as int)));
    trust_vc::assert!(pos1 =~= pos2);
    trust_vc::assert!(pos1 === pos2);
}
"#;
    let r = verify(code, "full_test1");
    assert!(
        verified(&r),
        "full test1 must verify end to end, got {:?}",
        r
    );
}

/// SOUNDNESS companion to the full-`test1` witness: in the SAME context, a FALSE
/// extensional equality `pos1 =~= nonneg` (0 is in `nonneg` but not `pos1`) must
/// NOT verify. Guards that the end-to-end pass above is not a vacuous/unsound
/// collapse of distinct sets.
#[test]
fn full_test1_context_false_extensional_eq_does_not_verify() {
    let code = r#"
#[trust_vc::ensures(true)]
fn full_test1_false_exteq() {
    let nonneg = Set::<int>::new(SpecFn::new(|i: int| i >= (0 as int)));
    let pos1 = nonneg.filter(SpecFn::new(|i: int| i > (0 as int)));
    let pos2 = nonneg.map(SpecFn::new(|i: int| i + (1 as int)));
    trust_vc::assert_forall_by!(|i: int| pos2.contains(i) == (i > (0 as int)), {
        trust_vc::assert!(pos2.contains(i) == nonneg.contains(i - (1 as int)));
    });
    trust_vc::assert!(forall|i: int| pos2.contains(i) == (i > (0 as int)));
    trust_vc::assert!(pos1 =~= nonneg);
}
"#;
    let r = verify(code, "full_test1_false_exteq");
    assert!(
        !verified(&r),
        "pos1 =~= nonneg is FALSE (0 in nonneg, not pos1); must NOT verify, got {:?}",
        r
    );
}
