//! Permanent soundness guards: the cardinality of a DERIVED set/map is not the
//! SOURCE collection's cardinality (FV-3).
//!
//! `Set::filter` / `Set::map` / `Set::new` / `Set::union` / `Map::filter_keys` /
//! `Seq::to_set` all deliberately register `CollectionMeta { len_term: None, .. }`
//! and document that as "fail-closed on cardinality". That design was defeated
//! by `lookup_collection_len`'s name fallback: a derived result is an ANONYMOUS
//! term, and `lowered_receiver_name` walks a chained `CollectionOp` down to its
//! base receiver, so the lookup missed on the term and then answered with
//! `collection_lengths[<source name>]`. The result was fully INVERTED, not merely
//! incomplete — `s.len() == 2` made `s.filter(|x| false).len() == 2` VERIFY while
//! the true `... .len() == 0` was refuted.
//!
//! The fix marks those results via `decline_collection_len`, which makes
//! `lookup_collection_len` skip the name fallback. Any future change that drops
//! the marker, or that "helpfully" restores a source length for a derived set,
//! flips these back to Verified.
//!
//! NARROWNESS PINS live here too (the `*_still_verifies` / `*_stays_sound`
//! tests): base-set cardinality must keep working, and membership on derived
//! sets — which was always encoded correctly — must not regress.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    let dir = Path::new("target/derived_set_cardinality_soundness");
    fs::create_dir_all(dir).unwrap();
    let f = dir.join(format!("{name}.rs"));
    fs::write(&f, code).unwrap();
    trust_vc_core::verify_function_from_file(f.to_str().unwrap(), name)
}

fn verified(r: &TrustVcResult<VerifyResult>) -> bool {
    matches!(r, Ok(VerifyResult::Verified))
}

// ─────────────────── CARDINAL: derived-set cardinality ───────────────────

/// `s.len() == 2` and the filter keeps only `x > 1`; the filtered set can hold
/// as few as 0 elements. Claiming 2 must NOT verify.
#[test]
fn set_filter_len_must_not_inherit_source_len() {
    let code = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::requires(s.len() == (2 as int))]
#[trust_vc::ensures(true)]
fn set_filter_len_must_not_inherit_source_len(s: Set<int>) {
    let f = s.filter(SpecFn::new(|i: int| i > (1 as int)));
    trust_vc::assert!(f.len() == (2 as int));
}
"#;
    let r = verify(code, "set_filter_len_must_not_inherit_source_len");
    assert!(
        !verified(&r),
        "SOUNDNESS: a filtered set's len must not be the source set's len: {r:?}"
    );
}

/// The sharpest form: the predicate is constantly `false`, so the filtered set
/// is EMPTY, yet the source's `len == 2` was handed back.
#[test]
fn set_filter_false_predicate_len_must_not_inherit_source_len() {
    let code = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::requires(s.len() == (2 as int))]
#[trust_vc::ensures(true)]
fn set_filter_false_predicate_len_must_not_inherit_source_len(s: Set<int>) {
    let f = s.filter(SpecFn::new(|i: int| false));
    trust_vc::assert!(f.len() == (2 as int));
}
"#;
    let r = verify(
        code,
        "set_filter_false_predicate_len_must_not_inherit_source_len",
    );
    assert!(
        !verified(&r),
        "SOUNDNESS: an empty filtered set must not carry the source's len: {r:?}"
    );
}

/// `Set::map` collapses collisions, so `|s.map(f)| == |s|` needs `f` injective
/// on `s` — never checked. A constant map sends every element to one value.
#[test]
fn set_map_len_must_not_inherit_source_len() {
    let code = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::requires(s.len() == (2 as int))]
#[trust_vc::ensures(true)]
fn set_map_len_must_not_inherit_source_len(s: Set<int>) {
    let m = s.map(SpecFn::new(|i: int| 7 as int));
    trust_vc::assert!(m.len() == (2 as int));
}
"#;
    let r = verify(code, "set_map_len_must_not_inherit_source_len");
    assert!(
        !verified(&r),
        "SOUNDNESS: a mapped set's len must not be the source set's len: {r:?}"
    );
}

/// No `let` binding — the leak also fired on a directly chained receiver, so the
/// guard must not be satisfiable by special-casing let-locals.
#[test]
fn set_filter_len_inline_chain_must_not_inherit_source_len() {
    let code = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::requires(s.len() == (2 as int))]
#[trust_vc::ensures(true)]
fn set_filter_len_inline_chain_must_not_inherit_source_len(s: Set<int>) {
    trust_vc::assert!(s.filter(SpecFn::new(|i: int| false)).len() == (2 as int));
}
"#;
    let r = verify(
        code,
        "set_filter_len_inline_chain_must_not_inherit_source_len",
    );
    assert!(
        !verified(&r),
        "SOUNDNESS: chained-receiver filter len must not resolve the base name: {r:?}"
    );
}

/// `is_empty()` reads the same length term, so it leaked identically: the
/// source's `len == 2` made `!f.is_empty()` provable for an empty filter.
#[test]
fn set_filter_is_empty_must_not_inherit_source_len() {
    let code = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::requires(s.len() == (2 as int))]
#[trust_vc::ensures(true)]
fn set_filter_is_empty_must_not_inherit_source_len(s: Set<int>) {
    let f = s.filter(SpecFn::new(|i: int| false));
    trust_vc::assert!(!f.is_empty());
}
"#;
    let r = verify(code, "set_filter_is_empty_must_not_inherit_source_len");
    assert!(
        !verified(&r),
        "SOUNDNESS: is_empty on a derived set must not read the source's len: {r:?}"
    );
}

/// Sibling op: `|s ∪ t|` is not `|s|` (inclusion-exclusion needs the overlap).
/// Here `t` is disjoint and non-empty, so the union is strictly larger.
#[test]
fn set_union_len_must_not_inherit_left_operand_len() {
    let code = r#"
use trust_vc_types::{int, Set};

#[trust_vc::requires(s.len() == (2 as int))]
#[trust_vc::requires(t.len() == (5 as int))]
#[trust_vc::ensures(true)]
fn set_union_len_must_not_inherit_left_operand_len(s: Set<int>, t: Set<int>) {
    let u = s.union(t);
    trust_vc::assert!(u.len() == (2 as int));
}
"#;
    let r = verify(code, "set_union_len_must_not_inherit_left_operand_len");
    assert!(
        !verified(&r),
        "SOUNDNESS: a union's len must not be the left operand's len: {r:?}"
    );
}

/// The leak followed the *chained base name*, not the immediate operand, so a
/// second set in scope pins that the fallback is gone rather than merely
/// mis-aimed: `t.filter(..)` claimed `t`'s cardinality.
#[test]
fn set_filter_len_must_not_inherit_immediate_receiver_len() {
    let code = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::requires(s.len() == (2 as int))]
#[trust_vc::requires(t.len() == (5 as int))]
#[trust_vc::ensures(true)]
fn set_filter_len_must_not_inherit_immediate_receiver_len(s: Set<int>, t: Set<int>) {
    let f = t.filter(SpecFn::new(|i: int| false));
    trust_vc::assert!(f.len() == (5 as int));
}
"#;
    let r = verify(
        code,
        "set_filter_len_must_not_inherit_immediate_receiver_len",
    );
    assert!(
        !verified(&r),
        "SOUNDNESS: filter len must not resolve the immediate receiver either: {r:?}"
    );
}

// ─────────────────────────── NARROWNESS PINS ───────────────────────────

/// PIN: base-set cardinality (no filter/map) must STILL verify. If this goes
/// red, the fix has become a blanket rejection of `Set::len()` rather than a
/// decline confined to derived sets.
#[test]
fn base_set_len_still_verifies() {
    let code = r#"
use trust_vc_types::{int, Set};

#[trust_vc::requires(s.len() == (2 as int))]
#[trust_vc::ensures(true)]
fn base_set_len_still_verifies(s: Set<int>) {
    trust_vc::assert!(s.len() == (2 as int));
}
"#;
    let r = verify(code, "base_set_len_still_verifies");
    assert!(
        verified(&r),
        "NARROWNESS: base-set cardinality must still verify: {r:?}"
    );
}

/// PIN (control for the pin above): the base-set length is a real fact, not a
/// vacuously-discharged one — a contradictory claim about it must fail.
#[test]
fn base_set_len_false_claim_still_fails() {
    let code = r#"
use trust_vc_types::{int, Set};

#[trust_vc::requires(s.len() == (2 as int))]
#[trust_vc::ensures(true)]
fn base_set_len_false_claim_still_fails(s: Set<int>) {
    trust_vc::assert!(s.len() == (1 as int));
}
"#;
    let r = verify(code, "base_set_len_false_claim_still_fails");
    assert!(
        !verified(&r),
        "NARROWNESS control: a false base-set len claim must not verify: {r:?}"
    );
}

/// PIN: membership on a FILTERED set was always encoded correctly (the filter
/// biconditional). Declining the length must not disturb it — an element the
/// predicate rejects must still be refuted.
#[test]
fn set_filter_membership_stays_sound() {
    let code = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::requires(s.contains(0 as int))]
#[trust_vc::ensures(true)]
fn set_filter_membership_stays_sound(s: Set<int>) {
    let f = s.filter(SpecFn::new(|i: int| i > (1 as int)));
    trust_vc::assert!(f.contains(0 as int));
}
"#;
    let r = verify(code, "set_filter_membership_stays_sound");
    assert!(
        !verified(&r),
        "SOUNDNESS: a filtered-out element must not be a member: {r:?}"
    );
}

/// PIN: membership on a filtered set must still be PROVABLE in the true
/// direction — the decline is about cardinality only. This is the positive half
/// of the membership pin, so a regression to "derived sets are opaque" is caught.
#[test]
fn set_filter_membership_positive_still_verifies() {
    let code = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::requires(s.contains(5 as int))]
#[trust_vc::ensures(true)]
fn set_filter_membership_positive_still_verifies(s: Set<int>) {
    let f = s.filter(SpecFn::new(|i: int| i > (0 as int)));
    trust_vc::assert!(f.contains(5 as int));
}
"#;
    let r = verify(code, "set_filter_membership_positive_still_verifies");
    assert!(
        verified(&r),
        "NARROWNESS: filtered-set membership must still verify: {r:?}"
    );
}

/// PIN: `Set::map` membership (forward image) must still verify.
#[test]
fn set_map_membership_positive_still_verifies() {
    let code = r#"
use trust_vc_types::{int, Set, SpecFn};

#[trust_vc::requires(s.contains(5 as int))]
#[trust_vc::ensures(true)]
fn set_map_membership_positive_still_verifies(s: Set<int>) {
    let m = s.map(SpecFn::new(|i: int| i + (1 as int)));
    trust_vc::assert!(m.contains(6 as int));
}
"#;
    let r = verify(code, "set_map_membership_positive_still_verifies");
    assert!(
        verified(&r),
        "NARROWNESS: mapped-set forward-image membership must still verify: {r:?}"
    );
}
