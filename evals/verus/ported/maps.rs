// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// TrustVc port for the active executable upstream maps.rs harness cases.
// The Rust type-error case `test1_fails_subtype` is mirrored by the paired
// `maps_fails_subtype` cargo-check fixture.

use trust_vc_types::{int, nat, Map, Set, SpecFn};

pub const MAPS_RS_EXPECTED_CASES: &[(&str, &str, &str, &str, usize)] = &[
    (
        "test1",
        "test1",
        "evals/verus/ported/maps.rs",
        "verified",
        8,
    ),
    (
        "test1_fails1",
        "test1_fails1",
        "evals/verus/ported/maps.rs",
        "counterexample",
        3,
    ),
    (
        "test1_fails2",
        "test1_fails2",
        "evals/verus/ported/maps.rs",
        "counterexample",
        3,
    ),
    (
        "test1_fails_subtype",
        "test1_fails_subtype",
        "evals/verus/ported/maps_fails_subtype",
        "error",
        0,
    ),
    (
        "test1_fails_eq",
        "test1_fails_eq",
        "evals/verus/ported/maps.rs",
        "counterexample",
        2,
    ),
    (
        "map_contains",
        "map_contains",
        "evals/verus/ported/maps.rs",
        "verified",
        3,
    ),
    (
        "map_insert_implies_contains",
        "map_insert_implies_contains",
        "evals/verus/ported/maps.rs",
        "verified",
        3,
    ),
    (
        "map_overwrite",
        "map_overwrite",
        "evals/verus/ported/maps.rs",
        "verified",
        9,
    ),
    (
        "set_choose_regression_408",
        "set_choose_regression_408",
        "evals/verus/ported/maps.rs",
        "verified",
        2,
    ),
];

pub fn maps_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, &'static str, usize)] {
    MAPS_RS_EXPECTED_CASES
}

pub const MAPS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] =
    &[("test1_fails_subtype", &["mismatched types"])];

pub fn maps_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])] {
    MAPS_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        Set::<i32>::empty()
            .insert(1i32)
            .insert(2i32)
            .insert(3i32)
            .mk_map(SpecFn::new(|k: i32| 10i32 * k))
            .get(2i32)
            == 20i32
    );

    trust_vc::assert!(trust_vc::ext_eq!(
        Set::<i32>::empty()
            .insert(1i32)
            .insert(2i32)
            .insert(3i32)
            .mk_map(SpecFn::new(|k: i32| 10i32 * k)),
        Set::<i32>::empty()
            .insert(1i32)
            .insert(3i32)
            .insert(2i32)
            .mk_map(SpecFn::new(|k: i32| 3i32 * k + 7i32 * k))
    ));

    trust_vc::assert!(!trust_vc_types::map![10i32 => false, 20i32 => true].get(10i32));
    trust_vc::assert!(trust_vc_types::map![10i32 => false, 20i32 => true].get(20i32));

    trust_vc::assert!(!trust_vc_types::map![10i32 => false, 20i32 => true,].get(10i32));
    trust_vc::assert!(trust_vc_types::map![10i32 => false, 20i32 => true,].get(20i32));

    trust_vc::assert!(trust_vc::strict_eq!(
        Set::<i32>::empty()
            .insert(1i32)
            .insert(2i32)
            .insert(3i32)
            .mk_map(SpecFn::new(|x: i32| x + 4i32)),
        Set::<i32>::empty()
            .insert(1i32)
            .insert(2i32)
            .insert(3i32)
            .mk_map(SpecFn::new(|y: i32| y + (2i32 + 2i32)))
    ));
}

#[trust_vc::ensures(true)]
fn test1_fails1() {
    let s1 = Set::<int>::empty().insert(1int).insert(2int).insert(3int);
    let m1 = s1.mk_map(SpecFn::new(|k: int| 10int * k));
    trust_vc::assert!(m1.index(2int) == 20int);
    trust_vc::assert!(m1.index(4int) == 40int); // FAILS
    let s2 = Set::<int>::empty().insert(1int).insert(3int).insert(2int);
    let m2 = s2.mk_map(SpecFn::new(|k: int| 3int * k + 7int * k));
    trust_vc::assert!(m1 =~= m2);
}

#[trust_vc::ensures(true)]
fn test1_fails2() {
    let s1 = Set::<int>::empty().insert(1int).insert(2int).insert(3int);
    let m1 = s1.mk_map(SpecFn::new(|k: int| 10int * k));
    trust_vc::assert!(m1.index(2int) == 20int);
    let s2 = Set::<int>::empty().insert(1int).insert(3int).insert(2int);
    let m2 = s2.mk_map(SpecFn::new(|k: int| 3int * k + 8int * k));
    trust_vc::assert!(trust_vc::equal!(m1, m2)); // FAILS
}

#[trust_vc::ensures(true)]
fn test1_fails_eq() {
    let s = Set::<int>::empty().insert(1int).insert(2int).insert(3int);
    let m1 = s.mk_map(SpecFn::new(|x: int| x + 4int));
    let m2 = s.mk_map(SpecFn::new(|y: int| (2int + 2int) + y));
    trust_vc::assert!(m1 === m2); // FAILS
}

fn map_strict_eq_same_finite_mk_map_function_model_verifies() {
    trust_vc::assert!(trust_vc::strict_eq!(
        Set::<i32>::empty()
            .insert(1i32)
            .insert(2i32)
            .insert(3i32)
            .mk_map(SpecFn::new(|x: i32| x + 4i32)),
        Set::<i32>::empty()
            .insert(1i32)
            .insert(2i32)
            .insert(3i32)
            .mk_map(SpecFn::new(|y: i32| y + (2i32 + 2i32)))
    ));
}

fn map_strict_eq_commuted_finite_mk_map_function_fails() {
    trust_vc::assert!(trust_vc::strict_eq!(
        Set::<i32>::empty()
            .insert(1i32)
            .insert(2i32)
            .insert(3i32)
            .mk_map(SpecFn::new(|x: i32| x + 4i32)),
        Set::<i32>::empty()
            .insert(1i32)
            .insert(2i32)
            .insert(3i32)
            .mk_map(SpecFn::new(|y: i32| (2i32 + 2i32) + y))
    ));
}

fn map_plain_eq_auto_ext_equal_model_verifies() {
    trust_vc::assert!(
        Set::<i32>::empty()
            .insert(1i32)
            .insert(2i32)
            .insert(3i32)
            .mk_map(SpecFn::new(|x: i32| x + 4i32))
            == Set::<i32>::empty()
                .insert(1i32)
                .insert(2i32)
                .insert(3i32)
                .mk_map(SpecFn::new(|y: i32| (2i32 + 2i32) + y))
    );
}

#[trust_vc::ensures(true)]
fn map_contains() {
    trust_vc::assert!(trust_vc_types::map![10i32 => 100i32, 20i32 => 200i32].contains_key(10i32));
    trust_vc::assert!(trust_vc_types::map![10i32 => 100i32, 20i32 => 200i32].contains_value(200i32));
}

// The refuted LIAR TWINS of this file's verified rows moved OUT of this file, to
// `evals/verus/ported/maps_local_witnesses.rs`, unchanged. Each carries a
// `#[trust_vc::ensures(..)]` contract, so the corpus gate's scanner reads it as a
// case of whatever declared `trust_vc_path` it sits in — and it cannot BE one here:
// their upstream cases (`map_contains`, `map_insert_implies_contains`, `map index
// syntax`) are `=> Ok(())`, so a mapped `counterexample` row would be a per-case
// verdict mismatch, while leaving them undeclared inside a declared path is an
// `unexpected observed case`. Moving them keeps every refutation and every
// `COUNTEREXAMPLE_CASES` pin in `crates/trust-vc/tests/maps_rs_trust_vc_regressions.rs`
// exactly as they were; nothing was deleted and no claim changed.
#[trust_vc::ensures(true)]
fn map_insert_implies_contains(m: Map<i32, i32>) {
    trust_vc::assert!(m.insert(1i32, 2i32).insert(3i32, 4i32).contains_key(1i32));
    trust_vc::assert!(m.insert(1i32, 2i32).insert(3i32, 4i32).contains_value(4i32));
}

fn map_index_syntax(m: Map<i32, i32>) {
    trust_vc::assert!(m.insert(1i32, 2i32).index(1i32) == 2i32);
    trust_vc::assert!(m.insert(1i32, 2i32)[1i32] == 2i32);
    trust_vc::assert!(trust_vc_types::map![10i32 => 100i32, 20i32 => 200i32][20i32] == 200i32);
}

fn map_insert_overwrite_updates_index() {
    trust_vc::assert!(
        trust_vc_types::map![1i32 => 10i32, 2i32 => 20i32]
            .insert(1i32, 30i32)
            .index(1i32)
            == 30i32
    );
    trust_vc::assert!(
        trust_vc_types::map![1i32 => 10i32, 2i32 => 20i32].insert(1i32, 30i32)[1i32] == 30i32
    );
    trust_vc::assert!(
        trust_vc_types::map![1i32 => 10i32, 2i32 => 20i32]
            .insert(1i32, 30i32)
            .get(2i32)
            == 20i32
    );
}

fn map_insert_overwrite_fails_keeps_old_value() {
    trust_vc::assert!(
        trust_vc_types::map![1i32 => 10i32, 2i32 => 20i32]
            .insert(1i32, 30i32)
            .index(1i32)
            == 10i32
    );
}

#[trust_vc::ensures(true)]
fn map_overwrite() {
    trust_vc::assert!(trust_vc_types::map![1i32 => 1i32, 2i32 => 3i32]
        .insert(1i32, 2i32)
        .insert(2i32, 4i32)
        .contains_value(2i32));
    trust_vc::assert!(trust_vc_types::map![1i32 => 1i32, 2i32 => 3i32]
        .insert(1i32, 2i32)
        .insert(2i32, 4i32)
        .contains_value(4i32));
    trust_vc::assert!(!trust_vc_types::map![1i32 => 1i32, 2i32 => 3i32]
        .insert(1i32, 2i32)
        .insert(2i32, 4i32)
        .contains_value(1i32));
    trust_vc::assert!(!trust_vc_types::map![1i32 => 1i32, 2i32 => 3i32]
        .insert(1i32, 2i32)
        .insert(2i32, 4i32)
        .contains_value(3i32));
    trust_vc::assert!(!trust_vc_types::map![1i32 => 1i32, 2i32 => 3i32]
        .insert(1i32, 2i32)
        .insert(2i32, 4i32)
        .contains_value(5i32));
    trust_vc::assert!(trust_vc_types::map![1i32 => 1i32, 2i32 => 3i32]
        .insert(1i32, 2i32)
        .insert(2i32, 4i32)
        .insert(1i32, 3i32)
        .contains_value(3i32));
    trust_vc::assert!(!trust_vc_types::map![1i32 => 1i32, 2i32 => 3i32]
        .insert(1i32, 2i32)
        .insert(2i32, 4i32)
        .insert(1i32, 3i32)
        .contains_value(2i32));
    trust_vc::assert!(trust_vc_types::map![1i32 => 1i32, 2i32 => 3i32]
        .insert(1i32, 2i32)
        .insert(2i32, 4i32)
        .insert(1i32, 3i32)
        .contains_value(4i32));
}

fn map_remove_preserves_unremoved_keys() {
    trust_vc::assert!(
        trust_vc_types::map![1i32 => 10i32, 2i32 => 20i32, 3i32 => 30i32]
            .remove(2i32)
            .contains_key(1i32)
    );
    trust_vc::assert!(
        trust_vc_types::map![1i32 => 10i32, 2i32 => 20i32, 3i32 => 30i32]
            .remove(2i32)
            .get(1i32)
            == 10i32
    );
    trust_vc::assert!(
        trust_vc_types::map![1i32 => 10i32, 2i32 => 20i32, 3i32 => 30i32]
            .remove(2i32)
            .contains_key(3i32)
    );
    trust_vc::assert!(
        trust_vc_types::map![1i32 => 10i32, 2i32 => 20i32, 3i32 => 30i32]
            .remove(2i32)
            .get(3i32)
            == 30i32
    );
    trust_vc::assert!(
        !trust_vc_types::map![1i32 => 10i32, 2i32 => 20i32, 3i32 => 30i32]
            .remove(2i32)
            .contains_key(2i32)
    );
}

fn map_remove_fails_drops_unremoved_key() {
    trust_vc::assert!(
        !trust_vc_types::map![1i32 => 10i32, 2i32 => 20i32, 3i32 => 30i32]
            .remove(2i32)
            .contains_key(1i32)
    );
}

fn set_mk_map_dom_tracks_source_set() {
    trust_vc::assert!(Set::<i32>::empty()
        .insert(1i32)
        .insert(2i32)
        .insert(3i32)
        .mk_map(SpecFn::new(|k: i32| 10i32 * k))
        .dom()
        .contains(1i32));
    trust_vc::assert!(Set::<i32>::empty()
        .insert(1i32)
        .insert(2i32)
        .insert(3i32)
        .mk_map(SpecFn::new(|k: i32| 10i32 * k))
        .dom()
        .contains(3i32));
    trust_vc::assert!(!Set::<i32>::empty()
        .insert(1i32)
        .insert(2i32)
        .insert(3i32)
        .mk_map(SpecFn::new(|k: i32| 10i32 * k))
        .dom()
        .contains(4i32));
}

fn set_mk_map_dom_fails_contains_absent_source_key() {
    trust_vc::assert!(Set::<i32>::empty()
        .insert(1i32)
        .insert(2i32)
        .insert(3i32)
        .mk_map(SpecFn::new(|k: i32| 10i32 * k))
        .dom()
        .contains(4i32));
}

#[trust_vc::requires(m.finite())]
#[trust_vc::requires(m.len() > 0usize)]
#[trust_vc::ensures(true)]
fn set_choose_regression_408(m: Set<nat>) {
    let c = m.choose();
    trust_vc::assert!(m.contains(c));
}

// HOLE, disclosed: `set_choose_regression_408` has NO refuted liar twin. Its negation
// (`requires(m.finite() && m.len() > 0)`, `let c = m.choose(); assert!(!m.contains(c))`)
// was measured 2026-09-15 at ay 0.26.0 with `TRUST_VC_DISABLE_VC_CACHE=1` and came back
// `NotProved (Solver returned unknown ((incomplete quantifier-unhandled)))`, never a
// Counterexample. An unrefuted liar is not refutation evidence, so none is pinned.
