// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (maps.rs `test1_fails2`, 2026-09-13): extensional equality
//! between maps built by `Set::mk_map(f)` over CONCRETE `Set::empty().insert(..)`
//! chains is decided by the finite per-key form (domain agreement and value
//! agreement at the union of the literal keys) instead of the symbolic-key
//! FORALL. `dom(S.mk_map(f)) == S` exactly, so the two are logically
//! equivalent; the ground form is what ay 0.26.0 decides. Before, the
//! strict-eq bridge's FORALL premise together with the set-cardinality chains
//! sent the `strict_eq!` refutation into a 30 s wall per retry (393 s for the
//! maps suite). The liars pin that a differing value, a differing domain, and
//! the negated equality are still refuted, and that a SYMBOLIC set keeps the
//! quantified form.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_fmm_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

const SRC: &str = r#"
use trust_vc_types::{Map, Set, SpecFn};

// LIAR (the corpus shape, test1_fails2): different values under strict equality.
#[trust_vc::ensures(true)]
fn strict_eq_differing_values_liar() {
    trust_vc::assert!(trust_vc::strict_eq!(
        Set::<i32>::empty().insert(1i32).insert(2i32).insert(3i32)
            .mk_map(SpecFn::new(|k: i32| 10i32 * k)),
        Set::<i32>::empty().insert(1i32).insert(3i32).insert(2i32)
            .mk_map(SpecFn::new(|k: i32| 3i32 * k + 8i32 * k))
    ));
}

// CONTROL: equal values, different insert order, extensional equality.
#[trust_vc::ensures(true)]
fn ext_eq_equal_values_different_order_verifies() {
    trust_vc::assert!(trust_vc::ext_eq!(
        Set::<i32>::empty().insert(1i32).insert(2i32).insert(3i32)
            .mk_map(SpecFn::new(|k: i32| 10i32 * k)),
        Set::<i32>::empty().insert(3i32).insert(1i32).insert(2i32)
            .mk_map(SpecFn::new(|k: i32| 3i32 * k + 7i32 * k))
    ));
}

// LIAR: extensional equality with one differing value.
#[trust_vc::ensures(true)]
fn ext_eq_differing_value_liar() {
    trust_vc::assert!(trust_vc::ext_eq!(
        Set::<i32>::empty().insert(1i32).insert(2i32).insert(3i32)
            .mk_map(SpecFn::new(|k: i32| 10i32 * k)),
        Set::<i32>::empty().insert(1i32).insert(2i32).insert(3i32)
            .mk_map(SpecFn::new(|k: i32| 11i32 * k))
    ));
}

// LIAR: extensional equality with a differing domain.
#[trust_vc::ensures(true)]
fn ext_eq_differing_domain_liar() {
    trust_vc::assert!(trust_vc::ext_eq!(
        Set::<i32>::empty().insert(1i32).insert(2i32).insert(3i32)
            .mk_map(SpecFn::new(|k: i32| 10i32 * k)),
        Set::<i32>::empty().insert(1i32).insert(2i32)
            .mk_map(SpecFn::new(|k: i32| 10i32 * k))
    ));
}

// CONTROL: a mk_map against a literal map with the same entries.
#[trust_vc::ensures(true)]
fn ext_eq_mk_map_vs_literal_map_verifies() {
    trust_vc::assert!(trust_vc::ext_eq!(
        Set::<i32>::empty().insert(1i32).insert(2i32)
            .mk_map(SpecFn::new(|k: i32| 10i32 * k)),
        trust_vc_types::map![1i32 => 10i32, 2i32 => 20i32]
    ));
}

// LIAR: a mk_map against a literal map with a differing entry.
#[trust_vc::ensures(true)]
fn ext_eq_mk_map_vs_literal_map_liar() {
    trust_vc::assert!(trust_vc::ext_eq!(
        Set::<i32>::empty().insert(1i32).insert(2i32)
            .mk_map(SpecFn::new(|k: i32| 10i32 * k)),
        trust_vc_types::map![1i32 => 10i32, 2i32 => 21i32]
    ));
}

// LIAR: the negated extensional equality of two equal maps.
#[trust_vc::ensures(true)]
fn ext_ne_equal_maps_liar() {
    trust_vc::assert!(trust_vc::ext_ne!(
        Set::<i32>::empty().insert(1i32).insert(2i32)
            .mk_map(SpecFn::new(|k: i32| 10i32 * k)),
        Set::<i32>::empty().insert(2i32).insert(1i32)
            .mk_map(SpecFn::new(|k: i32| 10i32 * k))
    ));
}

// CONTROL: a SYMBOLIC source set keeps the quantified form and still verifies
// the same-function case.
#[trust_vc::ensures(true)]
fn ext_eq_symbolic_set_same_function_verifies(s: Set<i32>) {
    trust_vc::assert!(trust_vc::ext_eq!(
        s.mk_map(SpecFn::new(|k: i32| 10i32 * k)),
        s.mk_map(SpecFn::new(|k: i32| 10i32 * k))
    ));
}
"#;

#[test]
fn strict_eq_differing_values_liar_is_refuted() {
    let r = verify("l1", "strict_eq_differing_values_liar", SRC);
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "CARDINAL (test1_fails2 shape): strict_eq over differing mk_map values must be refuted; got {r:?}"
    );
}

#[test]
fn ext_eq_equal_values_different_order_verifies() {
    let r = verify("c1", "ext_eq_equal_values_different_order_verifies", SRC);
    assert!(
        matches!(r, VerifyResult::Verified),
        "ext_eq over equal mk_map values (different insert order) must verify; got {r:?}"
    );
}

#[test]
fn ext_eq_differing_value_liar_is_refuted() {
    let r = verify("l2", "ext_eq_differing_value_liar", SRC);
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "CARDINAL: a differing value must refute ext_eq; got {r:?}"
    );
}

#[test]
fn ext_eq_differing_domain_liar_is_refuted() {
    let r = verify("l3", "ext_eq_differing_domain_liar", SRC);
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "CARDINAL: a differing domain must refute ext_eq; got {r:?}"
    );
}

#[test]
fn ext_eq_mk_map_vs_literal_map_verifies() {
    let r = verify("c2", "ext_eq_mk_map_vs_literal_map_verifies", SRC);
    assert!(
        matches!(r, VerifyResult::Verified),
        "mk_map against an equal literal map must verify; got {r:?}"
    );
}

#[test]
fn ext_eq_mk_map_vs_literal_map_liar_is_refuted() {
    let r = verify("l4", "ext_eq_mk_map_vs_literal_map_liar", SRC);
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "CARDINAL: mk_map against a differing literal map must be refuted; got {r:?}"
    );
}

#[test]
fn ext_ne_equal_maps_liar_is_refuted() {
    let r = verify("l5", "ext_ne_equal_maps_liar", SRC);
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "CARDINAL: ext_ne of two equal maps must be refuted; got {r:?}"
    );
}

#[test]
fn ext_eq_symbolic_set_same_function_verifies() {
    let r = verify("c3", "ext_eq_symbolic_set_same_function_verifies", SRC);
    assert!(
        matches!(r, VerifyResult::Verified),
        "a symbolic source set keeps the quantified form; same function must verify; got {r:?}"
    );
}
