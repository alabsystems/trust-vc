// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! COMPLETENESS PIN (trait rows, 2026-09-11): a trait DEFAULT method that
//! carries an explicit contract publishes ONLY that contract to callers; its
//! default body is checked AGAINST the contract by the conformance lane, not
//! published as a second axiom. Before, both were published, so a default
//! whose body disagrees with its contract (a conformance counterexample
//! fixture) made every function in the file vacuous — the vacuity precheck
//! reported "Assumptions are contradictory" for an unrelated `fn a() -> u8
//! { 20u8 }` — and the whole returns_postcondition port was unverifiable.

use trust_vc_core::{
    list_trait_conformance_obligations, verify_function_from_file,
    verify_trait_conformance_obligation, VerifyResult,
};

fn with_file<R>(tag: &str, src: &str, f: impl FnOnce(&str) -> R) -> R {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_tdca_{}_{}.rs", std::process::id(), tag));
    std::fs::write(&p, src).expect("write fixture");
    let out = f(p.to_str().expect("utf8 path"));
    let _ = std::fs::remove_file(&p);
    out
}

const MISMATCH: &str = r#"
#[trust_vc::ensures(result == 20u8)]
fn unrelated_neighbour() -> u8 {
    20u8
}

#[trust_vc::ensures(result == 21u8)]
fn unrelated_neighbour_liar() -> u8 {
    20u8
}

#[trust_vc::trait_spec]
trait Mismatch {
    #[trust_vc::ensures(result == true)]
    fn default_returns_false() -> bool {
        false
    }
}

#[trust_vc::trait_impl]
impl Mismatch for bool {}
"#;

const FINE: &str = r#"
#[trust_vc::ensures(result == 20u8)]
fn unrelated_neighbour() -> u8 {
    20u8
}

#[trust_vc::trait_spec]
trait Fine {
    #[trust_vc::ensures(result == true)]
    fn default_returns_true() -> bool {
        true
    }
}

#[trust_vc::trait_impl]
impl Fine for bool {}
"#;

fn verify(path: &str, func: &str) -> VerifyResult {
    verify_function_from_file(path, func).unwrap_or_else(|e| VerifyResult::Error {
        message: e.to_string(),
    })
}

#[test]
fn neighbour_of_a_mismatched_default_verifies() {
    with_file("m1", MISMATCH, |path| {
        match verify(path, "unrelated_neighbour") {
            VerifyResult::Verified => {}
            other => panic!("neighbour of a mismatched default: expected Verified, got {other:?}"),
        }
    });
}

#[test]
fn neighbour_liar_of_a_mismatched_default_is_rejected() {
    with_file("m2", MISMATCH, |path| {
        match verify(path, "unrelated_neighbour_liar") {
            VerifyResult::Counterexample { .. } => {}
            other => panic!("neighbour liar: expected Counterexample, got {other:?}"),
        }
    });
}

#[test]
fn mismatched_default_conformance_is_still_refuted() {
    with_file("m3", MISMATCH, |path| {
        let names = list_trait_conformance_obligations(path).expect("list conformance");
        assert!(
            !names.is_empty(),
            "the mismatched default must yield a conformance obligation"
        );
        let mut refuted = false;
        for name in &names {
            match verify_trait_conformance_obligation(path, name).expect("verify conformance") {
                VerifyResult::Counterexample { .. } => refuted = true,
                VerifyResult::Verified => {}
                other => panic!("conformance {name}: unexpected {other:?}"),
            }
        }
        assert!(
            refuted,
            "the default body `false` must be refuted against `ensures(result == true)`: {names:?}"
        );
    });
}

#[test]
fn matching_default_conformance_verifies_and_neighbour_verifies() {
    with_file("f1", FINE, |path| {
        match verify(path, "unrelated_neighbour") {
            VerifyResult::Verified => {}
            other => panic!("neighbour of a matching default: expected Verified, got {other:?}"),
        }
        let names = list_trait_conformance_obligations(path).expect("list conformance");
        for name in &names {
            match verify_trait_conformance_obligation(path, name).expect("verify conformance") {
                VerifyResult::Verified => {}
                other => panic!("conformance {name}: expected Verified, got {other:?}"),
            }
        }
    });
}
