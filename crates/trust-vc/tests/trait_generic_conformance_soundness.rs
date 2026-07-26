// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The CARDINAL gate for trait-side A2-generic (Probe 1): the instantiated
//! trait contract may reach concrete-receiver callers ONLY while every impl at
//! every instantiation keeps a checked conformance obligation. A
//! contract-violating impl of a parameterized trait must have its OWN
//! obligation rejected (Counterexample, or fail-closed Unknown — the gate
//! treats a non-discharged obligation as a failure); `Verified` here is the
//! cardinal false-verify and blocks the whole increment. Mirrors the
//! discipline of `trait_conformance_generic_result_soundness.rs`.

use std::path::PathBuf;
use trust_vc_core::{
    list_trait_conformance_obligations, verify_function_from_file,
    verify_trait_conformance_obligation, VerifyResult,
};

fn write_fixture(label: &str, source: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "trust_vc_trait_generic_conf_{label}_{}.rs",
        std::process::id()
    ));
    std::fs::write(&path, source).expect("write conformance fixture");
    path
}

fn conformance_verdict(label: &str, source: &str) -> VerifyResult {
    let path = write_fixture(label, source);
    let path_str = path.to_str().expect("fixture path utf-8");
    let names = list_trait_conformance_obligations(path_str)
        .unwrap_or_else(|err| panic!("{label}: conformance obligations should enumerate: {err}"));
    let name = names
        .into_iter()
        .next()
        .unwrap_or_else(|| panic!("{label}: fixture should declare one conformance obligation"));
    let result = verify_trait_conformance_obligation(path_str, &name).unwrap_or_else(|err| {
        VerifyResult::Error {
            message: err.to_string(),
        }
    });
    let _ = std::fs::remove_file(&path);
    result
}

/// A contract-violating impl's obligation must NOT be certified: Counterexample
/// (definitive) or fail-closed Unknown both reject; `Verified` is the cardinal
/// false-verify; `Error` means the obligation was never actually checked.
fn assert_rejected(label: &str, result: VerifyResult) {
    match result {
        VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. } => {}
        VerifyResult::Verified => panic!(
            "{label}: CARDINAL FALSE-VERIFY — a contract-violating instantiated impl's own \
             conformance obligation reported Verified; the impl was never checked."
        ),
        other => panic!(
            "{label}: expected the obligation to be rejected (Counterexample or fail-closed \
             Unknown), got {other:?} — an Error means the body never reached the solver."
        ),
    }
}

fn assert_verified(label: &str, result: VerifyResult) {
    assert!(
        matches!(result, VerifyResult::Verified),
        "{label}: a conforming instantiated impl's conformance obligation must Verify, got: \
         {result:?}"
    );
}

const VIOLATING: &str = r#"
struct W1 { v: u64 }

#[trust_vc::trait_spec]
trait ArithGive<A> {
    #[trust_vc::ensures(result == a)]
    fn give(&self, a: A) -> A;
}

#[trust_vc::trait_impl]
impl ArithGive<u64> for W1 {
    fn give(&self, a: u64) -> u64 { 5u64 }
}

#[trust_vc::ensures(true)]
fn bystander_true() {
    trust_vc::assert!(1u64 + 1u64 == 2u64);
}
"#;

const CONFORMING: &str = r#"
struct S1 { x: u64 }

#[trust_vc::trait_spec]
trait Give<A> {
    #[trust_vc::ensures(result == a)]
    fn give(&self, a: A) -> A;
}

#[trust_vc::trait_impl]
impl Give<u64> for S1 {
    fn give(&self, a: u64) -> u64 { a }
}
"#;

const EXTERNAL: &str = r#"
struct E1 { x: u64 }

#[trust_vc::trait_spec]
trait ExtGive<A> {
    #[trust_vc::ensures(result == a)]
    fn give(&self, a: A) -> A;
}

#[trust_vc::external]
#[trust_vc::trait_impl]
impl ExtGive<u64> for E1 {
    fn give(&self, a: u64) -> u64 { 5u64 }
}
"#;

/// The decisive soundness direction: the violating instantiated impl's own
/// obligation is rejected, never certified.
#[test]
fn violating_instantiated_impl_obligation_is_rejected() {
    assert_rejected(
        "violating_impl",
        conformance_verdict("violating", VIOLATING),
    );
}

/// No over-rejection: the identity impl genuinely establishes `result == a`.
#[test]
fn conforming_instantiated_impl_obligation_verifies() {
    assert_verified(
        "conforming_impl",
        conformance_verdict("conforming", CONFORMING),
    );
}

/// Attribution (a21bf875): the violating impl fails its OWN obligation; a
/// bystander function in the same file is not sunk.
#[test]
fn violating_impl_does_not_sink_bystander() {
    let path = write_fixture("bystander", VIOLATING);
    let path_str = path.to_str().expect("fixture path utf-8");
    let result = verify_function_from_file(path_str, "bystander_true").unwrap_or_else(|err| {
        VerifyResult::Error {
            message: err.to_string(),
        }
    });
    let _ = std::fs::remove_file(&path);
    assert!(
        matches!(result, VerifyResult::Verified),
        "bystander must verify (violating impl blames its own obligation), got {result:?}"
    );
}

const NAME_COLLISION: &str = r#"
struct C1 { x: u64 }

mod m1 {
    #[trust_vc::trait_spec]
    trait Twin<A> {
        #[trust_vc::ensures(result == a)]
        fn t(&self, a: A) -> A;
    }
}

mod m2 {
    #[trust_vc::trait_spec]
    trait Twin<A> {
        #[trust_vc::ensures(true)]
        fn t(&self, a: A) -> A;
    }
}

#[trust_vc::trait_impl]
impl Twin<u64> for C1 {
    fn t(&self, a: u64) -> u64 { a }
}

#[trust_vc::ensures(true)]
fn collision_caller(c: C1) {
    trust_vc::assert!(c.t(7u64) == 7u64);
}
"#;

/// Two DIFFERENT traits colliding on one name, with the name actually CONSUMED
/// through an impl, must fail closed — silently sharing one UF/axiom set (or
/// picking one declaration's contract arbitrarily) is a name-collapse
/// false-verify vector (`register_trait` hardening). The caller must NOT
/// verify against either declaration.
#[test]
fn same_name_different_trait_fails_closed() {
    let path = write_fixture("collision", NAME_COLLISION);
    let path_str = path.to_str().expect("fixture path utf-8");
    let result = verify_function_from_file(path_str, "collision_caller").unwrap_or_else(|err| {
        VerifyResult::Error {
            message: err.to_string(),
        }
    });
    let _ = std::fs::remove_file(&path);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "a consumed trait name collision must fail closed, got {result:?}"
    );
}

/// `#[trust_vc::external]` keeps the Verus external_trait_specification trust
/// model at an instantiation: the impl's body is trusted, so no conformance
/// obligation is enumerated for it.
#[test]
fn external_instantiated_impl_is_not_enumerated() {
    let path = write_fixture("external", EXTERNAL);
    let path_str = path.to_str().expect("fixture path utf-8");
    let names = list_trait_conformance_obligations(path_str)
        .expect("external fixture obligations should enumerate");
    let _ = std::fs::remove_file(&path);
    assert!(
        names.is_empty(),
        "external impl must be skipped by the conformance pass, got obligations: {names:?}"
    );
}
