// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Additional qualified-helper and abstract `self.<field>` conformance
//! scenarios, complementing `trait_multisegment_self_field_soundness.rs`.
//!
//! Verdicts are taken from the per-impl conformance obligations
//! (`list_trait_conformance_obligations` / `verify_trait_conformance_obligation`):
//! the impl or default is blamed, never the generic-bounded caller.  Every
//! violating default must Counterexample; every conforming analog must Verify
//! both as a conformance obligation and at the caller.

use std::path::PathBuf;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn write_fixture(label: &str, source: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "trust_vc_trait_self_field_regr_{label}_{}.rs",
        std::process::id()
    ));
    std::fs::write(&path, source).expect("write trait regression fixture");
    path
}

fn verify(label: &str, source: &str, function: &str) -> VerifyResult {
    let path = write_fixture(label, source);
    let result = verify_function_from_file(path.to_str().expect("UTF-8 fixture path"), function)
        .unwrap_or_else(|error| VerifyResult::Error {
            message: error.to_string(),
        });
    let _ = std::fs::remove_file(path);
    result
}

fn conformance_verdict(label: &str, source: &str) -> VerifyResult {
    let path = write_fixture(label, source);
    let path_str = path.to_str().expect("UTF-8 fixture path");
    let result = match trust_vc_core::list_trait_conformance_obligations(path_str) {
        Ok(names) if names.is_empty() => VerifyResult::Error {
            message: "no trait-conformance obligations were listed".to_string(),
        },
        Ok(names) => {
            let mut verdict = VerifyResult::Verified;
            for name in names {
                match trust_vc_core::verify_trait_conformance_obligation(path_str, &name) {
                    Ok(result) if result.is_verified() => {}
                    Ok(result) => {
                        verdict = result;
                        break;
                    }
                    Err(error) => {
                        verdict = VerifyResult::Error {
                            message: error.to_string(),
                        };
                        break;
                    }
                }
            }
            verdict
        }
        Err(error) => VerifyResult::Error {
            message: error.to_string(),
        },
    };
    let _ = std::fs::remove_file(path);
    result
}

fn expect_counterexample(label: &str, source: &str) {
    let result = conformance_verdict(label, source);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{label} must be refuted, got {result:?}"
    );
}

fn expect_verified(label: &str, source: &str, function: &str) {
    let result = verify(&format!("{label}_caller"), source, function);
    assert!(
        matches!(result, VerifyResult::Verified),
        "{label} caller must verify, got {result:?}"
    );
    let result = conformance_verdict(&format!("{label}_conformance"), source);
    assert!(
        matches!(result, VerifyResult::Verified),
        "{label} conformance must verify, got {result:?}"
    );
}

// A module-path SPEC callee is transparent: its body `3` contradicts the
// default's `ensures(result == 7)`, so the obligation must be refuted (not
// merely left opaque).
const MODULE_SPEC_BODY_CONTRADICTS: &str = r#"
mod helpers {
    #[trust_vc::spec]
    pub fn compute() -> u32 { 3u32 }
}
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn m(&self) -> u32 { helpers::compute() }
}
#[trust_vc::ensures(true)]
fn caller<X: T>(v: X) { trust_vc::assert!(v.m() == 7u32); }
"#;

#[test]
fn module_spec_body_contradicting_default_is_refuted() {
    expect_counterexample("module_spec_contradicts", MODULE_SPEC_BODY_CONTRADICTS);
}

// A module-path EXEC callee with arguments and an unconditional `ensures`
// that mentions those arguments still justifies the default.
const MODULE_EXEC_WITH_ARGS_CONFORMS: &str = r#"
mod helpers {
    #[trust_vc::ensures(result == a + b)]
    pub fn add(a: u32, b: u32) -> u32 { a + b }
}
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn m(&self) -> u32 { helpers::add(2u32, 5u32) }
}
#[trust_vc::ensures(true)]
fn caller<X: T>(v: X) { trust_vc::assert!(v.m() == 7u32); }
"#;

#[test]
fn module_exec_callee_with_args_and_ensures_conforms() {
    expect_verified("module_exec_args", MODULE_EXEC_WITH_ARGS_CONFORMS, "caller");
}

// The single-segment SPEC callee path is unchanged by qualified resolution.
const SINGLE_SEGMENT_SPEC_CONFORMS: &str = r#"
#[trust_vc::spec]
fn good_spec() -> u32 { 7u32 }
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn m(&self) -> u32 { good_spec() }
}
#[trust_vc::ensures(true)]
fn caller<X: T>(v: X) { trust_vc::assert!(v.m() == 7u32); }
"#;

#[test]
fn single_segment_spec_callee_conforms() {
    expect_verified(
        "single_segment_spec",
        SINGLE_SEGMENT_SPEC_CONFORMS,
        "caller",
    );
}

// Non-boolean dual of the abstract self-field projection: `self.n` is an
// arbitrary `u32`, so `ensures(result > 0)` cannot be established.
const SELF_FIELD_U32_UNRELATED: &str = r#"
struct Holder { n: u32 }
#[trust_vc::trait_spec]
trait DefPred {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result > 0u32)]
    fn dp(&self) -> u32 { self.n }
}
#[trust_vc::ensures(true)]
fn caller<X: DefPred>(x: X) { trust_vc::assert!(x.dp() > 0u32); }
"#;

#[test]
fn abstract_self_field_cannot_establish_unrelated_u32_bound() {
    expect_counterexample("self_field_u32", SELF_FIELD_U32_UNRELATED);
}

// Non-vacuity: the abstract self-field projection must not poison the caller
// context into UNSAT.  An unrelated false assertion after the call still
// Counterexamples at the caller.
const SELF_FIELD_NONVACUOUS: &str = r#"
struct Holder { flag: bool }
#[trust_vc::trait_spec]
trait DefPred {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == true)]
    fn dp(&self) -> bool { self.flag }
}
#[trust_vc::ensures(true)]
fn caller<X: DefPred>(x: X) {
    let _r = x.dp();
    trust_vc::assert!(1u32 == 2u32);
}
"#;

#[test]
fn self_field_projection_context_is_not_vacuous() {
    let result = verify("self_field_nonvacuous", SELF_FIELD_NONVACUOUS, "caller");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "an unrelated false assertion must still be refuted at the caller, got {result:?}"
    );
    expect_counterexample("self_field_nonvacuous_conformance", SELF_FIELD_NONVACUOUS);
}

// A generic-struct impl whose body is a literal (the struct declares a field
// it never reads) still conforms: field modeling must not perturb this path.
const GENERIC_STRUCT_LITERAL_BODY_CONFORMS: &str = r#"
#[trust_vc::trait_spec]
trait Predicate {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == true)]
    fn always_true(&self) -> bool;
}
struct Wrapper<P> { val: P, flag: bool }
#[trust_vc::trait_impl]
impl<P> Predicate for Wrapper<P> {
    fn always_true(&self) -> bool { true }
}
#[trust_vc::ensures(true)]
fn caller<T: Predicate>(t: T) { trust_vc::assert!(t.always_true() == true); }
"#;

#[test]
fn generic_struct_literal_body_conforms() {
    expect_verified(
        "generic_struct_literal",
        GENERIC_STRUCT_LITERAL_BODY_CONFORMS,
        "caller",
    );
}
