// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Distilled unsafe/safe matrix for qualified default helpers and abstract
//! `self.<field>` projections.  Every negative case must fail closed; every
//! supported body-justified analog must retain proof power.

use std::path::PathBuf;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn write_fixture(label: &str, source: &str) -> PathBuf {
    let mut path: PathBuf = std::env::temp_dir();
    path.push(format!(
        "trust_vc_trait_multiseg_field_{label}_{}.rs",
        std::process::id()
    ));
    // The file-path verifier discovers and schedules trait-conformance residuals
    // from an attributed target function.  Keep the fixtures focused on the
    // semantic delta and add the inert target postcondition uniformly here.
    let source = source.replace("fn caller", "#[trust_vc::ensures(true)]\nfn caller");
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

fn expect_counterexample(label: &str, source: &str, _function: &str) {
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

const MODULE_EXEC_OPAQUE: &str = r#"
mod helpers { pub fn compute() -> u32 { 0u32 } }
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn m(&self) -> u32 { helpers::compute() }
}
fn caller<X: T>(x: X) { trust_vc::assert!(x.m() == 7u32); }
"#;

#[test]
fn module_exec_without_contract_is_opaque() {
    expect_counterexample("module_exec_opaque", MODULE_EXEC_OPAQUE, "caller");
}

const CRATE_EXEC_OPAQUE: &str = r#"
pub fn compute() -> u32 { 0u32 }
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn m(&self) -> u32 { crate::compute() }
}
fn caller<X: T>(x: X) { trust_vc::assert!(x.m() == 7u32); }
"#;

#[test]
fn crate_exec_without_contract_is_opaque() {
    expect_counterexample("crate_exec_opaque", CRATE_EXEC_OPAQUE, "caller");
}

const ASSOCIATED_EXEC_OPAQUE: &str = r#"
struct Registry;
impl Registry { fn compute() -> u32 { 0u32 } }
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn m(&self) -> u32 { Registry::compute() }
}
fn caller<X: T>(x: X) { trust_vc::assert!(x.m() == 7u32); }
"#;

#[test]
fn associated_exec_without_contract_is_opaque() {
    expect_counterexample("associated_exec_opaque", ASSOCIATED_EXEC_OPAQUE, "caller");
}

const EXACT_PATH_COLLISION: &str = r#"
mod good { #[trust_vc::spec] pub fn compute() -> u32 { 7u32 } }
mod bad { pub fn compute() -> u32 { 3u32 } }
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn m(&self) -> u32 { bad::compute() }
}
fn caller<X: T>(x: X) { trust_vc::assert!(x.m() == 7u32); }
"#;

#[test]
fn qualified_resolution_never_borrows_same_leaf_spec_authority() {
    expect_counterexample("exact_path_collision", EXACT_PATH_COLLISION, "caller");
}

const UNKNOWN_OPAQUE: &str = r#"
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn m(&self) -> u32 { external::unknown() }
}
fn caller<X: T>(x: X) { trust_vc::assert!(x.m() == 7u32); }
"#;

#[test]
fn unknown_qualified_return_call_is_opaque() {
    expect_counterexample("unknown_opaque", UNKNOWN_OPAQUE, "caller");
}

const REQUIRES_EXEC_OPAQUE: &str = r#"
mod helpers {
    #[trust_vc::requires(a == 5u32)]
    #[trust_vc::ensures(result == 100u32)]
    pub fn compute(a: u32) -> u32 { a * 20u32 }
}
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 100u32)]
    fn m(&self) -> u32 { helpers::compute(7u32) }
}
fn caller<X: T>(x: X) { trust_vc::assert!(x.m() == 100u32); }
"#;

#[test]
fn requires_bearing_qualified_exec_never_publishes_unguarded_ensures() {
    let result = conformance_verdict("requires_exec_opaque", REQUIRES_EXEC_OPAQUE);
    assert!(
        matches!(
            result,
            VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
        ),
        "requires-bearing helper must fail closed, got {result:?}"
    );
}

const MODULE_SPEC_VISIBLE: &str = r#"
mod helpers { #[trust_vc::spec] pub fn compute() -> u32 { 7u32 } }
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn m(&self) -> u32 { helpers::compute() }
}
fn caller<X: T>(x: X) { trust_vc::assert!(x.m() == 7u32); }
"#;

#[test]
fn module_spec_definition_remains_visible() {
    expect_verified("module_spec_visible", MODULE_SPEC_VISIBLE, "caller");
}

const CRATE_SPEC_VISIBLE: &str = r#"
#[trust_vc::spec]
pub fn compute() -> u32 { 7u32 }
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn m(&self) -> u32 { crate::compute() }
}
fn caller<X: T>(x: X) { trust_vc::assert!(x.m() == 7u32); }
"#;

#[test]
fn crate_spec_definition_remains_visible() {
    expect_verified("crate_spec_visible", CRATE_SPEC_VISIBLE, "caller");
}

const ASSOCIATED_SPEC_VISIBLE: &str = r#"
struct Registry;
impl Registry { #[trust_vc::spec] fn compute() -> u32 { 7u32 } }
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn m(&self) -> u32 { Registry::compute() }
}
fn caller<X: T>(x: X) { trust_vc::assert!(x.m() == 7u32); }
"#;

#[test]
fn associated_spec_definition_remains_visible() {
    expect_verified("associated_spec_visible", ASSOCIATED_SPEC_VISIBLE, "caller");
}

const MODULE_EXEC_ENSURES_VISIBLE: &str = r#"
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
fn caller<X: T>(x: X) { trust_vc::assert!(x.m() == 7u32); }
"#;

#[test]
fn requires_free_body_justified_exec_ensures_remains_visible() {
    expect_verified(
        "module_exec_ensures_visible",
        MODULE_EXEC_ENSURES_VISIBLE,
        "caller",
    );
}

const SELF_FIELD_FALSE: &str = r#"
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == true)]
    fn m(&self) -> bool { self.flag }
}
fn caller<X: T>(x: X) { trust_vc::assert!(x.m()); }
"#;

#[test]
fn abstract_self_field_cannot_establish_unrelated_boolean() {
    expect_counterexample("self_field_false", SELF_FIELD_FALSE, "caller");
}

const SELF_FIELD_SAME_PROJECTION: &str = r#"
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == self.flag)]
    fn m(&self) -> bool { self.flag }
}
fn caller<X: T>(x: X) { let _ = x.m(); trust_vc::assert!(true); }
"#;

#[test]
fn contract_and_body_share_one_self_field_projection() {
    expect_verified(
        "self_field_same_projection",
        SELF_FIELD_SAME_PROJECTION,
        "caller",
    );
}

const GENERIC_STRUCT_FIELD_FALSE: &str = r#"
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == true)]
    fn m(&self) -> bool;
}
struct Wrapper<P> { payload: P, flag: bool }
#[trust_vc::trait_impl]
impl<P> T for Wrapper<P> { fn m(&self) -> bool { self.flag } }
fn caller<X: T>(x: X) { trust_vc::assert!(x.m()); }
"#;

#[test]
fn generic_struct_self_field_override_is_checked() {
    expect_counterexample(
        "generic_struct_field_false",
        GENERIC_STRUCT_FIELD_FALSE,
        "caller",
    );
}

const UNSUPPORTED_FIELD_INFERENCE: &str = r#"
fn consume(_x: u32) -> bool { true }
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == true)]
    fn m(&self) -> bool { consume(self.value) }
}
fn caller<X: T>(x: X) { trust_vc::assert!(x.m()); }
"#;

#[test]
fn unsupported_nested_self_field_type_never_verifies() {
    let result = conformance_verdict("unsupported_field_inference", UNSUPPORTED_FIELD_INFERENCE);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "a field with no supported type evidence must fail closed, got {result:?}"
    );
}
