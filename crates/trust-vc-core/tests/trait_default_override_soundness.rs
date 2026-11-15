// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A trait default body describes only the impls that inherit it.
//!
//! `register_trait_impl` emits, for each impl that does not override a default
//! method, an axiom that defines the trait function `Trait__m` by the default
//! body. The axiom quantifies over `s: T`, the impl's own type, and applies the
//! trait function to `Box_T(s)`. It used to quantify over every `Poly`
//! receiver, which also gave the default body to an impl that overrides the
//! method and to a generic caller's receiver.
//!
//! The fixture: `impl T for A {}` inherits `m() == 1`; `impl T for B` overrides
//! it with `2`. Each liar claims `1` for a `B` receiver (in the spec spelling,
//! the exec spelling and as a return value), or for a generic receiver that
//! may be `B`. All of them were `Verified`, and all are false at run time.
//! Each must now be checked and not proved: the return-value liars are
//! refuted, and the assertion liars come back `unknown`.
//!
//! The twins on `A` read the inherited default and must still verify. The liar
//! on `A` reaches the pruned per-assertion retry, which must register the
//! default-only impl so that its `Box_A` is declared; it used to answer `Error`.
//! ay answers `unknown` for it rather than a counterexample, because its model
//! gate commits no value for `Box_A` under the scoped quantifier.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn write_fixture(tag: &str, src: &str) -> String {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_trait_default_override_{}_{tag}_{seq}.rs",
        std::process::id()
    ));
    std::fs::write(&path, src).expect("write fixture");
    path.to_str().expect("utf8 path").to_string()
}

#[derive(Debug, Clone, Copy)]
enum Expect {
    Verified,
    /// Checked and not proved: `Counterexample`, `NotProved` or `Unknown`.
    /// Never `Verified`, and never `Error`, which would mean the goal was not
    /// checked at all.
    NotVerified,
}

fn run_pins(tag: &str, src: &str, pins: &[(&str, Expect)]) {
    let path = write_fixture(tag, src);
    let mut failures = Vec::new();
    for (function, expect) in pins {
        let result = trust_vc_core::env::with_serialized_env_vars(
            &[("TRUST_VC_DISABLE_VC_CACHE", "1")],
            || verify_function_from_file(&path, function),
        )
        .unwrap_or_else(|e| VerifyResult::Error {
            message: e.to_string(),
        });
        let ok = match expect {
            Expect::Verified => matches!(result, VerifyResult::Verified),
            Expect::NotVerified => matches!(
                result,
                VerifyResult::Counterexample { .. }
                    | VerifyResult::NotProved { .. }
                    | VerifyResult::Unknown { .. }
            ),
        };
        let text: String = format!("{result:?}").chars().take(260).collect();
        let line = format!("{tag} {function}: expect={expect:?} got={text}");
        println!("PIN {line}");
        if !ok {
            failures.push(line);
        }
    }
    let _ = std::fs::remove_file(&path);
    assert!(
        failures.is_empty(),
        "{} pin(s) failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

const DEFAULT_AND_OVERRIDE: &str = r#"
struct A;
struct B;

#[trust_vc::trait_spec]
trait T {
    fn m(&self) -> u64 {
        1u64
    }
}

#[trust_vc::trait_impl]
impl T for A {}

#[trust_vc::trait_impl]
impl T for B {
    fn m(&self) -> u64 {
        2u64
    }
}

#[trust_vc::ensures(true)]
fn b_liar(b: B) {
    trust_vc::assert!(b.m() == 1u64);
}

#[trust_vc::ensures(true)]
fn b_liar_exec(b: B) {
    let r = b.m();
    trust_vc::assert!(r == 1u64);
}

#[trust_vc::ensures(result == 1u64)]
fn b_ret_liar(b: B) -> u64 {
    b.m()
}

#[trust_vc::ensures(result == 1u64)]
fn g_ret_liar<X: T>(x: X) -> u64 {
    x.m()
}

#[trust_vc::ensures(true)]
fn a_liar(a: A) {
    trust_vc::assert!(a.m() == 2u64);
}

#[trust_vc::ensures(true)]
fn a_ctrl(a: A) {
    trust_vc::assert!(a.m() == 1u64);
}

#[trust_vc::ensures(result == 1u64)]
fn a_ret_ctrl(a: A) -> u64 {
    a.m()
}
"#;

#[test]
fn default_body_is_not_given_to_an_overriding_impl_or_a_generic_receiver() {
    use Expect::{NotVerified, Verified};
    run_pins(
        "override",
        DEFAULT_AND_OVERRIDE,
        &[
            ("b_liar", NotVerified),
            ("b_liar_exec", NotVerified),
            ("b_ret_liar", NotVerified),
            ("g_ret_liar", NotVerified),
            ("a_liar", NotVerified),
            ("a_ctrl", Verified),
            ("a_ret_ctrl", Verified),
        ],
    );
}
