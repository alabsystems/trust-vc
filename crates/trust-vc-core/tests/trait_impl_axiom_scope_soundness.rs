// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The per-impl linking axiom speaks only of the impl's own receivers.
//!
//! A trait method is one uninterpreted function `Trait__m(Poly, ..)` shared by
//! every impl. `register_trait_impl` emits, per impl of type `T`, a linking
//! axiom that ties it to the impl's concrete function. The axiom quantifies
//! over `self: T` and applies the trait function to `Box_T(self)`. It used to
//! quantify over every `Poly` receiver with `Unbox_T` on the concrete side,
//! which claims that every receiver (another impl's, a generic caller's)
//! dispatches to this impl. That is false as soon as a second impl behaves
//! differently, and ay uses it as written: it adopts a named definitional
//! `forall` as a definition of the trait function.
//!
//! * `link_*`: `impl T for S1` ensures `result == 1`; `impl T for S2` returns 2
//!   with no contract. `s1.f(5) == s2.f(5)` was Verified (false: 1 vs 2).
//! * `two_*`: two contracts, `result == 1` and `result == 2`. The axioms were
//!   contradictory, so both `a.f() == b.f()` and its true negation came back
//!   as the vacuity refusal. Now the negation verifies and the liar does not.
//!
//! Each liar has a control on the same fixture that still verifies, so the
//! scoped axiom still reaches the receivers it is about.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn write_fixture(tag: &str, src: &str) -> String {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_trait_axiom_scope_{}_{tag}_{seq}.rs",
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

struct Pin<'a> {
    function: &'a str,
    expect: Expect,
    /// The verdict before the axioms were scoped.
    before: &'a str,
}

fn run_pins(tag: &str, src: &str, pins: &[Pin<'_>]) {
    let path = write_fixture(tag, src);
    let mut failures = Vec::new();
    for pin in pins {
        let result = verify_function_from_file(&path, pin.function).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
        let ok = match pin.expect {
            Expect::Verified => matches!(result, VerifyResult::Verified),
            Expect::NotVerified => matches!(
                result,
                VerifyResult::Counterexample { .. }
                    | VerifyResult::NotProved { .. }
                    | VerifyResult::Unknown { .. }
            ),
        };
        let text: String = format!("{result:?}").chars().take(260).collect();
        let line = format!(
            "{tag} {}: expect={:?} got={text} (before: {})",
            pin.function, pin.expect, pin.before
        );
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

const LINK_ONE_CONTRACT: &str = r#"
struct S1;
struct S2;

#[trust_vc::trait_spec]
trait T {
    fn f(&self, a: u64) -> u64;
}

#[trust_vc::trait_impl]
impl T for S1 {
    #[trust_vc::ensures(result == 1u64)]
    fn f(&self, a: u64) -> u64 {
        1u64
    }
}

#[trust_vc::trait_impl]
impl T for S2 {
    fn f(&self, a: u64) -> u64 {
        2u64
    }
}

#[trust_vc::ensures(true)]
fn link_liar(s1: S1, s2: S2) {
    trust_vc::assert!(s1.f(5u64) == s2.f(5u64));
}

#[trust_vc::ensures(true)]
fn link_s2_liar(s2: S2) {
    trust_vc::assert!(s2.f(5u64) == 1u64);
}

#[trust_vc::ensures(true)]
fn link_ctrl(s1: S1) {
    trust_vc::assert!(s1.f(5u64) == 1u64);
}
"#;

#[test]
fn linking_axiom_does_not_give_one_impl_the_other_impls_contract() {
    run_pins(
        "link",
        LINK_ONE_CONTRACT,
        &[
            Pin {
                function: "link_liar",
                expect: Expect::NotVerified,
                before: "Verified",
            },
            Pin {
                function: "link_s2_liar",
                expect: Expect::NotVerified,
                before: "NotProved",
            },
            Pin {
                function: "link_ctrl",
                expect: Expect::Verified,
                before: "Verified",
            },
        ],
    );
}

const TWO_CONTRACTS: &str = r#"
struct A;
struct B;

#[trust_vc::trait_spec]
trait T {
    fn f(&self) -> u64;
}

#[trust_vc::trait_impl]
impl T for A {
    #[trust_vc::ensures(result == 1u64)]
    fn f(&self) -> u64 {
        1u64
    }
}

#[trust_vc::trait_impl]
impl T for B {
    #[trust_vc::ensures(result == 2u64)]
    fn f(&self) -> u64 {
        2u64
    }
}

#[trust_vc::ensures(true)]
fn two_liar(a: A, b: B) {
    trust_vc::assert!(a.f() == b.f());
}

#[trust_vc::ensures(true)]
fn two_neg(a: A, b: B) {
    trust_vc::assert!(a.f() != b.f());
}

#[trust_vc::ensures(true)]
fn two_a_liar(a: A) {
    trust_vc::assert!(a.f() == 2u64);
}

#[trust_vc::ensures(true)]
fn two_a_ctrl(a: A) {
    trust_vc::assert!(a.f() == 1u64);
}
"#;

#[test]
fn two_impl_contracts_are_consistent_premises() {
    run_pins(
        "two",
        TWO_CONTRACTS,
        &[
            Pin {
                function: "two_liar",
                expect: Expect::NotVerified,
                before: "Unknown (vacuity: the premises were contradictory)",
            },
            Pin {
                function: "two_neg",
                expect: Expect::Verified,
                before: "Unknown (vacuity: the premises were contradictory)",
            },
            Pin {
                function: "two_a_liar",
                expect: Expect::NotVerified,
                before: "NotProved",
            },
            Pin {
                function: "two_a_ctrl",
                expect: Expect::Verified,
                before: "Verified",
            },
        ],
    );
}
