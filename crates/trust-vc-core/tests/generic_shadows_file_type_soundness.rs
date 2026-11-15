// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A generic type parameter can be spelled like a type the file declares
//! (`struct W; fn gp1<W: Val>()`). Inside the parameter's scope rustc reads
//! `W` as the parameter, but the lane looks up `W::five()` in the inherent
//! impls by its spelling and finds `impl W`, and it lifts a method out of
//! `impl<W> H<W>` without the impl's generics, so its `a: W` reads as the unit
//! struct. A caller reads a callee's contract and a spec function's body the
//! same way. So every function of such a file gets no `Verified` answer
//! (`vc_extraction::type_name_rebinding`).
//!
//! Every liar below is false at run time for the instantiation `X`, whose
//! `five` is `7`, or for `H<u8>` with `a != b`. The twins declare the same
//! file types and generics spelled unlike them, and must still verify.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// The tag every refusal of the type-name rule starts with.
const TAG: &str = "type-name rebinding";

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_generic_shadows_file_type_{}_{}_{seq}.rs",
        std::process::id(),
        func
    ));
    std::fs::write(&path, src).expect("write fixture");
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(path.to_str().expect("utf8 path"), func)
        })
        .map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&path);
    result
}

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// A true program: must verify.
    Verified,
    /// A false program the lane refutes.
    Refuted,
    /// Refused by the type-name rule: an `Error` carrying the tag.
    Refused,
    /// A caller of the named generic callee: refused by the type-name rule,
    /// or earlier, when the callee is registered, by the generic-carriage
    /// gate (`spec_function_catalog::generic_carriage`), whose typed `Err`
    /// names the callee and its shadowed generic. Either way no `Verified`.
    RefusedAtCallee(&'static str),
}

fn render(r: &Result<VerifyResult, String>) -> String {
    match r {
        Ok(VerifyResult::Verified) => "Verified".into(),
        Ok(VerifyResult::Counterexample {
            obligation_name, ..
        }) => format!("Counterexample({obligation_name})"),
        Ok(VerifyResult::Error { message }) => {
            format!("Error({})", message.chars().take(240).collect::<String>())
        }
        Ok(other) => format!("{:.240}", format!("{other:?}")),
        Err(e) => format!("Err({})", e.chars().take(240).collect::<String>()),
    }
}

fn check_table(src: &str, table: &[(&str, Expect)]) {
    let mut failures = Vec::new();
    for (func, expect) in table {
        let r = verify(src, func);
        let ok = match expect {
            Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
            Expect::Refuted => matches!(r, Ok(VerifyResult::Counterexample { .. })),
            Expect::Refused => {
                matches!(&r, Ok(VerifyResult::Error { message }) if message.starts_with(TAG))
            }
            Expect::RefusedAtCallee(callee) => match &r {
                Ok(VerifyResult::Error { message }) => message.starts_with(TAG),
                Err(e) => {
                    e.contains("generic parameter shadowed")
                        && e.contains(&format!("source function `{callee}`"))
                }
                _ => false,
            },
        };
        println!(
            "{func}: expect={expect:?} got={} {}",
            render(&r),
            if ok { "ok" } else { "MISMATCH" }
        );
        if !ok {
            failures.push(format!("{func}: expected {expect:?}, got {}", render(&r)));
        }
    }
    assert!(
        failures.is_empty(),
        "{} mismatch(es):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

use Expect::{Refused, RefusedAtCallee, Refuted, Verified};

/// The backlog program: a generic `W` read as the file's `struct W`, whose
/// inherent `five` is `5`. `X::five` is `7`.
const SRC_INHERENT: &str = r#"
#![allow(dead_code, unused)]
struct W;
impl W {
    fn five() -> u8 { 5 }
    fn new() -> W { W }
    fn val(&self) -> u8 { 5 }
}
trait Val {
    fn five() -> u8;
    fn new() -> Self;
    fn val(&self) -> u8;
}
enum E { A }
impl E { fn five() -> u8 { 5 } }
struct X;
impl Val for X {
    fn five() -> u8 { 7 }
    fn new() -> X { X }
    fn val(&self) -> u8 { 7 }
}

#[trust_vc::ensures(true)]
fn gp1_path_call_liar<W: Val>() { let r = W::five(); assert!(r == 5u8); }

#[trust_vc::ensures(true)]
fn gp2_enum_liar<E: Val>() { let r = E::five(); assert!(r == 5u8); }

#[trust_vc::ensures(result == 5u8)]
fn gp3_return_liar<W: Val>() -> u8 { W::five() }

#[trust_vc::ensures(true)]
fn gp4_constructor_liar<W: Val>() { let w = W::new(); assert!(w.val() == 5u8); }

struct H<Y>(Y);
impl<W: Val> H<W> {
    #[trust_vc::ensures(result == 5u8)]
    fn gp5_impl_generic_liar(&self) -> u8 { W::five() }
}

#[trust_vc::ensures(true)]
fn gp6_closure_liar<W: Val>() { let c = || W::five(); assert!(c() == 5u8); }

#[trust_vc::ensures(result == W::five())]
fn helper<W: Val>() -> u8 { W::five() }

#[trust_vc::ensures(true)]
fn c1_callee_contract_liar() { let r = helper::<X>(); assert!(r == 5u8); }

#[trust_vc::spec]
fn sp<W: Val>() -> u8 { W::five() }

#[trust_vc::ensures(result == 5u8)]
fn c2_spec_body_liar() -> u8 { sp::<X>() }

#[trust_vc::requires(x == sp::<X>())]
#[trust_vc::ensures(x == 5u8)]
fn c3_spec_requires_liar(x: u8) {}
"#;

/// An impl generic `W` read as the file's `#[derive(PartialEq)] struct W`, a
/// unit struct, so `a == b` looked true for every `a` and `b`.
const SRC_IMPL_SIGNATURE: &str = r#"
#![allow(dead_code, unused)]
#[derive(PartialEq, Clone, Copy)]
struct W;
struct H<W>(W);
impl<W: PartialEq + Copy> H<W> {
    #[trust_vc::ensures(a == b)]
    fn s6_method_signature_liar(&self, a: W, b: W) {}
}
"#;

/// The same file types, with generics spelled unlike them.
const SRC_TWINS: &str = r#"
#![allow(dead_code, unused)]
#[derive(PartialEq, Clone, Copy)]
struct W;
impl W { fn five() -> u8 { 5 } }
trait Val { fn five() -> u8; }

#[trust_vc::ensures(true)]
fn t1_inherent_call() { let r = W::five(); assert!(r == 5u8); }

struct K<Y>(Y);
impl<Y: PartialEq + Copy> K<Y> {
    #[trust_vc::requires(a == b)]
    #[trust_vc::ensures(a == b)]
    fn t2_impl_generic_signature(&self, a: Y, b: Y) {}

    #[trust_vc::ensures(a == b)]
    fn l1_impl_generic_signature_liar(&self, a: Y, b: Y) {}
}
"#;

/// Each liar was `Verified` before the rule covered generics spelled like a
/// file type. The solver still answers `Verified`, and the rule refuses that
/// answer: only a `Verified` answer is turned into the tagged `Error`.
#[test]
fn a_generic_spelled_like_a_file_type_is_refused() {
    check_table(
        SRC_INHERENT,
        &[
            ("gp1_path_call_liar", Refused),
            ("gp2_enum_liar", Refused),
            ("gp3_return_liar", Refused),
            ("gp4_constructor_liar", Refused),
            ("gp5_impl_generic_liar", Refused),
            ("gp6_closure_liar", Refused),
            ("c1_callee_contract_liar", RefusedAtCallee("helper")),
            ("c2_spec_body_liar", RefusedAtCallee("sp")),
            ("c3_spec_requires_liar", RefusedAtCallee("sp")),
        ],
    );
    check_table(SRC_IMPL_SIGNATURE, &[("s6_method_signature_liar", Refused)]);
}

#[test]
fn generics_spelled_unlike_the_file_types_still_verify() {
    check_table(
        SRC_TWINS,
        &[
            ("t1_inherent_call", Verified),
            ("t2_impl_generic_signature", Verified),
            ("l1_impl_generic_signature_liar", Refuted),
        ],
    );
}
