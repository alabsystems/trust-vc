// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A trust_vc attribute under `#[cfg_attr(<predicate>, ..)]` is read as
//! present whatever the predicate, so a contract gated behind a cfg the build
//! never sets can still be verified from source. The predicate is not
//! evaluated, so the build may leave the attribute out:
//!
//! * a precondition: the body was checked assuming it, and the function the
//!   build runs does not have it (`f4(0)` divides by zero);
//! * a `spec` or `proof` mode: the lane reads the body as ghost code with no
//!   overflow obligation, and reads a call of it from exec code without one,
//!   while the build runs it as an ordinary exec function.
//!
//! A `cfg_attr` that carries one of these now stays beside the attribute it
//! unwraps, so the `cfg` refusal refuses the function and every function that
//! reaches it. A gated postcondition is still read as present: the body is
//! checked against it, and a caller relies only on what that check shows.
//!
//! Every liar below was `Verified` before, and each one panics at run time in
//! a build where the predicate is false (compiled with `trustc`, overflow
//! checks on): `f4`, `f5` (a non-test build), `f7`, `m6` and `f9` with `0`,
//! `f6` (a test build) with `0`, and `u1` to `u5` and `S::f` of
//! `SRC_CONFORMANCE` with `u64::MAX`. Every twin is true and must verify; each
//! `x*` is false and must still be refuted. The file-level trait conformance
//! context has no per-function `cfg` reach, so it is refused when the file
//! gates a precondition or a mode.

use trust_vc_core::{verify_function_from_file, verify_trait_conformance_obligation, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Verifies `name` of `src`: a function, or a trait impl conformance
/// obligation when `name` starts with `trait impl conformance `.
fn verify(src: &str, name: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    let stem: String = name
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    path.push(format!(
        "tvc_cfg_attr_contract_{}_{stem}_{seq}.rs",
        std::process::id()
    ));
    std::fs::write(&path, src).expect("write fixture");
    let file = path.to_str().expect("utf8 path");
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            if name.starts_with("trait impl conformance ") {
                verify_trait_conformance_obligation(file, name)
            } else {
                verify_function_from_file(file, name)
            }
        })
        .map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&path);
    result
}

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// A true program: must verify.
    Verified,
    /// Refused by the `cfg` refusal: its own `cfg_attr`, or one it reaches;
    /// for a conformance obligation, a gated precondition or mode in the file.
    Refused,
    /// A false program the lane still refutes.
    Refuted,
}

/// Both texts of the `cfg` refusal name a `cfg_attr`.
const CFG: &str = "`#[cfg]` / `#[cfg_attr]`";

/// The conformance context's refusal.
const CFG_CONFORMANCE: &str = "a `#[cfg_attr(..)]` gates a precondition or a mode of";

fn render(r: &Result<VerifyResult, String>) -> String {
    match r {
        Ok(VerifyResult::Verified) => "Verified".into(),
        Ok(VerifyResult::Counterexample {
            obligation_name, ..
        }) => format!("Counterexample({obligation_name})"),
        Ok(VerifyResult::Error { message }) => {
            format!("Error({})", message.chars().take(300).collect::<String>())
        }
        Ok(other) => format!("{:.300}", format!("{other:?}")),
        Err(e) => format!("Err({})", e.chars().take(300).collect::<String>()),
    }
}

fn matches(r: &Result<VerifyResult, String>, expect: Expect) -> bool {
    match expect {
        Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
        Expect::Refused => match r {
            Ok(VerifyResult::Error { message }) | Err(message) => {
                message.contains(CFG) || message.contains(CFG_CONFORMANCE)
            }
            _ => false,
        },
        Expect::Refuted => matches!(r, Ok(VerifyResult::Counterexample { .. })),
    }
}

fn check_table(src: &str, table: &[(&str, Expect)]) {
    let mut failures = Vec::new();
    for (func, expect) in table {
        let r = verify(src, func);
        let ok = matches(&r, *expect);
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

use Expect::{Refused, Refuted, Verified};

/// The backlog program.
const SRC_BACKLOG: &str = r#"
#![allow(dead_code, unused)]
#[cfg_attr(any(), trust_vc::requires(x > 0u64))]
fn f4(x: u64) -> u64 {
    10u64 / x
}
"#;

/// The backlog program with the precondition written directly.
const SRC_BACKLOG_TWIN: &str = r#"
#![allow(dead_code, unused)]
#[trust_vc::requires(x > 0u64)]
fn f4(x: u64) -> u64 {
    10u64 / x
}
"#;

const SRC: &str = r#"
#![allow(dead_code, unused)]

#[cfg_attr(test, trust_vc::requires(x > 0u64))]
fn f5(x: u64) -> u64 {
    10u64 / x
}

#[cfg_attr(not(test), trust_vc::requires(x > 0u64))]
fn f6(x: u64) -> u64 {
    10u64 / x
}

#[cfg_attr(trust_vc, trust_vc::contract(requires(x > 0u64)))]
fn f7(x: u64) -> u64 {
    10u64 / x
}

#[cfg_attr(trust_vc, trust_vc::ensures(x >= 1u64), trust_vc::requires(x > 0u64))]
fn f9(x: u64) -> u64 {
    10u64 / x
}

struct S;
impl S {
    #[cfg_attr(any(), trust_vc::requires(x > 0u64))]
    fn m6(&self, x: u64) -> u64 {
        10u64 / x
    }
}

#[cfg_attr(any(), trust_vc::spec)]
fn inc(x: u64) -> u64 {
    x + 1u64
}

#[trust_vc::ensures(true)]
fn u1(x: u64) -> u64 {
    inc(x)
}

#[cfg_attr(any(), trust_vc::proof)]
fn pinc(x: u64) -> u64 {
    x + 1u64
}

#[trust_vc::ensures(true)]
fn u2(x: u64) -> u64 {
    pinc(x)
}

#[cfg_attr(trust_vc, trust_vc::spec)]
fn inc3(x: u64) -> u64 {
    x + 1u64
}

#[trust_vc::ensures(result == inc3(x))]
fn u3(x: u64) -> u64 {
    if x < 10u64 { x + 1u64 } else { inc3(x) }
}

#[cfg_attr(any(), trust_vc::proof)]
#[trust_vc::ensures(true)]
fn u4(x: u64) -> u64 {
    x + 1u64
}

#[cfg_attr(trust_vc, trust_vc::spec)]
fn big(x: u64) -> bool {
    x + 1u64 > 5u64
}

#[trust_vc::ensures(true)]
fn u5(x: u64) {
    if big(x) {
        assert!(x > 4u64);
    }
}

// A gated postcondition is still read and checked.
#[cfg_attr(any(), trust_vc::ensures(result <= x))]
fn half(x: u64) -> u64 {
    x / 2u64
}

#[trust_vc::ensures(result <= x)]
fn t1(x: u64) -> u64 {
    half(x)
}

// `u4` with its gated mode line replaced by a precondition.
#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(true)]
fn t4(x: u64) -> u64 {
    x + 1u64
}

#[cfg_attr(any(), trust_vc::ensures(result == x))]
fn x1(x: u64) -> u64 {
    x / 2u64
}

#[trust_vc::ensures(result == x)]
fn x2(x: u64) -> u64 {
    half(x)
}
"#;

/// A trait impl body that calls a gated spec function: its conformance
/// obligation read the call as ghost code.
const SRC_CONFORMANCE: &str = r#"
#![allow(dead_code, unused)]
#[cfg_attr(any(), trust_vc::spec)]
fn inc(x: u64) -> u64 {
    x + 1u64
}

#[trust_vc::trait_spec]
trait T {
    #[trust_vc::ensures(true)]
    fn f(&self, x: u64) -> u64;
}

struct S;

#[trust_vc::trait_impl]
impl T for S {
    fn f(&self, x: u64) -> u64 {
        inc(x)
    }
}
"#;

/// `SRC_CONFORMANCE` with the gated mode replaced by a gated postcondition
/// and a body that meets it.
const SRC_CONFORMANCE_TWIN: &str = r#"
#![allow(dead_code, unused)]
#[cfg_attr(any(), trust_vc::ensures(result == x / 2u64))]
fn inc(x: u64) -> u64 {
    x / 2u64
}

#[trust_vc::trait_spec]
trait T {
    #[trust_vc::ensures(true)]
    fn f(&self, x: u64) -> u64;
}

struct S;

#[trust_vc::trait_impl]
impl T for S {
    fn f(&self, x: u64) -> u64 {
        inc(x)
    }
}
"#;

const CONFORMANCE: &str = "trait impl conformance T::f for S";

#[test]
fn a_gated_precondition_or_mode_gets_no_verified_answer() {
    check_table(SRC_BACKLOG, &[("f4", Refused)]);
    check_table(
        SRC,
        &[
            ("f5", Refused),
            ("f6", Refused),
            ("f7", Refused),
            ("f9", Refused),
            ("m6", Refused),
            ("u1", Refused),
            ("u2", Refused),
            ("u3", Refused),
            ("u4", Refused),
            ("u5", Refused),
        ],
    );
    check_table(SRC_CONFORMANCE, &[(CONFORMANCE, Refused)]);
}

#[test]
fn a_gated_postcondition_is_still_read_and_checked() {
    check_table(SRC_BACKLOG_TWIN, &[("f4", Verified)]);
    check_table(
        SRC,
        &[
            ("half", Verified),
            ("t1", Verified),
            ("t4", Verified),
            ("x1", Refuted),
            ("x2", Refuted),
        ],
    );
    check_table(SRC_CONFORMANCE_TWIN, &[(CONFORMANCE, Verified)]);
}
