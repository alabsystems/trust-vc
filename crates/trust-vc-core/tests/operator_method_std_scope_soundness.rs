// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `x.add(e)`, `x.shl(n)` and `x.shr(n)` on a primitive integer are the std
//! operator methods only where `std::ops::Add`, `Shl` or `Shr` is in scope.
//! None of these traits is in the prelude, so without the import the call
//! compiles only because another trait gives the integer a method of that
//! name: a trait of the file, or one a `use` brings in from another crate.
//! The lane used to lower the call to the std operator anyway, so it read
//! `MyAdd::add`, which returns 0, as `x + 1`.
//!
//! The lowering now reads such a call as the std operator only when every
//! call of that method in the file sits where the std trait is imported (by
//! the module holding it, or at the top of the function body holding it), and
//! refuses it otherwise. Every liar below is well typed; run with `trustc`,
//! `s1(5)`, `s3(1)`, `s6(5)` and `s11(5)` return 0, 0, 0 and `false`, `s4(4)`
//! returns 7, `s5(5)` panics, and `c1(5)` and `sp(5)` return 0. Every twin
//! imports the std trait and is true.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_operator_std_scope_{}_{}_{seq}.rs",
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
    /// Refused by the operator-method scope rule: an error naming the trait.
    Refused,
    /// Refused before any verdict, for any reason.
    FailClosed,
    /// Anything but `Verified`.
    NotVerified,
}

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

fn check_table(src: &str, table: &[(&str, Expect)]) {
    let mut failures = Vec::new();
    for (func, expect) in table {
        let r = verify(src, func);
        let ok = match expect {
            Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
            Expect::Refused => match &r {
                Ok(VerifyResult::Error { message }) => {
                    message.contains("is the std operator only where `std::ops::")
                }
                Err(message) => message.contains("is the std operator only where `std::ops::"),
                _ => false,
            },
            Expect::FailClosed => matches!(r, Ok(VerifyResult::Error { .. }) | Err(_)),
            Expect::NotVerified => !matches!(r, Ok(VerifyResult::Verified)),
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

use Expect::{FailClosed, NotVerified, Refused, Verified};

/// A file trait supplies `add`, `shl` and `shr` for `u64`; no std operator
/// trait is imported, so every call below is `MyAdd`'s.
const FILE_TRAIT: &str = r#"
#![allow(dead_code, unused)]

trait MyAdd {
    fn add(self, y: u64) -> u64;
    fn shl(self, y: u32) -> u64;
    fn shr(self, y: u32) -> u64;
}

impl MyAdd for u64 {
    fn add(self, y: u64) -> u64 {
        0
    }
    fn shl(self, y: u32) -> u64 {
        0
    }
    fn shr(self, y: u32) -> u64 {
        7
    }
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == x + 1)]
fn s1(x: u64) -> u64 {
    x.add(1u64)
}

#[trust_vc::requires(x == 1u64)]
#[trust_vc::ensures(result == 2u64)]
fn s3(x: u64) -> u64 {
    x.shl(1u32)
}

#[trust_vc::requires(x == 4u64)]
#[trust_vc::ensures(result == 2u64)]
fn s4(x: u64) -> u64 {
    x.shr(1u32)
}

#[trust_vc::requires(x < 100u64)]
fn s5(x: u64) {
    let y = x.add(1u64);
    assert!(y == x + 1);
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == x + 1)]
fn s6(x: u64) -> u64 {
    u64::add(x, 1u64)
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == x.add(1u64))]
fn s9(x: u64) -> u64 {
    x + 1
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result)]
fn s11(x: u64) -> bool {
    x.add(1u64) == x + 1
}

fn helper(x: u64) -> u64 {
    x.add(1u64)
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == x + 1)]
fn c1(x: u64) -> u64 {
    helper(x)
}

#[trust_vc::spec]
fn sp(x: u64) -> u64 {
    x.add(1u64)
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == sp(x))]
fn c2(x: u64) -> u64 {
    x + 1
}
"#;

/// The same call under a glob from another crate, which may export any
/// trait with an `add` for `u64`.
const FOREIGN_GLOB: &str = r#"
#![allow(dead_code, unused)]

use other::*;

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == x + 1)]
fn g1(x: u64) -> u64 {
    x.add(1u64)
}
"#;

/// The std trait is imported only by a module that does not hold the call,
/// which a module never sees, so the `add` in scope at the call is the one a
/// `use` brings in from another crate.
const PARTIAL_IMPORT: &str = r#"
#![allow(dead_code, unused)]

use other::MyAdd;

mod m {
    use std::ops::Add;
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == x + 1)]
fn p1(x: u64) -> u64 {
    x.add(1u64)
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == 7u64)]
fn p3(x: u64) -> u64 {
    7u64
}
"#;

/// The std traits are imported at the top of the file.
const STD_IMPORT: &str = r#"
#![allow(dead_code, unused)]

use std::ops::{Add, Shl, Shr};

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == x + 1)]
fn t1(x: u64) -> u64 {
    x.add(1u64)
}

#[trust_vc::requires(x == 1u64)]
#[trust_vc::ensures(result == 2u64)]
fn t3(x: u64) -> u64 {
    x.shl(1u32)
}

#[trust_vc::requires(x == 4u64)]
#[trust_vc::ensures(result == 2u64)]
fn t4(x: u64) -> u64 {
    x.shr(1u32)
}

#[trust_vc::requires(x < 100u64)]
fn t5(x: u64) {
    let y = x.add(1u64);
    assert!(y == x + 1);
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == x.add(1u64))]
fn t9(x: u64) -> u64 {
    x + 1
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result)]
fn t11(x: u64) -> bool {
    x.add(1u64) == x + 1
}

#[trust_vc::ensures(true)]
fn x1(x: u64) -> u64 {
    x.add(1u64)
}
"#;

/// Every call sits in a body that imports the std trait at its top.
const BODY_IMPORT: &str = r#"
#![allow(dead_code, unused)]

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == x + 1)]
fn b1(x: u64) -> u64 {
    use std::ops::Add;
    x.add(1u64)
}

#[trust_vc::requires(x == 1u64)]
#[trust_vc::ensures(result == 2u64)]
fn b3(x: u64) -> u64 {
    use core::ops::Shl;
    x.shl(1u32)
}
"#;

#[test]
fn an_operator_method_without_the_std_trait_is_refused() {
    check_table(
        FILE_TRAIT,
        &[
            ("s1", Refused),
            ("s3", Refused),
            ("s4", Refused),
            ("s5", Refused),
            ("s6", FailClosed),
            ("s9", Refused),
            ("s11", Refused),
            // A callee's body and a spec function's body are read the same way.
            ("c1", NotVerified),
            ("c2", NotVerified),
        ],
    );
    check_table(FOREIGN_GLOB, &[("g1", Refused)]);
    check_table(PARTIAL_IMPORT, &[("p1", Refused), ("p3", Verified)]);
}

#[test]
fn an_operator_method_under_the_std_trait_still_verifies() {
    check_table(
        STD_IMPORT,
        &[
            ("t1", Verified),
            ("t3", Verified),
            ("t4", Verified),
            ("t5", Verified),
            ("t9", Verified),
            ("t11", Verified),
        ],
    );
    // The std reading keeps the overflow check.
    let r = verify(STD_IMPORT, "x1");
    assert!(
        matches!(r, Ok(VerifyResult::Counterexample { .. })),
        "x1: {}",
        render(&r)
    );
    check_table(BODY_IMPORT, &[("b1", Verified), ("b3", Verified)]);
}
