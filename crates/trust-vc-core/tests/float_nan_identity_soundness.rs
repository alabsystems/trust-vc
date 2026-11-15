// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A float comparison is IEEE 754 comparison, and NaN breaks two readings
//! the lane relied on.
//!
//! IEEE order is partial: every comparison with a NaN is false. The lane
//! refuted a goal `a <= b` by asserting `a > b`, which is not its negation
//! over floats, so `assert!(x <= x)` was `Verified` for every `x`.
//!
//! IEEE `==` is not identity: `NaN == NaN` is false and `0.0 == -0.0` is
//! true. The lane wrote `==` for the equations it makes itself (the binding of
//! the return value, a function's definition by its body, the frame of a
//! variable a loop leaves alone), so each one assumed its value is not NaN:
//! `fn f(x: f64) -> f64 { x }` verified `ensures(r == x)`. It also substituted
//! `0.0` for `x` under `requires(x == 0.0)`, which `-0.0` satisfies.
//!
//! Every liar below was `Verified` before the fix, and built with the real
//! macros each one panics when called with a NaN (`z1` with `-0.0`), except
//! the trait default body `dh`: the macros do not check a trait method's
//! `ensures` at run time, but `ensures(x == x)` is false when `dh` returns for
//! a NaN, and every caller assumes it. They are now refuted. The true twins,
//! among them each liar over `u64` or with a clause that admits a NaN, still
//! verify.

use trust_vc_core::{verify_function_from_file, verify_trait_conformance_obligation, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

enum Target<'a> {
    Function(&'a str),
    Conformance(&'a str),
}

fn verify(src: &str, target: &Target<'_>) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_float_nan_identity_{}_{seq}.rs",
        std::process::id()
    ));
    std::fs::write(&path, src).expect("write fixture");
    let file = path.to_str().expect("utf8 path");
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            match target {
                Target::Function(name) => verify_function_from_file(file, name),
                Target::Conformance(name) => verify_trait_conformance_obligation(file, name),
            }
        })
        .map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&path);
    result
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Expect {
    /// A true program: must verify.
    Verified,
    /// A false program: must be refuted.
    Refuted,
}

fn render(r: &Result<VerifyResult, String>) -> String {
    match r {
        Ok(VerifyResult::Verified) => "Verified".into(),
        Ok(VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        }) => format!("Counterexample({obligation_name}, {model:?})"),
        Ok(other) => format!("{:.300}", format!("{other:?}")),
        Err(e) => format!("Err({})", e.chars().take(300).collect::<String>()),
    }
}

fn check(src: &str, table: &[(Target<'_>, Expect)]) {
    let mut failures = Vec::new();
    for (target, expect) in table {
        let name = match target {
            Target::Function(name) | Target::Conformance(name) => *name,
        };
        let r = verify(src, target);
        let ok = match expect {
            Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
            Expect::Refuted => matches!(r, Ok(VerifyResult::Counterexample { .. })),
        };
        println!(
            "{name}: expect={expect:?} got={} {}",
            render(&r),
            if ok { "ok" } else { "MISMATCH" }
        );
        if !ok {
            failures.push(format!("{name}: expected {expect:?}, got {}", render(&r)));
        }
    }
    assert!(
        failures.is_empty(),
        "{} mismatch(es):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

use Expect::{Refuted, Verified};
use Target::{Conformance, Function};

const ORDER_SRC: &str = r#"
#![allow(dead_code, unused)]

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e1(x: f64) -> u64 {
    assert!(x <= x);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e1u(x: u64) -> u64 {
    assert!(x <= x);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e2(x: f64) -> u64 {
    assert!(x >= x);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e3(x: f64) -> u64 {
    trust_vc::assert!(x <= x);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn e4(x: f32, y: f32) -> u64 {
    if !(x < y) {
        assert!(x >= y);
    }
    0u64
}

#[trust_vc::contract(ensures(r), returns(r))]
fn e5(x: f64) -> bool {
    x <= x
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn t1(x: f64) -> u64 {
    assert!(!(x < x));
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn t2(x: f32, y: f32) -> u64 {
    if x <= y {
        assert!(y >= x);
    }
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn t3(x: f64) -> u64 {
    assert!(x <= x || x != x);
    0u64
}
"#;

/// `e1` is the backlog program; `e1u` is its twin over `u64`.
#[test]
fn a_float_order_comparison_is_refuted_by_its_negation() {
    check(
        ORDER_SRC,
        &[
            (Function("e1"), Refuted),
            (Function("e2"), Refuted),
            (Function("e3"), Refuted),
            (Function("e4"), Refuted),
            (Function("e5"), Refuted),
            (Function("e1u"), Verified),
            (Function("t1"), Verified),
            (Function("t2"), Verified),
            (Function("t3"), Verified),
        ],
    );
}

const BINDING_SRC: &str = r#"
#![allow(dead_code, unused)]

#[trust_vc::contract(ensures(r == x), returns(r))]
fn fl(x: f64) -> f64 {
    x
}

#[trust_vc::contract(ensures(r == x), returns(r))]
fn flu(x: u64) -> u64 {
    x
}

#[trust_vc::contract(ensures(x == x), returns(r))]
fn f1(x: f64) -> f64 {
    x
}

#[trust_vc::contract(ensures(r <= x), returns(r))]
fn f4(x: f64) -> f64 {
    x
}

#[trust_vc::contract(ensures(x == x), returns(r))]
fn f5(x: f64, b: bool) -> f64 {
    if b { x } else { x }
}

#[trust_vc::contract(ensures(r == x || x != x), returns(r))]
fn t1(x: f64) -> f64 {
    x
}

#[trust_vc::contract(requires(x == x), ensures(r == x), returns(r))]
fn t2(x: f64) -> f64 {
    x
}

#[trust_vc::contract(ensures(r == 2.0f64), returns(r))]
fn t3() -> f64 {
    2.0f64
}

#[trust_vc::contract(ensures(r <= x || x != x), returns(r))]
fn t4(x: f64) -> f64 {
    x
}
"#;

/// `fl`, `f1` and `f4` are the backlog programs; `flu` is `fl` over `u64`.
#[test]
fn the_return_binding_keeps_a_nan() {
    check(
        BINDING_SRC,
        &[
            (Function("fl"), Refuted),
            (Function("f1"), Refuted),
            (Function("f4"), Refuted),
            (Function("f5"), Refuted),
            (Function("flu"), Verified),
            (Function("t1"), Verified),
            (Function("t2"), Verified),
            (Function("t3"), Verified),
            (Function("t4"), Verified),
        ],
    );
}

const DEFINITION_SRC: &str = r#"
#![allow(dead_code, unused)]

fn id(x: f64) -> f64 {
    x
}

#[trust_vc::spec]
fn sp(x: f64) -> f64 {
    x
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn d1(x: f64) -> u64 {
    let y = id(x);
    assert!(y == y);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn t1(x: f64) -> u64 {
    let y = id(x);
    assert!(y == y || x != x);
    0u64
}

#[trust_vc::contract(ensures(r == 2.0f64), returns(r))]
fn t2() -> f64 {
    id(2.0f64)
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn t3(x: f64) -> u64 {
    trust_vc::assert!(sp(x) == x || x != x);
    0u64
}
"#;

const DEFAULT_SRC: &str = r#"
#![allow(dead_code, unused)]

#[trust_vc::trait_spec]
trait Th {
    #[trust_vc::ensures(x == x)]
    fn dh(x: f64) -> f64 {
        x
    }
}

struct A;

#[trust_vc::trait_impl]
impl Th for A {}
"#;

/// A function's body definition, and a trait default body, keep a NaN.
#[test]
fn a_body_definition_keeps_a_nan() {
    check(
        DEFINITION_SRC,
        &[
            (Function("d1"), Refuted),
            (Function("t1"), Verified),
            (Function("t2"), Verified),
            (Function("t3"), Verified),
        ],
    );
    check(
        DEFAULT_SRC,
        &[
            (Function("dh"), Refuted),
            (Conformance("trait impl conformance Th::dh for A"), Refuted),
        ],
    );
}

const FRAME_SRC: &str = r#"
#![allow(dead_code, unused)]

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn l1(x: f64) -> u64 {
    let mut i = 0u64;
    while i < 2u64 {
        trust_vc::invariant!(i <= 2u64);
        i = i + 1u64;
    }
    assert!(x == x);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn l2(x: f64) -> u64 {
    let mut i = 0u64;
    while i < 2u64 {
        trust_vc::invariant!(i <= 2u64);
        assert!(x == x);
        i = i + 1u64;
    }
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn t1(x: f64) -> u64 {
    let mut i = 0u64;
    while i < 2u64 {
        trust_vc::invariant!(i <= 2u64);
        i = i + 1u64;
    }
    assert!(x == x || x != x);
    0u64
}

#[trust_vc::contract(ensures(r == 0u64), returns(r))]
fn t2(x: u64) -> u64 {
    let mut i = 0u64;
    while i < 2u64 {
        trust_vc::invariant!(i <= 2u64);
        assert!(x == x);
        i = i + 1u64;
    }
    0u64
}
"#;

/// The frame of a variable a loop leaves alone keeps a NaN, after the loop
/// (`l1`) and in its body (`l2`).
#[test]
fn a_loop_frame_keeps_a_nan() {
    check(
        FRAME_SRC,
        &[
            (Function("l1"), Refuted),
            (Function("l2"), Refuted),
            (Function("t1"), Verified),
            (Function("t2"), Verified),
        ],
    );
}

const ZERO_SRC: &str = r#"
#![allow(dead_code, unused)]

#[trust_vc::contract(requires(x == 0.0f64), ensures(r == 0u64), returns(r))]
fn z1(x: f64) -> u64 {
    assert!(1.0f64 / x > 0.0f64);
    0u64
}

#[trust_vc::contract(requires(x == 0.0f64), ensures(r == 0u64), returns(r))]
fn t1(x: f64) -> u64 {
    assert!(x + 1.0f64 == 1.0f64);
    0u64
}
"#;

/// `requires(x == 0.0)` holds for `-0.0`, so it does not make `x` the value
/// `0.0`: `1.0 / -0.0` is negative.
#[test]
fn an_ieee_equality_does_not_substitute_a_float() {
    check(
        ZERO_SRC,
        &[(Function("z1"), Refuted), (Function("t1"), Verified)],
    );
}
