// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A `Drop` impl runs where a value is dropped.
//!
//! The lane does not model the destructor call at the end of a scope, at an
//! overwrite, at `drop(x)` or in the drop glue of a value that holds one. So a
//! panic, an overflow or a callee precondition in a `drop` body was never an
//! obligation of the function that drops the value, and a write the
//! destructor makes through a reference it holds was not seen. A function
//! that can drop a value whose type has a `Drop` impl of the file is now
//! refused a `Verified` answer, and so is every function of a file whose
//! operator or iterator impl for another type drops one.
//!
//! Every liar below was `Verified` on main and fails at run time with the
//! arguments its comment gives (compiled with `trustc`, overflow checks on).
//! Every twin is true and must verify.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Verifies `func` of `src`, written as `lib.rs` in a fresh directory next to
/// the `(name, source)` files of `others`.
fn verify_in_dir(src: &str, others: &[(&str, &str)], func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut dir = std::env::temp_dir();
    dir.push(format!("tvc_drop_impl_{}_{func}_{seq}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create fixture dir");
    for (name, source) in others {
        std::fs::write(dir.join(name), source).expect("write fixture module");
    }
    let path = dir.join("lib.rs");
    std::fs::write(&path, src).expect("write fixture");
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(path.to_str().expect("utf8 path"), func)
        })
        .map_err(|e| e.to_string());
    let _ = std::fs::remove_dir_all(&dir);
    result
}

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    verify_in_dir(src, &[], func)
}

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// A true program: must verify.
    Verified,
    /// A false program refused because it can drop a value with a destructor.
    Dropped,
    /// A false program refuted for a reason of its own.
    Refuted,
}

/// The tag of the refusal.
const DROPPED: &str = "unmodeled drop";

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
        Expect::Dropped => match r {
            Ok(VerifyResult::Error { message }) | Err(message) => message.contains(DROPPED),
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

use Expect::{Dropped, Refuted, Verified};

/// The backlog program.
const SRC_BACKLOG: &str = r#"
pub struct D {
    pub a: u64,
}
impl Drop for D { fn drop(&mut self) { panic!("drop") } }

// dr(D { a: 0 }) panics when `d` is dropped.
#[trust_vc::ensures(true)]
pub fn dr(d: D) {}
"#;

/// [`SRC_BACKLOG`] without its `Drop` impl.
const SRC_BACKLOG_TWIN: &str = r#"
pub struct D {
    pub a: u64,
}

// dr(D { a: 0 }) returns.
#[trust_vc::ensures(true)]
pub fn dr(d: D) {}
"#;

#[test]
fn the_backlog_program_is_refused_and_its_twin_verifies() {
    check_table(SRC_BACKLOG, &[("dr", Dropped)]);
    check_table(SRC_BACKLOG_TWIN, &[("dr", Verified)]);
}

/// The drop sites, the values that hold one, and the destructor bodies.
const SRC_SITES: &str = r#"
pub struct D {
    pub a: u64,
}
impl Drop for D {
    fn drop(&mut self) {
        if self.a == 0u64 {
            panic!("drop")
        }
    }
}

// A parameter dropped at the end of the body: dr(D { a: 0 }) panics.
#[trust_vc::ensures(true)]
pub fn dr(d: D) {}

// A local dropped at the end of its scope: dl() panics.
#[trust_vc::ensures(true)]
pub fn dl() {
    let d = D { a: 0u64 };
}

// An explicit `drop`: dx(D { a: 0 }) panics.
#[trust_vc::ensures(true)]
pub fn dx(d: D) {
    drop(d);
}

// An overwrite drops the old value: dw(D { a: 0 }) panics.
#[trust_vc::ensures(true)]
pub fn dw(mut d: D) {
    d = D { a: 1u64 };
}

// A temporary a helper returns, discarded: dt() panics.
pub fn mk() -> D {
    D { a: 0u64 }
}
#[trust_vc::ensures(true)]
pub fn dt() {
    mk();
}

// The drop glue of a struct runs its field's destructor:
// df(W { d: D { a: 0 }, b: 1 }) panics.
pub struct W {
    pub d: D,
    pub b: u64,
}
#[trust_vc::ensures(result == w.b)]
pub fn df(w: W) -> u64 {
    w.b
}

// A collection and an `Option` of such values: dv(vec![D { a: 0 }]) and
// dopt(Some(D { a: 0 })) panic.
#[trust_vc::ensures(true)]
pub fn dv(v: Vec<D>) {}
#[trust_vc::ensures(true)]
pub fn dopt(o: Option<D>) {}

// An alias of the type: da(D { a: 0 }) panics.
pub type A = D;
#[trust_vc::ensures(true)]
pub fn da(a: A) {}

// A method that takes the value by value: D { a: 0 }.take_a() panics.
impl D {
    #[trust_vc::ensures(result == self.a)]
    pub fn take_a(self) -> u64 {
        self.a
    }
}

// An overflow in the destructor: de(E { a: 0 }) panics.
pub struct E {
    pub a: u64,
}
impl Drop for E {
    fn drop(&mut self) {
        self.a = self.a - 1u64;
    }
}
#[trust_vc::ensures(true)]
pub fn de(e: E) {}

// A callee precondition in the destructor: dp(P { a: 0 }) panics.
#[trust_vc::requires(x > 0u64)]
#[trust_vc::ensures(true)]
pub fn need(x: u64) -> u64 {
    10u64 / x
}
pub struct P {
    pub a: u64,
}
impl Drop for P {
    fn drop(&mut self) {
        need(self.a);
    }
}
#[trust_vc::ensures(true)]
pub fn dp(p: P) {}

// A destructor with a precondition that no drop site establishes: dq()
// panics.
pub struct Q {
    pub a: u64,
}
impl Drop for Q {
    #[trust_vc::requires(self.a > 0u64)]
    fn drop(&mut self) {
        let q = 10u64 / self.a;
    }
}
#[trust_vc::ensures(true)]
pub fn dq() {
    let q = Q { a: 0u64 };
}

// A destructor that writes through the reference it holds: the assertion
// fails once the guard's scope ends, so rv(&mut vec![1]) panics.
pub struct R<'a> {
    pub w: &'a mut Vec<u64>,
}
impl<'a> Drop for R<'a> {
    fn drop(&mut self) {
        self.w.clear();
    }
}
#[trust_vc::requires(v.len() == 1)]
#[trust_vc::ensures(true)]
pub fn rv(v: &mut Vec<u64>) {
    {
        let _r = R { w: v };
    }
    assert!(v.len() == 1);
}

// A type with a destructor declared in an inline module:
// dmod(m::D2 { a: 0 }) panics.
mod m {
    pub struct D2 {
        pub a: u64,
    }
    impl Drop for D2 {
        fn drop(&mut self) {
            panic!("m")
        }
    }
}
#[trust_vc::ensures(true)]
pub fn dmod(d: m::D2) {}

// Twins: they name no value with a destructor, and still verify.
#[trust_vc::ensures(result == x)]
pub fn t2(x: u64) -> u64 {
    x
}
pub struct N {
    pub a: u64,
}
#[trust_vc::ensures(result == n.a)]
pub fn t3(n: N) -> u64 {
    n.a
}
#[trust_vc::requires(v.len() == 1)]
#[trust_vc::ensures(true)]
pub fn t4(v: &mut Vec<u64>) {
    assert!(v.len() == 1);
}

// Refutations are kept.
#[trust_vc::ensures(result == 0u64)]
pub fn x1(x: u64) -> u64 {
    x
}
#[trust_vc::ensures(result == 5u64)]
pub fn x2(d: &D) -> u64 {
    d.a
}
"#;

#[test]
fn every_drop_site_is_refused() {
    check_table(
        SRC_SITES,
        &[
            ("dr", Dropped),
            ("dl", Dropped),
            ("dx", Dropped),
            ("dw", Dropped),
            ("dt", Dropped),
            ("df", Dropped),
            ("dv", Dropped),
            ("dopt", Dropped),
            ("da", Dropped),
            ("take_a", Dropped),
            ("de", Dropped),
            ("dp", Dropped),
            ("dq", Dropped),
            ("rv", Dropped),
            ("dmod", Dropped),
            ("t2", Verified),
            ("t3", Verified),
            ("t4", Verified),
            ("x1", Refuted),
            ("x2", Refuted),
        ],
    );
}

/// A file with an out-of-line module: `other.rs` implements `Drop` for `P`.
const SRC_OUT_OF_LINE: &str = r#"
mod other;

pub struct P {
    pub a: u64,
}

// p1(P { a: 0 }) panics in the destructor `other.rs` declares.
#[trust_vc::ensures(true)]
pub fn p1(p: P) {}

// Names no type of the file.
#[trust_vc::ensures(result == x)]
pub fn t1(x: u64) -> u64 {
    x
}
"#;

const OTHER_RS: &str = r#"
impl Drop for super::P {
    fn drop(&mut self) {
        panic!("other")
    }
}
"#;

#[test]
fn an_out_of_line_module_can_implement_drop_for_a_type_of_the_file() {
    for (func, expect) in [("p1", Dropped), ("t1", Verified)] {
        let r = verify_in_dir(SRC_OUT_OF_LINE, &[("other.rs", OTHER_RS)], func);
        assert!(
            matches(&r, expect),
            "{func}: expected {expect:?}, got {}",
            render(&r)
        );
    }
}

/// A `for` loop runs `It::next` without naming it, and `next` drops a `D`.
const SRC_IMPLICIT: &str = r#"
pub struct D {
    pub a: u64,
}
impl Drop for D {
    fn drop(&mut self) {
        if self.a == 0u64 {
            panic!("drop")
        }
    }
}

pub struct It {
    pub n: u64,
}
impl Iterator for It {
    type Item = u64;
    fn next(&mut self) -> Option<u64> {
        let d = D { a: self.n };
        None
    }
}

// itr(It { n: 0 }) panics in the destructor `next` runs.
#[trust_vc::ensures(true)]
pub fn itr(it: It) {
    for x in it {}
}
"#;

/// [`SRC_IMPLICIT`] without the line in `next` that makes a `D`.
const SRC_IMPLICIT_TWIN: &str = r#"
pub struct D {
    pub a: u64,
}
impl Drop for D {
    fn drop(&mut self) {
        if self.a == 0u64 {
            panic!("drop")
        }
    }
}

pub struct It {
    pub n: u64,
}
impl Iterator for It {
    type Item = u64;
    fn next(&mut self) -> Option<u64> {
        None
    }
}

// itr(It { n: 0 }) returns.
#[trust_vc::ensures(true)]
pub fn itr(it: It) {
    for x in it {}
}
"#;

#[test]
fn a_method_that_syntax_calls_without_naming_it_is_reached() {
    check_table(SRC_IMPLICIT, &[("itr", Dropped)]);
    check_table(SRC_IMPLICIT_TWIN, &[("itr", Verified)]);
}
