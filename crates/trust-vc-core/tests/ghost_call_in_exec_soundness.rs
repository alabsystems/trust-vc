// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A spec or proof function is ghost code: outside a verification build the
//! `trust_vc` macros expand its body to `loop { unreachable!(..) }`, so a call
//! of it from code that runs panics for every input. The lane read such a call
//! as the function's value (or, for a proof function, its postcondition) with
//! no panic, so an exec function that makes one came back `Verified`.
//!
//! The macros' own mode audit rejects an exec free function of the ghost
//! function's module that calls it by its bare name, and a path call elsewhere
//! in its file that it resolves through the crate, but not a method call
//! (`s.view()`), a path call of a method (`S::view(s)`), or a call in the
//! arguments of a std macro (`assert!`, `vec!`). Compiled with `trustc` and the
//! real `trust_vc` macros (each contract written as `contract(..)` or left
//! out), `a3`, `a11`, `b4`, `b5`, `b7`, `b8`, `b12` and `c1` compile and panic
//! on their first call, and so does `a1` of the two-file crate, which calls a
//! spec function of `specs.rs` from `lib.rs`. `v1` (the backlog program), `b3` and `b11` are path calls the audit rejects; they are
//! refused here too, since the lane cannot tell whether the audit resolves the
//! crate. `a10`, a bare-name call of a spec function of its own module, is the
//! one shape left to the audit.
//!
//! A call in a contract, in `trust_vc::assert!` or in `proof_block!` is ghost
//! code and is unchanged. Every liar is refused; every twin is true and must
//! verify; each `x*` is false and must still be refuted.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Verifies the function `name` of `src`.
fn verify(src: &str, name: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    let stem: String = name
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    path.push(format!(
        "tvc_ghost_call_in_exec_{}_{stem}_{seq}.rs",
        std::process::id()
    ));
    std::fs::write(&path, src).expect("write fixture");
    let file = path.to_str().expect("utf8 path");
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(file, name)
        })
        .map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&path);
    result
}

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// A true program: must verify.
    Verified,
    /// Refused by the ghost-call rule.
    Refused,
    /// A false program the lane still refutes.
    Refuted,
}

/// The tag of the ghost-call refusal.
const GHOST: &str = "ghost function called from exec code";

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
            Ok(VerifyResult::Error { message }) | Err(message) => message.contains(GHOST),
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

/// The ghost functions every fixture declares.
const GHOSTS: &str = r#"
#![allow(dead_code, unused)]
mod m {
    #[trust_vc::spec]
    pub fn inc(x: u64) -> u64 {
        x + 1u64
    }
    #[trust_vc::proof]
    pub fn lemma(x: u64) {}
}
pub struct S {
    a: u64,
}
impl S {
    #[trust_vc::spec]
    pub fn view(&self) -> u64 {
        self.a
    }
}
#[trust_vc::spec]
fn top(x: u64) -> u64 {
    x + 2u64
}
"#;

/// The backlog program and the other calls of a ghost function from code
/// that runs.
const LIARS: &str = r#"
#[trust_vc::ensures(true)]
fn v1(x: u64) -> u64 {
    m::inc(x)
}
#[trust_vc::ensures(true)]
fn a3(s: &S) -> u64 {
    s.view()
}
#[trust_vc::ensures(true)]
fn a11(s: &S) -> u64 {
    S::view(s)
}
#[trust_vc::ensures(true)]
fn b3(x: u64) {
    m::lemma(x);
}
#[trust_vc::ensures(true)]
fn b4(s: &S) {
    assert!(s.view() == s.a);
}
#[trust_vc::ensures(true)]
fn b5(x: u64) -> u64 {
    let v = vec![m::inc(x)];
    v[0]
}
#[trust_vc::ensures(result == s.a)]
fn b7(s: &S) -> u64 {
    s.view()
}
#[trust_vc::ensures(true)]
fn b8(s: &S) -> u64 {
    let v = s.view();
    v
}
#[trust_vc::ensures(true)]
fn b11(x: u64) -> u64 {
    if x < 10u64 { m::inc(x) } else { 0u64 }
}
#[trust_vc::ensures(true)]
fn b12(s: &S) -> bool {
    s.view() == s.view()
}
#[trust_vc::ensures(true)]
fn c1(x: u64) {
    assert!(m::inc(x) >= 0u64);
}
"#;

/// Each twin differs from a liar by one line: the ghost call moves into a
/// contract, `trust_vc::assert!` or `proof_block!`, or a field read takes
/// the place of the spec method. `a10` is left to the macros' audit, which
/// rejects it at compile time.
const TWINS: &str = r#"
#[trust_vc::ensures(true)]
fn a10(x: u64) -> u64 {
    top(x)
}
#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == m::inc(x))]
fn t1(x: u64) -> u64 {
    x + 1u64
}
#[trust_vc::ensures(true)]
fn t3(s: &S) -> u64 {
    s.a
}
#[trust_vc::ensures(true)]
fn t4(s: &S) {
    trust_vc::assert!(s.view() == s.a);
}
#[trust_vc::requires(x < 100u64)]
fn t5(x: u64) {
    trust_vc::assert!(m::inc(x) > x);
    trust_vc::proof_block!({
        m::lemma(x);
    });
}
#[trust_vc::ensures(result == s.view())]
fn t7(s: &S) -> u64 {
    s.a
}
#[trust_vc::ensures(true)]
fn t8(x: u64) -> u64 {
    let inc = x;
    inc
}
#[trust_vc::ensures(true)]
fn x1(s: &S) {
    assert!(s.view() != s.a);
}
#[trust_vc::ensures(result == s.a + 1u64)]
fn x2(s: &S) -> u64 {
    s.view()
}
"#;

#[test]
fn an_exec_call_of_a_ghost_function_is_never_verified() {
    let src = format!("{GHOSTS}{LIARS}");
    check_table(
        &src,
        &[
            ("v1", Refused),
            ("a3", Refused),
            ("a11", Refused),
            ("b3", Refused),
            ("b4", Refused),
            ("b5", Refused),
            ("b7", Refused),
            ("b8", Refused),
            ("b11", Refused),
            ("b12", Refused),
            ("c1", Refused),
        ],
    );
}

#[test]
fn ghost_code_in_an_exec_function_still_verifies() {
    let src = format!("{GHOSTS}{TWINS}");
    check_table(
        &src,
        &[
            ("a10", Verified),
            ("t1", Verified),
            ("t3", Verified),
            ("t4", Verified),
            ("t5", Verified),
            ("t7", Verified),
            ("t8", Verified),
            ("x1", Refuted),
            ("x2", Refuted),
        ],
    );
}

/// A spec function of another file of the crate, imported with `use`. The
/// lane reads it through the crate's spec index; the macros' audit scans only
/// the spec function's own file, so the call in `lib.rs` compiles and panics.
#[test]
fn a_spec_function_imported_from_another_file_is_ghost_code_too() {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let root =
        std::env::temp_dir().join(format!("tvc_ghost_call_crate_{}_{seq}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(root.join("src")).expect("create fixture crate");
    std::fs::write(
        root.join("Cargo.toml"),
        "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    )
    .expect("write manifest");
    std::fs::write(
        root.join("src/specs.rs"),
        "#[trust_vc::spec]\npub fn inc(x: u64) -> u64 {\n    x + 1u64\n}\n",
    )
    .expect("write specs.rs");
    let lib = root.join("src/lib.rs");
    std::fs::write(
        &lib,
        r#"
#![allow(dead_code, unused)]
mod specs;
use crate::specs::inc;

#[trust_vc::ensures(true)]
fn a1(x: u64) -> u64 {
    inc(x)
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == inc(x))]
fn t1(x: u64) -> u64 {
    x + 1u64
}
"#,
    )
    .expect("write lib.rs");
    let path = lib.to_str().expect("utf8 path");
    let mut failures = Vec::new();
    for (func, expect) in [("a1", Refused), ("t1", Verified)] {
        let r = trust_vc_core::env::with_serialized_env_vars(
            &[("TRUST_VC_DISABLE_VC_CACHE", "1")],
            || verify_function_from_file(path, func),
        )
        .map_err(|e| e.to_string());
        println!("{func}: expect={expect:?} got={}", render(&r));
        if !matches(&r, expect) {
            failures.push(format!("{func}: expected {expect:?}, got {}", render(&r)));
        }
    }
    let _ = std::fs::remove_dir_all(&root);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
