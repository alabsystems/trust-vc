// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A glob import shadows the prelude. Under `use heapless::*;`, `Vec` is
//! `heapless::Vec`; under a glob from a crate that exports an enum's variants,
//! `Some(x)` is that crate's variant; and under a glob from a crate that
//! exports its own `Default` trait, `Default::default()` calls that trait. The
//! lane reads these names with their std meaning, and it cannot see what a
//! glob from outside the file brings in. So a file that spells such a name
//! where such a glob reaches gets no `Verified` answer
//! (`vc_extraction::type_name_rebinding`).
//!
//! Every liar below was `Verified` before the rule covered globs, and each is
//! false at run time for some source of the glob: with `heapless` 0.8.0, the
//! second `push` into a `Vec<u32, 1>` is dropped and `v.len()` stays 1; with a
//! crate that exports `pub enum Maybe { Some(u8), None }` through `pub use
//! Maybe::*;` and a `Maybe::is_some` that returns `false`, `o1` panics; with a
//! crate that exports `pub trait Default` implemented for `u64` as `7`, `d1`
//! returns 7. Every twin uses the std types in a file whose globs import from
//! std, from an inline module of the file, or from outside the file into a
//! block that spells none of those names, or next to a `use` from std that
//! wins over the glob; each verified before the rule and must still pass it.
//! The last twin calls `push` where `heapless::*` reaches, and that glob can
//! bring a trait whose `push` Rust picks over `Vec::push`, so the method-call
//! rule (`vc_extraction::trait_method_resolution`) refuses it after this rule
//! lets it through.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// The tag every refusal of the type-name rule starts with.
const TAG: &str = "type-name rebinding";

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_glob_import_std_name_{}_{}_{seq}.rs",
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
    /// Refused by the type-name rule: an `Error` carrying the tag and naming
    /// the glob.
    Refused,
    /// Let through by the type-name rule and refused by the method-call rule,
    /// which runs after it, for a method call the glob's names reach. Only a
    /// `Verified` answer is refused.
    MethodCallRefused,
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
            Expect::Refused => matches!(&r, Ok(VerifyResult::Error { message })
                if message.starts_with(TAG) && message.contains("glob import")),
            Expect::MethodCallRefused => matches!(&r, Ok(VerifyResult::Error { message })
                if message.starts_with("trait method resolution")
                    && message.contains("`use heapless::*`")),
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

use Expect::{MethodCallRefused, Refused, Verified};

/// The backlog program.
const SRC_HEAPLESS_GLOB: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]
use heapless::*;

#[trust_vc::ensures(true)]
fn s5_heapless_glob_liar() {
    let mut v: Vec<u32, 1> = Vec::new();
    v.push(1);
    v.push(2);
    assert!(v.len() == 2);
}
"#;

/// Prelude variants, `Option`, `Result` and `Default` under a glob.
const SRC_VARIANT_GLOB: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]
use other::*;

#[trust_vc::ensures(true)]
fn o1_some_liar(x: u8) {
    let a = Some(x);
    assert!(a.is_some());
}

#[trust_vc::ensures(true)]
fn o2_none_liar() {
    let a: Option<u8> = None;
    assert!(a.is_none());
}

#[trust_vc::ensures(result == Ok(1u8))]
fn o3_ok_liar() -> Result<u8, u8> {
    Ok(1u8)
}

#[trust_vc::ensures(result == 0)]
fn d1_default_liar() -> u64 {
    Default::default()
}
"#;

/// A glob inside a function body.
const SRC_BODY_GLOB: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]

#[trust_vc::ensures(true)]
fn b1_body_glob_liar() {
    use heapless::*;
    let mut v: Vec<u32, 1> = Vec::new();
    v.push(1);
    v.push(2);
    assert!(v.len() == 2);
}
"#;

/// An inline module re-exports the glob, and the file imports that module.
const SRC_REEXPORTED_GLOB: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]
mod m {
    pub use heapless::*;
}
use m::*;

#[trust_vc::ensures(true)]
fn c1_reexported_glob_liar() {
    let mut v: Vec<u32, 1> = Vec::new();
    v.push(1);
    v.push(2);
    assert!(v.len() == 2);
}
"#;

/// `use super::*;` at file scope imports from the parent module, which is not
/// in this file.
const SRC_SUPER_GLOB: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]
use super::*;

#[trust_vc::ensures(true)]
fn p1_super_glob_liar() {
    let mut v: Vec<u32, 1> = Vec::new();
    v.push(1);
    v.push(2);
    assert!(v.len() == 2);
}
"#;

/// Globs over std and over an inline module of the file, and a glob from
/// outside the file inside a block that spells no std name.
const SRC_TWINS: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]
use std::collections::*;

mod util {
    pub fn helper() {}
}
use util::*;

#[trust_vc::ensures(true)]
fn t1_std_vec() {
    let mut v: Vec<u32> = Vec::new();
    v.push(1);
    v.push(2);
    assert!(v.len() == 2);
}

#[trust_vc::ensures(true)]
fn t2_std_some(x: u8) {
    let a = Some(x);
    assert!(a.is_some());
}

pub fn uses_heapless() {
    use heapless::*;
    helper();
}
"#;

/// A `use` from std in the glob's own scope wins over the glob, so `Vec` is
/// std's; the glob can still bring a trait with a `push` method into scope.
/// The element type is `()`: the glob can bind a primitive type name the file
/// spells, which the type-name rule refuses
/// (`glob_import_primitive_name_soundness`).
const SRC_STD_IMPORT_TWIN: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]
use heapless::*;
use std::vec::Vec;

#[trust_vc::ensures(true)]
fn t3_std_import_beats_glob() {
    let mut v: Vec<()> = Vec::new();
    v.push(());
    v.push(());
    assert!(v.len() == 2);
}
"#;

#[test]
fn a_std_name_a_glob_from_outside_the_file_can_bind_is_refused() {
    check_table(SRC_HEAPLESS_GLOB, &[("s5_heapless_glob_liar", Refused)]);
    check_table(
        SRC_VARIANT_GLOB,
        &[
            ("o1_some_liar", Refused),
            ("o2_none_liar", Refused),
            ("o3_ok_liar", Refused),
            ("d1_default_liar", Refused),
        ],
    );
    check_table(SRC_BODY_GLOB, &[("b1_body_glob_liar", Refused)]);
    check_table(SRC_REEXPORTED_GLOB, &[("c1_reexported_glob_liar", Refused)]);
    check_table(SRC_SUPER_GLOB, &[("p1_super_glob_liar", Refused)]);
}

#[test]
fn the_std_types_still_verify_beside_globs_the_file_can_read() {
    check_table(
        SRC_TWINS,
        &[("t1_std_vec", Verified), ("t2_std_some", Verified)],
    );
    check_table(
        SRC_STD_IMPORT_TWIN,
        &[("t3_std_import_beats_glob", MethodCallRefused)],
    );
}
