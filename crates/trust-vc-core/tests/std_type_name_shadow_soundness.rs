// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A std type name the lane gives std meaning (`Vec`, `Box`, `HashSet`, ...)
//! need not denote the std type. A file can declare its own type of that name,
//! import one (`use heapless::Vec;`, `use m::MyVec as Vec;`), alias one
//! (`type Vec<T> = MyVec<T>;`), or spell one through a path that does not
//! start at `std`, `core` or `alloc` (`heapless::Vec<u32, 1>`, `m::Vec<u32>`).
//! The lane reads the spelling, so every such function gets no `Verified`
//! answer (`vc_extraction::type_name_rebinding`).
//!
//! Every liar below is false at run time: its `Vec`, `Box` or `HashSet` does
//! not behave like the std type, and `heapless::Vec` drops a push once it is
//! full. Every twin uses the std types, in a file that also imports and
//! spells them in the ordinary ways (`use std::collections::HashSet;`,
//! `fmt::Result`, `type Result<T> = std::result::Result<T, E1>;`, an enum
//! variant named `String`), and must still verify.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// The tag every refusal of the type-name rule starts with.
const TAG: &str = "type-name rebinding";

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_std_type_name_shadow_{}_{}_{seq}.rs",
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
    /// Refused by the type-name rule: an `Error` carrying the tag.
    Refused,
    /// Refused before any verdict, by the type-name rule or an earlier one.
    FailClosed,
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
            Expect::Refused => {
                matches!(&r, Ok(VerifyResult::Error { message }) if message.starts_with(TAG))
            }
            Expect::FailClosed => matches!(r, Ok(VerifyResult::Error { .. }) | Err(_)),
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

use Expect::{FailClosed, Refused, Verified};

/// The backlog program: a file `struct Vec` whose `push` does nothing.
const SRC_FILE_STRUCT: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]
pub struct Vec<T>(Option<T>);
impl<T> Vec<T> {
    pub fn new() -> Self { Vec(None) }
    pub fn push(&mut self, _x: T) {}
    pub fn len(&self) -> usize { 0 }
    pub fn is_empty(&self) -> bool { false }
}

#[trust_vc::ensures(true)]
fn sv1_push_len_liar() {
    let mut v: Vec<u32> = Vec::new();
    v.push(3);
    assert!(v.len() == 1);
}

#[trust_vc::ensures(true)]
fn sv2_new_is_empty_liar() {
    let v: Vec<u32> = Vec::new();
    assert!(v.is_empty());
}
"#;

const MY_VEC: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]
mod m {
    pub struct MyVec<T>(pub Option<T>);
    impl<T> MyVec<T> {
        pub fn new() -> Self { MyVec(None) }
        pub fn push(&mut self, _x: T) {}
        pub fn len(&self) -> usize { 4 }
        pub fn is_empty(&self) -> bool { true }
    }
}
"#;

const MY_VEC_FNS: &str = r#"
#[trust_vc::ensures(true)]
fn x1_push_len_liar() {
    let mut v: Vec<u32> = Vec::new();
    v.push(3);
    assert!(v.len() == 1);
}

#[trust_vc::ensures(true)]
fn x2_param_liar(v: Vec<u32>) {
    if v.is_empty() {
        assert!(v.len() == 0);
    }
}
"#;

/// `m::Vec` from an inline module.
const SRC_QUALIFIED: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]
mod m {
    pub struct Vec<T>(pub Option<T>);
    impl<T> Vec<T> {
        pub fn new() -> Self { Vec(None) }
        pub fn push(&mut self, _x: T) {}
        pub fn len(&self) -> usize { 4 }
    }
}

#[trust_vc::ensures(true)]
fn m1_inline_module_liar() {
    let mut v: m::Vec<u32> = m::Vec::new();
    v.push(3);
    assert!(v.len() == 1);
}
"#;

/// `m::Vec` from an out-of-line module, which the lane cannot read.
const SRC_OUT_OF_LINE_MODULE: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]
mod m;

#[trust_vc::ensures(true)]
fn o1_out_of_line_module_liar() {
    let mut v: m::Vec<u32> = m::Vec::new();
    v.push(3);
    assert!(v.len() == 1);
}
"#;

/// `heapless::Vec`, imported and spelled in full.
const SRC_HEAPLESS_USE: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]
use heapless::Vec;

#[trust_vc::ensures(true)]
fn h1_use_liar() {
    let mut v: Vec<u32, 2> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    assert!(v.len() == 3);
}
"#;

const SRC_HEAPLESS_PATH: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]

#[trust_vc::ensures(true)]
fn h2_path_liar() {
    let mut v: heapless::Vec<u32, 1> = heapless::Vec::new();
    v.push(1);
    v.push(2);
    assert!(v.len() == 2);
}
"#;

const SRC_BOX: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]
pub struct Box<T>(pub T);
impl<T> Box<T> {
    pub fn new(x: T) -> Self { Box(x) }
}
impl<T> core::ops::Deref for Box<T> {
    type Target = u64;
    fn deref(&self) -> &u64 { &7 }
}

#[trust_vc::ensures(result == 5)]
fn bx1_deref_liar() -> u64 {
    let b = Box::new(5u64);
    *b
}
"#;

const SRC_HASHSET: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]
pub struct HashSet<K>(pub Option<K>);
impl<K> HashSet<K> {
    pub fn new() -> Self { HashSet(None) }
    pub fn len(&self) -> usize { 9 }
}

#[trust_vc::ensures(true)]
fn hs1_new_len_liar() {
    let s: HashSet<u64> = HashSet::new();
    assert!(s.len() == 0);
}
"#;

/// The std types, imported and spelled the ordinary ways.
const SRC_STD_TWINS: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]
use std::collections::HashSet;
use std::fmt;

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct E1(pub u8);
type Result<T> = std::result::Result<T, E1>;

enum Val {
    String(u64),
    Num(u64),
}

struct P;
impl fmt::Display for P {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

#[trust_vc::ensures(true)]
fn t1_std_vec_push_len() {
    let mut v: Vec<u32> = Vec::new();
    v.push(3);
    assert!(v.len() == 1);
}

#[trust_vc::ensures(true)]
fn t2_std_hashset_new_len() {
    let s: HashSet<u64> = HashSet::new();
    assert!(s.len() == 0);
}

#[trust_vc::ensures(result == 5)]
fn t3_std_box_deref() -> u64 {
    let b = Box::new(5u64);
    *b
}

#[trust_vc::ensures(result == x)]
fn t4_enum_variant_named_string(x: u64) -> u64 {
    match Val::String(x) {
        Val::String(y) => y,
        Val::Num(y) => y,
    }
}
"#;

/// Each liar was `Verified` before the rule covered std type names (the
/// `x2` liar under the `type` alias failed closed on its own). With the rule
/// on, the lane refuses each one before it answers.
#[test]
fn a_std_type_name_that_need_not_denote_the_std_type_is_refused() {
    check_table(
        SRC_FILE_STRUCT,
        &[
            ("sv1_push_len_liar", Refused),
            ("sv2_new_is_empty_liar", Refused),
        ],
    );
    let use_rename = format!("{MY_VEC}use m::MyVec as Vec;\n{MY_VEC_FNS}");
    check_table(
        &use_rename,
        &[("x1_push_len_liar", Refused), ("x2_param_liar", Refused)],
    );
    let type_alias = format!("{MY_VEC}type Vec<T> = m::MyVec<T>;\n{MY_VEC_FNS}");
    check_table(
        &type_alias,
        &[("x1_push_len_liar", Refused), ("x2_param_liar", FailClosed)],
    );
    check_table(SRC_QUALIFIED, &[("m1_inline_module_liar", Refused)]);
    check_table(
        SRC_OUT_OF_LINE_MODULE,
        &[("o1_out_of_line_module_liar", Refused)],
    );
    check_table(SRC_HEAPLESS_USE, &[("h1_use_liar", Refused)]);
    check_table(SRC_HEAPLESS_PATH, &[("h2_path_liar", Refused)]);
    check_table(SRC_BOX, &[("bx1_deref_liar", Refused)]);
    check_table(SRC_HASHSET, &[("hs1_new_len_liar", Refused)]);
}

#[test]
fn the_std_types_still_verify() {
    check_table(
        SRC_STD_TWINS,
        &[
            ("t1_std_vec_push_len", Verified),
            ("t2_std_hashset_new_len", Verified),
            ("t3_std_box_deref", Verified),
            ("t4_enum_variant_named_string", Verified),
        ],
    );
}
