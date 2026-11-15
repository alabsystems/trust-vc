// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A type name the file declares, spelled where Rust resolves it to another
//! type, and a ghost scalar name imported from outside this toolchain.
//!
//! The lane reads a type the file declares by its name, whatever inline module
//! holds it. Beside `mod a { pub type W = u64; }`, the `W` of `use c::V as
//! W;` (with `mod c { pub type V = u8; }`), of `use other::W;` and of `type V
//! = other::W;` is not `a::W`, and `v / 2 + 200` over it overflows at `v =
//! 255` when it is `u8`. The lane read every such `W` as `a::W` and answered
//! `Verified`. It also read `int` and `nat` as mathematical types under an
//! import from anywhere (`use crate::other::*;` where `other` holds `pub type
//! int = u8;`).
//!
//! Every liar below was `Verified`, and each is false at run time for a
//! source of the import that binds the narrower type. Each twin differs from
//! its liar by one line, which imports the declaration the lane reads, and
//! still verifies (`vc_extraction::type_name_rebinding`).

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// The tag every refusal of the type-name rule starts with.
const TAG: &str = "type-name rebinding";

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_imported_type_name_{}_{}_{seq}.rs",
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
    /// Refused by the type-name rule: an `Error` carrying the tag and this
    /// text.
    Refused(&'static str),
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

/// Runs every `(program, [(function, expectation)])` row and fails once,
/// listing each mismatch.
fn check_tables(tables: &[(&str, &[(&str, Expect)])]) {
    let mut failures = Vec::new();
    for (src, table) in tables {
        for (func, expect) in *table {
            let r = verify(src, func);
            let ok = match expect {
                Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
                Expect::Refused(text) => matches!(&r, Ok(VerifyResult::Error { message })
                    if message.starts_with(TAG) && message.contains(text)),
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
    }
    assert!(
        failures.is_empty(),
        "{} mismatch(es):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

use Expect::{Refused, Verified};

/// A `use` renames another type to the name an inline module declares.
const SRC_RENAME: &str = r#"
#![allow(dead_code, unused)]
mod a {
    pub type W = u64;
}
mod c {
    pub type V = u8;
}
use c::V as W;

fn h14(v: W) {
    let z = v / 2 + 200;
}
"#;

const SRC_RENAME_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod a {
    pub type W = u64;
}
mod c {
    pub type V = u8;
}
use a::W;

fn h14(v: W) {
    let z = v / 2 + 200;
}
"#;

/// The struct form: `S` is `c::T`, whose `v` is a byte.
const SRC_STRUCT_RENAME: &str = r#"
#![allow(dead_code, unused)]
mod a {
    pub struct S {
        pub v: u64,
    }
}
mod c {
    pub struct T {
        pub v: u8,
    }
}
use c::T as S;

fn h19(s: S) {
    let z = s.v / 2 + 200;
}
"#;

const SRC_STRUCT_RENAME_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod a {
    pub struct S {
        pub v: u64,
    }
}
mod c {
    pub struct T {
        pub v: u8,
    }
}
use a::S;

fn h19(s: S) {
    let z = s.v / 2 + 200;
}
"#;

/// `W` from a file of the crate, and from another crate.
const SRC_OUTSIDE: &str = r#"
#![allow(dead_code, unused)]
mod other;
mod a {
    pub type W = u64;
}
use other::W;

fn h1(v: W) -> W {
    v / 2 + 200
}
"#;

const SRC_OTHER_CRATE: &str = r#"
#![allow(dead_code, unused)]
mod other;
mod a {
    pub type W = u64;
}
use other_crate::W;

fn h1(v: W) -> W {
    v / 2 + 200
}
"#;

const SRC_OUTSIDE_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod other;
mod a {
    pub type W = u64;
}
use a::W;

fn h1(v: W) -> W {
    v / 2 + 200
}
"#;

/// An inline module re-exports `W` from outside the file, and the file
/// imports it from that module by name and by a glob.
const SRC_REEXPORT_NAMED: &str = r#"
#![allow(dead_code, unused)]
mod other;
mod a {
    pub type W = u64;
}
mod b {
    pub use crate::other::W;
}
use b::W;

fn h8(v: W) {
    let z = v / 2 + 200;
}
"#;

const SRC_REEXPORT_NAMED_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod other;
mod a {
    pub type W = u64;
}
mod b {
    pub use super::a::W;
}
use b::W;

fn h8(v: W) {
    let z = v / 2 + 200;
}
"#;

const SRC_REEXPORT_GLOB: &str = r#"
#![allow(dead_code, unused)]
mod other;
mod a {
    pub type W = u64;
}
mod b {
    pub use crate::other::W;
}
use b::*;

fn h7(v: W) {
    let z = v / 2 + 200;
}
"#;

const SRC_REEXPORT_GLOB_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod other;
mod a {
    pub type W = u64;
}
mod b {
    pub use super::a::W;
}
use b::*;

fn h7(v: W) {
    let z = v / 2 + 200;
}
"#;

/// A path through a module the file does not show. (A cast to `other::W` fails
/// closed as a cast to an unknown type.)
const SRC_PATH: &str = r#"
#![allow(dead_code, unused)]
mod other;
mod a {
    pub type W = u64;
}
type V = other::W;

fn h17(v: V) {
    let z = v / 2 + 200;
}
"#;

const SRC_PATH_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod other;
mod a {
    pub type W = u64;
}
type V = a::W;

fn h17(v: V) {
    let z = v / 2 + 200;
}
"#;

/// A module imports `W` while the file root declares it.
const SRC_INNER_IMPORT: &str = r#"
#![allow(dead_code, unused)]
type W = u64;
mod user {
    use other_crate::W;
    pub fn h22(v: W) {
        let z = v / 2 + 200;
    }
}
"#;

const SRC_INNER_RENAME: &str = r#"
#![allow(dead_code, unused)]
type W = u64;
mod c {
    pub type V = u8;
}
mod user {
    use super::c::V as W;
    pub fn h20(v: W) {
        let z = v / 2 + 200;
    }
}
"#;

const SRC_INNER_IMPORT_TWIN: &str = r#"
#![allow(dead_code, unused)]
type W = u64;
mod user {
    use super::W;
    pub fn h22(v: W) {
        let z = v / 2 + 200;
    }
}
"#;

const SRC_INNER_RENAME_TWIN: &str = r#"
#![allow(dead_code, unused)]
type W = u64;
mod c {
    pub type V = u8;
}
mod user {
    use super::W;
    pub fn h20(v: W) {
        let z = v / 2 + 200;
    }
}
"#;

/// A glob from outside the file binds `W`, which the file declares only in
/// `a`. No primitive is spelled, so the primitive glob rule does not apply.
/// Under `other_crate::W = f64`, `r == w` is false for NaN, and the run-time
/// check of the postcondition panics.
const SRC_GLOB: &str = r#"
#![allow(dead_code, unused)]
mod a {
    #[derive(Clone, Copy, PartialEq)]
    pub struct W;
}
use other_crate::*;

#[trust_vc::contract(ensures(r == w), returns(r))]
fn h30(w: W) -> W {
    w
}
"#;

const SRC_GLOB_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod a {
    #[derive(Clone, Copy, PartialEq)]
    pub struct W;
}
use a::*;

#[trust_vc::contract(ensures(r == w), returns(r))]
fn h30(w: W) -> W {
    w
}
"#;

#[test]
fn a_declared_type_name_bound_or_reached_from_elsewhere_is_refused() {
    check_tables(&[
        (
            SRC_RENAME,
            &[("h14", Refused("to an item of another name"))],
        ),
        (
            SRC_STRUCT_RENAME,
            &[("h19", Refused("to an item of another name"))],
        ),
        (
            SRC_OUTSIDE,
            &[("h1", Refused("does not lead to that declaration"))],
        ),
        (
            SRC_OTHER_CRATE,
            &[("h1", Refused("does not lead to that declaration"))],
        ),
        (
            SRC_REEXPORT_NAMED,
            &[("h8", Refused("does not lead to that declaration"))],
        ),
        (
            SRC_REEXPORT_GLOB,
            &[("h7", Refused("does not lead to that declaration"))],
        ),
        (
            SRC_PATH,
            &[("h17", Refused("the path `other :: W` spells `W`"))],
        ),
        (
            SRC_INNER_IMPORT,
            &[("h22", Refused("does not lead to that declaration"))],
        ),
        (
            SRC_INNER_RENAME,
            &[("h20", Refused("to an item of another name"))],
        ),
        (
            SRC_GLOB,
            &[(
                "h30",
                Refused("a type name this file declares in another scope"),
            )],
        ),
    ]);
}

#[test]
fn the_twins_that_import_the_declaration_still_verify() {
    check_tables(&[
        (SRC_RENAME_TWIN, &[("h14", Verified)]),
        (SRC_STRUCT_RENAME_TWIN, &[("h19", Verified)]),
        (SRC_OUTSIDE_TWIN, &[("h1", Verified)]),
        (SRC_REEXPORT_NAMED_TWIN, &[("h8", Verified)]),
        (SRC_REEXPORT_GLOB_TWIN, &[("h7", Verified)]),
        (SRC_PATH_TWIN, &[("h17", Verified)]),
        (SRC_INNER_IMPORT_TWIN, &[("h22", Verified)]),
        (SRC_INNER_RENAME_TWIN, &[("h20", Verified)]),
        (SRC_GLOB_TWIN, &[("h30", Verified)]),
    ]);
}

/// `int` and `nat` from a glob or a `use` outside this toolchain's crates.
/// With `other` holding `pub type int = u8;`, `x * 100` overflows at `x = 3`.
/// The twins import the toolchain's `int` (`i128`) and `nat` (`u128`), where
/// `x * 100` for `0 <= x < 100` fits.
const SRC_INT_GLOB: &str = r#"
#![allow(dead_code, unused)]
mod other;
use crate::other::*;

#[trust_vc::requires(x >= 0 && x < 100)]
fn k1(x: int) {
    let y = x * 100;
}
"#;

const SRC_INT_NAMED: &str = r#"
#![allow(dead_code, unused)]
mod other;
use crate::other::int;

#[trust_vc::requires(x >= 0 && x < 100)]
fn k1(x: int) {
    let y = x * 100;
}
"#;

const SRC_INT_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod other;
use trust_vc_types::int;

#[trust_vc::requires(x >= 0 && x < 100)]
fn k1(x: int) {
    let y = x * 100;
}
"#;

const SRC_NAT_GLOB: &str = r#"
#![allow(dead_code, unused)]
mod other;
use crate::other::*;

#[trust_vc::requires(x < 100)]
fn k5(x: nat) {
    let y = x * 100;
}
"#;

const SRC_NAT_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod other;
use trust_vc_types::nat;

#[trust_vc::requires(x < 100)]
fn k5(x: nat) {
    let y = x * 100;
}
"#;

/// An inline module imports `int` from the file root, which imports it from
/// another file of the crate. The twin's root imports the toolchain's.
const SRC_INT_CHAIN: &str = r#"
#![allow(dead_code, unused)]
mod other;
use crate::other::int;

mod m {
    use super::int;

    #[trust_vc::requires(x >= 0 && x < 100)]
    pub fn k6(x: int) {
        let y = x * 100;
    }
}
"#;

const SRC_INT_CHAIN_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod other;
use trust_vc_types::int;

mod m {
    use super::int;

    #[trust_vc::requires(x >= 0 && x < 100)]
    pub fn k6(x: int) {
        let y = x * 100;
    }
}
"#;

#[test]
fn a_ghost_scalar_from_outside_the_toolchain_is_refused() {
    check_tables(&[
        (SRC_INT_GLOB, &[("k1", Refused("can bind `int`"))]),
        (
            SRC_INT_NAMED,
            &[("k1", Refused("binds the ghost scalar name `int`"))],
        ),
        (SRC_NAT_GLOB, &[("k5", Refused("can bind `nat`"))]),
        (
            SRC_INT_CHAIN,
            &[("k6", Refused("binds the ghost scalar name `int`"))],
        ),
    ]);
}

#[test]
fn the_twins_that_import_the_toolchain_scalars_still_verify() {
    check_tables(&[
        (SRC_INT_TWIN, &[("k1", Verified)]),
        (SRC_NAT_TWIN, &[("k5", Verified)]),
        (SRC_INT_CHAIN_TWIN, &[("k6", Verified)]),
    ]);
}

/// A file that binds the name of a crate of this toolchain to something
/// else: `mod vstd;` beside `vstd.rs` holding `pub type int = u8;`, a module
/// `trust_vc_types`, another crate under that name, or `use other as vstd;`.
/// `use vstd::int;` and the globs then import from that module, so `x * 100`
/// overflows at `x = 3`, while the lane read the toolchain's `int` and `nat`.
/// Each twin binds the module under another name, or imports the crate
/// itself, so `vstd` and `trust_vc_types` are the toolchain's.
const SRC_VSTD_MODULE: &str = r#"
#![allow(dead_code, unused)]
mod vstd;
use vstd::int;

#[trust_vc::requires(x >= 0 && x < 100)]
fn v1(x: int) {
    let y = x * 100;
}
"#;

const SRC_VSTD_MODULE_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod other;
use vstd::int;

#[trust_vc::requires(x >= 0 && x < 100)]
fn v1(x: int) {
    let y = x * 100;
}
"#;

const SRC_VSTD_GLOB: &str = r#"
#![allow(dead_code, unused)]
mod vstd;
use vstd::*;

#[trust_vc::requires(x >= 0 && x < 100)]
fn v2(x: int) {
    let y = x * 100;
}
"#;

const SRC_VSTD_GLOB_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod other;
use vstd::*;

#[trust_vc::requires(x >= 0 && x < 100)]
fn v2(x: int) {
    let y = x * 100;
}
"#;

const SRC_VSTD_PRELUDE: &str = r#"
#![allow(dead_code, unused)]
mod vstd;
use vstd::prelude::*;

#[trust_vc::requires(x >= 0 && x < 100)]
fn v8(x: int) {
    let y = x * 100;
}
"#;

const SRC_VSTD_PRELUDE_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod other;
use vstd::prelude::*;

#[trust_vc::requires(x >= 0 && x < 100)]
fn v8(x: int) {
    let y = x * 100;
}
"#;

const SRC_TYPES_MODULE: &str = r#"
#![allow(dead_code, unused)]
mod trust_vc_types;
use trust_vc_types::nat;

#[trust_vc::requires(x < 100)]
fn v6(x: nat) {
    let y = x * 100;
}
"#;

const SRC_TYPES_MODULE_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod other;
use trust_vc_types::nat;

#[trust_vc::requires(x < 100)]
fn v6(x: nat) {
    let y = x * 100;
}
"#;

const SRC_TYPES_EXTERN: &str = r#"
#![allow(dead_code, unused)]
extern crate other_crate as trust_vc_types;
use trust_vc_types::int;

#[trust_vc::requires(x >= 0 && x < 100)]
fn v3(x: int) {
    let y = x * 100;
}
"#;

const SRC_TYPES_EXTERN_TWIN: &str = r#"
#![allow(dead_code, unused)]
extern crate trust_vc_types;
use trust_vc_types::int;

#[trust_vc::requires(x >= 0 && x < 100)]
fn v3(x: int) {
    let y = x * 100;
}
"#;

const SRC_VSTD_RENAME: &str = r#"
#![allow(dead_code, unused)]
mod other;
use other as vstd;
use vstd::int;

#[trust_vc::requires(x >= 0 && x < 100)]
fn k11(x: int) {
    let y = x * 100;
}
"#;

const SRC_VSTD_RENAME_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod other;
use other as vstd2;
use vstd::int;

#[trust_vc::requires(x >= 0 && x < 100)]
fn k11(x: int) {
    let y = x * 100;
}
"#;

#[test]
fn a_toolchain_crate_name_the_file_binds_elsewhere_is_refused() {
    let text = "the name of a crate of this toolchain";
    check_tables(&[
        (SRC_VSTD_MODULE, &[("v1", Refused(text))]),
        (SRC_VSTD_GLOB, &[("v2", Refused(text))]),
        (SRC_VSTD_PRELUDE, &[("v8", Refused(text))]),
        (SRC_TYPES_MODULE, &[("v6", Refused(text))]),
        (SRC_TYPES_EXTERN, &[("v3", Refused(text))]),
        (SRC_VSTD_RENAME, &[("k11", Refused(text))]),
    ]);
}

#[test]
fn the_twins_that_leave_the_toolchain_crate_names_alone_still_verify() {
    check_tables(&[
        (SRC_VSTD_MODULE_TWIN, &[("v1", Verified)]),
        (SRC_VSTD_GLOB_TWIN, &[("v2", Verified)]),
        (SRC_VSTD_PRELUDE_TWIN, &[("v8", Verified)]),
        (SRC_TYPES_MODULE_TWIN, &[("v6", Verified)]),
        (SRC_TYPES_EXTERN_TWIN, &[("v3", Verified)]),
        (SRC_VSTD_RENAME_TWIN, &[("k11", Verified)]),
    ]);
}
