// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A glob import shadows the primitive types. Under `use crate::other::*;`
//! where `other` holds `pub use core::primitive::u8 as u64;`, the spelling
//! `u64` is `u8`, so `(a as u64) / 2 + 200` overflows for `a = 255`. The lane
//! reads a primitive name by its spelling and cannot see what a glob from
//! outside the file brings in, so a file that spells a primitive type name
//! where such a glob reaches gets no `Verified` answer
//! (`vc_extraction::type_name_rebinding`).
//!
//! Every liar below was `Verified` before the rule covered primitive names,
//! and each is false at run time for a source of the glob that renames `u8`
//! to the wider name it spells. Each twin differs from its liar by the one
//! line that holds the glob, which there imports from std or from an inline
//! module of the file, and still verifies.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// The tag every refusal of the type-name rule starts with.
const TAG: &str = "type-name rebinding";

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_glob_import_primitive_name_{}_{}_{seq}.rs",
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
    /// Refused by the type-name rule: an `Error` carrying the tag, naming the
    /// glob and the primitive name it can bind.
    Refused(&'static str),
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

/// Runs every `(program, [(function, expectation)])` row and fails once,
/// listing each mismatch.
fn check_tables(tables: &[(&str, &[(&str, Expect)])]) {
    let mut failures = Vec::new();
    for (src, table) in tables {
        for (func, expect) in *table {
            let r = verify(src, func);
            let ok = match expect {
                Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
                Expect::Refused(name) => matches!(&r, Ok(VerifyResult::Error { message })
                    if message.starts_with(TAG)
                        && message.contains("glob import")
                        && message.contains(&format!("can bind `{name}`"))),
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

/// The backlog program: `other` is a file of the crate this file does not
/// show.
const SRC_CRATE_GLOB: &str = r#"
#![allow(dead_code, unused)]
mod other;
use crate::other::*;

fn g1(a: u8) {
    let y = (a as u64) / 2 + 200;
}
"#;

/// The same program with the glob over std.
const SRC_CRATE_GLOB_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod other;
use std::ops::*;

fn g1(a: u8) {
    let y = (a as u64) / 2 + 200;
}
"#;

/// A glob from another crate, and an associated constant of the primitive.
const SRC_EXTERN_GLOB: &str = r#"
#![allow(dead_code, unused)]
use other_crate::*;

fn x1(a: u8) -> u64 {
    (a as u64) * 2
}

fn x2() {
    assert!(u32::MAX / 4 > 100);
}
"#;

const SRC_EXTERN_GLOB_TWIN: &str = r#"
#![allow(dead_code, unused)]
use std::collections::*;

fn x1(a: u8) -> u64 {
    (a as u64) * 2
}

fn x2() {
    assert!(u32::MAX / 4 > 100);
}
"#;

/// A glob in a body reaches the body.
const SRC_BODY_GLOB: &str = r#"
#![allow(dead_code, unused)]

fn b1(a: u8) {
    use other_crate::*;
    let y = (a as u64) / 2 + 200;
}
"#;

/// The twin's body glob imports from std.
const SRC_BODY_GLOB_TWIN: &str = r#"
#![allow(dead_code, unused)]

fn b1(a: u8) {
    use std::ops::*;
    let y = (a as u64) / 2 + 200;
}
"#;

/// An inline module re-exports a glob from outside the file, and the file
/// imports that module. The twin's module re-exports a module of the file.
const SRC_REEXPORTED_GLOB: &str = r#"
#![allow(dead_code, unused)]
mod m {
    pub use other_crate::*;
}
mod util {
    pub fn helper() {}
}
use m::*;

fn c1(a: u8) {
    let y = (a as u64) / 2 + 200;
}
"#;

const SRC_REEXPORTED_GLOB_TWIN: &str = r#"
#![allow(dead_code, unused)]
mod m {
    pub use super::util::*;
}
mod util {
    pub fn helper() {}
}
use m::*;

fn c1(a: u8) {
    let y = (a as u64) / 2 + 200;
}
"#;

/// A body glob reaches only its own body: a primitive spelled in another
/// function, or in the signature of the glob's own function, keeps its
/// meaning.
const SRC_BODY_GLOB_ELSEWHERE: &str = r#"
#![allow(dead_code, unused)]

fn n1(a: u8) -> u64 {
    (a as u64) / 2 + 200
}

#[trust_vc::ensures(result == 0)]
fn n2(a: u8) -> u64 {
    use other_crate::*;
    0
}
"#;

#[test]
fn a_primitive_name_a_glob_from_outside_the_file_can_bind_is_refused() {
    check_tables(&[
        (SRC_CRATE_GLOB, &[("g1", Refused("u8"))]),
        (
            SRC_EXTERN_GLOB,
            &[("x1", Refused("u8")), ("x2", Refused("u8"))],
        ),
        (SRC_BODY_GLOB, &[("b1", Refused("u64"))]),
        (SRC_REEXPORTED_GLOB, &[("c1", Refused("u8"))]),
    ]);
}

#[test]
fn the_twins_with_a_glob_the_file_can_read_still_verify() {
    check_tables(&[
        (SRC_CRATE_GLOB_TWIN, &[("g1", Verified)]),
        (SRC_EXTERN_GLOB_TWIN, &[("x1", Verified), ("x2", Verified)]),
        (SRC_BODY_GLOB_TWIN, &[("b1", Verified)]),
        (SRC_REEXPORTED_GLOB_TWIN, &[("c1", Verified)]),
        (
            SRC_BODY_GLOB_ELSEWHERE,
            &[("n1", Verified), ("n2", Verified)],
        ),
    ]);
}

/// The same rename reached by a path instead of a glob: `other::u64` is `u8`.
/// The lane does not read a primitive name after a path that does not start at
/// std as that primitive, so these fail closed without the rule. The twin
/// spells the primitive.
const SRC_PATH: &str = r#"
#![allow(dead_code, unused)]
mod other;

fn q1(a: u8) {
    let y = (a as other::u64) / 2 + 200;
}

fn q2(a: u8) -> u64 {
    (a as other_crate::u64) as u64 * 2
}

fn q3() {
    assert!(other::u32::MAX / 4 > 100);
}

fn q4(a: u8) {
    let y = (a as u64) / 2 + 200;
}
"#;

#[test]
fn a_primitive_name_after_a_path_outside_std_is_not_verified() {
    for func in ["q1", "q2", "q3"] {
        let r = verify(SRC_PATH, func);
        println!("{func}: {}", render(&r));
        assert!(
            !matches!(r, Ok(VerifyResult::Verified)),
            "{func}: {}",
            render(&r)
        );
    }
    check_tables(&[(SRC_PATH, &[("q4", Verified)])]);
}
