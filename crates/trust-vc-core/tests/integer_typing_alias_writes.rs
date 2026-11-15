//! A write through a `&mut` alias of a struct FIELD or a collection CELL
//! stores one value, bound at the slot's type (design-trust-proof-backend.md
//! §5b rule 12, `bind_written_value`), in the owner AND in every alias that
//! reads it back. The owner's copy was bound; the alias's was the
//! right-hand side as written, so a read through the alias saw an untyped
//! literal (or a `u8` under an `int` field):
//!
//! * `let r = &mut s.g; *r = 200; let z = *r + 100;` (`g: u8`) and `let r =
//!   &mut v[0]; *r = 200; let z = *r + 100;` (`v: Vec<u8>`) were `Verified`
//!   while the program overflows; so were a reborrow `let q = &mut *r;`, a
//!   second write through the alias, and `*r = 255; assert!(*r + 1 > 255)`
//!   — and, before the one binder, the same through `&mut` of a local.
//! * `let r = &mut s.f; *r = x;` (`f: int`, `x: u8 == 255`) read `*r + 1 ==
//!   0` in `u8` (`Verified`, the honest twin refuted).
//!
//! Every `never_*` goal is false or its program panics and must not be
//! `Verified`; every `verified_*` twin differs by one line and must be
//! `Verified`; every `true_*` twin is the honest reading and must not be
//! refuted.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC_ALIAS_WRITES: &str = r####"
struct S2 {
    g: u8,
    h: u8,
}

struct SI {
    f: int,
    g: u8,
}

#[trust_vc::requires(x == 1u8)]
fn never_local_alias_literal_overflow(x: u8) {
    let mut v = x;
    let r = &mut v;
    *r = 200;
    let z = *r + 100;
}

#[trust_vc::requires(x == 1u8)]
fn never_field_alias_literal_overflow(x: u8) {
    let mut s = S2 { g: x, h: x };
    let r = &mut s.g;
    *r = 200;
    let z = *r + 100;
}

#[trust_vc::requires(x == 1u8)]
fn verified_field_alias_literal_no_overflow(x: u8) {
    let mut s = S2 { g: x, h: x };
    let r = &mut s.g;
    *r = 200;
    let z = *r + 50;
}

#[trust_vc::requires(x == 1u8)]
fn never_field_alias_literal_overflow_owner_read(x: u8) {
    let mut s = S2 { g: x, h: x };
    let r = &mut s.g;
    *r = 200;
    let z = s.g + 100;
}

#[trust_vc::requires(x == 1u8)]
fn never_field_alias_assert_wraps(x: u8) {
    let mut s = S2 { g: x, h: x };
    let r = &mut s.g;
    *r = 255;
    trust_vc::assert!(*r + 1 > 255);
}

#[trust_vc::requires(x == 1u8)]
fn never_reborrowed_field_alias_literal_overflow(x: u8) {
    let mut s = S2 { g: x, h: x };
    let r = &mut s.g;
    let q = &mut *r;
    *q = 200;
    let z = *q + 100;
}

#[trust_vc::requires(x == 1u8)]
fn never_field_alias_second_write_overflow(x: u8) {
    let mut s = S2 { g: x, h: x };
    let r = &mut s.g;
    *r = 5;
    *r = 200;
    let z = *r + 100;
}

#[trust_vc::requires(x == 1u8)]
fn never_index_alias_literal_overflow(x: u8) {
    let mut v: Vec<u8> = vec![x];
    let r = &mut v[0];
    *r = 200;
    let z = *r + 100;
}

#[trust_vc::requires(x == 1u8)]
fn verified_index_alias_literal_no_overflow(x: u8) {
    let mut v: Vec<u8> = vec![x];
    let r = &mut v[0];
    *r = 200;
    let z = *r + 50;
}

#[trust_vc::requires(x == 1u8)]
fn never_index_alias_literal_overflow_owner_read(x: u8) {
    let mut v: Vec<u8> = vec![x];
    let r = &mut v[0];
    *r = 200;
    let z = v[0] + 100;
}

#[trust_vc::requires(x == 1u8)]
fn never_index_alias_value_then_literal_overflow(x: u8, y: u8) {
    let mut v: Vec<u8> = vec![x, x];
    let r = &mut v[1];
    *r = y;
    *r = 250;
    let z = *r + 10;
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_int_field_alias_from_u8(x: u8) {
    let mut s = SI { f: 0, g: 0 };
    let r = &mut s.f;
    *r = x;
    trust_vc::assert!(*r + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn true_int_field_alias_from_u8(x: u8) {
    let mut s = SI { f: 0, g: 0 };
    let r = &mut s.f;
    *r = x;
    trust_vc::assert!(*r + 1 == 256);
}
"####;

fn verdict(r: &VerifyResult) -> &'static str {
    match r {
        VerifyResult::Verified => "Verified",
        VerifyResult::Counterexample { .. } => "Refuted",
        VerifyResult::NotProved { .. } => "NotProved",
        _ => "Unknown",
    }
}

fn run_source(src: &str, file: &str, func: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/alias_writes_src");
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let path = dir.join(file);
    let mut f = std::fs::File::create(&path).expect("create source");
    f.write_all(src.as_bytes()).expect("write source");
    drop(f);
    verify_function_from_file(path.to_str().expect("utf-8 path"), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    })
}

#[test]
fn a_write_through_a_field_or_cell_alias_binds_at_the_slot_type() {
    let names: Vec<&str> = SRC_ALIAS_WRITES
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| {
            ["never_", "true_", "verified_"]
                .iter()
                .any(|prefix| n.starts_with(prefix))
        })
        .collect();
    assert_eq!(names.len(), 13, "case list truncated: {names:?}");
    let mut wrong = Vec::new();
    for func in names {
        let r = run_source(SRC_ALIAS_WRITES, "alias_writes.rs", func);
        let got = verdict(&r);
        let raw: String = format!("{r:?}").chars().take(240).collect();
        println!("ALIASWRITE|{func}|{got}|{raw}");
        if func.starts_with("never_") && got == "Verified" {
            wrong.push(format!("FALSE VERIFIED {func}"));
        }
        if func.starts_with("true_") && got == "Refuted" {
            wrong.push(format!("TRUE CLAIM REFUTED {func}: {raw}"));
        }
        if func.starts_with("verified_") && got != "Verified" {
            wrong.push(format!("NOT VERIFIED {func}: {raw}"));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
