//! A WRITE in a file whose declared-width lane is OFF (a glob import), and
//! a `choose!` in any file, binds its value at the slot's type
//! (design-trust-proof-backend.md §5b rule 12). Every `never_*` goal is false
//! (or the program is one Rust rejects) and was `Verified` before this rule;
//! every `true_*` twin is the honest reading and must not be refuted; every
//! `verified_*` twin must be `Verified`.
//!
//! An assignment routed through `render_bound_at_ascription`, whose lane-off
//! all-unsuffixed exemption and `choose!` exemption returned the value BARE:
//! `v = seq![300]` under `Seq<u8>` held 300, `v = seq![2147483647]` under
//! `Seq<i64>` read `v[0] + 1` in `i32` (its true twin was REFUTED), and `v =
//! choose!(|t: (int, int)| t == w)` under `(u8, u8)` held 300. The `let`
//! form of the same shapes is pinned here too: an all-literal composite whose
//! width the file cannot decide is refused.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

/// The declared-width lane is OFF for this file (a glob import). The glob is
/// over std: a glob from outside the file can bind the primitive type names
/// this file spells, so the type-name rule
/// (`vc_extraction::type_name_rebinding`) would refuse a `Verified` answer
/// anywhere in it, and the `verified_*` twin would measure that rule rather
/// than the binder.
const SRC_GLOB: &str = r####"
use std::collections::*;
use trust_vc_types::{int, seq, Seq};

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_glob_assign_seq_u8_literal_300() {
    let mut v: Seq<u8> = seq![1];
    v = seq![300];
    trust_vc::assert!(v[0] == 300);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_glob_assign_seq_i64_literal_wraps() {
    let mut v: Seq<i64> = seq![1];
    v = seq![2147483647];
    trust_vc::assert!(v[0] + 1 == -2147483648);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn true_glob_assign_seq_i64_literal_exact() {
    let mut v: Seq<i64> = seq![1];
    v = seq![2147483647];
    trust_vc::assert!(v[0] + 1 == 2147483648);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_glob_mut_param_assign_seq_u8_literal_300(mut v: Seq<u8>) {
    v = seq![300];
    trust_vc::assert!(v[0] == 300);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_glob_deferred_seq_u8_literal_300() {
    let v: Seq<u8>;
    v = seq![300];
    trust_vc::assert!(v[0] == 300);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_glob_assign_array_u8_300() {
    let mut v: [u8; 1] = [1];
    v = [300];
    trust_vc::assert!(v[0] == 300);
}

#[trust_vc::ensures(true)]
fn never_glob_exec_array_u8_assign_300() {
    let mut v: [u8; 1] = [1];
    v = [300];
    trust_vc::assert!(v[0] == 300);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_glob_let_seq_u8_literal_300() {
    let v: Seq<u8> = seq![300];
    trust_vc::assert!(v[0] == 300);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_glob_let_seq_i64_literal_wraps() {
    let v: Seq<i64> = seq![2147483647];
    trust_vc::assert!(v[0] + 1 == -2147483648);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn true_glob_let_seq_i64_literal_exact() {
    let v: Seq<i64> = seq![2147483647];
    trust_vc::assert!(v[0] + 1 == 2147483648);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_glob_assign_int_from_u8(x: u8) {
    let mut v: int = 0;
    v = x;
    trust_vc::assert!(v + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn verified_glob_assign_int_from_u8(x: u8) {
    let mut v: int = 0;
    v = x;
    trust_vc::assert!(v + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_glob_inferred_assign_from_u8(x: u8, v: int) {
    let mut w = v;
    w = x;
    trust_vc::assert!(w + 1 == 0);
}
"####;

/// The same lane-off writes into slots whose type the file spells with a
/// `std` name (`Option`, `Vec`). A glob from outside the file can bind that
/// name, so the type-name rule (`vc_extraction::type_name_rebinding`) would
/// refuse a `Verified` answer anywhere in such a file; it is kept apart so
/// that `SRC_GLOB`'s `verified_*` twin measures the binder, not that rule.
const SRC_GLOB_STD: &str = r####"
use trust_vc_types::*;

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_glob_assign_option_u8_300() {
    let mut o: Option<u8> = None;
    o = Some(300);
    trust_vc::assert!(o == Some(300));
}

#[trust_vc::ensures(true)]
fn never_glob_exec_vec_u8_assign_300() {
    let mut v: Vec<u8> = vec![1];
    v = vec![300];
    trust_vc::assert!(v[0] == 300);
}
"####;

/// A choose under a composite ascription, in a file whose lane is ON.
const SRC_CHOOSE: &str = r####"
use trust_vc_types::Seq;

#[trust_vc::proof]
#[trust_vc::requires(w.0 == 300)]
#[trust_vc::ensures(true)]
fn never_assign_choose_tuple_int_into_tuple_u8(w: (int, int)) {
    let mut v: (u8, u8) = (0, 0);
    v = trust_vc::choose!(|t: (int, int)| t == w);
    trust_vc::assert!(v.0 == 300);
}

#[trust_vc::proof]
#[trust_vc::requires(w.0 == 300)]
#[trust_vc::ensures(true)]
fn never_param_assign_choose_tuple_int_into_tuple_u8(w: (int, int), mut v: (u8, u8)) {
    v = trust_vc::choose!(|t: (int, int)| t == w);
    trust_vc::assert!(v.0 == 300);
}

#[trust_vc::proof]
#[trust_vc::requires(w.0 == 300)]
#[trust_vc::ensures(true)]
fn never_let_choose_tuple_int_into_tuple_u8(w: (int, int)) {
    let v: (u8, u8) = trust_vc::choose!(|t: (int, int)| t == w);
    trust_vc::assert!(v.0 == 300);
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
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/write_sites_src");
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

fn check(src: &str, file: &str, expected_cases: usize) {
    let names: Vec<&str> = src
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| {
            ["never_", "true_", "verified_", "refused_"]
                .iter()
                .any(|prefix| n.starts_with(prefix))
        })
        .collect();
    assert_eq!(
        names.len(),
        expected_cases,
        "case list truncated: {names:?}"
    );
    let mut wrong = Vec::new();
    for func in names {
        let r = run_source(src, file, func);
        let got = verdict(&r);
        let raw: String = format!("{r:?}").chars().take(240).collect();
        println!("WRITESITE|{func}|{got}|{raw}");
        if func.starts_with("never_") && got == "Verified" {
            wrong.push(format!("FALSE VERIFIED {func}"));
        }
        if func.starts_with("true_") && got == "Refuted" {
            wrong.push(format!("TRUE CLAIM REFUTED {func}: {raw}"));
        }
        if func.starts_with("verified_") && got != "Verified" {
            wrong.push(format!("NOT VERIFIED {func}: {raw}"));
        }
        // A write a slot's type cannot hold is a program Rust rejects, even
        // where the value survives (a slot is never widened: `v = y` of an
        // `i8` into an `i32` binding).
        if func.starts_with("refused_") && got != "Unknown" {
            wrong.push(format!("DECIDED A REFUSED WRITE {func}: {raw}"));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

#[test]
fn a_write_in_a_lane_off_file_binds_at_its_slot_type() {
    check(SRC_GLOB, "write_sites_glob.rs", 13);
    check(SRC_GLOB_STD, "write_sites_glob_std.rs", 2);
}

#[test]
fn a_choose_binds_at_its_slot_type() {
    check(SRC_CHOOSE, "write_sites_choose.rs", 3);
}
