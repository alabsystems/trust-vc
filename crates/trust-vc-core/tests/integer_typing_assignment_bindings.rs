//! A literal constructor under a FIXED-WIDTH ascription, every assignment,
//! and a reference alias bind at the declared type
//! (design-trust-proof-backend.md §5b rule 12). Every `never_*` goal is false
//! (or the program is one Rust rejects) and was `Verified` when the r10
//! verifier measured it at 9fd50172 and at its parent; every `verified_*`
//! twin is the honest program and stays decided.
//!
//! * The all-unsuffixed-literal exemption still applied to a fixed-width
//!   ascription, and nothing re-spells a `seq!` literal there: its elements
//!   stayed the `i32` placeholder — never_seq_i64_literal_wraps_at_i32 (the
//!   `verified_*` twin was refuted), never_seq_u64_literal_square_wraps_at_i32
//!   — and `seq![300]` was a `Seq<u8>` holding 300: never_seq_u8_literal_300.
//! * An assignment was bound at the ascription only for a name bound exactly
//!   ONCE in the function by an ascription spelling a primitive: a shadowed
//!   name (never_assign_nat_neg1_shadowed), a `let` shadowing a parameter
//!   (never_param_shadowed_assign_int_from_u8), a `type` alias
//!   (never_assign_alias_nat_neg1) and a compound assignment
//!   (never_compound_assign_nat_sub) were assigned bare.
//! * A `&mut int` ascription was checked only against a direct `&mut x`, so a
//!   reborrow of `x: u8` read `*q + 1` in `u8`: never_mut_ref_int_via_reborrow.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
use trust_vc_types::Seq;

type N = nat;

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_seq_i64_literal_wraps_at_i32() {
    let v: Seq<i64> = seq![2147483647];
    trust_vc::assert!(v[0] + 1 == -2147483648);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn verified_seq_i64_literal_exact() {
    let v: Seq<i64> = seq![2147483647];
    trust_vc::assert!(v[0] + 1 == 2147483648);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_seq_u64_literal_square_wraps_at_i32() {
    let v: Seq<u64> = seq![65536];
    trust_vc::assert!(v[0] * v[0] == 0);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_seq_u8_literal_300() {
    let v: Seq<u8> = seq![300];
    trust_vc::assert!(v[0] == 300);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn verified_seq_u8_literal_200() {
    let v: Seq<u8> = seq![200];
    trust_vc::assert!(v[0] == 200);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_assign_nat_neg1_shadowed() {
    let mut v: nat = 0;
    v = -1;
    trust_vc::assert!(v == -1);
    let v: int = 3;
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_param_shadowed_assign_int_from_u8(x: u8, v: int) {
    let mut v: int = 0;
    v = x;
    trust_vc::assert!(v + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn verified_param_shadowed_assign_int_from_u8(x: u8, v: int) {
    let mut v: int = 0;
    v = x;
    trust_vc::assert!(v + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_assign_alias_nat_neg1() {
    let mut v: N = 0;
    v = -1;
    trust_vc::assert!(v == -1);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_compound_assign_nat_sub() {
    let mut v: nat = 0;
    v -= 1;
    trust_vc::assert!(v < 0);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn verified_compound_assign_nat_add() {
    let mut v: nat = 0;
    v += 1;
    trust_vc::assert!(v == 1);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_mut_ref_int_via_reborrow(x: u8) {
    let r = &mut x;
    let q: &mut int = r;
    trust_vc::assert!(*q + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn verified_mut_ref_u8_via_reborrow(x: u8) {
    let r = &mut x;
    let q: &mut u8 = r;
    trust_vc::assert!(*q == 255);
}
"####;

fn verdict(r: &VerifyResult) -> &'static str {
    match r {
        VerifyResult::Verified => "Verified",
        VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. } => "Refuted",
        _ => "Unknown",
    }
}

fn run_source(func: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/integer_typing_src");
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let path = dir.join("integer_typing_assignment_bindings.rs");
    let mut f = std::fs::File::create(&path).expect("create source");
    f.write_all(SRC.as_bytes()).expect("write source");
    drop(f);
    verify_function_from_file(path.to_str().expect("utf-8 path"), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    })
}

#[test]
fn every_assignment_and_literal_binds_at_its_declared_type() {
    let names: Vec<&str> = SRC
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| n.starts_with("never_") || n.starts_with("verified_"))
        .collect();
    assert_eq!(names.len(), 13, "case list truncated: {names:?}");
    let mut wrong = Vec::new();
    for func in names {
        let r = run_source(func);
        let got = verdict(&r);
        let raw: String = format!("{r:?}").chars().take(220).collect();
        println!("ASSIGN|{func}|{got}|{raw}");
        if func.starts_with("never_") && got == "Verified" {
            wrong.push(format!("FALSE VERIFIED {func}"));
        }
        if func.starts_with("verified_") && got != "Verified" {
            wrong.push(format!("NOT VERIFIED {func}: {got}"));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
