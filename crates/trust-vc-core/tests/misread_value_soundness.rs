//! Values the lowering or the encoder read as something the program does not
//! hold. Each group is one cause:
//!
//! * an unsuffixed float literal is an exact `real` to the lowering (the
//!   value it has next to a `real` peer), so `let f: f64 = 300.0` held the
//!   real 300 and `f as u8` floored and wrapped to 44 (Rust saturates to 255;
//!   `-1.5 as i8` is -1, not -2), and `0.1 + 0.2 == 0.3` held: a float slot
//!   now refuses an exact value, an exact real is never cast to a fixed-width
//!   integer, and an operation over float literals alone is refused;
//! * an inlined closure's result was not bound at its declared result type:
//!   `let f: SpecFn<int, nat> = |a: int| a;` gave `f(-1) < 0`;
//! * a read past the end of a sequence, in a spec function's defining axiom
//!   (where no bounds obligation is checked), was the carrier's cell, which an
//!   in-domain update shares with its receiver: `s.update(5, 7u8)[300] ==
//!   s[300]` held for `s.len() == 300`, which Verus does not state
//!   (`axiom_seq_update_different` is in domain only).
//!
//! Every `never_*` goal is false or its program panics and must not be
//! `Verified`; every `verified_*` twin must be `Verified`; every `true_*` twin
//! is the honest reading and must not be refuted.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC_FLOAT: &str = r####"
#[trust_vc::ensures(result == 44u8)]
fn never_f64_300_to_u8_wraps() -> u8 {
    let f: f64 = 300.0;
    f as u8
}

#[trust_vc::ensures(result == -24i8)]
fn never_f64_1000_to_i8_wraps() -> i8 {
    let f: f64 = 1000.0;
    f as i8
}

#[trust_vc::ensures(result == 255u8)]
fn never_f64_neg_to_u8_wraps() -> u8 {
    let f: f64 = -1.0;
    f as u8
}

#[trust_vc::ensures(result == 44u8)]
fn never_f32_300_to_u8_wraps() -> u8 {
    let f: f32 = 300.0;
    f as u8
}

#[trust_vc::ensures(result != 255u8)]
fn never_f64_huge_to_u8_not_saturated() -> u8 {
    let f: f64 = 1.0e10;
    f as u8
}

#[trust_vc::requires(y == 100u8)]
fn never_f64_cast_then_overflow(y: u8) {
    let f: f64 = 300.0;
    let b = f as u8;
    let z = b + y;
}

#[trust_vc::ensures(result == -2i8)]
fn never_f64_neg_fraction_to_i8_floors() -> i8 {
    let f: f64 = -1.5;
    f as i8
}

fn never_f64_sum_is_exact() {
    let a: f64 = 0.1;
    let b: f64 = 0.2;
    trust_vc::assert!(a + b == 0.3);
}

fn never_f32_add_one_grows() {
    let a: f32 = 16777216.0;
    trust_vc::assert!(a + 1.0 > a);
}

fn never_unascribed_sum_is_exact() {
    let a = 0.1;
    let b = 0.2;
    trust_vc::assert!(a + b == 0.3);
}

#[trust_vc::ensures(result == 44u8)]
fn never_unascribed_300_to_u8_wraps() -> u8 {
    let f = 300.0;
    f as u8
}

#[trust_vc::requires(y == 100u8)]
fn never_literal_cast_then_overflow(y: u8) {
    let b = 300.0 as u8;
    let z = b + y;
}

#[trust_vc::ensures(result == 44u8)]
fn never_assigned_f64_300_to_u8_wraps() -> u8 {
    let mut f: f64 = 0.0f64;
    f = 300.0;
    f as u8
}

#[trust_vc::ensures(result == -1i8)]
fn true_f64_neg_fraction_to_i8_truncates() -> i8 {
    let f: f64 = -1.5;
    f as i8
}

#[trust_vc::ensures(result == 255u8)]
fn true_f64_300_to_u8_saturates() -> u8 {
    let f: f64 = 300.0;
    f as u8
}

#[trust_vc::ensures(result == 0u8)]
fn true_f64_neg_to_u8_zero() -> u8 {
    let f: f64 = -1.0;
    f as u8
}
"####;

const SRC_SPEC_CLOSURE_RESULT: &str = r####"
use trust_vc_types::SpecFn;

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_specfn_nat_result_negative() {
    let f: SpecFn<int, nat> = |a: int| a;
    trust_vc::assert!(f(-1) < 0);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_specfn_u8_result_300() {
    let f: SpecFn<int, u8> = |a: int| a;
    trust_vc::assert!(f(300) == 300);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_specfn_nat_result_arith() {
    let f: SpecFn<int, nat> = |a: int| a - 5;
    trust_vc::assert!(f(0) == -5);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_closure_return_type_nat_negative() {
    let f = |a: int| -> nat { a };
    trust_vc::assert!(f(-1) < 0);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn verified_specfn_int_result_negative() {
    let f: SpecFn<int, int> = |a: int| a;
    trust_vc::assert!(f(-1) < 0);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn verified_specfn_nat_result_of_nat() {
    let f: SpecFn<nat, nat> = |a: nat| a;
    trust_vc::assert!(f(3) == 3);
}
"####;

const SRC_UPDATE_READ_PAST_END: &str = r####"
use trust_vc_types::Seq;

#[trust_vc::spec]
fn up300(s: Seq<u8>) -> int {
    s.update(5, 7u8)[300] as int
}

#[trust_vc::spec]
fn at300(s: Seq<u8>) -> int {
    s[300] as int
}

#[trust_vc::spec]
fn upd_tied(s: Seq<u8>) -> bool {
    s.update(5, 7u8)[300] == s[300]
}

#[trust_vc::spec]
fn up_i(s: Seq<u8>, i: int) -> int {
    s.update(5, 7u8)[i] as int
}

#[trust_vc::spec]
fn at_i(s: Seq<u8>, i: int) -> int {
    s[i] as int
}

#[trust_vc::spec]
fn up_u(s: Seq<u8>, i: usize) -> u8 {
    s.update(5, 7u8)[i]
}

#[trust_vc::spec]
fn at_u(s: Seq<u8>, i: usize) -> u8 {
    s[i]
}

#[trust_vc::spec]
fn tied_past_end(s: Seq<u8>) -> bool {
    forall(|j: int| !(j >= s.len()) || s.update(5, 7u8)[j] == s[j])
}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(up300(s) == at300(s))]
fn never_update_read_past_end_tied(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(tied_past_end(s))]
fn never_update_read_past_end_tied_quantified(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(upd_tied(s))]
fn never_update_read_past_end_tied_one_fn(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(up_i(s, 400) == at_i(s, 400))]
fn never_update_read_past_end_tied_param(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(up_u(s, 400usize) == at_u(s, 400usize))]
fn never_update_read_past_end_tied_usize(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(up_i(s, 7) == at_i(s, 7))]
fn verified_update_read_other_cell_in_domain(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(up_i(s, 5) == 7)]
fn verified_update_read_written_cell(s: Seq<u8>) {}
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
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/misread_value_src");
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

fn check(src: &str, file: &str, expected: usize) {
    let names: Vec<&str> = src
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| {
            ["never_", "true_", "verified_"]
                .iter()
                .any(|prefix| n.starts_with(prefix))
        })
        .collect();
    assert_eq!(names.len(), expected, "case list truncated: {names:?}");
    let mut wrong = Vec::new();
    for func in names {
        let r = run_source(src, file, func);
        let got = verdict(&r);
        let raw: String = format!("{r:?}").chars().take(240).collect();
        println!("MISREAD|{file}|{func}|{got}|{raw}");
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

#[test]
fn an_unsuffixed_float_literal_is_never_read_as_an_exact_float() {
    check(SRC_FLOAT, "float_literal.rs", 16);
}

#[test]
fn an_inlined_closure_result_binds_at_its_declared_type() {
    check(SRC_SPEC_CLOSURE_RESULT, "spec_closure_result.rs", 6);
}

#[test]
fn a_read_past_the_end_of_a_sequence_is_unspecified_in_an_axiom() {
    check(SRC_UPDATE_READ_PAST_END, "update_read_past_end.rs", 7);
}
