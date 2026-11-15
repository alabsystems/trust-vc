//! Two more places a value was re-read at a type that is not its own
//! (design-trust-proof-backend.md §5b rules 2 and 10), measured by the r9
//! verifier identically at 44e93f72 and 50b27076:
//!
//! * a `take`/`skip` COUNT was lifted to a length UNSIGNED
//!   (`collection_shared.rs` `len_match_sort` lifts every bit-vector with
//!   `bv2int`), whatever the count's own sign: with `s: Seq<u8>`,
//!   `s.len() == 300` and `n: i8 == -1`, `s.skip(n).len() == 45` and
//!   `s.take(n).len() == 255` were `Verified` (proof and exec), and for `n:
//!   i16 == -1`, `s.len() == 70000`, `s.take(n).len() == 65535`. An `int`
//!   count met no `0 <= n` obligation at all (`subrange`'s start has one), so
//!   `s.skip(-1 as int).len() == 301` was `Verified`;
//! * a SUFFIXED literal `match` pattern of another type of the same width was
//!   compared by its bits (only the widths were checked): `match x_u8 { -1i8
//!   => 1, _ => 0 }` took the arm at 255, and `match y_i8 { 200u8 => 1, _ =>
//!   0 }` at -56. A pattern is bound at the scrutinee's type by its VALUE,
//!   which that type must hold.
//!
//! `never_*` must not be `Verified`; `verified_*` must be `Verified`.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
use trust_vc_types::Seq;

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(n == -1)]
#[trust_vc::ensures(s.skip(n).len() == 45)]
fn never_skip_neg1_i8_len_45(s: Seq<u8>, n: i8) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(n == -1)]
#[trust_vc::ensures(s.take(n).len() == 255)]
fn never_take_neg1_i8_len_255(s: Seq<u8>, n: i8) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(n == -1)]
#[trust_vc::ensures(s.skip(n).len() < s.len())]
fn never_skip_neg1_i8_shorter(s: Seq<u8>, n: i8) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 70000)]
#[trust_vc::requires(n == -1)]
#[trust_vc::ensures(s.take(n).len() == 65535)]
fn never_take_neg1_i16_len_65535(s: Seq<u8>, n: i16) {}

#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(n == -1)]
fn never_exec_skip_neg1_i8_len_45(s: Seq<u8>, n: i8) {
    trust_vc::assert!(s.skip(n).len() == 45);
}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(s.skip(-1 as int).len() == 301)]
fn never_skip_int_neg1_len_301(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(s.skip(0int - 1int).len() == 301)]
fn never_skip_int_expr_neg1_len_301(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(s.take(-1 as int).len() == -1)]
fn never_take_int_neg1_len_neg1(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(n == 5)]
#[trust_vc::ensures(s.skip(n).len() == 295 && s.take(n).len() == 5)]
fn verified_skip_take_i8_5(s: Seq<u8>, n: i8) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(n == 7)]
#[trust_vc::ensures(s.skip(n).len() == 293 && s.take(n).len() == 7)]
fn verified_skip_take_int_7(s: Seq<u8>, n: int) {}

#[trust_vc::spec]
fn pat_neg(x: u8) -> int {
    match x {
        -1i8 => 1,
        _ => 0,
    }
}

#[trust_vc::spec]
fn pat_200(y: i8) -> int {
    match y {
        200u8 => 1,
        _ => 0,
    }
}

#[trust_vc::spec]
fn pat_ok(x: u8) -> int {
    match x {
        7u8 => 1,
        200 => 2,
        _ => 0,
    }
}

#[trust_vc::proof]
#[trust_vc::ensures(pat_neg(255u8) == 1)]
fn never_pat_neg1_i8_matches_u8_255() {}

#[trust_vc::proof]
#[trust_vc::ensures(pat_200(-56i8) == 1)]
fn never_pat_200u8_matches_i8_neg56() {}

#[trust_vc::proof]
#[trust_vc::ensures(pat_ok(7u8) == 1 && pat_ok(200u8) == 2 && pat_ok(8u8) == 0)]
fn verified_pat_of_the_scrutinee_type() {}
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
    let path = dir.join("integer_typing_counts_and_patterns.rs");
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
fn counts_and_literal_patterns_are_read_at_their_own_values() {
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
        println!("COUNTPAT|{func}|{got}|{raw}");
        if func.starts_with("never_") && got == "Verified" {
            wrong.push(format!("FALSE VERIFIED {func}"));
        }
        if func.starts_with("verified_") && got != "Verified" {
            wrong.push(format!("NOT VERIFIED {func}: {got}"));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
