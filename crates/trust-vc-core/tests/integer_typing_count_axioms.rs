//! A take/skip/subrange COUNT read inside a spec fn body — a DEFINING AXIOM,
//! which checks no precondition — fixes no out-of-domain length
//! (design-trust-proof-backend.md §5b rule 10, `length_within_domain`).
//!
//! `count_as_length` lifts a count by its own sign and pushes `0 <= n` as an
//! OBLIGATION; a body axiom drops obligations, so the axiom stated
//! `s.take(-1).len() == -1` and `s.skip(-1).len() == len + 1`. Verus leaves
//! `take`/`skip`/`subrange` outside `0 <= n <= len` unspecified and every
//! `len()` is a `nat`, so every `never_*` goal below is unprovable (the
//! requires are satisfiable; `s.len() == 7` contradicts `s.len() == 300`).
//!
//! Measured by the r9 re-verifier (A = 50b27076, B = 3319adfa), each
//! `never_*` `Verified` at B:
//! * i8/i16 counts — introduced by f14723e5 (A read the count unsigned, 255):
//!   never_len_negative_i8, never_vacuous_take_i8,
//!   never_vacuous_take_i8_len_nonneg, never_vacuous_skip_i8,
//!   never_vacuous_skip_i16, never_skip_i8_len301, never_take_i8_len_neg1;
//! * int counts — pre-existing (f14723e5's own `s.skip(-1 as int).len() ==
//!   301` through a spec fn): never_len_negative_int, never_vacuous_skip_int,
//!   never_vacuous_take_int_len_nonneg, never_vacuous_subrange_int,
//!   never_skip_int_len301.
//!
//! `verified_in_domain` pins the in-domain definition: still exact. (With
//! the count a pinned VARIABLE, `requires n == 5`, the same goal needs the
//! domain derived through `bv2int_signed` inside the quantified axiom and
//! timed out under load — a completeness cost of the guarded length, not a
//! wrong verdict.)

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
use trust_vc_types::Seq;

#[trust_vc::spec]
fn skl8(s: Seq<u8>, n: i8) -> int {
    s.skip(n).len() as int
}

#[trust_vc::spec]
fn tkl8(s: Seq<u8>, n: i8) -> int {
    s.take(n).len() as int
}

#[trust_vc::spec]
fn skl16(s: Seq<u8>, n: i16) -> int {
    s.skip(n).len() as int
}

#[trust_vc::spec]
fn skli(s: Seq<u8>, n: int) -> int {
    s.skip(n).len() as int
}

#[trust_vc::spec]
fn tkli(s: Seq<u8>, n: int) -> int {
    s.take(n).len() as int
}

#[trust_vc::spec]
fn subli(s: Seq<u8>, i: int) -> int {
    s.subrange(i, s.len() as int).len() as int
}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(n == -1)]
#[trust_vc::ensures(tkl8(s, n) < 0)]
fn never_len_negative_i8(s: Seq<u8>, n: i8) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(n == -1)]
#[trust_vc::requires(tkl8(s, n) == 255)]
#[trust_vc::ensures(s.len() == 7)]
fn never_vacuous_take_i8(s: Seq<u8>, n: i8) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(n == -1)]
#[trust_vc::requires(tkl8(s, n) >= 0)]
#[trust_vc::ensures(s.len() == 7)]
fn never_vacuous_take_i8_len_nonneg(s: Seq<u8>, n: i8) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(n == -1)]
#[trust_vc::requires(skl8(s, n) == 45)]
#[trust_vc::ensures(s.len() == 7)]
fn never_vacuous_skip_i8(s: Seq<u8>, n: i8) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 70000)]
#[trust_vc::requires(n == -1)]
#[trust_vc::requires(skl16(s, n) == 4465)]
#[trust_vc::ensures(s.len() == 7)]
fn never_vacuous_skip_i16(s: Seq<u8>, n: i16) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(n == -1)]
#[trust_vc::ensures(skl8(s, n) == 301)]
fn never_skip_i8_len301(s: Seq<u8>, n: i8) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(n == -1)]
#[trust_vc::ensures(tkl8(s, n) == -1)]
fn never_take_i8_len_neg1(s: Seq<u8>, n: i8) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(tkli(s, -1) < 0)]
fn never_len_negative_int(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(skli(s, -1) == 45)]
#[trust_vc::ensures(s.len() == 7)]
fn never_vacuous_skip_int(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(tkli(s, -1) >= 0)]
#[trust_vc::ensures(s.len() == 7)]
fn never_vacuous_take_int_len_nonneg(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(subli(s, -1) == 300)]
#[trust_vc::ensures(s.len() == 7)]
fn never_vacuous_subrange_int(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(skli(s, -1) == 301)]
fn never_skip_int_len301(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(skl8(s, 5i8) == 295 && tkl8(s, 5i8) == 5)]
fn verified_in_domain(s: Seq<u8>) {}
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
    let path = dir.join("integer_typing_count_axioms.rs");
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
fn an_out_of_domain_count_in_a_body_axiom_fixes_no_length() {
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
        println!("COUNTAX|{func}|{got}|{raw}");
        if func.starts_with("never_") && got == "Verified" {
            wrong.push(format!("FALSE VERIFIED {func}"));
        }
        if func.starts_with("verified_") && got != "Verified" {
            wrong.push(format!("NOT VERIFIED {func}: {got}"));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
