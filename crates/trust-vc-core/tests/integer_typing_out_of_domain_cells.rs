//! A collection operation OUTSIDE its domain is unspecified
//! (design-trust-proof-backend.md §5b rule 10): Verus states
//! `axiom_seq_update_len`/`axiom_seq_update_same`/`_different` only for `0 <=
//! i < s.len()`, `take`/`skip` only for `0 <= n <= s.len()`, and a sequence
//! read only for `0 <= i < s.len()`. Each such value is a function of the
//! operation's arguments and of nothing else; in particular two different
//! out-of-domain operations are not related, and no cell of an out-of-domain
//! result is tied to a cell of its receiver.
//!
//! Every `never_*` goal is unprovable in Verus and was `Verified` before the
//! out-of-domain encodings. Each goes through a spec function, whose defining
//! axiom checks no precondition. Every `verified_*` twin is the in-domain
//! reading and must stay `Verified`.
//!
//! * The out-of-domain update length was an uninterpreted function of
//!   `(receiver, len, i)` only, so two updates at the same out-of-domain index
//!   storing different values had the same length.
//! * An out-of-domain update's cells were the receiver's cells (a ground seed
//!   of the receiver array), a `take`/`skip` result's cells were tied to the
//!   receiver's by unguarded ground seeds, and an `int` index was wrapped
//!   into the 64-bit carrier, so `s[-1]` was `s[2^64 - 1]` and `s[2^64]` was
//!   `s[0]`.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
use trust_vc_types::Seq;

#[trust_vc::spec]
fn upl0(s: Seq<u8>, i: int) -> int {
    s.update(i, 0u8).len() as int
}

#[trust_vc::spec]
fn upl7(s: Seq<u8>, i: int) -> int {
    s.update(i, 7u8).len() as int
}

#[trust_vc::spec]
fn upd0(s: Seq<u8>, i: int) -> int {
    s.update(i, 0u8)[0] as int
}

#[trust_vc::spec]
fn updi(s: Seq<u8>, i: int) -> int {
    s.update(i, 7u8)[i] as int
}

#[trust_vc::spec]
fn tk0(s: Seq<u8>, n: int) -> int {
    s.take(n)[0] as int
}

#[trust_vc::spec]
fn tk3(s: Seq<u8>, n: int) -> int {
    s.take(n)[3] as int
}

#[trust_vc::spec]
fn sk1(s: Seq<u8>, n: int) -> int {
    s.skip(n)[1] as int
}

#[trust_vc::spec]
fn at(s: Seq<u8>, i: int) -> int {
    s[i] as int
}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(upl0(s, -1) == upl7(s, -1))]
fn never_update_len_ignores_value(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(upl0(s, 5) == upl7(s, 5))]
fn verified_update_len_in_domain_same(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(upl0(s, 5) == 300)]
fn verified_update_len_in_domain(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(upd0(s, -1) == s[0] as int)]
fn never_update_oob_cell_via_spec(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(updi(s, 18446744073709551616) == 7)]
fn never_update_index_2_pow_64_cell_via_spec(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(upd0(s, 5) == s[0] as int)]
fn verified_update_other_cell_in_domain(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(updi(s, 5) == 7)]
fn verified_update_same_cell_in_domain(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(tk0(s, -1) == s[0] as int)]
fn never_take_neg_cell_via_spec(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(tk3(s, 2) == s[3] as int)]
fn never_take_cell_past_count_via_spec(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(sk1(s, -1) == s[0] as int)]
fn never_skip_neg_cell_via_spec(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(tk0(s, 5) == s[0] as int)]
fn verified_take_cell_in_domain(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(sk1(s, 5) == s[6] as int)]
fn verified_skip_cell_in_domain(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(at(s, -1) == at(s, 18446744073709551615))]
fn never_index_int_wraps_via_spec(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300 && s[0] == 200)]
#[trust_vc::ensures(at(s, 18446744073709551616) == 200)]
fn never_index_2_pow_64_wraps_to_0_via_spec(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300 && s[0] == 200)]
#[trust_vc::ensures(at(s, 0) == 200)]
fn verified_index_in_domain_via_spec(s: Seq<u8>) {}
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
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/out_of_domain_src");
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let path = dir.join("integer_typing_out_of_domain_cells.rs");
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
fn an_operation_outside_its_domain_is_unspecified() {
    let names: Vec<&str> = SRC
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| n.starts_with("never_") || n.starts_with("verified_"))
        .collect();
    assert_eq!(names.len(), 15, "case list truncated: {names:?}");
    let mut wrong = Vec::new();
    for func in names {
        let r = run_source(func);
        let got = verdict(&r);
        let raw: String = format!("{r:?}").chars().take(240).collect();
        println!("OUTOFDOMAIN|{func}|{got}|{raw}");
        if func.starts_with("never_") && got == "Verified" {
            wrong.push(format!("FALSE VERIFIED {func}"));
        }
        if func.starts_with("verified_") && got != "Verified" {
            wrong.push(format!("NOT VERIFIED {func}: {raw}"));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
