//! `s.update(i, v).len()` is the receiver's length only for `0 <= i <
//! s.len()` (design-trust-proof-backend.md §5b rule 10; Verus's
//! `axiom_seq_update_len` requires it). The domain is also an obligation, but
//! a spec function's DEFINING AXIOM drops obligations, and there the
//! receiver's length defined the out-of-domain update's. Every `never_*` goal
//! is about an unspecified length (unprovable in Verus) and was `Verified` at
//! 9fd50172 and at its parent (r10 verifier: `never_update_len_neg_via_spec`;
//! `never_update_len_at_len_via_spec` measured in the same round); every
//! `verified_*` twin is in the domain and stays `Verified`.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
use trust_vc_types::Seq;

#[trust_vc::spec]
fn upl(s: Seq<u8>, i: int) -> int {
    s.update(i, 0u8).len() as int
}

#[trust_vc::spec]
fn upd0(s: Seq<u8>, i: int) -> int {
    s.update(i, 0u8)[0] as int
}

#[trust_vc::spec]
fn updi(s: Seq<u8>, i: int) -> int {
    s.update(i, 7u8)[i] as int
}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(upl(s, -1) == 300)]
fn never_update_len_neg_via_spec(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(upl(s, 300) == 300)]
fn never_update_len_at_len_via_spec(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(upl(s, 5) == 300)]
fn verified_update_len_in_domain_via_spec(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(upd0(s, 5) == s[0] as int)]
fn verified_update_other_cell_in_domain_via_spec(s: Seq<u8>) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::ensures(updi(s, 5) == 7)]
fn verified_update_same_in_domain_via_spec(s: Seq<u8>) {}
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
    let path = dir.join("integer_typing_update_domain.rs");
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
fn an_update_is_specified_only_in_its_domain() {
    let names: Vec<&str> = SRC
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| n.starts_with("never_") || n.starts_with("verified_"))
        .collect();
    assert_eq!(names.len(), 5, "case list truncated: {names:?}");
    let mut wrong = Vec::new();
    for func in names {
        let r = run_source(func);
        let got = verdict(&r);
        let raw: String = format!("{r:?}").chars().take(220).collect();
        println!("UPDDOM|{func}|{got}|{raw}");
        if func.starts_with("never_") && got == "Verified" {
            wrong.push(format!("FALSE VERIFIED {func}"));
        }
        if func.starts_with("verified_") && got != "Verified" {
            wrong.push(format!("NOT VERIFIED {func}: {got}"));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
