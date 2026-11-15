//! A body `let` binds its value at its ascribed type — for EVERY pattern shape
//! and every spelling of the type (design-trust-proof-backend.md §5b rule 12).
//!
//! The extractor models a `let` by substituting the value for each name it
//! binds. Only a bare identifier with a primitive/`int`/`nat` ascription used
//! to be bound (`__trust_vc_let_bound::<T>(..)`); with `x: u8 == 255`, each of
//! `let (v, w): (int, int) = (x, x)`, `let (v): int = x`, `type MyInt = int;
//! let v: MyInt = x` and `let t: (int, int) = (x, x)` substituted `x` bare, so
//! `v + 1` wrapped in `u8` and `assert!(v + 1 == 0)` was `Verified` (r9
//! verifier, identical at 44e93f72 and 50b27076) — the fix's own
//! `never_body_let_int_wraps`, through another pattern shape. So did every
//! composite ascription that names an integer type (measured at 50b27076):
//! `let v: Seq<int> = s` (`s: Seq<u8>`, `v[0] + 1 == 0`), `let a: [int; 1] =
//! [x]`, `let r: &int = &x` and `let o: Option<int> = Some(x)`.
//!
//! `never_*` must not be `Verified`; `refused_*` (a binding the ascription
//! cannot hold, a pattern the extractor cannot bind at it) must be `Unknown`;
//! `verified_*` must be `Verified`.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
use trust_vc_types::Seq;

type MyInt = int;
type Byte = u8;

pub struct Wrap<T> {
    pub f: T,
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_tuple_let_int_wraps(x: u8) {
    let (v, w): (int, int) = (x, x);
    trust_vc::assert!(v + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_paren_let_int_wraps(x: u8) {
    let (v): int = x;
    trust_vc::assert!(v + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_alias_let_int_wraps(x: u8) {
    let v: MyInt = x;
    trust_vc::assert!(v + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_tuple_typed_ident_let_int_wraps(x: u8) {
    let t: (int, int) = (x, x);
    trust_vc::assert!(t.0 + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_nested_tuple_let_int_wraps(x: u8) {
    let t: (u8, (int, int)) = (x, (x, x));
    trust_vc::assert!((t.1).0 + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(true)]
fn refused_tuple_let_u8_from_i16(y: i16) {
    let (v, w): (u8, u8) = (y, y);
    trust_vc::assert!(v == 255);
}

#[trust_vc::proof]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(true)]
fn refused_alias_let_u8_from_i16(y: i16) {
    let v: Byte = y;
    trust_vc::assert!(v == 255);
}

#[trust_vc::proof]
#[trust_vc::requires(p.0 == 255)]
#[trust_vc::ensures(true)]
fn refused_tuple_typed_let_from_tuple_of_another_type(p: (u8, u8)) {
    let t: (int, int) = p;
    trust_vc::assert!(t.0 + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(w.f == 255)]
#[trust_vc::ensures(true)]
fn refused_struct_pattern_under_integer_ascription(w: Wrap<u8>) {
    let Wrap { f }: Wrap<int> = w;
    trust_vc::assert!(f + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 1)]
#[trust_vc::requires(s[0] == 255)]
#[trust_vc::ensures(true)]
fn never_seq_int_let_from_seq_u8_wraps(s: Seq<u8>) {
    let v: Seq<int> = s;
    trust_vc::assert!(v[0] + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_array_int_let_wraps(x: u8) {
    let a: [int; 1] = [x];
    trust_vc::assert!(a[0] + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_ref_int_let_wraps(x: u8) {
    let r: &int = &x;
    trust_vc::assert!(*r + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_option_int_let_wraps(x: u8) {
    let o: Option<int> = Some(x);
    trust_vc::assert!(o.unwrap() + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 1)]
#[trust_vc::requires(s[0] == 255)]
#[trust_vc::ensures(true)]
fn verified_seq_u8_let_from_seq_u8(s: Seq<u8>) {
    let v: Seq<u8> = s;
    trust_vc::assert!(v[0] == 255);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn verified_ident_let_int_exact(x: u8) {
    let v: int = x;
    trust_vc::assert!(v + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn verified_tuple_let_int_exact(x: u8) {
    let (v, w): (int, int) = (x, x);
    trust_vc::assert!(v + w + 1 == 511);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn verified_paren_let_int_exact(x: u8) {
    let (v): int = x;
    trust_vc::assert!(v + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn verified_alias_let_int_exact(x: u8) {
    let v: MyInt = x;
    trust_vc::assert!(v + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn verified_tuple_typed_ident_let_int_exact(x: u8) {
    let t: (int, u8) = (x, x);
    trust_vc::assert!(t.0 + 1 == 256 && t.1 == 255);
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
    let path = dir.join("integer_typing_let_patterns.rs");
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
fn a_body_let_binds_at_its_ascription_for_every_pattern_shape() {
    let names: Vec<&str> = SRC
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| {
            n.starts_with("never_") || n.starts_with("refused_") || n.starts_with("verified_")
        })
        .collect();
    assert_eq!(names.len(), 19, "case list truncated: {names:?}");
    let mut wrong = Vec::new();
    for func in names {
        let r = run_source(func);
        let got = verdict(&r);
        let raw: String = format!("{r:?}").chars().take(220).collect();
        println!("LETPAT|{func}|{got}|{raw}");
        if func.starts_with("never_") && got == "Verified" {
            wrong.push(format!("FALSE VERIFIED {func}"));
        }
        if func.starts_with("refused_") && got != "Unknown" {
            wrong.push(format!("DECIDED A REFUSED BINDING {func}: {got}"));
        }
        if func.starts_with("verified_") && got != "Verified" {
            wrong.push(format!("NOT VERIFIED {func}: {got}"));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
