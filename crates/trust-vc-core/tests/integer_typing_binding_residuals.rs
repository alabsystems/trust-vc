//! Every binding site binds its value at its declared type
//! (design-trust-proof-backend.md §5b rules 6, 11 and 12). Every `never_*`
//! was `Verified` when the r9 re-verifier measured it (at 50b27076 and
//! 3319adfa alike); every `verified_*` twin was REFUTED there.
//!
//! WELL-TYPED Verus programs: the all-unsuffixed-literal exemption of
//! `render_bound_at_ascription` kept an `int`/`nat` composite's literals at
//! the `i32` placeholder, so `v[0] + 1` wrapped at 32 bits —
//!   never_seq_int_literal_wraps, never_array_int_literal_wraps,
//!   never_option_int_literal_wraps, never_ref_int_literal_wraps,
//!   never_tuple_nested_seq_int_literal_wraps; and a `Seq<nat>`/`Option<nat>`
//!   held -1: never_seq_nat_neg1, never_seq_nat_elem_negative,
//!   never_option_nat_neg1.
//! Programs Rust/Verus reject, decided `Verified` (now refused):
//!   ascription spellings the alias table does not resolve —
//!   never_self_alias_let, never_mod_alias_let, never_generic_alias_let, a
//!   generic struct never_wrap_int_from_wrap_u8; assignment sites —
//!   never_assign_nat_neg1, never_assign_int_from_u8 (refuted now: the value
//!   is lifted), never_exec_assign_u8_from_u16,
//!   never_exec_deferred_init_u8_from_u16; a closure parameter —
//!   never_closure_param_int (refuted now: the argument is lifted); a `&mut
//!   int` alias of a `u8` — never_mut_ref_int_let; a composite spec-fn result
//!   — never_spec_result_seq_u8_as_seq_i8.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
use trust_vc_types::Seq;

type MyInt = int;
type Id<T> = T;

mod m {
    pub type MyInt = int;
}

pub struct Wrap<T> {
    pub f: T,
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_seq_int_literal_wraps() {
    let v: Seq<int> = seq![2147483647];
    trust_vc::assert!(v[0] + 1 == -2147483648);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn verified_seq_int_literal_exact() {
    let v: Seq<int> = seq![2147483647];
    trust_vc::assert!(v[0] + 1 == 2147483648);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_array_int_literal_wraps() {
    let a: [int; 1] = [2147483647];
    trust_vc::assert!(a[0] + 1 == -2147483648);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_option_int_literal_wraps() {
    let o: Option<int> = Some(2147483647);
    trust_vc::assert!(o.unwrap() + 1 == -2147483648);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn verified_option_int_literal_exact() {
    let o: Option<int> = Some(2147483647);
    trust_vc::assert!(o.unwrap() + 1 == 2147483648);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_ref_int_literal_wraps() {
    let r: &int = &2147483647;
    trust_vc::assert!(*r + 1 == -2147483648);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_tuple_nested_seq_int_literal_wraps() {
    let t: (int, Seq<int>) = (0, seq![2147483647]);
    trust_vc::assert!(t.1[0] + 1 == -2147483648);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_seq_nat_neg1() {
    let s: Seq<nat> = seq![-1];
    trust_vc::assert!(s[0] == -1);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_seq_nat_elem_negative() {
    let s: Seq<nat> = seq![-1];
    trust_vc::assert!(s[0] < 0);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_option_nat_neg1() {
    let o: Option<nat> = Some(-1);
    trust_vc::assert!(o.unwrap() == -1);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_self_alias_let(x: u8) {
    let v: self::MyInt = x;
    trust_vc::assert!(v + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_mod_alias_let(x: u8) {
    let v: m::MyInt = x;
    trust_vc::assert!(v + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_generic_alias_let(x: u8) {
    let v: Id<int> = x;
    trust_vc::assert!(v + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(w.f == 255)]
#[trust_vc::ensures(true)]
fn never_wrap_int_from_wrap_u8(w: Wrap<u8>) {
    let v: Wrap<int> = w;
    trust_vc::assert!(v.f + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_assign_nat_neg1() {
    let mut v: nat = 0;
    v = -1;
    trust_vc::assert!(v == -1);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_assign_int_from_u8(x: u8) {
    let mut v: int = 0;
    v = x;
    trust_vc::assert!(v + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn verified_assign_int_from_u8_exact(x: u8) {
    let mut v: int = 0;
    v = x;
    trust_vc::assert!(v + 1 == 256);
}

#[trust_vc::requires(y == 255)]
fn never_exec_assign_u8_from_u16(y: u16) {
    let mut v: u8 = 0;
    v = y;
    trust_vc::assert!(v + 1 == 256);
}

#[trust_vc::requires(y == 255)]
fn never_exec_deferred_init_u8_from_u16(y: u16) {
    let v: u8;
    v = y;
    trust_vc::assert!(v + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_closure_param_int(x: u8) {
    let f = |a: int| a + 1;
    trust_vc::assert!(f(x) == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn verified_closure_param_int_exact(x: u8) {
    let f = |a: int| a + 1;
    trust_vc::assert!(f(x) == 256);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_mut_ref_int_let(x: u8) {
    let r: &mut int = &mut x;
    trust_vc::assert!(*r + 1 == 0);
}

#[trust_vc::spec]
fn as_i8(s: Seq<u8>) -> Seq<i8> {
    s
}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 1)]
#[trust_vc::requires(s[0] == 200)]
#[trust_vc::ensures(as_i8(s)[0] == -56)]
fn never_spec_result_seq_u8_as_seq_i8(s: Seq<u8>) {}
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
    let path = dir.join("integer_typing_binding_residuals.rs");
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
fn every_binding_site_binds_at_its_declared_type() {
    let names: Vec<&str> = SRC
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| n.starts_with("never_") || n.starts_with("verified_"))
        .collect();
    assert_eq!(names.len(), 23, "case list truncated: {names:?}");
    let mut wrong = Vec::new();
    for func in names {
        let r = run_source(func);
        let got = verdict(&r);
        let raw: String = format!("{r:?}").chars().take(220).collect();
        println!("BINDRES|{func}|{got}|{raw}");
        if func.starts_with("never_") && got == "Verified" {
            wrong.push(format!("FALSE VERIFIED {func}"));
        }
        // A well-typed program is DECIDED: its binding is modelled, not
        // merely refused.
        if func.starts_with("verified_") && got != "Verified" {
            wrong.push(format!("NOT VERIFIED {func}: {got}"));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
