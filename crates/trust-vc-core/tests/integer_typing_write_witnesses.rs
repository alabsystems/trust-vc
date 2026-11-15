//! More WRITE shapes that bind their value at the slot's type through the
//! one binder (design-trust-proof-backend.md §5b rule 12,
//! `bind_written_value`): a binding with no ascription takes the type of
//! its WITNESS, the value it was first bound to, however that value is
//! spelled. Each `never_*` goal below was `Verified` before the binder (the
//! value was substituted bare):
//!
//! * proof bodies (`x: u8 == 255`): a witness that is a shadowed name, a
//!   chain of unascribed bindings, a conditional with one literal branch, a
//!   whole-value `match` binding, the referent of `*r = x`, a sequence or
//!   `Option` value, and a `mut` tuple-pattern binding (the last two kinds
//!   are programs Rust rejects and are refused);
//! * exec bodies (`x == 1`): a literal written into an unascribed binding,
//!   a tuple field, a referent through `&mut`, an `if let` / `match`
//!   payload, a deferred binding, or a binding beside a shadow in an inner
//!   block stayed an untyped `i32`, so `+ 100` after `= 200` did not
//!   overflow.
//!
//! Every `never_*` goal is false or its program panics and must not be
//! `Verified`; every `verified_*` twin differs by one line and must be
//! `Verified`; every `true_*` twin is the honest reading and must not be
//! refuted.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC_WITNESSES: &str = r####"
use trust_vc_types::Seq;

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_shadowed_witness_write(x: u8, v: int) {
    let mut w = v;
    let v = x;
    w = v;
    trust_vc::assert!(w + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn true_shadowed_witness_write(x: u8, v: int) {
    let mut w = v;
    let v = x;
    w = v;
    trust_vc::assert!(w + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_chained_witness_write(x: u8, v: int) {
    let mut w = v;
    let mut z = w;
    z = x;
    trust_vc::assert!(z + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn true_chained_witness_write(x: u8, v: int) {
    let mut w = v;
    let mut z = w;
    z = x;
    trust_vc::assert!(z + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_conditional_witness_write(x: u8, v: int, c: bool) {
    let mut w = if c { v } else { 0 };
    w = x;
    trust_vc::assert!(w + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn true_conditional_witness_write(x: u8, v: int, c: bool) {
    let mut w = if c { v } else { 0 };
    w = x;
    trust_vc::assert!(w + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_match_whole_binding_write(x: u8, v: int) {
    match v {
        mut w => {
            w = x;
            trust_vc::assert!(w + 1 == 0);
        }
    }
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn true_match_whole_binding_write(x: u8, v: int) {
    match v {
        mut w => {
            w = x;
            trust_vc::assert!(w + 1 == 256);
        }
    }
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_unascribed_referent_write(x: u8, u: int) {
    let mut v = u;
    let r = &mut v;
    *r = x;
    trust_vc::assert!(v + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn true_unascribed_referent_write(x: u8, u: int) {
    let mut v = u;
    let r = &mut v;
    *r = x;
    trust_vc::assert!(v + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_sequence_witness_write(x: u8, s: Seq<int>) {
    let mut t = s;
    t = seq![x];
    trust_vc::assert!(t[0] + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_option_witness_write(x: u8, o: Option<int>) {
    let mut p = o;
    p = Some(x);
    trust_vc::assert!(p == Some(255u8));
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_tuple_pattern_write(x: u8, v: int) {
    let (mut a, mut b) = (v, v);
    a = x;
    trust_vc::assert!(a + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_tuple_parameter_pattern_write(x: u8, p: (int, int)) {
    let (mut a, mut b) = p;
    a = x;
    trust_vc::assert!(a + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_iflet_tuple_payload_write(x: u8, o: Option<(int, int)>) {
    if let Some((mut a, b)) = o {
        a = x;
        trust_vc::assert!(a + 1 == 0);
    }
}

#[trust_vc::requires(x == 1u8)]
fn never_unascribed_literal_write_overflow(x: u8) {
    let mut w = x;
    w = 200;
    let z = w + 100;
}

#[trust_vc::requires(x == 1u8)]
fn verified_unascribed_literal_write_no_overflow(x: u8) {
    let mut w = x;
    w = 200;
    let z = w + 50;
}

#[trust_vc::requires(x == 1u8)]
fn never_tuple_field_literal_write_overflow(x: u8) {
    let mut t = (x, x);
    t.0 = 200;
    let z = t.0 + 100;
}

#[trust_vc::requires(x == 1u8)]
fn verified_tuple_field_literal_write_no_overflow(x: u8) {
    let mut t = (x, x);
    t.0 = 200;
    let z = t.0 + 50;
}

#[trust_vc::requires(x == 1u8)]
fn never_referent_literal_write_overflow(x: u8) {
    let mut v = x;
    let r = &mut v;
    *r = 200;
    let z = v + 100;
}

#[trust_vc::requires(o == Some(1u8))]
fn never_iflet_literal_write_overflow(o: Option<u8>) {
    if let Some(mut v) = o {
        v = 200;
        let z = v + 100;
    }
}

#[trust_vc::requires(x == 1u8)]
fn never_match_arm_literal_write_overflow(x: u8, o: Option<u8>) {
    match o {
        Some(mut v) => {
            v = 200;
            let z = v + 100;
        }
        None => {}
    }
}

#[trust_vc::requires(x == 1u8)]
fn never_deferred_then_literal_write_overflow(x: u8) {
    let w;
    w = x;
    let mut u = w;
    u = 250;
    let z = u + 10;
}

#[trust_vc::requires(x == 1u8)]
fn never_literal_write_beside_inner_shadow_overflow(x: u8) {
    let mut w = x;
    {
        let w = 5u64;
    }
    w = 200;
    let z = w + 100;
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
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/write_witnesses_src");
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
fn a_write_binds_like_its_witness_in_every_shape() {
    let names: Vec<&str> = SRC_WITNESSES
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| {
            ["never_", "true_", "verified_"]
                .iter()
                .any(|prefix| n.starts_with(prefix))
        })
        .collect();
    assert_eq!(names.len(), 24, "case list truncated: {names:?}");
    let mut wrong = Vec::new();
    for func in names {
        let r = run_source(SRC_WITNESSES, "write_witnesses.rs", func);
        let got = verdict(&r);
        let raw: String = format!("{r:?}").chars().take(240).collect();
        println!("WITNESSWRITE|{func}|{got}|{raw}");
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
