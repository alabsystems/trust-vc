//! Every WRITE into a typed slot binds its value at the slot's type
//! (design-trust-proof-backend.md §5b rule 12): an assignment, a compound
//! assignment, a write through an `&mut` alias, a tuple- or struct-field
//! write, a write to a binding whose type is inferred from its initializer or
//! from a pattern. A value bound at a type that cannot hold it is refused; a
//! value the type holds is bound (a fixed-width value under `int` is the
//! integer it denotes). The lane-off and `choose!` forms are in
//! `integer_typing_write_sites_lane_off.rs`.
//!
//! Every `never_*` goal is false (or the program is one Rust rejects);
//! every `true_*` twin is the honest reading and must not be refuted; every
//! `verified_*` twin must be `Verified`.
//!
//! * Write sites that substituted their value bare (each `Verified` before
//!   this rule, each honest twin REFUTED): `*r = x` through `let r = &mut
//!   v`, `t.0 = x` / `t.0 = -1` under a tuple ascription, `w = x` for `let
//!   mut w = v` (`v: int`), `v = x` for `if let Some(mut v) = o` (`o:
//!   Option<int>`), and a tuple pattern under a `type` alias of a tuple.
//! * Every `refused_*` write stores a value its slot's type cannot hold
//!   (`v = y` of an `i8` into an `i32` binding, a program Rust rejects) and
//!   must be refused, not widened: the oracle's generated write sites found
//!   the call-argument widening rule applied to a slot, and (seed 7) a field
//!   of a `(i32, i32)` ascription whose `0`s read as the untyped placeholder.
//! * A struct-field write stored its value at the field unbound: `s.g = y`
//!   (`g: u8`, `y: i8 == -1`) made `s.g == 255` `Verified` (a program Rust
//!   rejects); `s.f = x` under `f: int` was a sort mismatch.
//! * A witness is read by its SHAPE, not by a literal it mentions (measured
//!   on the first version of the binder, which returned the value bare for
//!   any witness that MENTIONED an untyped literal): `let mut w = s[0]` (`s:
//!   Seq<int>`) then `w = x` read `w + 1 == 0` `Verified` and its honest twin
//!   refuted — the index `0` is not the element's type; the same through a
//!   deferred `let mut w; w = s[0];`; `w = y` of an `i8` into a `Seq<u8>`
//!   element's binding was decided; and `t = (x, 5)` into `let mut t = (v,
//!   0)` (`v: int`) held `x` at `u8`. An untyped literal POSITION of a tuple
//!   witness, and a witness that is wholly a literal form, still take the
//!   written value's type (`verified_*`).

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

/// Write sites other than a plain assignment to an ascribed name.
const SRC_SITES: &str = r####"
use trust_vc_types::Seq;

type P2 = (int, int);

struct S {
    f: int,
    g: u8,
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_deref_assign_int_from_u8(x: u8) {
    let mut v: int = 0;
    let r = &mut v;
    *r = x;
    trust_vc::assert!(v + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn true_deref_assign_int_from_u8(x: u8) {
    let mut v: int = 0;
    let r = &mut v;
    *r = x;
    trust_vc::assert!(v + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_deref_assign_int_read_through_ref(x: u8) {
    let mut v: int = 0;
    let r = &mut v;
    *r = x;
    trust_vc::assert!(*r + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_tuple_field_assign_int_from_u8(x: u8) {
    let mut t: (int, int) = (0, 0);
    t.0 = x;
    trust_vc::assert!(t.0 + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn true_tuple_field_assign_int_from_u8(x: u8) {
    let mut t: (int, int) = (0, 0);
    t.0 = x;
    trust_vc::assert!(t.0 + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn never_tuple_field_assign_nat_neg1() {
    let mut t: (nat, nat) = (0, 0);
    t.0 = -1;
    trust_vc::assert!(t.0 == -1);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_assign_inferred_int_from_u8(x: u8, v: int) {
    let mut w = v;
    w = x;
    trust_vc::assert!(w + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn true_assign_inferred_int_from_u8(x: u8, v: int) {
    let mut w = v;
    w = x;
    trust_vc::assert!(w + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_compound_assign_inferred_int_from_u8(x: u8, v: int) {
    let mut w = v;
    w = 0;
    w += x;
    trust_vc::assert!(w + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn verified_assign_inferred_u8_from_u8(x: u8, y: u8) {
    let mut w = y;
    w = x;
    trust_vc::assert!(w == 255);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn verified_assign_inferred_placeholder_from_u8(x: u8) {
    let mut w = 0;
    w = x;
    trust_vc::assert!(w == 255);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_iflet_payload_int_assign_from_u8(x: u8, o: Option<int>) {
    if let Some(mut v) = o {
        v = x;
        trust_vc::assert!(v + 1 == 0);
    }
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_match_payload_int_assign_from_u8(x: u8, o: Option<int>) {
    match o {
        Some(mut v) => {
            v = x;
            trust_vc::assert!(v + 1 == 0);
        }
        None => {}
    }
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_alias_tuple_pattern_assign(x: u8) {
    let (mut a, mut b): P2 = (0, 0);
    a = x;
    trust_vc::assert!(a + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_struct_field_assign_int_from_u8(x: u8) {
    let mut s = S { f: 0, g: 0 };
    s.f = x;
    trust_vc::assert!(s.f + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn true_struct_field_assign_int_from_u8(x: u8) {
    let mut s = S { f: 0, g: 0 };
    s.f = x;
    trust_vc::assert!(s.f + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(true)]
fn never_struct_field_assign_u8_from_i8(y: i8) {
    let mut s = S { f: 0, g: 0 };
    s.g = y;
    trust_vc::assert!(s.g == 255);
}

#[trust_vc::proof]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(true)]
fn never_mut_ref_struct_field_assign_u8_from_i8(y: i8) {
    let mut s = S { f: 0, g: 0 };
    let r = &mut s;
    r.g = y;
    trust_vc::assert!(s.g == 255);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn verified_deferred_unascribed_first_write(x: u8) {
    let w;
    w = x;
    trust_vc::assert!(w == 255);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255 && y == -1)]
#[trust_vc::ensures(true)]
fn refused_deferred_unascribed_second_write_i16_into_u8(x: u8, y: i16) {
    let mut w;
    w = x;
    w = y;
    trust_vc::assert!(w == -1);
}

#[trust_vc::requires(y == -8)]
#[trust_vc::ensures(true)]
fn refused_tuple_field_i32_from_i16(y: i16) {
    let mut t: (i32, i32) = (0, 0);
    t.0 = y;
    trust_vc::assert!(t.0 == -8);
}

#[trust_vc::requires(y == -8)]
#[trust_vc::ensures(true)]
fn refused_iflet_payload_i32_from_i8(y: i8, o: Option<i32>) {
    if let Some(mut v) = o {
        v = y;
        trust_vc::assert!(v == -8);
    }
}

#[trust_vc::requires(y == -8)]
#[trust_vc::ensures(true)]
fn refused_assign_inferred_i32_from_i8(y: i8, w: i32) {
    let mut v = w;
    v = y;
    trust_vc::assert!(v == -8);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn true_alias_tuple_pattern_assign(x: u8) {
    let (mut a, mut b): P2 = (0, 0);
    a = x;
    trust_vc::assert!(a + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_element_witness_int_from_u8(x: u8, s: Seq<int>) {
    let mut w = s[0];
    w = x;
    trust_vc::assert!(w + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn true_element_witness_int_from_u8(x: u8, s: Seq<int>) {
    let mut w = s[0];
    w = x;
    trust_vc::assert!(w + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_deferred_element_witness_int_from_u8(x: u8, s: Seq<int>) {
    let mut w;
    w = s[0];
    w = x;
    trust_vc::assert!(w + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(true)]
fn refused_element_witness_u8_from_i8(y: i8, s: Seq<u8>) {
    let mut w = s[0];
    w = y;
    trust_vc::assert!(w < 0);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_tuple_witness_literal_sibling_whole_write(x: u8, v: int) {
    let mut t = (v, 0);
    t = (x, 5);
    trust_vc::assert!(t.0 + 1 == 0);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn verified_tuple_witness_literal_position_takes_the_value(v: int) {
    let mut t = (v, 0);
    t = (v, 5);
    trust_vc::assert!(t.1 == 5);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn verified_literal_sequence_witness_takes_the_value(x: u8) {
    let mut s = seq![0, 1];
    s = seq![x];
    trust_vc::assert!(s[0] == 255);
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
fn every_write_site_binds_at_its_slot_type() {
    check(SRC_SITES, "write_sites.rs", 31);
}
