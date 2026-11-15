//! Writes and bindings the extractor read as something the program does not
//! hold. Each group is one cause:
//!
//! * a write to a NAMED field of an indexed element (`v[0].g = x`) reached no
//!   handler and was DROPPED: a write no handler models now poisons its
//!   binding at the one assignment funnel, so a later read fails closed;
//! * a write through one `&mut` alias of a struct field (`let r = &mut s.g;
//!   let q = &mut *r; *q = y;`) updated the owner and `q` but not `r`: the
//!   field write now reaches every alias of the field, as a cell write does;
//! * a pattern binding the extractor does not project (`if let Some(mut v) =
//!   o`, a closure parameter `|v: u64|`) was shadowed by its own name, which
//!   is the symbol of an OUTER binding of that name when there is one: `v + 1`
//!   was checked against the parameter `v < 10`.
//!
//! Every `never_*` goal is false or its program panics and must not be
//! `Verified`; every `verified_*` twin must be `Verified`; every `true_*` twin
//! is the honest reading and must not be refuted.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC_INDEXED_NAMED_FIELD: &str = r####"
struct S2 {
    g: u8,
    h: u8,
}

#[trust_vc::requires(y == 1u8)]
fn never_vec_elem_field_write_dropped(y: u8, x: u8) {
    let mut v: Vec<S2> = vec![S2 { g: y, h: y }];
    v[0].g = x;
    trust_vc::assert!(v[0].g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_vec_elem_second_field_write_dropped(y: u8, x: u8) {
    let mut v: Vec<S2> = vec![S2 { g: y, h: y }];
    v[0].h = x;
    trust_vc::assert!(v[0].h == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_array_elem_field_write_dropped(y: u8, x: u8) {
    let mut a: [S2; 1] = [S2 { g: y, h: y }];
    a[0].g = x;
    trust_vc::assert!(a[0].g == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_vec_elem_field_var_index_dropped(y: u8, x: u8, i: usize) {
    let mut v: Vec<S2> = vec![S2 { g: y, h: y }, S2 { g: y, h: y }];
    if i < 2 {
        v[i].g = x;
        trust_vc::assert!(v[i].g == 1u8);
    }
}

#[trust_vc::requires(y == 1u8)]
fn never_vec_elem_nested_tuple_field_dropped(y: u8, x: u8) {
    let mut v: Vec<((u8, u8), u8)> = vec![((y, y), y)];
    v[0].0.1 = x;
    trust_vc::assert!(((v[0]).0).1 == 1u8);
}

#[trust_vc::requires(y == 1u8)]
fn never_paren_vec_elem_field_dropped(y: u8, x: u8) {
    let mut v: Vec<S2> = vec![S2 { g: y, h: y }];
    (v[0]).g = x;
    trust_vc::assert!(v[0].g == 1u8);
}

#[trust_vc::requires(y == 100u8)]
fn never_vec_elem_field_literal_overflow(y: u8) {
    let mut v: Vec<S2> = vec![S2 { g: y, h: y }];
    v[0].g = 200;
    let z = v[0].g + y;
}

#[trust_vc::requires(y == 1u8)]
#[trust_vc::ensures(result == 1u8)]
fn never_vec_elem_field_returned(y: u8, x: u8) -> u8 {
    let mut v: Vec<S2> = vec![S2 { g: y, h: y }];
    v[0].g = x;
    v[0].g
}

#[trust_vc::requires(y == 1u8)]
fn true_vec_elem_field_write_read_back(y: u8, x: u8) {
    let mut v: Vec<S2> = vec![S2 { g: y, h: y }];
    v[0].g = x;
    trust_vc::assert!(v[0].g == x);
}
"####;

const SRC_FIELD_REBORROW: &str = r####"
struct S2 {
    g: u8,
    h: u8,
}

#[trust_vc::requires(x == 1u8 && y == 2u8)]
fn never_field_reborrow_outer_stale(x: u8, y: u8) {
    let mut s = S2 { g: x, h: x };
    let r = &mut s.g;
    let q = &mut *r;
    *q = y;
    trust_vc::assert!(*r == 1u8);
}

#[trust_vc::requires(x == 1u8)]
fn never_field_reborrow_outer_value(x: u8, y: u8) {
    let mut s = S2 { g: x, h: x };
    let r = &mut s.g;
    let q = &mut *r;
    *q = y;
    trust_vc::assert!(*r == x);
}

#[trust_vc::requires(x == 1u8)]
fn never_field_reborrow_outer_overflow(x: u8) {
    let mut s = S2 { g: x, h: x };
    let r = &mut s.g;
    let q = &mut *r;
    *q = 200;
    let z = *r + 100;
}

#[trust_vc::requires(x == 1u8 && y == 2u8)]
fn never_field_reborrow_ascribed_outer_stale(x: u8, y: u8) {
    let mut s = S2 { g: x, h: x };
    let r: &mut u8 = &mut s.g;
    let q: &mut u8 = &mut *r;
    *q = y;
    trust_vc::assert!(*r == 1u8);
}

#[trust_vc::requires(x == 1u8 && y == 2u8)]
fn never_field_double_reborrow_outer_stale(x: u8, y: u8) {
    let mut s = S2 { g: x, h: x };
    let r = &mut s.g;
    let q = &mut *r;
    let p = &mut *q;
    *p = y;
    trust_vc::assert!(*r == 1u8);
}

#[trust_vc::requires(x == 1u8)]
fn verified_field_reborrow_outer_no_overflow(x: u8) {
    let mut s = S2 { g: x, h: x };
    let r = &mut s.g;
    let q = &mut *r;
    *q = 100;
    let z = *r + 100;
}

#[trust_vc::requires(x == 1u8 && y == 2u8)]
fn verified_field_reborrow_outer_fresh(x: u8, y: u8) {
    let mut s = S2 { g: x, h: x };
    let r = &mut s.g;
    let q = &mut *r;
    *q = y;
    trust_vc::assert!(*r == 2u8);
}
"####;

const SRC_PATTERN_SHADOW: &str = r####"
#[trust_vc::requires(v < 10u64)]
fn never_if_let_mut_payload(v: u64, o: Option<u64>) {
    if let Some(mut v) = o {
        let w = v + 1u64;
    }
}

#[trust_vc::requires(v < 10u64)]
fn never_if_let_mut_payload_compound(v: u64, o: Option<u64>) {
    if let Some(mut v) = o {
        v += 1u64;
    }
}

#[trust_vc::requires(v < 10u64)]
fn never_match_mut_payload_compound(v: u64, o: Option<u64>) {
    match o {
        Some(mut v) => {
            v += 1u64;
        }
        None => {}
    }
}

#[trust_vc::requires(v < 10u64)]
fn never_let_tuple_mut_compound(v: u64, o: (u64, u64)) {
    let (mut v, _) = o;
    v += 1u64;
}

#[trust_vc::requires(v < 10u64)]
fn never_if_let_tuple_payload(v: u64, o: Option<(u64, u64)>) {
    if let Some((v, _)) = o {
        let w = v + 1u64;
    }
}

#[trust_vc::requires(v < 10u64)]
fn never_or_pattern_mut(v: u64, o: Result<u64, u64>) {
    match o {
        Ok(mut v) | Err(mut v) => {
            v += 1u64;
        }
    }
}

#[trust_vc::requires(v < 10u64)]
fn never_closure_param_shadow(v: u64) {
    let f = |v: u64| {
        let w = v + 1u64;
    };
    f(u64::MAX);
}

#[trust_vc::requires(v < 10u64)]
fn never_closure_mut_param_shadow(v: u64) {
    let f = |mut v: u64| {
        v += 1u64;
    };
    f(u64::MAX);
}

#[trust_vc::requires(v == 0u64)]
fn never_for_pattern_shadow(v: u64) {
    for v in 1..3u64 {
        trust_vc::invariant!(true);
        let w = v + 18446744073709551615u64;
    }
}

#[trust_vc::requires(v < 10u64)]
fn verified_if_let_payload_halved(v: u64, o: Option<u64>) {
    if let Some(v) = o {
        let w = v / 2u64;
    }
}

#[trust_vc::requires(v < 10u64)]
fn true_if_let_mut_payload_halved(v: u64, o: Option<u64>) {
    if let Some(mut v) = o {
        v /= 2u64;
    }
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
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/misread_write_src");
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
fn a_named_field_write_of_an_indexed_element_is_never_dropped() {
    check(SRC_INDEXED_NAMED_FIELD, "indexed_named_field.rs", 9);
}

#[test]
fn a_write_through_a_field_reborrow_reaches_every_alias() {
    check(SRC_FIELD_REBORROW, "field_reborrow.rs", 7);
}

#[test]
fn a_pattern_binding_is_never_read_as_the_outer_binding() {
    check(SRC_PATTERN_SHADOW, "pattern_shadow.rs", 11);
}
