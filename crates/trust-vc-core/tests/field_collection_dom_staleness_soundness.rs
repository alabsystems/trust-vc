// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Staleness and framing guards for the dom/len companion of a field-held
//! Map, Seq or Multiset: after a write to that field, a `&mut` clobber, a
//! loop or a rebind, no stale pre-write fact may be read, and a write must
//! never leave the assumptions contradictory. Every false program must come
//! back not Verified; the TRUE controls report completeness only.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(name: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_atk_{}_{}.rs", std::process::id(), name));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), "t").unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

fn short(r: &VerifyResult) -> String {
    match r {
        VerifyResult::Verified => "VERIFIED".to_string(),
        VerifyResult::Error { message } => {
            let m: String = message.chars().take(160).collect();
            format!("ERROR: {m}")
        }
        other => {
            let s = format!("{other:?}");
            let s: String = s.chars().take(160).collect();
            s
        }
    }
}

// ---------------------------------------------------------------- attacks

// A1 direct field write of the Map, then read the PRE-write fact.
const A1: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::requires(!m2.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S, m2: Map<u32, u32>) {
    let mut s = s;
    s.m = m2;
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

// A2 field write, then read the NEGATION of the post-write fact.
const A2: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::requires(!m2.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S, m2: Map<u32, u32>) {
    let mut s = s;
    s.m = m2;
    trust_vc::assert!(!s.m.contains_key(1u32));
}
"#;

// A3 loop writes the field; pre-loop fact must not survive.
const A3: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S, other: Map<u32, u32>) {
    let mut s = s;
    let mut i = 0u32;
    while i < 3u32 { trust_vc::invariant!(i <= 3u32); s.m = other; i = i + 1u32; }
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

// A4 &mut on the FIELD (not the struct) handed to a function that promises nothing.
const A4: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::ensures(true)]
fn clobber_field(m: &mut Map<u32, u32>) { }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S) {
    let mut s = s;
    clobber_field(&mut s.m);
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

// A5 &mut on the WHOLE struct through an alias binding.
const A5: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::ensures(true)]
fn clobber(s: &mut S) { }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S) {
    let mut s = s;
    let r = &mut s;
    clobber(r);
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

// A6 write a DIFFERENT field of the same struct, then read the Map fact.
// TRUE claim - completeness probe, not a false verify.
const A6: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32>, n: u32 }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S) {
    let mut s = s;
    s.n = 7u32;
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

// A7 rebind the root to a new struct built from an UNCONSTRAINED map.
const A7: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::requires(!m2.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S, m2: Map<u32, u32>) {
    let mut s = s;
    s = S { m: m2 };
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

// A8 &mut self method with an ensures that says nothing about m.
const A8: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32>, n: u32 }
#[trust_vc::ensures(s.n == 1u32)]
fn bump(s: &mut S) { s.n = 1u32; }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S) {
    let mut s = s;
    bump(&mut s);
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

// A9 the classic vacuity check: if a field write leaves the assumption set
// contradictory, EVERYTHING verifies. Assert plain false after a field write.
const A9: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S, m2: Map<u32, u32>) {
    let mut s = s;
    s.m = m2;
    trust_vc::assert!(1u32 == 2u32);
}
"#;

// A10 vacuity after a &mut clobber.
const A10: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::ensures(true)]
fn clobber(s: &mut S) { }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S) {
    let mut s = s;
    clobber(&mut s);
    trust_vc::assert!(1u32 == 2u32);
}
"#;

// A11 Seq length twin: write the field, then read the pre-write length.
const A11: &str = r#"
use trust_vc_types::Seq;
struct S { q: Seq<u32> }
#[trust_vc::requires(v.q.len() == 3int)]
#[trust_vc::requires(other.len() == 5int)]
#[trust_vc::ensures(true)]
fn t(v: S, other: Seq<u32>) {
    let mut v = v;
    v.q = other;
    trust_vc::assert!(v.q.len() == 3int);
}
"#;

// A12 two DIFFERENT struct values must not share a dom.
const A12: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(a.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(a: S, b: S) {
    trust_vc::assert!(b.m.contains_key(1u32));
}
"#;

// A13 nested: clobber the OUTER struct, read the inner field fact.
const A13: &str = r#"
use trust_vc_types::Map;
struct Inner { m: Map<u32, u32> }
struct Outer { i: Inner }
#[trust_vc::ensures(true)]
fn clobber(o: &mut Outer) { }
#[trust_vc::requires(o.i.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(o: Outer) {
    let mut o = o;
    clobber(&mut o);
    trust_vc::assert!(o.i.m.contains_key(1u32));
}
"#;

// A14 nested: write the INNER struct field, read the map fact.
const A14: &str = r#"
use trust_vc_types::Map;
struct Inner { m: Map<u32, u32> }
struct Outer { i: Inner }
#[trust_vc::requires(o.i.m.contains_key(1u32))]
#[trust_vc::requires(!m2.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(o: Outer, m2: Map<u32, u32>) {
    let mut o = o;
    o.i = Inner { m: m2 };
    trust_vc::assert!(o.i.m.contains_key(1u32));
}
"#;

// A15 ensures-side staleness: a callee that REPLACES the field and promises
// only about the new one; the caller must not keep the old membership.
const A15: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(!m2.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn put(s: &mut S, m2: Map<u32, u32>) { s.m = m2; }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::requires(!m2.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S, m2: Map<u32, u32>) {
    let mut s = s;
    put(&mut s, m2);
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

// C1 COMPLETENESS probe: a loop that never touches the struct.
const C1: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S) {
    let mut i = 0u32;
    while i < 3u32 { trust_vc::invariant!(i <= 3u32); i = i + 1u32; }
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

// C2 COMPLETENESS probe: plain param Map across the same loop (baseline shape).
const C2: &str = r#"
use trust_vc_types::Map;
#[trust_vc::requires(m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(m: Map<u32, u32>) {
    let mut i = 0u32;
    while i < 3u32 { trust_vc::invariant!(i <= 3u32); i = i + 1u32; }
    trust_vc::assert!(m.contains_key(1u32));
}
"#;

// ---- quantifier-over-struct: the minted dom is NOT bound by the quantifier ----

// Q1 TRUE completeness probe: a universal over structs should instantiate at a
// specific struct.
const Q1: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(forall(|x: S| x.m.contains_key(1u32)))]
#[trust_vc::ensures(true)]
fn t(a: S) { trust_vc::assert!(a.m.contains_key(1u32)); }
"#;

// Q2 FALSE: one struct having the key does not make every struct have it.
const Q2: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(a.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(a: S) { trust_vc::assert!(forall(|x: S| x.m.contains_key(1u32))); }
"#;

// Q3 FALSE and the sharpest shape: binder name SHADOWS the parameter. If the
// bound struct term is the parameter's term, the param fact proves the
// universal.
const Q3: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(x.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(x: S) { trust_vc::assert!(forall(|x: S| x.m.contains_key(1u32))); }
"#;

// Q4 FALSE: existential to universal. Both collapse to the same free dom if
// the bound struct's companion is not bound by the quantifier.
const Q4: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(exists(|x: S| x.m.contains_key(1u32)))]
#[trust_vc::ensures(true)]
fn t(a: S) { trust_vc::assert!(forall(|x: S| x.m.contains_key(1u32))); }
"#;

// Q5 FALSE: a universal over structs must not prove a DIFFERENT key.
const Q5: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(forall(|x: S| x.m.contains_key(1u32)))]
#[trust_vc::ensures(true)]
fn t(a: S) { trust_vc::assert!(a.m.contains_key(2u32)); }
"#;

// Q6 FALSE: spec-function results. Two different arguments must not share a dom.
const Q6: &str = r#"
use trust_vc_types::Map;
#[trust_vc::spec]
fn pick(i: u32) -> Map<u32, u32> { Map::empty() }
#[trust_vc::requires(pick(0u32).contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(z: u32) { trust_vc::assert!(pick(1u32).contains_key(1u32)); }
"#;

// ---- ensures / invariant staleness ----

// A16 FALSE: a &mut fn that replaces the field must not satisfy an ensures
// that repeats the precondition.
const A16: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::requires(!m2.contains_key(1u32))]
#[trust_vc::ensures(s.m.contains_key(1u32))]
fn t(s: &mut S, m2: Map<u32, u32>) { s.m = m2; }
"#;

// A17 FALSE: an ensures about a field with nothing to back it.
const A17: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::ensures(s.m.contains_key(1u32))]
fn t(s: &mut S) { }
"#;

// A19 FALSE: an invariant that a field write inside the loop destroys.
const A19: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S, other: Map<u32, u32>) {
    let mut s = s;
    let mut i = 0u32;
    while i < 3u32 {
        trust_vc::invariant!(i <= 3u32);
        trust_vc::invariant!(s.m.contains_key(1u32));
        s.m = other;
        i = i + 1u32;
    }
}
"#;

// C3 TRUE completeness probe: the same invariant with a body that never
// touches the struct.
const C3: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S) {
    let mut i = 0u32;
    while i < 3u32 {
        trust_vc::invariant!(i <= 3u32);
        trust_vc::invariant!(s.m.contains_key(1u32));
        i = i + 1u32;
    }
}
"#;

// A20 FALSE: a shared read-only borrow of the field handed to a fn that
// promises nothing, followed by a whole-struct clobber through an alias chain.
const A20: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::ensures(true)]
fn clobber(s: &mut S) { }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S) {
    let mut s = s;
    let a = &mut s;
    let b = a;
    clobber(b);
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

#[test]
fn dom_staleness_attack_matrix() {
    let cases: Vec<(&str, &str, bool)> = vec![
        ("A1_field_write_then_pre_fact", A1, false),
        ("A2_field_write_then_negation", A2, false),
        ("A3_loop_writes_field", A3, false),
        ("A4_mut_ref_on_field", A4, false),
        ("A5_mut_ref_alias_on_struct", A5, false),
        ("A6_other_field_write_TRUE", A6, true),
        ("A7_root_rebind_struct_literal", A7, false),
        ("A8_mut_self_ensures_other_field", A8, false),
        ("A9_vacuity_after_field_write", A9, false),
        ("A10_vacuity_after_clobber", A10, false),
        ("A11_seq_len_after_field_write", A11, false),
        ("A12_two_structs_share_dom", A12, false),
        ("A13_nested_outer_clobber", A13, false),
        ("A14_nested_inner_write", A14, false),
        ("A15_callee_replaces_field", A15, false),
        ("Q1_forall_struct_instantiate_TRUE", Q1, true),
        ("Q2_one_struct_to_all", Q2, false),
        ("Q3_binder_shadows_param", Q3, false),
        ("Q4_exists_to_forall", Q4, false),
        ("Q5_forall_other_key", Q5, false),
        ("Q6_spec_fn_two_args", Q6, false),
        ("A16_ensures_after_field_write", A16, false),
        ("A17_bare_ensures_on_field", A17, false),
        ("A19_invariant_broken_by_field_write", A19, false),
        ("A20_alias_chain_clobber", A20, false),
        ("C3_invariant_untouched_TRUE", C3, true),
        ("C1_loop_untouched_struct_TRUE", C1, true),
        ("C2_loop_untouched_param_TRUE", C2, true),
    ];
    let mut bad = Vec::new();
    for (name, src, truth) in cases {
        let r = verify(name, src);
        let v = r.is_verified();
        println!("{name}: truth={truth} verdict={}", short(&r));
        if v && !truth {
            bad.push(name.to_string());
        }
    }
    assert!(bad.is_empty(), "FALSE VERIFY on: {bad:?}");
}
