// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Field writes through `&mut` parameters, reborrows and alias chains, and
//! carriers reached by indexing a Seq of structs: none may leave a stale
//! field dom behind. Every false program must come back not Verified; the
//! TRUE controls report completeness only.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(name: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_atk2_{}_{}.rs", std::process::id(), name));
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
        other => {
            let s = format!("{other:?}");
            s.chars().take(150).collect()
        }
    }
}

const B1: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::requires(!m2.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: &mut S, m2: Map<u32, u32>) {
    s.m = m2;
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

const B2: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::requires(!m2.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: &mut S, m2: Map<u32, u32>) {
    let r = &mut *s;
    r.m = m2;
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

const B3: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::requires(!m2.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S, m2: Map<u32, u32>) {
    let mut s = s;
    let r = &mut s;
    r.m = m2;
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

const B4: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::requires(!m2.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S, m2: Map<u32, u32>) {
    let mut s = s;
    let a = &mut s;
    let b = a;
    b.m = m2;
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

// Multiset field: capability + liar.
const B5: &str = r#"
use trust_vc_types::Multiset;
struct S { b: Multiset<u32> }
#[trust_vc::requires(s.b.len() == 3int)]
#[trust_vc::ensures(true)]
fn t(s: S) { trust_vc::assert!(s.b.len() == 3int); }
"#;

const B6: &str = r#"
use trust_vc_types::Multiset;
struct S { b: Multiset<u32> }
#[trust_vc::requires(s.b.len() == 3int)]
#[trust_vc::ensures(true)]
fn t(s: S) { trust_vc::assert!(s.b.len() == 4int); }
"#;

// Multiset field length after replacing the field.
const B7: &str = r#"
use trust_vc_types::Multiset;
struct S { b: Multiset<u32> }
#[trust_vc::requires(s.b.len() == 3int)]
#[trust_vc::requires(other.len() == 5int)]
#[trust_vc::ensures(true)]
fn t(s: S, other: Multiset<u32>) {
    let mut s = s;
    s.b = other;
    trust_vc::assert!(s.b.len() == 3int);
}
"#;

// A field read whose carrier is an indexed element of a Seq of structs.
const B8: &str = r#"
use trust_vc_types::{Map, Seq};
struct S { m: Map<u32, u32> }
#[trust_vc::requires(v.len() > 0int)]
#[trust_vc::requires(v[0int].m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(v: Seq<S>) { trust_vc::assert!(v[0int].m.contains_key(1u32)); }
"#;

const B9: &str = r#"
use trust_vc_types::{Map, Seq};
struct S { m: Map<u32, u32> }
#[trust_vc::requires(v.len() > 1int)]
#[trust_vc::requires(v[0int].m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(v: Seq<S>) { trust_vc::assert!(v[1int].m.contains_key(1u32)); }
"#;

// Vacuity control on the &mut field write.
const B10: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::requires(!m2.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: &mut S, m2: Map<u32, u32>) {
    s.m = m2;
    trust_vc::assert!(1u32 == 2u32);
}
"#;

#[test]
fn dom_staleness_attack_matrix_2() {
    let cases: Vec<(&str, &str, bool)> = vec![
        ("B1_mutref_param_field_write", B1, false),
        ("B2_reborrow_field_write", B2, false),
        ("B3_alias_field_write", B3, false),
        ("B4_alias_chain_field_write", B4, false),
        ("B5_multiset_field_len_TRUE", B5, true),
        ("B6_multiset_field_len_liar", B6, false),
        ("B7_multiset_field_len_after_write", B7, false),
        ("B8_seq_of_structs_same_index_TRUE", B8, true),
        ("B9_seq_of_structs_other_index", B9, false),
        ("B10_vacuity_mutref_field_write", B10, false),
    ];
    let mut bad = Vec::new();
    for (name, src, truth) in cases {
        let r = verify(name, src);
        println!("{name}: truth={truth} verdict={}", short(&r));
        if r.is_verified() && !truth {
            bad.push(name.to_string());
        }
    }
    assert!(bad.is_empty(), "FALSE VERIFY on: {bad:?}");
}
