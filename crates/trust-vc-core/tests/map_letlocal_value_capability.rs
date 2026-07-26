// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A ghost `Map` bound to a LET-LOCAL (`let m = Map::empty().insert(k, v); ..`)
//! and then used (`m.get(k)`, `m.dom().contains(k)`) is now modeled — previously
//! it failed closed at the binding ("Vec::insert receiver is unsupported in
//! vc_extraction: `Map::<..>::empty()`").
//!
//! Root: `Vec::insert(index, value)` and `Map::insert(key, value)` share arity 2,
//! so the AST-walk (`visit_expr_method_call`) routed a Map value insert to the
//! Vec in-place-insert handler, whose non-`Vec` receiver check then rejected the
//! `Map::empty()` constructor. Seq's `push` / Set's 1-arg `insert` decline for a
//! ghost receiver, so those let-locals already worked — this restores the
//! Seq/Set/Map symmetry (the insert handler now declines for a ghost-collection
//! receiver, without a parse error, so the value renders through the normal
//! ghost path). A real `Vec` local is never ghost-marked, so `Vec::insert` is
//! unaffected. SOUNDNESS: a false `get`/`dom` claim must still COUNTEREXAMPLE.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(name: &str, src: &str, target: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_map_ll_{}_{}.rs", std::process::id(), name));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), target).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

const GET_TRUE: &str = r#"
use trust_vc_types::Map;
#[trust_vc::ensures(true)]
fn t() { let m = Map::<u32,u32>::empty().insert(1u32,10u32); trust_vc::assert!(m.get(1u32) == 10u32); }
"#;

const GET_FALSE: &str = r#"
use trust_vc_types::Map;
#[trust_vc::ensures(true)]
fn t() { let m = Map::<u32,u32>::empty().insert(1u32,10u32); trust_vc::assert!(m.get(1u32) == 999u32); }
"#;

const DOM_TRUE: &str = r#"
use trust_vc_types::Map;
#[trust_vc::ensures(true)]
fn t() { let m = Map::<u32,u32>::empty().insert(1u32,10u32); trust_vc::assert!(m.dom().contains(1u32)); }
"#;

const DOM_FALSE: &str = r#"
use trust_vc_types::Map;
#[trust_vc::ensures(true)]
fn t() { let m = Map::<u32,u32>::empty().insert(1u32,10u32); trust_vc::assert!(m.dom().contains(2u32)); }
"#;

// Regression control: a real exec `Vec::insert` still models (not ghost-declined).
const VEC_INSERT: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); v.push(2u32); v.insert(1usize, 9u32); trust_vc::assert!(v.len() == 3usize); }
"#;

// The same arity-collision affects `.remove`: `Vec::remove(index)` and
// `Map`/`Set`/`Multiset::remove(elem)` are all arity 1. A ghost `.remove` is a
// functional value and must decline the Vec handler.
const MAP_REMOVE_TRUE: &str = r#"
use trust_vc_types::Map;
#[trust_vc::ensures(true)]
fn t() { let m = Map::<u32,u32>::empty().insert(1u32,10u32).insert(2u32,20u32).remove(1u32); trust_vc::assert!(!m.dom().contains(1u32)); }
"#;

const MAP_REMOVE_FALSE: &str = r#"
use trust_vc_types::Map;
#[trust_vc::ensures(true)]
fn t() { let m = Map::<u32,u32>::empty().insert(1u32,10u32).insert(2u32,20u32).remove(1u32); trust_vc::assert!(m.dom().contains(1u32)); }
"#;

const MULTISET_REMOVE_TRUE: &str = r#"
use trust_vc_types::Multiset;
#[trust_vc::ensures(true)]
fn t() { let m = Multiset::<u32>::empty().insert(5u32).insert(5u32).remove(5u32); trust_vc::assert!(m.count(5u32) == 1nat); }
"#;

// Regression control: a real exec `Vec::remove` still models.
const VEC_REMOVE: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); v.push(2u32); v.remove(0usize); trust_vc::assert!(v.len() == 1usize); }
"#;

#[test]
fn letlocal_map_get_verifies() {
    assert!(
        matches!(verify("get_t", GET_TRUE, "t"), VerifyResult::Verified),
        "a let-local Map `m.get(1) == 10` must verify (was fail-closed at the binding)"
    );
}

#[test]
fn letlocal_map_get_false_counterexamples() {
    let r = verify("get_f", GET_FALSE, "t");
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "CARDINAL: `m.get(1) == 999` must COUNTEREXAMPLE; got {r:?}"
    );
}

#[test]
fn letlocal_map_dom_contains_verifies() {
    assert!(
        matches!(verify("dom_t", DOM_TRUE, "t"), VerifyResult::Verified),
        "a let-local Map `m.dom().contains(1)` must verify"
    );
}

#[test]
fn letlocal_map_dom_absent_counterexamples() {
    let r = verify("dom_f", DOM_FALSE, "t");
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "CARDINAL: `m.dom().contains(2)` (absent key) must COUNTEREXAMPLE; got {r:?}"
    );
}

#[test]
fn vec_insert_still_models() {
    assert!(
        matches!(verify("vec", VEC_INSERT, "t"), VerifyResult::Verified),
        "a real exec Vec::insert must still model (ghost-decline must not affect Vec)"
    );
}

#[test]
fn ghost_map_remove_verifies() {
    assert!(
        matches!(
            verify("map_rm_t", MAP_REMOVE_TRUE, "t"),
            VerifyResult::Verified
        ),
        "a ghost `Map::remove(k)` value must model so `!m.dom().contains(k)` verifies"
    );
}

#[test]
fn ghost_map_remove_false_counterexamples() {
    let r = verify("map_rm_f", MAP_REMOVE_FALSE, "t");
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "CARDINAL: `m.dom().contains(1)` after removing 1 must COUNTEREXAMPLE; got {r:?}"
    );
}

#[test]
fn ghost_multiset_remove_verifies() {
    assert!(
        matches!(
            verify("ms_rm_t", MULTISET_REMOVE_TRUE, "t"),
            VerifyResult::Verified
        ),
        "a ghost `Multiset::remove` value must model so `count` decrements"
    );
}

#[test]
fn vec_remove_still_models() {
    assert!(
        matches!(verify("vec_rm", VEC_REMOVE, "t"), VerifyResult::Verified),
        "a real exec Vec::remove must still model (ghost-decline must not affect Vec)"
    );
}
