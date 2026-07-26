// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A ghost collection whose ELEMENT type is a TUPLE (`Seq<(u32, u32)>`,
//! `Set<(u32, u32)>`, `Map<u32, (u32, u32)>`) is now modeled — previously the
//! collection-constructor element-type parser rejected a tuple ("unsupported
//! collection constructor type '(u32,u32)'") because a tuple is a `syn::Type::Tuple`,
//! not a `Type::Path`. It now routes through the same general resolver the unknown-
//! `Path` element arm uses (`env.resolve_syn_type`), which models the tuple sort.
//!
//! Sound-by-construction: a resolvable tuple element encodes like any other sort;
//! an unresolvable one becomes opaque and fails closed downstream. A false claim
//! on a tuple field must still COUNTEREXAMPLE.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(name: &str, src: &str, target: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_tup_{}_{}.rs", std::process::id(), name));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), target).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

const SEQ_FIELD0: &str = r#"
use trust_vc_types::Seq;
#[trust_vc::ensures(true)]
fn t() { let s = Seq::<(u32,u32)>::empty().push((3u32, 4u32)); trust_vc::assert!(s.index(0int).0 == 3u32); }
"#;

const SEQ_FIELD1: &str = r#"
use trust_vc_types::Seq;
#[trust_vc::ensures(true)]
fn t() { let s = Seq::<(u32,u32)>::empty().push((3u32, 4u32)); trust_vc::assert!(s.index(0int).1 == 4u32); }
"#;

const SEQ_FALSE: &str = r#"
use trust_vc_types::Seq;
#[trust_vc::ensures(true)]
fn t() { let s = Seq::<(u32,u32)>::empty().push((3u32, 4u32)); trust_vc::assert!(s.index(0int).0 == 999u32); }
"#;

const SET_TUPLE: &str = r#"
use trust_vc_types::Set;
#[trust_vc::ensures(true)]
fn t() { let s = Set::<(u32,u32)>::empty().insert((1u32, 2u32)); trust_vc::assert!(s.contains((1u32, 2u32))); }
"#;

const MAP_TUPLE_VALUE: &str = r#"
use trust_vc_types::Map;
#[trust_vc::ensures(true)]
fn t() { let m = Map::<u32,(u32,u32)>::empty().insert(1u32, (7u32, 8u32)); trust_vc::assert!(m.get(1u32).1 == 8u32); }
"#;

const MAP_TUPLE_FALSE: &str = r#"
use trust_vc_types::Map;
#[trust_vc::ensures(true)]
fn t() { let m = Map::<u32,(u32,u32)>::empty().insert(1u32, (7u32, 8u32)); trust_vc::assert!(m.get(1u32).1 == 999u32); }
"#;

#[test]
fn seq_tuple_field0_verifies() {
    assert!(
        matches!(verify("s0", SEQ_FIELD0, "t"), VerifyResult::Verified),
        "`Seq<(u32,u32)>` element field `.0` must verify"
    );
}

#[test]
fn seq_tuple_field1_verifies() {
    assert!(
        matches!(verify("s1", SEQ_FIELD1, "t"), VerifyResult::Verified),
        "`Seq<(u32,u32)>` element field `.1` must verify"
    );
}

#[test]
fn seq_tuple_false_counterexamples() {
    let r = verify("sf", SEQ_FALSE, "t");
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "CARDINAL: a false tuple-field claim (`.0 == 999`) must COUNTEREXAMPLE; got {r:?}"
    );
}

#[test]
fn set_tuple_contains_verifies() {
    assert!(
        matches!(verify("set", SET_TUPLE, "t"), VerifyResult::Verified),
        "`Set<(u32,u32)>` contains of an inserted tuple must verify"
    );
}

#[test]
fn map_tuple_value_verifies() {
    assert!(
        matches!(verify("mv", MAP_TUPLE_VALUE, "t"), VerifyResult::Verified),
        "`Map<u32,(u32,u32)>` value field `.1` must verify"
    );
}

#[test]
fn map_tuple_false_counterexamples() {
    let r = verify("mf", MAP_TUPLE_FALSE, "t");
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "CARDINAL: a false Map-tuple-value claim must COUNTEREXAMPLE; got {r:?}"
    );
}
