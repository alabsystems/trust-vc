// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! A `let` binding whose pattern is a struct pattern with a rest
//! (`let S { a, .. } = obj;`) now lowers — previously "Failed to lower
//! obligation". `struct_rest_pattern_desugar.rs` rewrites it to the equivalent
//! per-field `let a = obj.a;` bindings, reusing the field-projection path.
//!
//! CARDINAL SOUNDNESS: the rewrite reproduces Rust's field/binding mapping
//! exactly (shorthand `a` ⇒ `obj.a`, rename `a: x` ⇒ `x = obj.a`), so a wrong
//! field mapping is refuted (`liar_field`). It fires only for plain-ident field
//! bindings and a side-effect-free identifier initializer (a call/index init is
//! left fail-closed, since re-projecting it per field would re-run the effect).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_srp_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}
fn verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}

const SRC: &str = r#"
struct S3 { a: u64, b: u64, c: u64 }
// shorthand binding + rest
#[trust_vc::requires(s.a == 5u64)]
#[trust_vc::ensures(result == 5u64)]
fn shorthand(s: S3) -> u64 { let S3 { a, .. } = s; a }
// several fields
#[trust_vc::requires(s.a == 5u64 && s.b == 7u64)]
#[trust_vc::ensures(result == 12u64)]
fn multi(s: S3) -> u64 { let S3 { a, b, .. } = s; a + b }
// renamed field
#[trust_vc::requires(s.a == 5u64)]
#[trust_vc::ensures(result == 5u64)]
fn renamed(s: S3) -> u64 { let S3 { a: x, .. } = s; x }
// CARDINAL LIAR: `a` maps to s.a (== 5), so a claim `result == 6` (== s.b) is false
#[trust_vc::requires(s.a == 5u64 && s.b == 6u64)]
#[trust_vc::ensures(result == 6u64)]
fn liar_field(s: S3) -> u64 { let S3 { a, .. } = s; a }
// fixed-array pattern (`_` elements skipped)
#[trust_vc::requires(arr[0] == 5u64 && arr[2] == 7u64)]
#[trust_vc::ensures(result == 12u64)]
fn array_multi(arr: [u64; 3]) -> u64 { let [a, _, c] = arr; a + c }
// CARDINAL LIAR: `a` binds arr[0] (== 5), so `result == 7` (== arr[2]) is false
#[trust_vc::requires(arr[0] == 5u64 && arr[2] == 7u64)]
#[trust_vc::ensures(result == 7u64)]
fn array_liar(arr: [u64; 3]) -> u64 { let [a, _, _] = arr; a }
"#;

const TUPLE_STRUCT: &str = r#"
struct TS(u64, u64, u64);
// tuple-struct pattern binds by position; `_` skipped
#[trust_vc::requires(t.0 == 5u64 && t.2 == 7u64)]
#[trust_vc::ensures(result == 12u64)]
fn ts_multi(t: TS) -> u64 { let TS(a, _, c) = t; a + c }
// CARDINAL LIAR: `a` binds t.0 (== 5), so `result == 7` (== t.2) is false
#[trust_vc::requires(t.0 == 5u64 && t.2 == 7u64)]
#[trust_vc::ensures(result == 7u64)]
fn ts_liar(t: TS) -> u64 { let TS(a, _, _) = t; a }
"#;

const NESTED: &str = r#"
struct Inner { v: u64, w: u64 }
struct Outer { inner: Inner, tag: u64 }
// nested struct pattern with an outer rest
#[trust_vc::requires(o.inner.v == 5u64)]
#[trust_vc::ensures(result == 5u64)]
fn nested(o: Outer) -> u64 { let Outer { inner: Inner { v, .. }, .. } = o; v }
// full outer + nested rest (fires on the nested-struct field, not a top-level rest)
#[trust_vc::requires(o.inner.v == 5u64 && o.tag == 3u64)]
#[trust_vc::ensures(result == 8u64)]
fn nested_sibling(o: Outer) -> u64 { let Outer { inner: Inner { v, .. }, tag } = o; v + tag }
// CARDINAL LIAR: `v` binds o.inner.v (== 5), so `result == 6` (== o.inner.w) is false
#[trust_vc::requires(o.inner.v == 5u64 && o.inner.w == 6u64)]
#[trust_vc::ensures(result == 6u64)]
fn nested_liar(o: Outer) -> u64 { let Outer { inner: Inner { v, .. }, .. } = o; v }
"#;

#[test]
fn struct_rest_and_array_patterns_bind_elements() {
    for f in ["shorthand", "multi", "renamed", "array_multi"] {
        assert!(
            verified(&verify(f, f, SRC)),
            "`{f}`: a struct-rest or fixed-array let pattern should bind its elements; got {:?}",
            verify(f, f, SRC)
        );
    }
}

#[test]
fn wrong_element_mapping_fails_closed() {
    for f in ["liar_field", "array_liar"] {
        assert!(
            !verified(&verify(f, f, SRC)),
            "CARDINAL: `{f}`: a binding maps to a specific field/index, so a claim about a \
             DIFFERENT element must NOT verify — a mis-mapping would false-verify here"
        );
    }
}

#[test]
fn tuple_struct_patterns_bind_by_position() {
    assert!(
        verified(&verify("ts_multi", "ts_multi", TUPLE_STRUCT)),
        "a tuple-struct let pattern should bind by position; got {:?}",
        verify("ts_multi", "ts_multi", TUPLE_STRUCT)
    );
    assert!(
        !verified(&verify("ts_liar", "ts_liar", TUPLE_STRUCT)),
        "CARDINAL: `a` binds `t.0` (== 5), so `result == 7` (== t.2) must NOT verify"
    );
}

#[test]
fn nested_struct_patterns_flatten_field_paths() {
    for f in ["nested", "nested_sibling"] {
        assert!(
            verified(&verify(f, f, NESTED)),
            "`{f}`: a nested struct pattern should flatten to a field-path binding; got {:?}",
            verify(f, f, NESTED)
        );
    }
    assert!(
        !verified(&verify("nested_liar", "nested_liar", NESTED)),
        "CARDINAL: `v` binds `o.inner.v` (== 5), so `result == 6` (== o.inner.w) must NOT verify"
    );
}
