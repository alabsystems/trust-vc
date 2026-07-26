// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! `.clone()` in spec/exec context is the value-model identity `x.clone() == x`
//! for types whose `Clone` is structural — primitives (incl. floats already
//! supported), structural tuples, and Option/Result of integer payloads. A user
//! type may carry a non-structural custom `Clone`, so those fail closed.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_clone_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write fixture");
    let r =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
                VerifyResult::Error {
                    message: e.to_string(),
                }
            })
        });
    let _ = std::fs::remove_file(&p);
    r
}
fn verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}

const SRC: &str = r#"
#[trust_vc::ensures(result == x)]
fn clone_u64(x: u64) -> u64 { x.clone() }
#[trust_vc::ensures(result == b)]
fn clone_bool(b: bool) -> bool { b.clone() }
#[trust_vc::ensures(result == t)]
fn clone_tuple(t: (u64, bool)) -> (u64, bool) { t.clone() }
#[trust_vc::ensures(result == o)]
fn clone_option(o: Option<u64>) -> Option<u64> { o.clone() }
#[trust_vc::ensures(result == r)]
fn clone_result(r: Result<u64, u64>) -> Result<u64, u64> { r.clone() }

// Nested Option/Result/tuple combinations (structural recursively).
#[trust_vc::ensures(result == o)]
fn clone_option_tuple(o: Option<(u64, bool)>) -> Option<(u64, bool)> { o.clone() }
#[trust_vc::ensures(result == o)]
fn clone_nested_option(o: Option<Option<u64>>) -> Option<Option<u64>> { o.clone() }
#[trust_vc::ensures(result == t)]
fn clone_tuple_option(t: (Option<u64>, bool)) -> (Option<u64>, bool) { t.clone() }

// A user struct that DERIVES Clone: its clone is the structural identity.
#[derive(Clone)]
struct Point { x: u64, y: u64 }
#[trust_vc::ensures(result == p)]
fn clone_derived_struct(p: Point) -> Point { p.clone() }

// A user ENUM that DERIVES Clone (incl. payloads).
#[derive(Clone)]
enum Shape { Circle(u64), Square(u64, u64) }
#[trust_vc::ensures(result == s)]
fn clone_derived_enum(s: Shape) -> Shape { s.clone() }

// CARDINAL: a struct WITHOUT `#[derive(Clone)]` must fail closed (a custom Clone
// may not be the structural identity), so a function using it must NOT verify.
struct Wrap(u64);
#[trust_vc::ensures(true)]
fn clone_custom_fails_closed(w: Wrap) -> Wrap { w.clone() }
"#;

const BUILTIN_SHADOW_SRC: &str = r#"
enum Option<T> { None, Some(T) }
impl Clone for Option<u64> {
    fn clone(&self) -> Self { Option::None }
}
#[trust_vc::ensures(result == o)]
fn clone_user_option_shadow_fails_closed(o: Option<u64>) -> Option<u64> { o.clone() }
"#;

#[test]
fn clone_is_identity_for_structural_types() {
    for f in [
        "clone_u64",
        "clone_bool",
        "clone_tuple",
        "clone_option",
        "clone_result",
        "clone_option_tuple",
        "clone_nested_option",
        "clone_tuple_option",
        "clone_derived_struct",
        "clone_derived_enum",
    ] {
        assert!(
            verified(&verify(f, f, SRC)),
            "`{f}` should verify (clone == identity for structural Clone); got {:?}",
            verify(f, f, SRC)
        );
    }
}

#[test]
fn clone_on_custom_type_fails_closed() {
    assert!(
        !verified(&verify("c", "clone_custom_fails_closed", SRC)),
        "CARDINAL: a custom-type `.clone()` must fail closed (custom Clone may differ \
         from structural identity)"
    );
    assert!(
        !verified(&verify(
            "shadow",
            "clone_user_option_shadow_fails_closed",
            BUILTIN_SHADOW_SRC,
        )),
        "CARDINAL: a user `Option` must not inherit std Option clone identity"
    );
}
