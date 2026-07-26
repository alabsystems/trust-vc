// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Value-in-field constructor patterns: `Some(5)`, `Point { x: 5, .. }` — a
//! literal sub-pattern inside a tuple-struct/struct pattern, in both the
//! `matches` operator and a direct spec `match`. Desugars to a fresh binder plus
//! an equality guard (`Some(__v) if __v == 5`), reusing the encoder's verified
//! guard fall-through. Positives Verify; every cardinal liar is fail-closed, and
//! fall-through past a failed value-guard lands on the later arm (never the
//! literal arm's body).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_vsp_{}_{}.rs", std::process::id(), id));
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
struct Point { x: u64, y: u64 }

// `matches` operator with a value-in-field pattern.
#[trust_vc::ensures(result matches Some(5u64))]
fn matches_op_pos() -> Option<u64> { Some(5u64) }
#[trust_vc::ensures(result matches Some(5u64))]
fn matches_op_liar() -> Option<u64> { Some(6u64) }

// Direct spec `match` with a value-in-field tuple pattern + explicit wildcard.
#[trust_vc::ensures((match result { Some(5u64) => 1u64, _ => 2u64 }) == 1u64)]
fn disc_pos() -> Option<u64> { Some(5u64) }
#[trust_vc::ensures((match result { Some(5u64) => 1u64, _ => 2u64 }) == 2u64)]
fn disc_fallthrough() -> Option<u64> { Some(7u64) }
#[trust_vc::ensures((match result { Some(5u64) => 1u64, _ => 2u64 }) == 1u64)]
fn disc_liar() -> Option<u64> { Some(7u64) }

// Struct value pattern: a named field pinned to a literal, another bound.
#[trust_vc::ensures((match result { Point { x: 5u64, y } => y, _ => 0u64 }) == 9u64)]
fn struct_pos() -> Point { Point { x: 5u64, y: 9u64 } }
#[trust_vc::ensures((match result { Point { x: 5u64, y } => y, _ => 0u64 }) == 9u64)]
fn struct_liar() -> Point { Point { x: 6u64, y: 9u64 } }

// Multi-field tuple pattern: two literals must both hold.
#[trust_vc::ensures((match result { Pair(1u64, 2u64) => 10u64, _ => 20u64 }) == 10u64)]
fn pair_pos() -> Pair { Pair(1u64, 2u64) }
#[trust_vc::ensures((match result { Pair(1u64, 2u64) => 10u64, _ => 20u64 }) == 10u64)]
fn pair_liar() -> Pair { Pair(1u64, 3u64) }

struct Pair(u64, u64);

// Freshness adversaries: the implementation's preferred synthesized spelling
// is a perfectly legal user identifier. It must avoid both a sibling pattern
// binding and an outer parameter referenced by the arm guard/body.
#[trust_vc::ensures((match result { Pair(__trust_vc_valpat_0, 2u64) => __trust_vc_valpat_0, _ => 0u64 }) == 9u64)]
fn same_pattern_name_pos() -> Pair { Pair(9u64, 2u64) }
#[trust_vc::ensures((match result { Pair(__trust_vc_valpat_0, 2u64) => __trust_vc_valpat_0, _ => 0u64 }) == 9u64)]
fn same_pattern_name_liar() -> Pair { Pair(8u64, 2u64) }

#[trust_vc::requires(__trust_vc_valpat_0 == 9u64)]
#[trust_vc::ensures((match result { Some(5u64) => __trust_vc_valpat_0, _ => 0u64 }) == 9u64)]
fn outer_body_name_pos(__trust_vc_valpat_0: u64) -> Option<u64> { Some(5u64) }
#[trust_vc::requires(__trust_vc_valpat_0 == 9u64)]
#[trust_vc::ensures((match result { Some(5u64) => __trust_vc_valpat_0, _ => 0u64 }) == 10u64)]
fn outer_body_name_liar(__trust_vc_valpat_0: u64) -> Option<u64> { Some(5u64) }

#[trust_vc::requires(__trust_vc_valpat_0 == 5u64)]
#[trust_vc::ensures((match result { Some(6u64) if __trust_vc_valpat_0 == 5u64 => 1u64, _ => 2u64 }) == 1u64)]
fn outer_guard_name_pos(__trust_vc_valpat_0: u64) -> Option<u64> { Some(6u64) }
#[trust_vc::requires(__trust_vc_valpat_0 == 5u64)]
#[trust_vc::ensures((match result { Some(6u64) if __trust_vc_valpat_0 == 5u64 => 1u64, _ => 2u64 }) == 2u64)]
fn outer_guard_name_liar(__trust_vc_valpat_0: u64) -> Option<u64> { Some(6u64) }
"#;

#[test]
fn matches_operator_value_pattern() {
    assert!(
        verified(&verify("mp", "matches_op_pos", SRC)),
        "result matches Some(5) on Some(5) must verify"
    );
    assert!(
        !verified(&verify("ml", "matches_op_liar", SRC)),
        "CARDINAL: result matches Some(5) on Some(6) must NOT verify"
    );
}

#[test]
fn direct_match_value_pattern_and_fallthrough() {
    assert!(
        verified(&verify("dp", "disc_pos", SRC)),
        "Some(5) selects the literal arm (==1)"
    );
    assert!(
        verified(&verify("df", "disc_fallthrough", SRC)),
        "Some(7) falls through the failed value-guard to the wildcard (==2)"
    );
    assert!(
        !verified(&verify("dl", "disc_liar", SRC)),
        "CARDINAL: Some(7) must NOT reach the literal arm's body (== 1 is false)"
    );
}

#[test]
fn struct_value_pattern_and_liar() {
    assert!(
        verified(&verify("sp", "struct_pos", SRC)),
        "struct value pattern matches when x==5, binding y"
    );
    assert!(
        !verified(&verify("sl", "struct_liar", SRC)),
        "CARDINAL: struct value pattern must NOT match when x==6"
    );
}

#[test]
fn multi_literal_tuple_pattern_and_liar() {
    assert!(
        verified(&verify("pp", "pair_pos", SRC)),
        "Pair(1, 2) matches Pair(1, 2)"
    );
    assert!(
        !verified(&verify("pl", "pair_liar", SRC)),
        "CARDINAL: Pair(1, 2) must NOT match Pair(1, 3)"
    );
}

#[test]
fn synthesized_binders_are_fresh_against_pattern_bindings() {
    assert!(
        verified(&verify("fp", "same_pattern_name_pos", SRC)),
        "a generated binder must not overwrite a sibling user binding"
    );
    assert!(
        !verified(&verify("fl", "same_pattern_name_liar", SRC)),
        "CARDINAL: collision avoidance must not make a false payload verify"
    );
}

#[test]
fn synthesized_binders_do_not_shadow_outer_guard_or_body_names() {
    assert!(
        verified(&verify("fbp", "outer_body_name_pos", SRC)),
        "a generated binder must not shadow an outer name in the arm body"
    );
    assert!(
        !verified(&verify("fbl", "outer_body_name_liar", SRC)),
        "CARDINAL: outer body references must retain their source binding"
    );
    assert!(
        verified(&verify("fgp", "outer_guard_name_pos", SRC)),
        "a generated binder must not shadow an outer name in the arm guard"
    );
    assert!(
        !verified(&verify("fgl", "outer_guard_name_liar", SRC)),
        "CARDINAL: outer guard references must retain their source binding"
    );
}
