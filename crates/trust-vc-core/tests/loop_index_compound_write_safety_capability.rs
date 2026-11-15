// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! An index compound write inside a loop body carries the arithmetic
//! obligation of its plain spelling.
//!
//! Outside loops `a[i] op= rhs` pins one reflexive element-safety obligation
//! (write bound + element overflow). Inside ANY loop that obligation was
//! deferred and nothing replaced it, so `while i < 10 { a[0] += 1u8; .. }`
//! under `requires(a[0] == 250u8)` VERIFIED a guaranteed overflow, as did the
//! `for` form and a local array — while the plain `a[0] = a[0] + 1u8` is
//! checked against the loop-body head state (the RHS obligation of an index
//! write). The compound now pins the plain write's obligation on every checked
//! site of `(a[i]) op (rhs)` — a bitwise compound over an arithmetic right
//! operand (`a[0] ^= b + 255u8`, measured VERIFIED by the first cut of this
//! fix, which only looked at a top-level arithmetic `op`) included; a place or
//! right operand with an embedded assignment fails closed.
//!
//! Every positive is paired with a refuted sibling in the same file context.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_licws_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

const SRC: &str = r#"
#[trust_vc::requires(a[0] == 250u8)]
fn while_param_compound_overflow(mut a: [u8; 2]) { let mut i = 0u64; while i < 10u64 { trust_vc::invariant!(i <= 10u64); a[0] += 1u8; i = i + 1u64; } }
#[trust_vc::requires(a[0] == 250u8)]
fn for_param_compound_overflow(mut a: [u8; 2]) { for _j in 0u64..10u64 { a[0] += 1u8; } }
#[trust_vc::ensures(true)]
fn while_local_compound_overflow() { let mut a = [250u8, 0u8]; let mut i = 0u64; while i < 10u64 { trust_vc::invariant!(i <= 10u64); a[0] += 1u8; i = i + 1u64; } }

#[trust_vc::ensures(true)]
fn bitwise_compound_over_overflowing_rhs(mut a: [u8; 2], b: u8) { let mut i = 0u64; while i < 2u64 { trust_vc::invariant!(i <= 2u64); a[0] ^= b + 255u8; i = i + 1u64; } }
#[trust_vc::ensures(true)]
fn bitwise_compound_over_dividing_rhs(mut a: [u8; 2], d: u8) { let mut i = 0u64; while i < 2u64 { trust_vc::invariant!(i <= 2u64); a[1] &= 7u8 / d; i = i + 1u64; } }

#[trust_vc::ensures(true)]
fn guarded_increment_is_safe(mut a: [u8; 2]) { let mut i = 0u64; while i < 10u64 { trust_vc::invariant!(i <= 10u64); if a[0] < 255u8 { a[0] += 1u8; } i = i + 1u64; } }
#[trust_vc::ensures(true)]
fn bitwise_compound_needs_no_arithmetic_check(mut a: [u8; 2]) { let mut i = 0u64; while i < 10u64 { trust_vc::invariant!(i <= 10u64); a[1] ^= 1u8; i = i + 1u64; } }
#[trust_vc::ensures(true)]
fn divide_by_nonzero_literal(mut a: [u8; 2]) { let mut i = 0u64; while i < 3u64 { trust_vc::invariant!(i <= 3u64); a[0] /= 2u8; i = i + 1u64; } }
#[trust_vc::ensures(true)]
fn divide_by_unconstrained_parameter(mut a: [u8; 2], d: u8) { let mut i = 0u64; while i < 3u64 { trust_vc::invariant!(i <= 3u64); a[0] /= d; i = i + 1u64; } }
"#;

#[test]
fn an_index_compound_write_in_a_loop_is_checked() {
    let mut failures = Vec::new();
    for (index, func) in [
        "while_param_compound_overflow",
        "for_param_compound_overflow",
        "while_local_compound_overflow",
        "bitwise_compound_over_overflowing_rhs",
    ]
    .into_iter()
    .enumerate()
    {
        let r = verify(&format!("o{index}"), func, SRC);
        if matches!(r, VerifyResult::Verified) {
            failures.push(format!("{func}: {r:?}"));
        }
    }
    assert!(
        failures.is_empty(),
        "CARDINAL: these overflow inside the loop body and must not verify:\n{}",
        failures.join("\n")
    );
    for (id, func) in [
        ("d1", "divide_by_unconstrained_parameter"),
        ("d2", "bitwise_compound_over_dividing_rhs"),
    ] {
        let r = verify(id, func, SRC);
        assert!(
            matches!(&r, VerifyResult::Counterexample { obligation_name, .. } if obligation_name.starts_with("overflow_check_")),
            "CARDINAL: {func} divides by an unconstrained parameter and must be refuted at its division obligation, got {r:?}"
        );
    }
}

#[test]
fn a_safe_index_compound_write_in_a_loop_still_verifies() {
    for (index, func) in [
        "guarded_increment_is_safe",
        "bitwise_compound_needs_no_arithmetic_check",
        "divide_by_nonzero_literal",
    ]
    .into_iter()
    .enumerate()
    {
        let r = verify(&format!("s{index}"), func, SRC);
        assert!(
            matches!(r, VerifyResult::Verified),
            "{func} should verify, got {r:?}"
        );
    }
}
