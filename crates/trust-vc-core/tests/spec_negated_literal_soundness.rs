// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A negated literal in a `requires` clause, compared with a fixed-width
//! operand.
//!
//! A `requires` clause is spec code, so `spec_arith::to_math_int_spec_arith`
//! folds `-c` to the `int` constant `-c`. When the other side of the
//! comparison is a fixed-width operand whose type holds `-c`, the constant is
//! written at that operand's type instead
//! (`negated_literal_at_fixed_width_peer`): both forms state the same
//! predicate, and the second one keeps the comparison in one sort. When the
//! operand's type cannot hold `-c` (`x == -1` with `x: u32`), the constant
//! stays `int`, so the clause stays false for every `x`.
//!
//! Each control is a true program and must verify. Each liar changes one
//! line so the claim is false and must be refuted.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

const SRC: &str = r####"
use trust_vc_types::Seq;

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 1)]
#[trust_vc::requires(s[0] == -1)]
#[trust_vc::requires(x == -1)]
#[trust_vc::ensures(s.contains(x))]
fn n1_contains_ctrl(s: Seq<i64>, x: i32) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 1)]
#[trust_vc::requires(s[0] == -2)]
#[trust_vc::requires(x == -1)]
#[trust_vc::ensures(s.contains(x))]
fn n1_contains_liar(s: Seq<i64>, x: i32) {}

#[trust_vc::requires(x == -5i8)]
#[trust_vc::ensures(result == 0i8)]
fn n2_scalar_ctrl(x: i8) -> i8 {
    x + 5i8
}

#[trust_vc::requires(x == -6i8)]
#[trust_vc::ensures(result == 0i8)]
fn n2_scalar_liar(x: i8) -> i8 {
    x + 5i8
}

#[trust_vc::requires(x < -100i8)]
#[trust_vc::ensures(result < 0i8)]
fn n3_order_ctrl(x: i8) -> i8 {
    x
}

#[trust_vc::requires(x > -100i8)]
#[trust_vc::ensures(result < 0i8)]
fn n3_order_liar(x: i8) -> i8 {
    x
}

#[trust_vc::requires(x == -1i64)]
#[trust_vc::ensures(result == x)]
fn neg_one_i64(x: i64) -> i64 {
    x
}

#[trust_vc::ensures(true)]
fn n4_caller_ctrl() {
    let r = neg_one_i64(-1i64);
}

#[trust_vc::ensures(true)]
fn n4_caller_liar() {
    let r = neg_one_i64(1i64);
}

#[trust_vc::requires(x == -1)]
#[trust_vc::ensures(result == x)]
fn neg_one_u32(x: u32) -> u32 {
    x
}

#[trust_vc::ensures(true)]
fn n5_unsigned_peer_caller_liar() {
    let r = neg_one_u32(4294967295u32);
}
"####;

fn verify(func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_spec_negated_literal_{}_{}_{seq}.rs",
        std::process::id(),
        func
    ));
    std::fs::write(&path, SRC).expect("write fixture");
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(path.to_str().expect("utf8 path"), func)
        })
        .map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&path);
    result
}

fn render(r: &Result<VerifyResult, String>) -> String {
    match r {
        Ok(VerifyResult::Verified) => "Verified".into(),
        Ok(VerifyResult::Counterexample {
            obligation_name, ..
        }) => format!("Counterexample({obligation_name})"),
        Ok(other) => format!("{other:?}").chars().take(240).collect(),
        Err(e) => format!("Err({})", e.chars().take(240).collect::<String>()),
    }
}

/// Controls verify; each one-line liar is a Counterexample.
///
/// Measured without the peer rule: `n1_contains_ctrl` and `n1_contains_liar`
/// are both `NotProved` (the solver does not decide `contains` over the
/// `bv2int`-bridged facts), the other controls verify, and the other liars
/// are Counterexamples.
#[test]
fn a_negated_literal_at_a_fixed_width_peer_is_decided_both_ways() {
    let mut wrong = Vec::new();
    for func in [
        "n1_contains_ctrl",
        "n2_scalar_ctrl",
        "n3_order_ctrl",
        "n4_caller_ctrl",
    ] {
        let r = verify(func);
        println!("{func}: {}", render(&r));
        if !matches!(r, Ok(VerifyResult::Verified)) {
            wrong.push(format!("{func} must verify: {}", render(&r)));
        }
    }
    for func in [
        "n1_contains_liar",
        "n2_scalar_liar",
        "n3_order_liar",
        "n4_caller_liar",
    ] {
        let r = verify(func);
        println!("{func}: {}", render(&r));
        if !matches!(r, Ok(VerifyResult::Counterexample { .. })) {
            wrong.push(format!("{func} must be refuted: {}", render(&r)));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// `x == -1` is false for every `x: u32`, so a caller passing `u32::MAX`
/// cannot establish it. The fit check keeps the constant `int` here. Measured
/// with the fit check removed, the constant is written at `u32`, reads
/// `4294967295`, and this call is `Verified`.
#[test]
fn a_negated_literal_an_unsigned_peer_cannot_hold_is_not_retyped() {
    let r = verify("n5_unsigned_peer_caller_liar");
    println!("n5_unsigned_peer_caller_liar: {}", render(&r));
    assert!(
        matches!(r, Ok(VerifyResult::Counterexample { .. })),
        "n5_unsigned_peer_caller_liar must be refuted: {}",
        render(&r)
    );
}
