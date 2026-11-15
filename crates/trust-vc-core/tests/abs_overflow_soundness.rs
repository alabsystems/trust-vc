// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `abs` on a signed integer panics at `MIN` (overflow checks on), so every
//! evaluated `x.abs()` in an exec body carries an overflow obligation, wherever
//! its value goes: a tail expression, a discarded statement, a `let`, an
//! assignment, a call argument, a tuple element, a branch, a loop body, or a
//! block that is an `if` condition.
//!
//! Every liar below is well typed and panics at run time on `x == MIN`
//! (checked with trustc, overflow checks on). Every twin is true and must
//! verify, including on a `mut` binding: `abs` on a signed primitive integer
//! is the inherent by-value method, so the call keeps the receiver's binding.
//!
//! A liar the lane cannot model (the UFCS spellings, a `&i64` receiver) must
//! fail closed. One true program is a recorded cost: a float `abs` whose value
//! reaches no obligation used to verify, and now fails closed because the lane
//! does not lower `f64::abs`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_abs_overflow_{}_{}_{seq}.rs",
        std::process::id(),
        func
    ));
    std::fs::write(&path, src).expect("write fixture");
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(path.to_str().expect("utf8 path"), func)
        })
        .map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&path);
    result
}

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// A true program: must verify.
    Verified,
    /// A panicking program: refuted with a counterexample.
    Counterexample,
    /// Refused before any verdict.
    FailClosed,
}

fn render(r: &Result<VerifyResult, String>) -> String {
    match r {
        Ok(VerifyResult::Verified) => "Verified".into(),
        Ok(VerifyResult::Counterexample {
            obligation_name, ..
        }) => format!("Counterexample({obligation_name})"),
        Ok(VerifyResult::Error { message }) => {
            format!("Error({})", message.chars().take(240).collect::<String>())
        }
        Ok(other) => format!("{:.240}", format!("{other:?}")),
        Err(e) => format!("Err({})", e.chars().take(240).collect::<String>()),
    }
}

fn check_table(src: &str, table: &[(&str, Expect)]) {
    let mut failures = Vec::new();
    for (func, expect) in table {
        let r = verify(src, func);
        let ok = match expect {
            Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
            Expect::Counterexample => matches!(r, Ok(VerifyResult::Counterexample { .. })),
            Expect::FailClosed => matches!(r, Ok(VerifyResult::Error { .. }) | Err(_)),
        };
        println!(
            "{func}: expect={expect:?} got={} {}",
            render(&r),
            if ok { "ok" } else { "MISMATCH" }
        );
        if !ok {
            failures.push(format!("{func}: expected {expect:?}, got {}", render(&r)));
        }
    }
    assert!(
        failures.is_empty(),
        "{} mismatch(es):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

use Expect::{Counterexample, FailClosed, Verified};

const SRC: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]

fn take(v: i64) -> u64 {
    1u64
}

#[trust_vc::ensures(true)]
fn b13_tail_liar(x: i64) -> i64 {
    x.abs()
}

#[trust_vc::ensures(true)]
fn r1_cond_block_mut_liar(mut x: i64) -> u64 {
    let v = if ({ x.abs(); true }) { 1u64 } else { 0u64 };
    v
}

#[trust_vc::ensures(true)]
fn r3_cond_block_liar(x: i64) -> u64 {
    let v = if ({ x.abs(); true }) { 1u64 } else { 0u64 };
    v
}

#[trust_vc::ensures(true)]
fn r4_statement_mut_liar(mut x: i64) -> u64 {
    x.abs();
    1u64
}

#[trust_vc::ensures(true)]
fn l1_let_liar(x: i32) -> u64 {
    let _y = x.abs();
    1u64
}

#[trust_vc::ensures(true)]
fn l2_call_arg_liar(x: i64) -> u64 {
    take(x.abs())
}

#[trust_vc::ensures(true)]
fn l3_i8_tuple_liar(x: i8) -> u64 {
    let _t = (x.abs(), 0u64);
    1u64
}

#[trust_vc::ensures(true)]
fn l4_branch_tail_liar(x: i64, c: bool) -> i64 {
    if c { x.abs() } else { 0i64 }
}

#[trust_vc::ensures(true)]
fn l5_match_arm_liar(x: i64, c: u8) -> i64 {
    match c {
        0u8 => x.abs(),
        _ => 0i64,
    }
}

#[trust_vc::ensures(true)]
fn l6_assign_liar(x: i64) -> i64 {
    let mut y = 0i64;
    y = x.abs();
    y
}

#[trust_vc::ensures(true)]
fn l7_return_liar(x: i64) -> i64 {
    return x.abs();
}

#[trust_vc::ensures(true)]
fn l8_loop_body_liar(x: i64) -> u64 {
    let mut i = 0u64;
    while i < 1u64 {
        x.abs();
        i = i + 1u64;
    }
    1u64
}

#[trust_vc::ensures(true)]
fn l9_nested_liar(x: i64) -> i64 {
    x.abs() / 2i64
}

#[trust_vc::ensures(true)]
fn f1_ufcs_liar(x: i64) -> i64 {
    i64::abs(x)
}

#[trust_vc::ensures(true)]
fn f2_qself_ufcs_liar(x: i64) -> i64 {
    <i64>::abs(x)
}

#[trust_vc::ensures(true)]
fn f3_ref_receiver_liar(x: &i64) -> i64 {
    x.abs()
}

#[trust_vc::requires(x > i64::MIN)]
#[trust_vc::ensures(true)]
fn t1_tail_twin(x: i64) -> i64 {
    x.abs()
}

#[trust_vc::requires(x > i64::MIN)]
#[trust_vc::ensures(true)]
fn t2_statement_twin(x: i64) -> u64 {
    x.abs();
    1u64
}

#[trust_vc::requires(x > i32::MIN)]
#[trust_vc::ensures(true)]
fn t3_let_twin(x: i32) -> u64 {
    let _y = x.abs();
    1u64
}

#[trust_vc::ensures(result >= 0i64)]
fn t4_saturating_twin(x: i64) -> i64 {
    x.saturating_abs()
}

#[trust_vc::requires(x > i64::MIN)]
#[trust_vc::ensures(true)]
fn t5_mut_tail_twin(mut x: i64) -> i64 {
    x.abs()
}

#[trust_vc::requires(x > i64::MIN)]
#[trust_vc::ensures(true)]
fn t6_mut_let_twin(mut x: i64) -> i64 {
    let y = x.abs();
    y
}

#[trust_vc::requires(x > i64::MIN && x < i64::MAX)]
#[trust_vc::ensures(true)]
fn t7_mut_rebound_tail_twin(mut x: i64) -> i64 {
    x = x + 1i64;
    x.abs()
}

#[trust_vc::requires(x > i64::MIN)]
#[trust_vc::ensures(true)]
fn t8_mut_statement_twin(mut x: i64) -> u64 {
    x.abs();
    1u64
}

#[trust_vc::ensures(result == 1u64)]
fn t9_mut_read_after_twin(mut x: i64) -> u64 {
    x = 3i64;
    x.abs();
    if x == 3i64 { 1u64 } else { 0u64 }
}

struct M(u64);
impl M {
    fn abs(&self) -> u64 {
        self.0
    }
}

#[trust_vc::ensures(true)]
fn t10_file_type_abs_twin(m: M) -> u64 {
    m.abs()
}

#[trust_vc::ensures(true)]
fn t11_file_type_abs_statement_twin(m: M) -> u64 {
    m.abs();
    1u64
}

#[trust_vc::ensures(true)]
fn c1_float_let_cost(x: f64) -> u64 {
    let _y = x.abs();
    1u64
}

#[trust_vc::ensures(result == 1u64)]
fn k1_mut_read_after_liar(mut x: i64) -> u64 {
    x = 3i64;
    x.abs();
    if x == 4i64 { 1u64 } else { 0u64 }
}
"#;

#[test]
fn every_evaluated_signed_abs_is_checked_for_overflow() {
    check_table(
        SRC,
        &[
            ("b13_tail_liar", Counterexample),
            ("r1_cond_block_mut_liar", Counterexample),
            ("r3_cond_block_liar", Counterexample),
            ("r4_statement_mut_liar", Counterexample),
            ("l1_let_liar", Counterexample),
            ("l2_call_arg_liar", Counterexample),
            ("l3_i8_tuple_liar", Counterexample),
            ("l4_branch_tail_liar", Counterexample),
            ("l5_match_arm_liar", Counterexample),
            ("l6_assign_liar", Counterexample),
            ("l7_return_liar", Counterexample),
            ("l8_loop_body_liar", Counterexample),
            ("l9_nested_liar", Counterexample),
            ("f1_ufcs_liar", FailClosed),
            ("f2_qself_ufcs_liar", FailClosed),
            ("f3_ref_receiver_liar", FailClosed),
            ("t1_tail_twin", Verified),
            ("t2_statement_twin", Verified),
            ("t3_let_twin", Verified),
            ("t4_saturating_twin", Verified),
            ("t5_mut_tail_twin", Verified),
            ("t6_mut_let_twin", Verified),
            ("t7_mut_rebound_tail_twin", Verified),
            ("t8_mut_statement_twin", Verified),
            ("t9_mut_read_after_twin", Verified),
            ("t10_file_type_abs_twin", Verified),
            ("t11_file_type_abs_statement_twin", Verified),
            ("c1_float_let_cost", FailClosed),
            // `abs` keeps `x` at its current value, not its entry value: the
            // read after the call sees the assignment before it.
            ("k1_mut_read_after_liar", Counterexample),
        ],
    );
}

/// An item-position macro invocation makes the file unenumerable: its
/// expansion may declare a type spelled `i64`, so `abs` does not keep a `mut`
/// receiver there. The binding is poisoned and the program fails closed.
const SRC_UNENUMERABLE: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]

macro_rules! nothing {
    () => {};
}
nothing!();

#[trust_vc::ensures(result == 1u64)]
fn g1_unenumerable_mut_read_after_gated(mut x: i64) -> u64 {
    x = 3i64;
    x.abs();
    if x == 3i64 { 1u64 } else { 0u64 }
}

#[trust_vc::ensures(true)]
fn g2_unenumerable_statement_liar(x: i64) -> u64 {
    x.abs();
    1u64
}
"#;

#[test]
fn abs_keeps_a_mut_receiver_only_in_an_enumerable_file() {
    check_table(
        SRC_UNENUMERABLE,
        &[
            ("g1_unenumerable_mut_read_after_gated", FailClosed),
            ("g2_unenumerable_statement_liar", Counterexample),
        ],
    );
}
