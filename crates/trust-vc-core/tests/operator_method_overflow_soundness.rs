// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A std integer method that can panic (overflow checks on) panics even when
//! its value reaches no obligation, so every evaluated call is checked.
//!
//! `x.add(e)`, `x.shl(n)` and `x.shr(n)` on a primitive integer are the std
//! operator impls, which panic exactly where `x + e`, `x << n` and `x >> n`
//! do, and the lane lowers them to those operators. So every evaluated call
//! carries the operator's overflow or shift-amount obligation, wherever its
//! value goes: a tail expression, a discarded statement, a `let`, an
//! assignment, a call argument, a tuple element, a closure body, a
//! comparison, or a block that is an `if` condition. The other panicking
//! methods (`sub`, `mul`, `div`, `pow`, `ilog2`, ...), and every spelling
//! that names one through a path (`u64::pow(x, n)`, `Add::add(x, 1)`), carry
//! their check where the lane models the method and fail closed where it
//! does not.
//!
//! Every liar below is well typed and panics at run time (checked with
//! trustc, overflow checks on). Every twin is true and must verify, including
//! on a `mut` binding when the file imports the std trait: the call is then
//! the by-value std method, so it keeps the receiver's binding. Without that
//! import the call may resolve to another trait's `&mut self` method, so a
//! `mut` receiver is not kept and a read after the call fails closed.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_operator_method_{}_{}_{seq}.rs",
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

use std::ops::{Add, Shl, Shr};

fn take(v: u64) -> u64 {
    1u64
}

#[trust_vc::ensures(true)]
fn b15_tail_liar(x: u64) -> u64 {
    x.add(1u64)
}

#[trust_vc::ensures(true)]
fn r2_cond_block_mut_liar(mut x: u64) -> u64 {
    let v = if ({ x.add(1u64); true }) { 1u64 } else { 0u64 };
    v
}

#[trust_vc::ensures(true)]
fn r5_cond_block_liar(x: u64) -> u64 {
    let v = if ({ x.add(1u64); true }) { 1u64 } else { 0u64 };
    v
}

#[trust_vc::ensures(true)]
fn l1_statement_liar(x: u64) -> u64 {
    x.add(1u64);
    1u64
}

#[trust_vc::ensures(true)]
fn l2_let_liar(x: i32) -> u64 {
    let _y = x.add(1i32);
    1u64
}

#[trust_vc::ensures(true)]
fn l3_mut_assign_liar(mut x: u64) -> u64 {
    x = x.add(1u64);
    1u64
}

#[trust_vc::ensures(true)]
fn l4_call_arg_liar(x: u64) -> u64 {
    take(x.add(1u64))
}

#[trust_vc::ensures(true)]
fn l5_i8_tuple_liar(x: i8) -> u64 {
    let _t = (x.add(1i8), 0u64);
    1u64
}

#[trust_vc::ensures(true)]
fn l6_closure_liar(x: u64) -> u64 {
    let f = |y: u64| y.add(1u64);
    f(x)
}

#[trust_vc::ensures(true)]
fn l7_comparison_liar(x: u64) -> bool {
    x.add(1u64) > 0u64
}

#[trust_vc::ensures(true)]
fn l8_chained_liar(x: u64) -> u64 {
    x.add(1u64).add(1u64)
}

#[trust_vc::ensures(true)]
fn h1_shl_statement_liar(x: u64) -> u64 {
    x.shl(70u32);
    1u64
}

#[trust_vc::ensures(true)]
fn h2_shr_let_liar(x: u64, n: u32) -> u64 {
    let _y = x.shr(n);
    1u64
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == x + 1)]
fn t1_tail_twin(x: u64) -> u64 {
    x.add(1u64)
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(true)]
fn t2_statement_twin(x: u64) -> u64 {
    x.add(1u64);
    1u64
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == x + 2)]
fn t3_chained_twin(x: u64) -> u64 {
    x.add(1u64).add(1u64)
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == 1u64)]
fn t4_cond_twin(x: u64) -> u64 {
    if x.add(1u64) > 0u64 { 1u64 } else { 0u64 }
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == x + 1)]
fn t5_mut_tail_twin(mut x: u64) -> u64 {
    x.add(1u64)
}

#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(result == x + 1)]
fn t6_mut_assign_twin(mut x: u64) -> u64 {
    x = x.add(1u64);
    x
}

#[trust_vc::requires(n < 64u32)]
#[trust_vc::ensures(true)]
fn t7_shr_twin(x: u64, n: u32) -> u64 {
    x.shr(n)
}

#[trust_vc::ensures(result == 1u64)]
fn t8_mut_read_after_twin(mut x: u64) -> u64 {
    x = 3u64;
    x.add(1u64);
    if x == 3u64 { 1u64 } else { 0u64 }
}

#[trust_vc::ensures(result == 1u64)]
fn k1_mut_read_after_liar(mut x: u64) -> u64 {
    x = 3u64;
    x.add(1u64);
    if x == 4u64 { 1u64 } else { 0u64 }
}

#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn k2_mut_current_value_liar(mut x: u64, y: u64) -> u64 {
    x = y;
    x.add(1u64);
    1u64
}
"#;

#[test]
fn every_evaluated_integer_operator_method_is_checked() {
    check_table(
        SRC,
        &[
            ("b15_tail_liar", Counterexample),
            ("r2_cond_block_mut_liar", Counterexample),
            ("r5_cond_block_liar", Counterexample),
            ("l1_statement_liar", Counterexample),
            ("l2_let_liar", Counterexample),
            ("l3_mut_assign_liar", Counterexample),
            ("l4_call_arg_liar", Counterexample),
            ("l5_i8_tuple_liar", Counterexample),
            ("l6_closure_liar", Counterexample),
            ("l7_comparison_liar", Counterexample),
            ("l8_chained_liar", Counterexample),
            ("h1_shl_statement_liar", Counterexample),
            ("h2_shr_let_liar", Counterexample),
            ("t1_tail_twin", Verified),
            ("t2_statement_twin", Verified),
            ("t3_chained_twin", Verified),
            ("t4_cond_twin", Verified),
            ("t5_mut_tail_twin", Verified),
            ("t6_mut_assign_twin", Verified),
            ("t7_shr_twin", Verified),
            ("t8_mut_read_after_twin", Verified),
            // The call keeps `x` at its current value, not its entry value.
            ("k1_mut_read_after_liar", Counterexample),
            ("k2_mut_current_value_liar", Counterexample),
        ],
    );
}

/// The other std integer methods that can panic, and the iterator folds `sum`
/// and `product`. The lane does not model most of them, so a call whose value reaches no obligation fails closed; the
/// Euclidean division and remainder carry their divisor check. The UFCS
/// spellings and a method named as a value fail closed too. Methods that
/// cannot panic are no sites, and a true program that uses them still
/// verifies. Two true programs are recorded costs: `x.pow(2u32)` under a
/// bound, and `f64` division spelled as a method, used to verify and now fail
/// closed, because the lane models neither.
const SRC_OTHER_METHODS: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]

use std::ops::{Add, Div, Mul, Neg, Rem, Sub};

#[trust_vc::ensures(true)]
fn o1_sub_liar(x: u64) -> u64 {
    x.sub(1u64);
    1u64
}

#[trust_vc::ensures(true)]
fn o2_mul_liar(x: u64) -> u64 {
    let _y = x.mul(2u64);
    1u64
}

#[trust_vc::ensures(true)]
fn o3_div_liar(x: u64, y: u64) -> u64 {
    x.div(y);
    1u64
}

#[trust_vc::ensures(true)]
fn o4_rem_liar(x: u64, y: u64) -> u64 {
    x.rem(y);
    1u64
}

#[trust_vc::ensures(true)]
fn o5_neg_liar(x: i64) -> u64 {
    x.neg();
    1u64
}

#[trust_vc::ensures(true)]
fn o6_pow_liar(x: u64) -> u64 {
    x.pow(70u32);
    1u64
}

#[trust_vc::ensures(true)]
fn o7_ilog2_liar(x: u64) -> u64 {
    let _y = x.ilog2();
    1u64
}

#[trust_vc::ensures(true)]
fn o8_next_power_of_two_liar(x: u64) -> u64 {
    x.next_power_of_two();
    1u64
}

#[trust_vc::ensures(true)]
fn o9_wrapping_div_liar(x: u64, y: u64) -> u64 {
    x.wrapping_div(y);
    1u64
}

#[trust_vc::ensures(true)]
fn o10_div_euclid_liar(x: u64, y: u64) -> u64 {
    x.div_euclid(y);
    1u64
}

#[trust_vc::ensures(true)]
fn o11_rem_euclid_liar(x: i64, y: i64) -> u64 {
    let _r = x.rem_euclid(y);
    1u64
}

#[trust_vc::ensures(true)]
fn u1_ufcs_pow_liar(x: u64) -> u64 {
    u64::pow(x, 70u32);
    1u64
}

#[trust_vc::ensures(true)]
fn u2_ufcs_abs_liar(x: i64) -> u64 {
    i64::abs(x);
    1u64
}

#[trust_vc::ensures(true)]
fn u3_ufcs_trait_add_liar(x: u64) -> u64 {
    Add::add(x, 1u64);
    1u64
}

#[trust_vc::ensures(true)]
fn u4_qself_add_liar(x: u64) -> u64 {
    let _y = <u64 as Add>::add(x, 1u64);
    1u64
}

#[trust_vc::ensures(true)]
fn u5_fn_item_value_liar(x: u64) -> u64 {
    let f = u64::pow;
    f(x, 70u32);
    1u64
}

#[trust_vc::ensures(true)]
fn i1_iter_sum_liar(v: Vec<u64>) -> u64 {
    let _s: u64 = v.iter().sum();
    1u64
}

#[trust_vc::ensures(true)]
fn i2_iter_product_liar(v: Vec<u64>) -> u64 {
    let _p: u64 = v.iter().product();
    1u64
}

#[trust_vc::requires(y > 0u64)]
#[trust_vc::ensures(true)]
fn t1_div_euclid_twin(x: u64, y: u64) -> u64 {
    x.div_euclid(y);
    1u64
}

#[trust_vc::ensures(true)]
fn t2_non_panicking_twin(x: u64, y: u64) -> u64 {
    x.checked_add(1u64);
    x.wrapping_add(y);
    x.abs_diff(y);
    x.checked_div(y);
    x.saturating_mul(y);
    u64::checked_div(x, y);
    1u64
}

#[trust_vc::requires(x < 10u64)]
#[trust_vc::ensures(true)]
fn c1_pow_cost(x: u64) -> u64 {
    x.pow(2u32);
    1u64
}

#[trust_vc::ensures(true)]
fn c2_float_div_cost(x: f64, y: f64) -> u64 {
    let _z = x.div(y);
    1u64
}
"#;

#[test]
fn every_other_panicking_integer_method_is_checked_or_fails_closed() {
    check_table(
        SRC_OTHER_METHODS,
        &[
            ("o1_sub_liar", FailClosed),
            ("o2_mul_liar", FailClosed),
            ("o3_div_liar", FailClosed),
            ("o4_rem_liar", FailClosed),
            ("o5_neg_liar", FailClosed),
            ("o6_pow_liar", FailClosed),
            ("o7_ilog2_liar", FailClosed),
            ("o8_next_power_of_two_liar", FailClosed),
            ("o9_wrapping_div_liar", FailClosed),
            ("o10_div_euclid_liar", Counterexample),
            ("o11_rem_euclid_liar", Counterexample),
            ("u1_ufcs_pow_liar", FailClosed),
            ("u2_ufcs_abs_liar", FailClosed),
            ("u3_ufcs_trait_add_liar", FailClosed),
            ("u4_qself_add_liar", FailClosed),
            ("u5_fn_item_value_liar", FailClosed),
            ("i1_iter_sum_liar", FailClosed),
            ("i2_iter_product_liar", FailClosed),
            ("t1_div_euclid_twin", Verified),
            ("t2_non_panicking_twin", Verified),
            ("c1_pow_cost", FailClosed),
            ("c2_float_div_cost", FailClosed),
        ],
    );
}

/// No `use` of the std trait: `x.add(1u64)` is the file trait's `&mut self`
/// method, which sets `x` to 0. The call does not keep a `mut` receiver, so
/// the read after it fails closed. An inline module does not see the file's
/// import, so the same holds for a file that imports `Add` at its top level
/// but calls `add` in such a module.
const SRC_NO_IMPORT: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]

trait Bump {
    fn add(&mut self, y: u64);
}

impl Bump for u64 {
    fn add(&mut self, y: u64) {
        *self = 0u64;
    }
}

#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(result == 5u64)]
fn m1_mut_trait_method_liar(mut x: u64) -> u64 {
    x.add(1u64);
    x
}
"#;

const SRC_MODULE_WITHOUT_IMPORT: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]

use std::ops::Add;

mod m {
    pub trait Bump {
        fn add(&mut self, y: u64);
    }

    impl Bump for u64 {
        fn add(&mut self, y: u64) {
            *self = 0u64;
        }
    }

    #[trust_vc::requires(x == 5u64)]
    #[trust_vc::ensures(result == 5u64)]
    pub fn m2_module_mut_trait_method_liar(mut x: u64) -> u64 {
        x.add(1u64);
        x
    }
}
"#;

/// An item-position macro invocation makes the file unenumerable: its
/// expansion may declare a type spelled `u64`, so the call does not keep a
/// `mut` receiver there either.
const SRC_UNENUMERABLE: &str = r#"
#![allow(dead_code, unused, unused_mut, unused_must_use)]

use std::ops::Add;

macro_rules! nothing {
    () => {};
}
nothing!();

#[trust_vc::ensures(result == 1u64)]
fn g1_unenumerable_mut_read_after_gated(mut x: u64) -> u64 {
    x = 3u64;
    x.add(1u64);
    if x == 3u64 { 1u64 } else { 0u64 }
}

#[trust_vc::ensures(true)]
fn g2_unenumerable_statement_liar(x: u64) -> u64 {
    x.add(1u64);
    1u64
}
"#;

#[test]
fn a_mut_receiver_is_kept_only_where_the_std_trait_is_imported() {
    check_table(SRC_NO_IMPORT, &[("m1_mut_trait_method_liar", FailClosed)]);
    check_table(
        SRC_MODULE_WITHOUT_IMPORT,
        &[("m2_module_mut_trait_method_liar", FailClosed)],
    );
    check_table(
        SRC_UNENUMERABLE,
        &[
            ("g1_unenumerable_mut_read_after_gated", FailClosed),
            ("g2_unenumerable_statement_liar", Counterexample),
        ],
    );
}
