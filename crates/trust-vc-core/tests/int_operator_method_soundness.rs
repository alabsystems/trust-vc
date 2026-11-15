// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Operator assignment methods on a primitive integer binding.
//!
//! Two rules, both keyed on `CollectorLaneSeed::single_typed_int_bindings`
//! (names the function binds exactly once, to a primitive integer type):
//!
//! 1. In the value lane (a block rendered as a value: a `let` initializer, an
//!    `if` condition, a returned block), a method statement on such a name
//!    (`x.add_assign(1u64);`) is framed by poison even when the modified-set
//!    collector records it (`value_lane_frames_int_receiver_write`). The
//!    collector records it only after a rebinding put `x` in a scope frame
//!    (its untyped-receiver seed); the same statement on a parameter never
//!    rebound, or on a typed scalar `let`, was already framed. A later read
//!    of `x` in the value computation fails closed, and a container whose
//!    value never reads the write keeps its value. Before this, the whole
//!    container was refused.
//! 2. `x.add_assign(e)` and the other std operator assignment methods on such
//!    a name carry the panic obligation `x OP= e` carries
//!    (`AssertionCollector::emit_int_operator_assign_method_safety`). Before
//!    this, the method spelling was never checked for overflow, division by
//!    zero or shift bounds anywhere.
//!
//! Rule 2 is what makes rule 1 safe: rule 1 lets a value-position container
//! whose write is unread keep its value, and without rule 2 the write's own
//! overflow would then go unchecked (`r_if_cond_unread_overflow_liar`).
//! Outside the value lane nothing changes: a loop frame, a join and a
//! closure exit treat these receivers as before.
//!
//! Each control below is a true program that must verify. Each liar changes
//! it so the claim is false and must not verify. Each test's doc comment says
//! what its liars returned, measured, with one rule switched off.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_int_operator_method_{}_{}_{seq}.rs",
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

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// A true program: must verify.
    Verified,
    /// A false claim refuted with a counterexample whose obligation name
    /// contains the fragment.
    Refuted(&'static str),
    /// A false claim the extractor refuses (an extraction or lowering error).
    FailClosed,
    /// A read of a poisoned binding: a lowering error naming the variable.
    Poisoned(&'static str),
    /// Refuted, on whichever obligation.
    Counterexample,
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

const POISON_NOTE: &str = "vc_extraction does not track is unknown, so this read fails closed";

fn matches_expect(r: &Result<VerifyResult, String>, expect: Expect) -> bool {
    match expect {
        Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
        Expect::Refuted(fragment) => matches!(
            r,
            Ok(VerifyResult::Counterexample { obligation_name, .. })
                if obligation_name.contains(fragment)
        ),
        Expect::FailClosed => matches!(r, Ok(VerifyResult::Error { .. }) | Err(_)),
        Expect::Counterexample => matches!(r, Ok(VerifyResult::Counterexample { .. })),
        Expect::Poisoned(var) => matches!(
            r,
            Ok(VerifyResult::Error { message })
                if message.contains(&format!("unresolved variable `{var}`"))
                    && message.contains(POISON_NOTE)
        ),
    }
}

fn check_table(table: &[(&str, Expect)]) {
    let mut failures = Vec::new();
    for (func, expect) in table {
        let r = verify(func);
        let ok = matches_expect(&r, *expect);
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

const SRC: &str = r#"
#![allow(dead_code, unused, unused_mut)]
use std::ops::{AddAssign, DivAssign, MulAssign, RemAssign, ShlAssign, ShrAssign, SubAssign};

// ---- rule 2: the method's own panic -----------------------------------------

// LIAR: panics at x = u64::MAX.
#[trust_vc::ensures(true)]
fn o_add_liar(mut x: u64) {
    x.add_assign(1u64);
}

// CONTROL: bounded.
#[trust_vc::requires(x < 10u64)]
#[trust_vc::ensures(true)]
fn o_add_ctrl(mut x: u64) {
    x.add_assign(1u64);
}

// LIAR: panics at x = 0.
#[trust_vc::ensures(true)]
fn o_sub_liar(mut x: u64) {
    x.sub_assign(1u64);
}

// CONTROL: bounded below.
#[trust_vc::requires(x > 0u64)]
#[trust_vc::ensures(true)]
fn o_sub_ctrl(mut x: u64) {
    x.sub_assign(1u64);
}

// LIAR: panics at x = u64::MAX.
#[trust_vc::ensures(true)]
fn o_mul_liar(mut x: u64) {
    x.mul_assign(2u64);
}

// LIAR: panics at d = 0.
#[trust_vc::ensures(true)]
fn o_div_liar(mut x: u64, d: u64) {
    x.div_assign(d);
}

// CONTROL: nonzero divisor.
#[trust_vc::requires(d > 0u64)]
#[trust_vc::ensures(true)]
fn o_div_ctrl(mut x: u64, d: u64) {
    x.div_assign(d);
}

// LIAR: panics at d = 0.
#[trust_vc::ensures(true)]
fn o_rem_liar(mut x: u64, d: u64) {
    x.rem_assign(d);
}

// LIAR: panics at s = 64.
#[trust_vc::ensures(true)]
fn o_shl_liar(mut x: u64, s: u32) {
    x.shl_assign(s);
}

// CONTROL: in-range shift.
#[trust_vc::requires(s < 64u32)]
#[trust_vc::ensures(true)]
fn o_shl_ctrl(mut x: u64, s: u32) {
    x.shl_assign(s);
}

// LIAR: panics at s = 64.
#[trust_vc::ensures(true)]
fn o_shr_liar(mut x: u64, s: u32) {
    x.shr_assign(s);
}

// LIAR: a typed local bound once, panics at y = u64::MAX.
#[trust_vc::ensures(true)]
fn o_local_liar(y: u64) {
    let mut x: u64 = y;
    x.add_assign(1u64);
}

// LIAR: signed, panics at x = i8::MIN.
#[trust_vc::ensures(true)]
fn o_i8_liar(mut x: i8) {
    x.sub_assign(1i8);
}

// GATED (runtime-true): the second call's receiver is already poisoned, so
// its obligation cannot be rendered and the function fails closed.
#[trust_vc::requires(x < 10u64)]
#[trust_vc::ensures(true)]
fn o_twice_gated(mut x: u64) {
    x.add_assign(1u64);
    x.add_assign(1u64);
}

// ---- rule 1: a rebound integer receiver is framed by poison ----------------

// CONTROL: the condition's write is never read.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn r_if_cond_unread_ctrl(mut x: u64, b: bool) {
    let v: u64 = if ({
        x.add_assign(1u64);
        b
    }) {
        5u64
    } else {
        7u64
    };
    trust_vc::assert!(v >= 5u64);
}

// CONTROL: the same after an explicit rebinding of the parameter.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn r_rebound_if_cond_unread_ctrl(mut x: u64, b: bool) {
    x = 0u64;
    let v: u64 = if ({
        x.add_assign(1u64);
        b
    }) {
        5u64
    } else {
        7u64
    };
    trust_vc::assert!(v >= 5u64);
}

// LIAR: the branch reads the write (v = 1).
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn r_rebound_if_cond_read_liar(mut x: u64) {
    x = 0u64;
    let v: u64 = if ({
        x.add_assign(1u64);
        true
    }) {
        x
    } else {
        0u64
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR: the unread write overflows at x = u64::MAX.
#[trust_vc::ensures(true)]
fn r_if_cond_unread_overflow_liar(mut x: u64, b: bool) {
    let v: u64 = if ({
        x.add_assign(1u64);
        b
    }) {
        5u64
    } else {
        7u64
    };
    trust_vc::assert!(v >= 5u64);
}

// LIAR: a value block's tail reads the write (v = 1).
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn r_rebound_value_block_liar(mut x: u64) {
    x = 0u64;
    let v: u64 = {
        x.add_assign(1u64);
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR: the returned block's tail reads the write (result = 1).
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(result == 0u64)]
fn r_rebound_return_block_liar(mut x: u64) -> u64 {
    x = 0u64;
    {
        x.add_assign(1u64);
        x
    }
}

// LIAR: a branch write, read after the join (b = true).
#[trust_vc::requires(x == 0u64 && b)]
#[trust_vc::ensures(true)]
fn r_rebound_if_liar(mut x: u64, b: bool) {
    x = 0u64;
    if b {
        x.add_assign(1u64);
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR: a plain block write, read after the block.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn r_rebound_block_liar(mut x: u64) {
    x = 0u64;
    {
        x.add_assign(1u64);
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR: a match arm write, read after the match (b = true).
#[trust_vc::requires(x == 0u64 && b)]
#[trust_vc::ensures(true)]
fn r_rebound_match_liar(mut x: u64, b: bool) {
    x = 0u64;
    match b {
        true => {
            x.add_assign(1u64);
        }
        false => {}
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR: a called closure writes the capture.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn r_rebound_closure_liar(mut x: u64) {
    x = 0u64;
    let mut f = || x.add_assign(1u64);
    f();
    trust_vc::assert!(x == 0u64);
}

// LIAR: a loop body writes the receiver (n = 1).
#[trust_vc::requires(x == 0u64 && n == 1u64)]
#[trust_vc::ensures(true)]
fn r_rebound_loop_liar(mut x: u64, n: u64) {
    x = 0u64;
    let mut i: u64 = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        x.add_assign(1u64);
        i = i + 1u64;
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR: a closure called in a loop body writes the capture (n = 1).
#[trust_vc::requires(x == 0u64 && n == 1u64)]
#[trust_vc::ensures(true)]
fn r_rebound_closure_in_loop_liar(mut x: u64, n: u64) {
    x = 0u64;
    let mut i: u64 = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let mut f = || x.add_assign(1u64);
        f();
        i = i + 1u64;
    }
    trust_vc::assert!(x == 0u64);
}
"#;

use Expect::{Counterexample, FailClosed, Poisoned, Refuted, Verified};

/// Rule 2. Discriminator: with the obligation switched off every liar here is
/// `Verified`; the method spelling was checked nowhere. `o_twice_gated` is the
/// recorded cost: `Verified` before, because neither call was checked.
#[test]
fn operator_assign_method_panics_are_checked() {
    check_table(&[
        ("o_add_liar", Refuted("addition overflow")),
        ("o_add_ctrl", Verified),
        ("o_sub_liar", Refuted("subtraction overflow")),
        ("o_sub_ctrl", Verified),
        ("o_mul_liar", Refuted("multiplication overflow")),
        ("o_div_liar", Refuted("division by zero")),
        ("o_div_ctrl", Verified),
        ("o_rem_liar", Refuted("division by zero")),
        ("o_shl_liar", Refuted("left shift overflow")),
        ("o_shl_ctrl", Verified),
        ("o_shr_liar", Refuted("right shift overflow")),
        ("o_local_liar", Refuted("addition overflow")),
        ("o_i8_liar", Refuted("subtraction overflow")),
        ("o_twice_gated", FailClosed),
    ]);
}

/// Rule 1. Discriminator: with it switched off both controls are refused
/// (the value lane declines the condition block, and the raw fallback refuses
/// it for dropping the write); the value-lane liars are refused the same way
/// rather than poisoned, so they still do not verify. With rule 1 on and rule
/// 2 off, `r_if_cond_unread_overflow_liar` is `Verified`. The liars outside
/// the value lane pin that nothing else moved: the closure exit havocs the
/// capture (refuted at the assertion), and the loop frame havocs the receiver
/// (refuted).
#[test]
fn rebound_int_receiver_is_framed_by_poison() {
    check_table(&[
        ("r_if_cond_unread_ctrl", Verified),
        ("r_rebound_if_cond_unread_ctrl", Verified),
        ("r_rebound_if_cond_read_liar", Poisoned("x")),
        (
            "r_if_cond_unread_overflow_liar",
            Refuted("addition overflow"),
        ),
        ("r_rebound_value_block_liar", Poisoned("x")),
        ("r_rebound_return_block_liar", Poisoned("x")),
        ("r_rebound_if_liar", Poisoned("x")),
        ("r_rebound_block_liar", Poisoned("x")),
        ("r_rebound_match_liar", Poisoned("x")),
        ("r_rebound_closure_liar", Refuted("assertion_")),
        ("r_rebound_loop_liar", Counterexample),
        ("r_rebound_closure_in_loop_liar", FailClosed),
    ]);
}
