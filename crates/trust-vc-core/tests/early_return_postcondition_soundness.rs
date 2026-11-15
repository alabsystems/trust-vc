// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS PIN (upstream control_flow.rs `postconditions_fail_in_returns_in_conditional`
//! shape): a function's postcondition must hold at EVERY exit, and
//! an explicit `return` exits with only the facts established before it.
//!
//! The postcondition used to be checked once, at function exit, against every
//! body fact — including facts established AFTER an early `return` on the
//! fall-through path (a later `assume!`, a later call's `ensures`, a later
//! loop's exit fact, the unreachability after `loop {}`). Each such fact was
//! then used to excuse the early-return path, which never saw it: all the
//! `*_early_return_escapes_*` functions below came back `Verified` although an
//! input exists that takes the early return and violates the postcondition.
//!
//! Every exit is now checked where it happens, with only the facts established
//! before it; a `return` in dead code (after a statement-level `return`) or in
//! the diverge arm of an irrefutable `let`-`else` is not an exit. The `*_holds`
//! controls keep the same shapes with a postcondition that is genuinely
//! established on every path, and must still verify.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static NEXT_FIXTURE: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(func: &str) -> Result<VerifyResult, String> {
    let serial = NEXT_FIXTURE.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut p = std::env::temp_dir();
    p.push(format!(
        "tvc_erps_{}_{serial}_{func}.rs",
        std::process::id()
    ));
    std::fs::write(&p, SRC).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&p);
    result
}

fn assert_verified(func: &str) {
    match verify(func) {
        Ok(VerifyResult::Verified) => {}
        other => panic!("{func} should verify, got: {other:?}"),
    }
}

fn assert_refuted(func: &str) {
    match verify(func) {
        Ok(VerifyResult::Counterexample { .. }) => {}
        other => panic!("{func} should be refuted with a counterexample, got: {other:?}"),
    }
}

const SRC: &str = r#"
// ---- a later assume! ------------------------------------------------------

#[trust_vc::requires(x < 10u64)]
#[trust_vc::ensures(x < 5u64)]
fn unit_early_return_escapes_later_assume(x: u64) {
    if x > 7u64 {
        return;
    }
    trust_vc::assume!(x < 5u64);
}

#[trust_vc::requires(x < 5u64)]
#[trust_vc::ensures(x < 5u64)]
fn unit_early_return_later_assume_holds(x: u64) {
    if x > 7u64 {
        return;
    }
    trust_vc::assume!(x < 5u64);
}

#[trust_vc::requires(x < 10u64)]
#[trust_vc::ensures(result < 5u64)]
fn value_early_return_escapes_later_assume(x: u64) -> u64 {
    if x > 7u64 {
        return x;
    }
    trust_vc::assume!(x < 5u64);
    x
}

#[trust_vc::requires(x < 10u64)]
#[trust_vc::ensures(result < 5u64)]
fn value_early_return_later_assume_holds(x: u64) -> u64 {
    if x > 7u64 {
        return 1u64;
    }
    trust_vc::assume!(x < 5u64);
    x
}

#[trust_vc::requires(x < 10u64)]
#[trust_vc::ensures(x < 5u64)]
fn match_arm_early_return_escapes_later_assume(x: u64) {
    match x > 7u64 {
        true => {
            return;
        }
        false => {}
    }
    trust_vc::assume!(x < 5u64);
}

// ---- a later call's ensures -------------------------------------------------

#[trust_vc::ensures(x < 5u64)]
fn lemma_small(x: u64) {
    trust_vc::assume!(x < 5u64);
}

#[trust_vc::requires(x < 10u64)]
#[trust_vc::ensures(x < 5u64)]
fn unit_early_return_escapes_later_call_ensures(x: u64) {
    if x > 7u64 {
        return;
    }
    lemma_small(x);
}

// ---- a later loop's facts ---------------------------------------------------

#[trust_vc::ensures(false)]
fn unit_early_return_escapes_later_infinite_loop(b: bool) {
    if b {
        return;
    }
    loop {}
}

#[trust_vc::ensures(!b)]
fn unit_early_return_later_infinite_loop_holds(b: bool) {
    if !b {
        return;
    }
    loop {}
}

#[trust_vc::requires(x < 10u64)]
#[trust_vc::ensures(x <= 7u64)]
fn return_inside_loop_escapes_loop_exit_fact(x: u64) {
    while x > 7u64 {
        trust_vc::invariant!(x < 10u64);
        return;
    }
}

#[trust_vc::requires(x < 10u64)]
#[trust_vc::ensures(x < 10u64)]
fn return_inside_loop_holds(x: u64) {
    while x > 7u64 {
        trust_vc::invariant!(x < 10u64);
        return;
    }
}

// ---- dead code after a statement-level return ----------------------------------

#[trust_vc::requires(x < 10u64)]
#[trust_vc::ensures(x < 5u64)]
fn top_level_return_escapes_dead_assume(x: u64) {
    return;
    trust_vc::assume!(x < 5u64);
}

// ---- a let-else diverge arm -----------------------------------------------------

enum Opt {
    Some(u64),
    None,
}

#[trust_vc::ensures(o.is_Some())]
fn let_else_return_escapes_later_assume(o: Opt) {
    let Opt::Some(v) = o else {
        return;
    };
    trust_vc::assume!(o.is_Some());
}

#[trust_vc::ensures(o.is_None() || o.get_Some_0() > 0u64)]
fn let_else_return_guarded_holds(o: Opt) {
    let Opt::Some(v) = o else {
        return;
    };
    trust_vc::assume!(v > 0u64);
}

// ---- the returned value is checked where it is returned ----------------------

#[trust_vc::ensures(result == 1u64 || result == 2u64)]
fn tail_if_return_holds(flag: bool) -> u64 {
    if flag {
        return 1u64;
    } else {
        2u64
    }
}

#[trust_vc::ensures(result == 2u64)]
fn tail_if_return_wrong_value(flag: bool) -> u64 {
    if flag {
        return 1u64;
    } else {
        2u64
    }
}

"#;

#[test]
fn facts_after_an_early_return_do_not_excuse_it() {
    assert_refuted("unit_early_return_escapes_later_assume");
    assert_refuted("value_early_return_escapes_later_assume");
    assert_refuted("match_arm_early_return_escapes_later_assume");
    assert_refuted("unit_early_return_escapes_later_call_ensures");
    assert_refuted("unit_early_return_escapes_later_infinite_loop");
    assert_refuted("return_inside_loop_escapes_loop_exit_fact");
    assert_refuted("top_level_return_escapes_dead_assume");
    assert_refuted("let_else_return_escapes_later_assume");
}

#[test]
fn postconditions_established_on_every_exit_still_verify() {
    assert_verified("unit_early_return_later_assume_holds");
    assert_verified("value_early_return_later_assume_holds");
    assert_verified("unit_early_return_later_infinite_loop_holds");
    assert_verified("return_inside_loop_holds");
    assert_verified("tail_if_return_holds");
    assert_verified("let_else_return_guarded_holds");
    assert_refuted("tail_if_return_wrong_value");
}

/// Prints every fixture function's verdict (run with `--nocapture`); asserts nothing.
#[test]
fn dump_verdicts() {
    let file = syn::parse_file(SRC).expect("fixture parses");
    for item in &file.items {
        if let syn::Item::Fn(function) = item {
            let name = function.sig.ident.to_string();
            let verdict = match verify(&name) {
                Ok(VerifyResult::Verified) => "Verified".to_string(),
                Ok(VerifyResult::Counterexample {
                    obligation_name, ..
                }) => format!("Counterexample at {obligation_name}"),
                Ok(other) => format!("{other:?}").chars().take(240).collect(),
                Err(err) => format!("Err: {err}").chars().take(240).collect(),
            };
            println!("VERDICT {name}: {verdict}");
        }
    }
}
