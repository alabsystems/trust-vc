// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS PIN (compound write on a DECLARED scalar): a compound
//! assignment `x op= rhs` whose target is a declared solver variable was
//! modelled by `invalidate_scoped(x)` inside every loop body. `invalidate_scoped`
//! fails closed only for an UNDECLARED name; a declared one reads back as its
//! BARE symbol — the loop-head value inside a body — so the write was silently
//! dropped for every later read: `while x < 10 { let h = x; x += 1;
//! assert!(x == h); }` over a `mut x` parameter and over a let-local, the same
//! over `loop` + `^=`, `>>=`, a range-`for` accumulator and a `continue` site
//! were `Verified`.
//!
//! Inside a loop body the compound is now the plain-assignment model
//! `x = (x) op (rhs)`; a right-hand side that embeds an assignment havocs a
//! declared target instead. Every stale-read liar is a Counterexample AT ITS
//! ASSERTION; the in-iteration relations and the invariant-lane counters now
//! verify, with refuted liar twins. Outside a loop body a target with no scoped
//! binding (a parameter) is poisoned, so a later read fails closed.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(func: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_cadts_{}_{}.rs", std::process::id(), func));
    std::fs::write(&p, SRC).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

const SRC: &str = r#"
// ---------- loop bodies: a read after the compound sees THIS iteration's write ----------

#[trust_vc::requires(x == 3u64)]
fn while_param_stale_liar(mut x: u64) {
    while x < 10u64 {
        let h = x;
        x += 1u64;
        trust_vc::assert!(x == h);
    }
}

#[trust_vc::ensures(true)]
fn while_letlocal_stale_liar() {
    let mut x = 0u64;
    while x < 10u64 {
        let h = x;
        x += 1u64;
        trust_vc::assert!(x == h);
    }
}

#[trust_vc::ensures(true)]
fn while_letlocal_relation_verifies() {
    let mut x = 0u64;
    while x < 10u64 {
        let h = x;
        x += 1u64;
        trust_vc::assert!(x == h + 1u64);
    }
}

#[trust_vc::ensures(true)]
fn loop_xor_stale_liar(c: bool) {
    let mut x = 0u64;
    loop {
        let h = x;
        x ^= 1u64;
        trust_vc::assert!(x == h);
        if c {
            break;
        }
    }
}

#[trust_vc::ensures(true)]
fn loop_xor_relation_verifies(c: bool) {
    let mut x = 0u64;
    loop {
        let h = x;
        x ^= 1u64;
        trust_vc::assert!(x == h ^ 1u64);
        if c {
            break;
        }
    }
}

// The pre-loop value is the FIRST iteration's head only.
#[trust_vc::ensures(true)]
fn loop_xor_first_iteration_liar(c: bool) {
    let mut x = 0u64;
    loop {
        x ^= 1u64;
        trust_vc::assert!(x == 1u64);
        if c {
            break;
        }
    }
}

#[trust_vc::ensures(true)]
fn for_accumulator_stale_liar(n: u64) {
    let mut acc = 0u64;
    for _k in 0u64..n {
        let h = acc;
        acc |= 1u64;
        acc ^= 3u64;
        trust_vc::assert!(acc == h);
    }
}

#[trust_vc::ensures(true)]
fn loop_shift_stale_liar(c: bool) {
    let mut x = 1u64;
    loop {
        let h = x;
        x >>= 1u64;
        trust_vc::assert!(x == h);
        if c {
            break;
        }
    }
}

#[trust_vc::ensures(true)]
fn continue_site_stale_liar(c: bool) {
    let mut x = 0u64;
    let mut i = 0u64;
    while i < 10u64 {
        let h = x;
        x ^= 1u64;
        i += 1u64;
        if c {
            continue;
        }
        trust_vc::assert!(x == h);
    }
}

// ---------- the invariant lane: the compound is the step's transition ----------

#[trust_vc::ensures(true)]
fn invariant_counter_verifies(n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        i += 1u64;
    }
    trust_vc::assert!(i == n);
}

#[trust_vc::ensures(true)]
fn invariant_counter_post_loop_liar(n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        i += 1u64;
    }
    trust_vc::assert!(i == 0u64);
}

// The counter changes, so an invariant pinning it is not inductive.
#[trust_vc::ensures(true)]
fn invariant_counter_eq_zero_liar(n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i == 0u64);
        i += 1u64;
    }
}

#[trust_vc::requires(x < 10u64)]
fn invariant_param_counter_verifies(mut x: u64) {
    while x < 10u64 {
        trust_vc::invariant!(x <= 10u64);
        x += 1u64;
    }
    trust_vc::assert!(x == 10u64);
}

#[trust_vc::requires(x < 10u64)]
fn invariant_param_counter_liar(mut x: u64) {
    while x < 10u64 {
        trust_vc::invariant!(x <= 10u64);
        x += 1u64;
    }
    trust_vc::assert!(x == 9u64);
}

// ---------- straight line: a parameter target has no scoped binding ----------

#[trust_vc::requires(x < 100u64)]
fn param_straight_line_stale_liar(mut x: u64) {
    let h = x;
    x += 1u64;
    trust_vc::assert!(x == h);
}

#[trust_vc::requires(x < 100u64)]
fn param_straight_line_relation_verifies(mut x: u64) {
    let h = x;
    x += 1u64;
    trust_vc::assert!(x == h + 1u64);
}

// A right-hand side that embeds an assignment keeps the read-then-rebind off:
// the declared target is havoc'd, never left at its entry value.
#[trust_vc::requires(x < 100u64)]
fn param_rhs_side_effect_stale_liar(mut x: u64) {
    let mut y = 0u64;
    let h = x;
    x += {
        y = 5u64;
        y
    };
    trust_vc::assert!(x == h);
}
"#;

fn assert_verified(func: &str) {
    let r = verify(func);
    assert!(r.is_verified(), "{func} must verify, got: {r:?}");
}

/// A Counterexample on a user `assert!` — the stale read itself is refuted,
/// not an arithmetic side check of the same function.
fn assert_assertion_counterexample(func: &str) {
    let r = verify(func);
    let VerifyResult::Counterexample {
        obligation_name, ..
    } = &r
    else {
        panic!("{func} must be a Counterexample (never Verified), got: {r:?}");
    };
    assert!(
        obligation_name.starts_with("assertion"),
        "{func} must be refuted at its assertion, got obligation `{obligation_name}`"
    );
}

fn assert_counterexample(func: &str) {
    let r = verify(func);
    assert!(
        r.is_counterexample(),
        "{func} must be a Counterexample (never Verified), got: {r:?}"
    );
}

#[test]
fn loop_body_reads_see_the_compound_write() {
    assert_assertion_counterexample("while_param_stale_liar");
    assert_assertion_counterexample("while_letlocal_stale_liar");
    assert_assertion_counterexample("loop_xor_stale_liar");
    assert_assertion_counterexample("for_accumulator_stale_liar");
    assert_assertion_counterexample("loop_shift_stale_liar");
    assert_assertion_counterexample("continue_site_stale_liar");
    assert_assertion_counterexample("loop_xor_first_iteration_liar");
}

#[test]
fn loop_body_relations_verify() {
    assert_verified("while_letlocal_relation_verifies");
    assert_verified("loop_xor_relation_verifies");
}

#[test]
fn invariant_lane_counters_both_directions() {
    assert_verified("invariant_counter_verifies");
    assert_assertion_counterexample("invariant_counter_post_loop_liar");
    assert_counterexample("invariant_counter_eq_zero_liar");
    assert_verified("invariant_param_counter_verifies");
    assert_assertion_counterexample("invariant_param_counter_liar");
}

#[test]
fn straight_line_parameter_target_never_reads_its_entry_value() {
    // Outside a loop body a compound write to a target with no scoped binding
    // poisons it, so a later read fails closed (an error, never `Verified`).
    for func in [
        "param_straight_line_stale_liar",
        "param_straight_line_relation_verifies",
        "param_rhs_side_effect_stale_liar",
    ] {
        let r = verify(func);
        assert!(!r.is_verified(), "{func} must not verify, got: {r:?}");
    }
}
