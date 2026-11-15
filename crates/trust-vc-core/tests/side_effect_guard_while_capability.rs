// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (audit row 430 — upstream `complex_while`, 2026-09-11): a
//! `while` whose guard is a BLOCK with flat scalar side effects
//! (`while { x = x + 1; i < 10 } { … }`) is rotated at the source level into
//! `S; while c { INV over snapshots; injected transition; B; snapshot; S }`
//! (`while_guard_desugar.rs`). The user's invariants hold at the ORIGINAL head
//! (before the guard block runs); the exit state is a head state transformed
//! by the guard block with the condition false. The liars pin that the
//! invariants are NOT assumed over the exit state and that the exit value is
//! exactly the guard block's last evaluation.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_segw_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
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
// CONTROL (the loops_no_spinoff scout shape of upstream complex_while): the
// guard block runs once more than the body, so `x == i + 1` at exit.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
pub fn complex_while_exit_values(mut i: u64, mut x: u64) {
    while {
        x = x + 1u64;
        i < 10u64
    } {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::invariant!(x == i);
        i = i + 1u64;
    }
    trust_vc::assert!(i == 10u64);
    trust_vc::assert!(x == 11u64);
}

// CONTROL (upstream complex_while, let-local shape): `i` from 10 to 20.
#[trust_vc::ensures(true)]
pub fn complex_while_upstream_shape() {
    let mut i: u64 = 10;
    let mut x: u64 = 0;
    while {
        x = x + 1u64;
        i < 20u64
    } {
        trust_vc::invariant!(10u64 <= i);
        trust_vc::invariant!(i <= 20u64);
        trust_vc::invariant!(x == i - 10u64);
        i = i + 1u64;
    }
    trust_vc::assert!(i == 20u64);
    trust_vc::assert!(x == 11u64);
}

// LIAR (upstream complex_while_fail1 shape): the guard block ran 11 times.
#[trust_vc::ensures(true)]
pub fn complex_while_wrong_exit_value() {
    let mut i: u64 = 10;
    let mut x: u64 = 0;
    while {
        x = x + 1u64;
        i < 20u64
    } {
        trust_vc::invariant!(10u64 <= i);
        trust_vc::invariant!(i <= 20u64);
        trust_vc::invariant!(x == i - 10u64);
        i = i + 1u64;
    }
    trust_vc::assert!(x == 10u64);
}

// LIAR: the head invariant `x == i` is NOT an exit fact — the guard block runs
// before the exit (`x == 11`, `i == 10`).
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
pub fn head_invariant_is_not_an_exit_fact(mut i: u64, mut x: u64) {
    while {
        x = x + 1u64;
        i < 10u64
    } {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::invariant!(x == i);
        i = i + 1u64;
    }
    trust_vc::assert!(x == i);
}

// LIAR: an invariant false at the original head (base case) is refuted.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
pub fn invariant_false_at_entry(mut i: u64, mut x: u64) {
    while {
        x = x + 1u64;
        i < 10u64
    } {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::invariant!(x == i + 1u64);
        i = i + 1u64;
    }
}

// CONTROL: the condition reads the var the guard block modifies, and the
// assignment is compound.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn guard_block_modifies_the_tested_var(mut i: u64) {
    while {
        i += 1u64;
        i < 10u64
    } {
        trust_vc::invariant!(i <= 9u64);
    }
    trust_vc::assert!(i == 10u64);
}

// LIAR: … and the exit value is 10, not 9.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn guard_block_modifies_the_tested_var_liar(mut i: u64) {
    while {
        i += 1u64;
        i < 10u64
    } {
        trust_vc::invariant!(i <= 9u64);
    }
    trust_vc::assert!(i == 9u64);
}

// CONTROL: a `break` skips the guard block exactly as in the source, and the
// head invariants still hold at the break site, so `x == i + 1` at every exit.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
pub fn break_skips_the_guard_block(mut i: u64, mut x: u64) {
    while {
        x = x + 1u64;
        i < 10u64
    } {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::invariant!(x == i);
        if i == 5u64 {
            break;
        }
        i = i + 1u64;
    }
    trust_vc::assert!(x == i + 1u64);
}

// LIAR: the break leaves at `i == 5`, so `i == 10` is not an exit fact.
#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
pub fn break_skips_the_guard_block_liar(mut i: u64, mut x: u64) {
    while {
        x = x + 1u64;
        i < 10u64
    } {
        trust_vc::invariant!(i <= 10u64);
        trust_vc::invariant!(x == i);
        if i == 5u64 {
            break;
        }
        i = i + 1u64;
    }
    trust_vc::assert!(i == 10u64);
}
"#;

fn expect_verified(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

fn expect_counterexample(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("{func}: expected Counterexample, got {other:?}"),
    }
}

#[test]
fn control_complex_while_exit_values_verifies() {
    expect_verified("c1", "complex_while_exit_values");
}

#[test]
fn control_complex_while_upstream_shape_verifies() {
    expect_verified("c2", "complex_while_upstream_shape");
}

#[test]
fn liar_complex_while_wrong_exit_value_is_rejected() {
    expect_counterexample("l1", "complex_while_wrong_exit_value");
}

#[test]
fn liar_head_invariant_is_not_an_exit_fact() {
    expect_counterexample("l2", "head_invariant_is_not_an_exit_fact");
}

#[test]
fn liar_invariant_false_at_entry_is_rejected() {
    expect_counterexample("l3", "invariant_false_at_entry");
}

#[test]
fn control_guard_block_modifies_the_tested_var_verifies() {
    expect_verified("c3", "guard_block_modifies_the_tested_var");
}

#[test]
fn liar_guard_block_modifies_the_tested_var_is_rejected() {
    expect_counterexample("l4", "guard_block_modifies_the_tested_var_liar");
}

#[test]
fn control_break_skips_the_guard_block_verifies() {
    expect_verified("c4", "break_skips_the_guard_block");
}

#[test]
fn liar_break_skips_the_guard_block_is_rejected() {
    expect_counterexample("l5", "break_skips_the_guard_block_liar");
}
