// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness regression (BOTH directions) for arithmetic-safety obligations in
//! SPEC-closure comprehension bodies vs genuine EXEC fixed-width arithmetic.
//!
//! # The bug
//!
//! `Seq`/`Set`/`Map` `map`/`filter`/`fold` apply their `SpecFn` closure to a
//! universally-bound element/index that ranges over the whole (unbounded)
//! domain. In Verus these closures are SPEC mode: arithmetic on them is
//! mathematical `int`/`nat` and is **never** overflow-checked. trust-vc was
//! collecting a per-operation bit-vector overflow obligation for the closure
//! body (e.g. `2 * i` where `i: usize`), which the solver then refuted on the
//! *unconstrained* bound variable (`2 * usize::MAX` overflows). The result was a
//! **false counterexample** on a perfectly valid spec proof — fired even when
//! the surrounding goal (`s.map(f).len() == s.len()`) is trivially true and the
//! closure is never evaluated on a real element (the cex model is an empty
//! sequence). Reproduced from the upstream Verus `seqs.rs` scout case
//! `s.map(|i: int, a: int| 2 * i + a)`.
//!
//! # The fix
//!
//! `with_closure_body_bindings` temporarily drops only the arithmetic-safety
//! *behaviors* (overflow → `Truncate`, div0/shift → `Allow`) around the closure
//! body, so the spec-closure body carries no fixed-width overflow / div0 / shift
//! obligation while its encoded *value* (BV wrap / int clip) is unchanged.
//!
//! # Soundness in BOTH directions
//!
//! (i)  SPEC int/nat (and fixed-width-typed operands inside a spec closure):
//!      `2 * i + a`, `i * i`, `a + b + c`, guarded `nat` subtraction, and the
//!      seqs map/filter cases VERIFY with **no false overflow counterexample**.
//! (ii) EXEC fixed-width arithmetic STILL emits overflow obligations: a
//!      genuinely-overflowing `u8`/`u32`/`i32` op is a Counterexample, and a
//!      bounded op verifies. Stripping these would be a catastrophic false
//!      Verified — the tests below pin that they are preserved exactly.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify_src(tag: &str, src: &str, func: &str) -> VerifyResult {
    let path = std::env::temp_dir().join(format!("trust_vc_spec_overflow_{tag}.rs"));
    let mut f = std::fs::File::create(&path).expect("create temp source");
    f.write_all(src.as_bytes()).expect("write temp source");
    verify_function_from_file(path.to_str().unwrap(), func)
        .unwrap_or_else(|e| panic!("{tag}: extract/verify failed: {e}"))
}

fn assert_verified(tag: &str, src: &str, func: &str) {
    match verify_src(tag, src, func) {
        VerifyResult::Verified => {}
        other => {
            panic!("{tag}: SPEC arithmetic must verify with no false overflow cex, got: {other:?}")
        }
    }
}

fn assert_counterexample(tag: &str, src: &str, func: &str) {
    match verify_src(tag, src, func) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!(
            "{tag}: genuine EXEC overflow MUST stay a Counterexample (never false Verified), \
             got: {other:?}"
        ),
    }
}

// =====================================================================
// (i) SPEC direction — no false overflow counterexample
// =====================================================================

/// The seqs scout case: `Seq::map` closure body `2 * i + a` on a `usize` index
/// and `usize` element. Before the fix this was a false "possible multiplication
/// overflow" counterexample (model: empty seq); now it verifies.
#[test]
fn seq_map_usize_index_mul_no_false_overflow() {
    let src = r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(
        Seq::<usize>::empty()
            .push(10usize)
            .push(20usize)
            .push(30usize)
            .map(SpecFn::new(|(i, a): (usize, usize)| 2usize * i + a))
            .len()
            == 3usize
    );
}
"#;
    assert_verified("seq_map_usize_index_mul", src, "test1");
}

/// `Seq::map` over a *symbolic* `Seq<i32>` with an `i32` arithmetic body
/// (`2 * a + a`). The element `a` is unbounded-symbolic, so an exec-style check
/// would refute; in the spec closure it must verify (the goal is a length fact).
#[test]
fn seq_map_i32_mul_symbolic_seq_no_false_overflow() {
    let src = r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1(s: Seq<i32>) {
    trust_vc::assert!(s.map(SpecFn::new(|(i, a): (usize, i32)| 2i32 * a + a)).len() == s.len());
}
"#;
    assert_verified("seq_map_i32_mul_symbolic", src, "test1");
}

/// `Seq::filter` predicate body containing arithmetic (`2 * x > x`) must not
/// emit an overflow obligation on the unconstrained filtered element.
#[test]
fn seq_filter_arith_predicate_no_false_overflow() {
    let src = r#"
use trust_vc_types::{Seq, SpecFn};
#[trust_vc::ensures(true)]
fn test1(s: Seq<i32>) {
    trust_vc::assert!(s.filter(SpecFn::new(|x: i32| 2i32 * x > x)).len() <= s.len());
}
"#;
    assert_verified("seq_filter_arith_predicate", src, "test1");
}

/// Plain SPEC `int` arithmetic: `i * i + a + b + c`. Mathematical, unbounded,
/// never overflow-checked.
#[test]
fn spec_int_polynomial_no_overflow() {
    let src = r#"
use trust_vc_types::int;
#[trust_vc::ensures(result == i * i + a + b + c)]
fn f(i: int, a: int, b: int, c: int) -> int {
    i * i + a + b + c
}
"#;
    assert_verified("spec_int_polynomial", src, "f");
}

/// SPEC `int` arithmetic inside an `assert!` carried by an exec function:
/// `2 * i + a` must not acquire an overflow obligation.
#[test]
fn spec_int_assert_commutes_no_overflow() {
    let src = r#"
use trust_vc_types::int;
#[trust_vc::ensures(true)]
fn g(i: int, a: int) {
    trust_vc::assert!(2 * i + a == a + 2 * i);
}
"#;
    assert_verified("spec_int_assert_commutes", src, "g");
}

/// Guarded `nat` subtraction (`a - b` with `a >= b`) verifies under nat
/// semantics with no spurious underflow obligation.
#[test]
fn spec_nat_subtraction_guarded_no_underflow() {
    let src = r#"
use trust_vc_types::nat;
#[trust_vc::requires(a >= b)]
#[trust_vc::ensures(result + b == a)]
fn f(a: nat, b: nat) -> nat {
    a - b
}
"#;
    assert_verified("spec_nat_subtraction_guarded", src, "f");
}

// =====================================================================
// (ii) EXEC direction — genuine overflow STILL caught (no false Verified)
// =====================================================================

/// Unconstrained `u32` multiplication overflows; must stay a Counterexample.
#[test]
fn exec_u32_mul_unbounded_is_counterexample() {
    let src = r#"
#[trust_vc::ensures(true)]
fn h(x: u32, y: u32) {
    let z = x * y;
}
"#;
    assert_counterexample("exec_u32_mul_unbounded", src, "h");
}

/// Unconstrained `u8` addition overflows; must stay a Counterexample.
#[test]
fn exec_u8_add_unbounded_is_counterexample() {
    let src = r#"
#[trust_vc::ensures(true)]
fn h(x: u8, y: u8) {
    let z = x + y;
}
"#;
    assert_counterexample("exec_u8_add_unbounded", src, "h");
}

/// All-constant `200u8 + 100u8` overflows `u8`; constant-folded Counterexample.
#[test]
fn exec_u8_const_addition_overflow_is_counterexample() {
    let src = r#"
#[trust_vc::ensures(true)]
fn h() {
    let z = 200u8 + 100u8;
}
"#;
    assert_counterexample("exec_u8_const_addition", src, "h");
}

/// `i32` addition overflows at `i32::MAX`; must stay a Counterexample.
#[test]
fn exec_i32_add_one_is_counterexample() {
    let src = r#"
#[trust_vc::ensures(true)]
fn h(x: i32) {
    let z = x + 1i32;
}
"#;
    assert_counterexample("exec_i32_add_one", src, "h");
}

/// Bounded EXEC multiplication (`x < 10, y < 10`) cannot overflow `u32`; the
/// auto-emitted obligation is discharged and the body verifies. Pins that the
/// fix does NOT blanket-suppress exec checks — only spec-closure ones.
#[test]
fn exec_u32_mul_bounded_verifies() {
    let src = r#"
#[trust_vc::requires(x < 10u32)]
#[trust_vc::requires(y < 10u32)]
#[trust_vc::ensures(true)]
fn h(x: u32, y: u32) {
    let z = x * y;
}
"#;
    assert_verified("exec_u32_mul_bounded", src, "h");
}
