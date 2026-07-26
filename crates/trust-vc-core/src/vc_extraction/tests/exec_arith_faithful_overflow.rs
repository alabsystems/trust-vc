// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Faithful (surrogate-free) re-port of the exec-arithmetic overflow cluster
//! from upstream Verus `source/rust_verify_test/tests/overflow.rs` (#2778).
//!
//! These regressions pin the property that makes the literal upstream bodies
//! portable *without* an `assert!(b > a)` surrogate: the engine auto-emits an
//! arithmetic-safety obligation at every discarded-result exec arithmetic site
//! (`body_extract::maybe_emit_exec_arith_overflow_check`, gated on
//! `with_mode_overflow` for `Exec` functions). A bare `let b = a + 1;` or
//! `j = j + 2;` therefore carries the same no-overflow obligation Verus checks,
//! so the unguarded upstream `// FAILS` bodies are Counterexamples and the
//! guarded/bounded bodies Verify — with no surrogate assertion to carry them.
//!
//! Covered upstream cases (scalar `+`/`-`/`/`/`%`, which `rhs_is_checked_scalar_arithmetic`
//! routes through the auto-emitted check):
//! * `test_overflow_fails_1`           — unguarded `j = j + 2`            ⇒ Counterexample
//! * `test_overflow_fails_2`           — unguarded `j = j + 2`            ⇒ Counterexample
//! * `test_overflow_fails_usize`       — unguarded `let b = a + 1`        ⇒ Counterexample
//! * `underflow`                       — `a = 0; a = a - 1`               ⇒ Counterexample
//! * `arith_bounds_asserted_and_assumed` — unguarded `let z = a + b`     ⇒ Counterexample
//! * `test_divide_by_zero` (fail1/fail2) — unguarded `a / b`, `a % b`    ⇒ Counterexample
//! * `test_overflow_ensures_pass`      — `requires a < 30` guard         ⇒ Verified
//! * `test_divide_by_zero` (ok)        — `requires b != 0` guard         ⇒ Verified
//! * `test_const_ok` / `test_const_fail` — constant-folded `254+1`/`255+1`
//!
//! Soundness invariant: every unguarded `// FAILS` body is rejected
//! (Counterexample, never Verified/Unknown), and every guarded body Verifies,
//! using only the auto-emitted obligation — no surrogate assertions.

use super::*;
use crate::encoder::VerifyResult;

/// Extract VCs from the named function in `code` and return `(verdict, obligation_count)`.
fn verify_named(code: &str, name: &str) -> (VerifyResult, usize) {
    let file = parse_file(code).expect("faithful overflow port fixture should parse");
    let func =
        find_function(&file, name).unwrap_or_else(|| panic!("fixture should define fn {name}"));
    let vc = extract_verification_conditions(func)
        .unwrap_or_else(|err| panic!("fn {name} should extract: {err}"));
    let obligations = vc.obligations.len();
    (vc.verify(), obligations)
}

fn assert_counterexample(code: &str, name: &str, min_obligations: usize, upstream: &str) {
    let (result, obligations) = verify_named(code, name);
    assert!(
        obligations >= min_obligations,
        "fn {name} ({upstream}) should collect at least {min_obligations} obligation(s), got {obligations}"
    );
    match result {
        VerifyResult::Counterexample { .. } => {}
        VerifyResult::Unknown { reason, .. } => panic!(
            "fn {name} ({upstream}) returned solver Unknown, which is not stable evidence: {reason}"
        ),
        other => panic!("fn {name} ({upstream}) should be rejected, got: {other:?}"),
    }
}

fn assert_verified(code: &str, name: &str, min_obligations: usize, upstream: &str) {
    let (result, obligations) = verify_named(code, name);
    assert!(
        obligations >= min_obligations,
        "fn {name} ({upstream}) should collect at least {min_obligations} obligation(s), got {obligations}"
    );
    match result {
        VerifyResult::Verified => {}
        VerifyResult::Unknown { reason, .. } => panic!(
            "fn {name} ({upstream}) returned solver Unknown, which is not stable evidence: {reason}"
        ),
        other => panic!("fn {name} ({upstream}) should verify, got: {other:?}"),
    }
}

// ========================================================================
// should-fail direction: literal upstream `// FAILS` bodies, no surrogate
// ========================================================================

/// Upstream `test_overflow_fails_1`:
/// ```ignore
/// fn test(a: u64) { let mut j = a; j = j + 2; /* FAILS */ }
/// ```
/// The unguarded `j = j + 2` assignment carries the auto-emitted overflow
/// obligation; no `assert!` surrogate is present, yet the body is rejected at
/// `a == u64::MAX`.
#[test]
fn faithful_overflow_fails_1_assignment_is_rejected() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test(a: u64) {
            let mut j = a;
            j = j + 2u64;
        }
    "#;
    assert_counterexample(code, "test", 1, "test_overflow_fails_1");
}

/// Upstream `test_overflow_fails_2` (same body as `_fails_1`):
/// ```ignore
/// fn test(a: u64) { let mut j = a; j = j + 2; /* FAILS */ }
/// ```
#[test]
fn faithful_overflow_fails_2_assignment_is_rejected() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test(a: u64) {
            let mut j = a;
            j = j + 2u64;
        }
    "#;
    assert_counterexample(code, "test", 1, "test_overflow_fails_2");
}

/// Upstream `test_overflow_fails_usize`:
/// ```ignore
/// fn test(a: usize) -> usize { let b = a + 1; /* FAILS */ b }
/// ```
/// The `let` initializer carries the auto-emitted overflow obligation; the
/// returned `b` needs no surrogate assertion.
#[test]
fn faithful_overflow_fails_usize_let_is_rejected() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test(a: usize) -> usize {
            let b = a + 1usize;
            b
        }
    "#;
    assert_counterexample(code, "test", 1, "test_overflow_fails_usize");
}

/// Upstream `underflow`:
/// ```ignore
/// fn underflow() { let mut a: u64 = 0; a = a - 1; /* FAILS */ }
/// ```
/// All-constant `0 - 1` is a constant-folded subtraction-overflow refutation.
#[test]
fn faithful_underflow_subtraction_is_rejected() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn underflow() {
            let mut a: u64 = 0u64;
            a = a - 1u64;
        }
    "#;
    assert_counterexample(code, "underflow", 1, "underflow");
}

/// Upstream `arith_bounds_asserted_and_assumed`:
/// ```ignore
/// fn test(a: u64, b: u64) { let z = a + b; /* FAILS */ let y = a + b; }
/// ```
/// The first unguarded `let z = a + b` is refuted at `a == u64::MAX, b == 1`.
#[test]
fn faithful_arith_bounds_unguarded_add_is_rejected() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test(a: u64, b: u64) {
            let z = a + b;
            let y = a + b;
        }
    "#;
    assert_counterexample(code, "test", 1, "arith_bounds_asserted_and_assumed");
}

/// Upstream `test_divide_by_zero` `fail1`:
/// ```ignore
/// fn fail1(a: u8, b: u8) { let x = a / b; /* FAILS */ }
/// ```
/// The `let` initializer carries the auto-emitted divide-by-zero obligation,
/// refuted at `b == 0`.
#[test]
fn faithful_divide_by_zero_let_is_rejected() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn fail1(a: u8, b: u8) {
            let x = a / b;
        }
    "#;
    assert_counterexample(code, "fail1", 1, "test_divide_by_zero::fail1");
}

/// Upstream `test_divide_by_zero` `fail2`:
/// ```ignore
/// fn fail2(a: u8, b: u8) { let y = a % b; /* FAILS */ }
/// ```
#[test]
fn faithful_remainder_by_zero_let_is_rejected() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn fail2(a: u8, b: u8) {
            let y = a % b;
        }
    "#;
    assert_counterexample(code, "fail2", 1, "test_divide_by_zero::fail2");
}

/// Upstream `test_const_fail`:
/// ```ignore
/// const C: u8 = 255 + 1 /* FAILS */;
/// ```
/// The all-constant initializer overflows u8 — a constant-folded refutation.
#[test]
fn faithful_const_initializer_overflow_is_rejected() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            const C: u8 = 255u8 + 1u8;
        }
    "#;
    assert_counterexample(code, "test", 1, "test_const_fail");
}

// ========================================================================
// should-verify direction: guarded/in-range bodies, no surrogate
// ========================================================================

/// Upstream `test_overflow_ensures_pass`:
/// ```ignore
/// fn test(a: usize) -> (r: usize) requires a < 30 ensures r == a + 1 {
///     let b = a + 1; b
/// }
/// ```
/// The `requires a < 30` precondition discharges the auto-emitted overflow
/// obligation on `a + 1`, and the postcondition holds — no surrogate assertion.
#[test]
fn faithful_overflow_ensures_pass_verifies() {
    let code = r#"
        #[trust_vc::requires(a < 30usize)]
        #[trust_vc::ensures(result == a + 1usize)]
        fn test(a: usize) -> usize {
            let b = a + 1usize;
            b
        }
    "#;
    assert_verified(code, "test", 2, "test_overflow_ensures_pass");
}

/// Upstream `test_divide_by_zero` `ok`:
/// ```ignore
/// fn ok(a: u8, b: u8) requires b != 0 { let x = a / b; let y = a % b; }
/// ```
/// The `requires b != 0` precondition discharges both auto-emitted
/// divide/remainder-by-zero obligations — no surrogate assertion.
#[test]
fn faithful_divide_by_nonzero_guard_verifies() {
    let code = r#"
        #[trust_vc::requires(b != 0u8)]
        #[trust_vc::ensures(true)]
        fn ok(a: u8, b: u8) {
            let x = a / b;
            let y = a % b;
        }
    "#;
    assert_verified(code, "ok", 2, "test_divide_by_zero::ok");
}

/// Upstream `test_const_ok`:
/// ```ignore
/// const C: u8 = 254 + 1;
/// ```
/// The all-constant initializer stays in range, so the auto-emitted overflow
/// obligation is discharged.
#[test]
fn faithful_const_initializer_in_range_verifies() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            const C: u8 = 254u8 + 1u8;
        }
    "#;
    assert_verified(code, "test", 1, "test_const_ok");
}

// ========================================================================
// exec signed-shift (possibly-negative amount) ⇒ VIR Error, byte-exact label
// ========================================================================

/// Assert the named function surfaces a `VerifyResult::Error` whose message
/// contains `expect_msg` (upstream `assert_vir_error_msg` parity), collecting at
/// least `min_obligations`. A solver `Unknown` is an explicit failure: the whole
/// point of the exec signed-shift diagnostic-parity path is that ay-dpll's CEGQI
/// empty-model SAT must NOT sink the faithful Error into Unknown.
fn assert_vir_error(
    code: &str,
    name: &str,
    min_obligations: usize,
    expect_msg: &str,
    upstream: &str,
) {
    let (result, obligations) = verify_named(code, name);
    assert!(
        obligations >= min_obligations,
        "fn {name} ({upstream}) should collect at least {min_obligations} obligation(s), got {obligations}"
    );
    match result {
        VerifyResult::Error { message } => assert!(
            message.contains(expect_msg),
            "fn {name} ({upstream}) Error message {message:?} should contain {expect_msg:?}"
        ),
        VerifyResult::Unknown { reason, .. } => panic!(
            "fn {name} ({upstream}) returned solver Unknown, which is not faithful VIR-error \
             evidence (ay-dpll CEGQI empty-model must reclassify to Error): {reason}"
        ),
        other => panic!("fn {name} ({upstream}) should be a VIR Error, got: {other:?}"),
    }
}

/// Upstream `bit_shift_unsigned_shift_signed`:
/// ```ignore
/// fn test_underflow() { let x: u16 = 0; let y: i16 = -1; let z = x << y; /* FAILS */ }
/// ```
/// Upstream verdict: `Err(e) => assert_vir_error_msg(e, "possible bit shift underflow/overflow")`.
/// The shift amount `y: i16` is possibly-negative, so the `0 <= y < 16` bound is
/// undischargeable; ay-dpll refutes it (validated SAT) but cannot render a
/// concrete witness, so the faithful path reclassifies the empty-model SAT to a
/// VIR `Error` carrying the byte-exact upstream label — not a `Counterexample`
/// (those are `assert_fails`) and not an `Unknown`.
#[test]
fn faithful_bit_shift_unsigned_shift_signed_is_vir_error() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test_underflow() {
            let x: u16 = 0u16;
            let y: i16 = -1i16;
            let z = x << y;
        }
    "#;
    assert_vir_error(
        code,
        "test_underflow",
        1,
        "possible bit shift underflow/overflow",
        "bit_shift_unsigned_shift_signed",
    );
}

/// Upstream `bit_shift_underflow`:
/// ```ignore
/// fn test_underflow() { let x: i16 = 0; let y: i16 = -1; let z = x << y; /* FAILS */ }
/// ```
/// Same shape with a signed `x: i16` operand; identical upstream verdict
/// `assert_vir_error_msg(e, "possible bit shift underflow/overflow")`.
#[test]
fn faithful_bit_shift_underflow_is_vir_error() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test_underflow() {
            let x: i16 = 0i16;
            let y: i16 = -1i16;
            let z = x << y;
        }
    "#;
    assert_vir_error(
        code,
        "test_underflow",
        1,
        "possible bit shift underflow/overflow",
        "bit_shift_underflow",
    );
}

/// SOUNDNESS / faithfulness guard for the reclassification above: a signed
/// shift amount that is *provably in range* must still VERIFY (UNSAT ->
/// Verified), proving the empty-model→Error reclassification only fires on a
/// genuinely refuted shift and does not blanket-reject all signed-amount shifts.
/// Here `requires 0 <= y < 16` discharges the bound, mirroring upstream
/// `bit_shift_no_underflow`-style in-range bodies.
#[test]
fn faithful_in_range_signed_shift_still_verifies() {
    let code = r#"
        #[trust_vc::requires(y >= 0i16)]
        #[trust_vc::requires(y < 16i16)]
        #[trust_vc::ensures(true)]
        fn test_in_range(x: u16, y: i16) {
            let z = x << y;
        }
    "#;
    assert_verified(code, "test_in_range", 1, "in-range signed shift");
}

// ========================================================================
// declared-width preservation for const-substituted unsigned shift amounts
// (faithful upstream `bit_shift_overflow` literal bodies; #2778)
//
// These pin the syn-frontend fix that re-attaches a `let v: <intty> = <bare
// literal>;` local's DECLARED width when it const-substitutes `v` into a shift.
// Without it the substituted amount (and, when the LHS is also a substituted
// literal, the shifted operand) defaults to a signed width-32 `i32` and either
// routes to the signed `bit shift underflow/overflow` path or verifies
// spuriously against a width-32 bound. The unsuffixed *literal* upstream bodies
// (`let x: u16 = 0; let y: u16 = 16; let z = x >> y;`) are exercised verbatim —
// no parameter/suffix surrogate — composing with the unsigned over-shift
// empty-model counterexample reclassification (Feature A).
// ========================================================================

/// Upstream `bit_shift_overflow::test_overflow_right_shift` (verbatim body):
/// ```ignore
/// fn test() { let x: u16 = 0; let y: u16 = 16; let z = x >> y; /* FAILS */ }
/// ```
/// `16 >= 16` (the u16 bit width) is a right-shift over-shift. Both `x` and `y`
/// are unsuffixed typed-literal locals; the declared-width fix keeps them u16,
/// so the obligation routes to `right shift overflow` and the ground over-shift
/// surfaces as a Counterexample (never Verified, never the signed Error path).
#[test]
fn faithful_unsuffixed_u16_right_over_shift_is_counterexample() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let x: u16 = 0;
            let y: u16 = 16;
            let z = x >> y;
        }
    "#;
    assert_counterexample(
        code,
        "test",
        1,
        "bit_shift_overflow::test_overflow_right_shift",
    );
}

/// Upstream `bit_shift_overflow::test_overflow_right_shift2`: `y: u16 = 17`, an
/// over-boundary right shift (`17 >= 16`). Same declared-width path.
#[test]
fn faithful_unsuffixed_u16_right_over_shift_above_boundary_is_counterexample() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let x: u16 = 0;
            let y: u16 = 17;
            let z = x >> y;
        }
    "#;
    assert_counterexample(
        code,
        "test",
        1,
        "bit_shift_overflow::test_overflow_right_shift2",
    );
}

/// Upstream `bit_shift_overflow::test_overflow_left_shift`: `let x: u16 = 0;
/// let y: u16 = 16; let z = x << y; // FAILS`. The left-shift over-shift mirror
/// of the right-shift case (`left shift overflow`).
#[test]
fn faithful_unsuffixed_u16_left_over_shift_is_counterexample() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let x: u16 = 0;
            let y: u16 = 16;
            let z = x << y;
        }
    "#;
    assert_counterexample(
        code,
        "test",
        1,
        "bit_shift_overflow::test_overflow_left_shift",
    );
}

/// SOUNDNESS (no false counterexample). Upstream
/// `bit_shift_overflow::test_overflow_right_shift3`: `let x: u16 = 0; let y:
/// u16 = 15; let z = x >> y;` — `15 < 16` is in range and must VERIFY. Proves
/// the declared-width fix does not blanket-reject substituted-literal shifts;
/// it only refutes a genuine `>= width` over-shift.
#[test]
fn faithful_unsuffixed_u16_in_range_shift_verifies() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let x: u16 = 0;
            let y: u16 = 15;
            let z = x >> y;
        }
    "#;
    assert_verified(
        code,
        "test",
        1,
        "bit_shift_overflow::test_overflow_right_shift3",
    );
}

/// SOUNDNESS (no false counterexample). Upstream
/// `bit_shift_overflow::test_overflow_left_arg_doesnt_matter`: a nonzero left
/// operand with an in-range amount (`5 < 16`) still verifies — the over-shift
/// bound is on the amount, not the shifted value.
#[test]
fn faithful_unsuffixed_u16_in_range_left_shift_nonzero_lhs_verifies() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let x: u16 = 16;
            let y: u16 = 5;
            let z = x >> y;
        }
    "#;
    assert_verified(
        code,
        "test",
        1,
        "bit_shift_overflow::test_overflow_left_arg_doesnt_matter",
    );
}

/// DIFFERENT declared width (`u8`, bit width 8) is preserved correctly: `8 >= 8`
/// over-shifts a u8 and must be a Counterexample, while `7 < 8` verifies. Pins
/// that the suffix re-attachment tracks the *actual* declared width, not a
/// single hard-coded one — a u8 amount of 8 would be a perfectly in-range
/// shift if it were mis-attributed the width-16/32 default.
#[test]
fn faithful_unsuffixed_u8_over_shift_is_counterexample_and_in_range_verifies() {
    let over = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let x: u8 = 0;
            let y: u8 = 8;
            let z = x << y;
        }
    "#;
    assert_counterexample(over, "test", 1, "u8 over-shift (8 >= 8)");

    let in_range = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let x: u8 = 0;
            let y: u8 = 7;
            let z = x << y;
        }
    "#;
    assert_verified(in_range, "test", 1, "u8 in-range shift (7 < 8)");
}

/// `usize` declared width is preserved by SPELLING (not frozen to a concrete
/// width), so `usize::BITS as usize` is still resolved through the pointer
/// width: an `x << usize::BITS` over-shift is a Counterexample and
/// `usize::BITS - 1` verifies. Mirrors upstream
/// `bit_shift_overflow::test_usize_overflow*`. The amount here is a `BITS` cast,
/// not a bare literal, so this also confirms the existing `usize` path is
/// undisturbed by the literal fix.
#[test]
fn faithful_usize_bits_over_shift_is_counterexample_and_minus_one_verifies() {
    let over = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let x: usize = 0;
            let y: usize = usize::BITS as usize;
            let z = x << y;
        }
    "#;
    assert_counterexample(over, "test", 1, "bit_shift_overflow::test_usize_overflow2");

    let in_range = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let x: usize = 0;
            let y: usize = (usize::BITS - 1) as usize;
            let z = x << y;
        }
    "#;
    assert_verified(
        in_range,
        "test",
        1,
        "bit_shift_overflow::test_usize_overflow3",
    );
}

/// SYMBOLIC (non-const) shift amount is unchanged by the fix: the declared-width
/// re-attachment only fires for bare *literal* initializers, so a symbolic
/// unsigned parameter amount with no range guard is still a Counterexample
/// (`x << y` with `y: u16` unconstrained can over-shift), exactly as before the
/// fix. There is no `let` literal to re-suffix here.
#[test]
fn symbolic_unsigned_shift_amount_unchanged_is_counterexample() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test(x: u16, y: u16) {
            let z = x << y;
        }
    "#;
    assert_counterexample(code, "test", 1, "symbolic unsigned shift amount");
}

/// SYMBOLIC amount with a discharging range guard still VERIFIES — the fix does
/// not perturb the symbolic path in either direction (`0 <= y < 16` ⇒ in range).
#[test]
fn symbolic_unsigned_shift_amount_guarded_verifies() {
    let code = r#"
        #[trust_vc::requires(y < 16u16)]
        #[trust_vc::ensures(true)]
        fn test(x: u16, y: u16) {
            let z = x << y;
        }
    "#;
    assert_verified(code, "test", 1, "symbolic guarded unsigned shift amount");
}

// ========================================================================
// soundness guard: spec/proof functions must NOT receive the exec check
// ========================================================================

/// The auto-emitted overflow obligation is gated on `Exec` mode
/// (`maybe_emit_exec_arith_overflow_check` early-returns unless
/// `vc.check_overflow()`, which `with_mode_overflow` only enables for `Exec`).
/// A `spec` function with the same overflowing `let`-initializer arithmetic
/// must NOT acquire an `overflow_check_*` obligation (matching Verus, where
/// spec/proof arithmetic is unbounded). This guards against the faithful exec
/// re-port leaking overflow checks into spec bodies — which would otherwise
/// turn this safe spec body into a spurious Counterexample.
#[test]
fn spec_mode_arithmetic_does_not_get_exec_overflow_check() {
    let code = r#"
        #[trust_vc::spec]
        fn s(a: u64) -> u64 {
            let b = a + 2u64;
            b
        }
    "#;
    let file = parse_file(code).expect("spec fixture should parse");
    let func = find_function(&file, "s").expect("fixture should define fn s");
    let vc = extract_verification_conditions(func).expect("fn s should extract");

    let synthetic_overflow_checks = vc
        .obligations
        .iter()
        .filter(|o| o.name().starts_with("overflow_check_"))
        .count();
    assert_eq!(
        synthetic_overflow_checks, 0,
        "spec-mode arithmetic must not emit an exec overflow check; \
         leaking one would spuriously refute unbounded spec arithmetic"
    );
}

/// Contrast with the spec guard above: the *same* `let b = a + 2u64;` site in
/// an `Exec` function (the default classification for a `#[trust_vc::ensures]`
/// fn) DOES acquire exactly one auto-emitted `overflow_check_*` obligation.
/// This pins that the faithful re-port's no-surrogate bodies are actually
/// carrying the overflow obligation, not silently passing for lack of a check.
#[test]
fn exec_mode_arithmetic_emits_exactly_one_overflow_check() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn e(a: u64) {
            let b = a + 2u64;
        }
    "#;
    let file = parse_file(code).expect("exec fixture should parse");
    let func = find_function(&file, "e").expect("fixture should define fn e");
    let vc = extract_verification_conditions(func).expect("fn e should extract");

    let synthetic_overflow_checks = vc
        .obligations
        .iter()
        .filter(|o| o.name().starts_with("overflow_check_"))
        .count();
    assert_eq!(
        synthetic_overflow_checks, 1,
        "an exec discarded-result `let b = a + 2` site must auto-emit exactly \
         one overflow obligation, so the surrogate-free body is actually checked"
    );
}
