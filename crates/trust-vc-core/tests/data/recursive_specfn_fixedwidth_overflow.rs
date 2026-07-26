// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! P1-E (shifts cluster, recursive-u8) soundness fixtures: fixed-width
//! arithmetic inside a recursive spec-fn body must WRAP in two's complement,
//! consistent with the symbolic encoder. The by(compute) interpreter (used to
//! discharge / refute closed ground recursive goals) previously computed
//! `x + 1` for `x: u8` with UNBOUNDED `i128`, so `x + 1 > x` folded to `true`
//! even at `x == 255` (where the wrapped value is `0` and `0 > 255` is false),
//! manufacturing a spurious `Verified` for a genuinely-false goal.
//!
//! Ground truth: trust-vc models spec-mode fixed-width `+` as wrapping (a
//! non-recursive `255u8 + 1u8` is `0`, confirmed by `add1`/`nr` below), so
//! `h(0, 255)` is `false` and `h(0, 100)` is `true`.

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn h(n: u8, x: u8) -> bool {
    if n == 0u8 {
        x + 1u8 > x
    } else {
        h(n - 1u8, x)
    }
}

#[trust_vc::spec]
fn nr(x: u8) -> bool {
    x + 1u8 > x
}

// FALSE: h(0, 255) wraps to `0 > 255` == false, so claiming it is true is false.
#[trust_vc::ensures(true)]
fn h0_255_true_FALSE() {
    trust_vc::assert!(h(0u8, 255u8) == true);
}

// TRUE companion: h(0, 255) really is false.
#[trust_vc::ensures(true)]
fn h0_255_false_TRUE() {
    trust_vc::assert!(h(0u8, 255u8) == false);
}

// Contradiction canary: a single goal asserting both must NOT verify.
#[trust_vc::ensures(true)]
fn h0_255_both_FALSE() {
    trust_vc::assert!(h(0u8, 255u8) == true && h(0u8, 255u8) == false);
}

// TRUE: no overflow at x = 100, so x + 1 > x holds.
#[trust_vc::ensures(true)]
fn h0_100_true_TRUE() {
    trust_vc::assert!(h(0u8, 100u8) == true);
}

// FALSE: h(0, 100) is true, so claiming it is false is false.
#[trust_vc::ensures(true)]
fn h0_100_false_FALSE() {
    trust_vc::assert!(h(0u8, 100u8) == false);
}

// Non-recursive companion: same wrapping, false at the overflow point.
#[trust_vc::ensures(true)]
fn nr_255_true_FALSE() {
    trust_vc::assert!(nr(255u8) == true);
}

#[trust_vc::ensures(true)]
fn nr_255_false_TRUE() {
    trust_vc::assert!(nr(255u8) == false);
}
