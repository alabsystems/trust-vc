//! Arithmetic and bitwise encoding for TrustVcExpr IR.
//!
//! Split into submodules by concern:
//! - `bv_arith`: BV, Real, and bitwise/shift arithmetic
//! - `compare`: comparison operators (eq, lt, le, gt, ge)
//! - `int_arith`: Int-mode arithmetic operators
//! - `int_mode`: Int-mode bitwise/shift for quantifier bodies
//! - `overflow`: BV overflow/underflow checks
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod bv_arith;
mod compare;
mod compare_inference;
mod compare_seq;
mod int_arith;
mod int_mode;
mod overflow;
