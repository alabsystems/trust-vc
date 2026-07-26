// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
//! Soundness regression (round-2 audit, compute-fallback cluster): the
//! ComputeEvaluator must WRAP a fixed-width unary negation in two's complement
//! (`-(-128i8) == -128i8`, not the unbounded `128`). The `Neg` IR node carries no
//! width; without inferring the operand type and wrapping, the compute fallback
//! manufactured a false `Verified` on `-(i8::MIN) >= 0`.

#[trust_vc::spec]
fn neg_i8(x: i8) -> i8 { -x }

#[trust_vc::spec]
fn neg_i16(x: i16) -> i16 { -x }

// FALSE under two's-complement wrap (-(-128i8) == -128i8, NOT 128) -> must NOT verify.
#[trust_vc::proof] fn i8_min_neg_ge0_false() { trust_vc::assert!(neg_i8(-128i8) >= 0i8); }
#[trust_vc::proof] fn i8_min_neg_eq0_false() { trust_vc::assert!(neg_i8(-128i8) == 0i8); }
#[trust_vc::proof] fn i16_min_neg_ge0_false() { trust_vc::assert!(neg_i16(-32768i16) >= 0i16); }

// TRUE: the negation wraps to MIN; non-MIN negation is exact.
#[trust_vc::proof] fn i8_min_neg_wraps_true() { trust_vc::assert!(neg_i8(-128i8) == -128i8); }
#[trust_vc::proof] fn i8_nonmin_neg_true() { trust_vc::assert!(neg_i8(-5i8) == 5i8); }
