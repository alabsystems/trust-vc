// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
//! Soundness regression (round-2 audit, compute-fallback cluster): the
//! ComputeEvaluator's `int`/`nat` division and remainder must be EUCLIDEAN,
//! matching the symbolic encoder. Truncating semantics let the compute fallback
//! (`recover_assert_by_incompleteness_via_compute`) manufacture `Verified` on
//! genuinely-false negative-`int` div/mod goals.

#[trust_vc::spec]
fn dq(x: int, y: int) -> int { x / y }

#[trust_vc::spec]
fn dr(x: int, y: int) -> int { x % y }

// FALSE under Euclidean semantics (these are the TRUNCATED values) -> must NOT verify.
#[trust_vc::proof] fn dq_neg_trunc_false() { trust_vc::assert!(dq(-7, 2) == -3); }
#[trust_vc::proof] fn dr_neg_trunc_false() { trust_vc::assert!(dr(-7, 2) == -1); }
#[trust_vc::proof] fn dr_neg8_trunc_false() { trust_vc::assert!(dr(-8, 3) == -2); }

// TRUE under Euclidean semantics -> must verify.
#[trust_vc::proof] fn dq_neg_eucl_true() { trust_vc::assert!(dq(-7, 2) == -4); }
#[trust_vc::proof] fn dr_neg_eucl_true() { trust_vc::assert!(dr(-7, 2) == 1); }
#[trust_vc::proof] fn dr_neg8_eucl_true() { trust_vc::assert!(dr(-8, 3) == 1); }

// Non-negative: Euclidean == truncated, unaffected.
#[trust_vc::proof] fn pos_true() { trust_vc::assert!(dq(7, 2) == 3 && dr(7, 2) == 1); }
