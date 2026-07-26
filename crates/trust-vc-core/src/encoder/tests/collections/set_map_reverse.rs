//! Set::map reverse image-exactness regression (GAP 3).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `Set::map(f)` is encoded as the EXACT image of the receiver. Previously only
//! the forward direction was asserted:
//!     forward: forall x. s[x] => s.map(f)[f(x)]
//! which left mapped-set membership facts under-constrained (an element known
//! to be in `s.map(f)` told the solver nothing about a preimage in `s`). This
//! suite pins the added reverse/exactness direction
//!     reverse: forall y. s.map(f)[y] => exists x. s[x] && f(x) == y
//! (Skolemized with a fresh inverse array), AND proves the reverse axiom does
//! not overconstrain: a wrong preimage claim must still fail closed.

use super::*;

/// CORRECTNESS (new capability): from `s.map(|i| i+1).contains(3)` the reverse
/// image-exactness axiom yields a preimage `2` in `s`, so `s.contains(2)` must
/// verify. Before the reverse axiom this returned Unknown (forward-only).
#[test]
fn test_set_map_reverse_image_witness_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<int>"));
    ctx.push_obligation(ProofObligation::assume(
        "mapped_has_3",
        "s.map(SpecFn::new(|i: int| i + (1 as int))).contains(3 as int)",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "preimage_2",
        "s.contains(2 as int)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "s.map(|i| i+1).contains(3) implies s.contains(2) via reverse image-exactness (GAP 3)",
    );
}

/// ADVERSARIAL (soundness): the reverse axiom must not let an arbitrary element
/// be claimed in `s`. From `s.map(|i| i+1).contains(3)` the only forced
/// preimage is `2`; `s.contains(99)` must NOT verify.
#[test]
fn test_set_map_reverse_wrong_witness_fails() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<int>"));
    ctx.push_obligation(ProofObligation::assume(
        "mapped_has_3",
        "s.map(SpecFn::new(|i: int| i + (1 as int))).contains(3 as int)",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wrong_witness_99",
        "s.contains(99 as int)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "s.map(|i| i+1).contains(3) must NOT prove s.contains(99) — preimage is 2, not 99 (GAP 3 soundness)",
    );
}

/// ADVERSARIAL (soundness): the mapped element itself is generally not a member
/// of the receiver. From `s.map(|i| i+1).contains(3)` the forced preimage is
/// `2`, not `3`; `s.contains(3)` must NOT verify.
#[test]
fn test_set_map_reverse_self_element_fails() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<int>"));
    ctx.push_obligation(ProofObligation::assume(
        "mapped_has_3",
        "s.map(SpecFn::new(|i: int| i + (1 as int))).contains(3 as int)",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wrong_witness_3",
        "s.contains(3 as int)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "s.map(|i| i+1).contains(3) must NOT prove s.contains(3) — preimage is 2 (GAP 3 soundness)",
    );
}

/// REGRESSION GUARD: the forward direction must keep verifying after adding the
/// reverse axiom. `s.contains(2)` implies `s.map(|i| i+1).contains(3)`.
#[test]
fn test_set_map_forward_image_still_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<int>"));
    ctx.push_obligation(ProofObligation::assume("has_2", "s.contains(2 as int)"));
    ctx.push_obligation(ProofObligation::assert(
        "mapped_has_3",
        "s.map(SpecFn::new(|i: int| i + (1 as int))).contains(3 as int)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forward image: s.contains(2) implies s.map(|i| i+1).contains(3)",
    );
}
