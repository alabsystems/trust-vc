//! Permanent soundness guards: a near-MAX collection length must not let a
//! length-overflowing operation be reasoned about as if it wrapped silently.
//!
//! These mirror the existing `test_set_insert_absent_element_does_not_wrap_len_
//! to_zero` guard, extended to concat / push / Multiset insert — which had NO
//! such guard. That gap is exactly why an UNSOUND "assume no-wrap" axiom
//! (route B, 2026-06-14) passed the lib diff for those ops before being caught
//! by the set-insert guard and reverted (see
//! the internal parity-to-100 program notes + memory trust-vc-collections-length-soundness).
//!
//! The invariant: with `len == u64::MAX` assumed, a goal that is only true under
//! silent BV wraparound (`len(op) == 0`) MUST NOT verify. Any future fix that
//! relaxes the length-overflow obligation by ASSUMING no-wrap on the bounded BV
//! makes the context vacuous here and flips these to Verified — a soundness
//! regression these tests will catch. The sound fix (route A: unbounded nat/Int
//! length) keeps them fail-closed because MAX+1 != 0 over the integers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use trust_vc_core::ir::TrustVcType;
use trust_vc_core::vc::{ProofObligation, VerificationContext};
use trust_vc_core::VerifyResult;

const U64_MAX: &str = "18446744073709551615u64";

fn run(decls: &[(&str, &str)], assumes: &[(&str, &str)], assert: (&str, &str)) -> VerifyResult {
    let mut ctx = VerificationContext::new();
    for (name, ty) in decls {
        ctx.declare_var_typed(name, TrustVcType::parse_or_opaque(ty));
    }
    for (n, e) in assumes {
        ctx.push_obligation(ProofObligation::assume(*n, *e));
    }
    ctx.push_obligation(ProofObligation::assert(assert.0, assert.1));
    ctx.verify()
}

#[test]
fn concat_nearmax_len_does_not_wrap_to_zero() {
    // s.len()==MAX, t.len()==1  =>  (s++t).len() is MAX+1, never 0.
    let r = run(
        &[("s", "Seq<i32>"), ("t", "Seq<i32>")],
        &[
            ("s_max", &format!("s.len() == {U64_MAX}")),
            ("t_one", "t.len() == 1"),
        ],
        ("wraps", "s.add(t).len() == 0"),
    );
    eprintln!("[concat nearmax] {r:?}");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "SOUNDNESS: concat at near-MAX length must not verify a wrap-to-zero goal: {r:?}"
    );
}

#[test]
fn push_nearmax_len_does_not_wrap_to_zero() {
    let r = run(
        &[("s", "Seq<i32>"), ("v", "i32")],
        &[("s_max", &format!("s.len() == {U64_MAX}"))],
        ("wraps", "s.push(v).len() == 0"),
    );
    eprintln!("[push nearmax] {r:?}");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "SOUNDNESS: push at near-MAX length must not verify a wrap-to-zero goal: {r:?}"
    );
}

#[test]
fn multiset_insert_nearmax_len_does_not_wrap_to_zero() {
    let r = run(
        &[("m", "Multiset<i32>"), ("x", "i32")],
        &[("m_max", &format!("m.len() == {U64_MAX}"))],
        ("wraps", "m.insert(x).len() == 0"),
    );
    eprintln!("[multiset nearmax] {r:?}");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "SOUNDNESS: multiset insert at near-MAX length must not verify a wrap-to-zero goal: {r:?}"
    );
}
