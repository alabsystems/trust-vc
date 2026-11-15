// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Extensional equality between two SYMBOLIC collection expressions that SHARE
//! an operand must be decided by CONTENTS, never by structure.
//!
//! Origin: a corpus survey reported that trust-vc might PROVE
//! `a.add(b) =~= a.add(a)` for multisets — a claim that is false whenever
//! `b != a`, and which upstream Verus refutes (`multiset_fail2`). Measured, the
//! report was REFUTED: the body assert is a concrete Counterexample in
//! isolation. What the surveyor actually saw was obligation ORDER plus
//! first-failure short-circuit — the port's `ensures` is ALSO false, the engine
//! checks postconditions before body asserts and returns at the first failing
//! obligation (`encoder/verification/typed.rs`), so the port names the
//! postcondition where upstream names the assert. Both report exactly one
//! failure, which is what upstream's `assert_one_fails` measures.
//!
//! The hole the report DID expose is in the pins, not the engine: the corpus
//! cases for `multiset_fail2` / `multiset_fail3` carry a FALSE `ensures`, so a
//! `Counterexample` assertion over them is satisfied by the postcondition alone
//! and would stay green even if the body assert were falsely proved. Every liar
//! below therefore neutralises the postcondition to `ensures(true)`, which makes
//! the `=~=` assert the ONLY obligation that can fail.
//!
//! Each liar is paired with its TRUE twin, so a blanket refusal cannot pass this
//! file: commutativity, associativity, syntactic reflexivity of a compound
//! operand, and an equality established ELEMENTWISE by hypothesis must all still
//! verify.
//!
//! A structural-keying mistake rarely lives in one type alone, so the same
//! shared-operand shape is probed across Multiset, Set and Map.

use std::collections::hash_map::DefaultHasher;
use std::fs;
use std::hash::{Hash, Hasher};
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    let dir = Path::new("target/ext_eq_shared_operand_soundness");
    fs::create_dir_all(dir).unwrap();
    // Key the temp file by CONTENT so parallel tests that share a function name
    // can never read each other's variant (the race `multiset_upstream_ports.rs`
    // documents).
    let mut h = DefaultHasher::new();
    code.hash(&mut h);
    let f = dir.join(format!("{name}_{:016x}.rs", h.finish()));
    fs::write(&f, code).unwrap();
    trust_vc_core::verify_function_from_file(f.to_str().unwrap(), name)
}

fn verified(r: &TrustVcResult<VerifyResult>) -> bool {
    matches!(r, Ok(VerifyResult::Verified))
}

fn counterexample(r: &TrustVcResult<VerifyResult>) -> bool {
    matches!(r, Ok(VerifyResult::Counterexample { .. }))
}

/// A liar must never be `Verified`. Stated as "not verified" rather than
/// "Counterexample" because a fail-closed `NotProved` (solver incompleteness) is
/// also a correct refusal — it is only a false `Verified` that is unsound. Where
/// a real model IS produced today, the stronger `counterexample` assertion is
/// used instead and says so.
fn must_not_verify(r: &TrustVcResult<VerifyResult>, claim: &str) {
    assert!(
        !verified(r),
        "FALSE claim `{claim}` must NOT verify, got {r:?}"
    );
}

// ════════════════════════════════ Multiset ════════════════════════════════

const MS: &str = "use trust_vc_types::Multiset;\n";

/// THE REPORTED CLAIM. `a.add(b) =~= a.add(a)` holds only when `b == a`, so a
/// general claim of it is false; upstream `multiset_fail2` refutes it. Pinned at
/// the stronger `Counterexample` because the engine produces a real model.
#[test]
fn multiset_add_shared_operand_false_is_counterexample() {
    let code = format!(
        "{MS}
#[trust_vc::ensures(true)]
fn ms_add_shared_operand<V>(a: Multiset<V>, b: Multiset<V>) {{
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b), a.add(a)));
}}
"
    );
    let r = verify(&code, "ms_add_shared_operand");
    assert!(
        counterexample(&r),
        "FALSE a.add(b) =~= a.add(a) must be a Counterexample, got {r:?}"
    );
}

/// Upstream `multiset_fail3`'s body assert, ISOLATED. Missing `b.subset_of(a)`,
/// so `a.sub(b).add(b) =~= a` is false where `b` has more of some element.
#[test]
fn multiset_sub_add_cancel_false_is_counterexample() {
    let code = format!(
        "{MS}
#[trust_vc::ensures(true)]
fn ms_sub_add_cancel<V>(a: Multiset<V>, b: Multiset<V>) {{
    trust_vc::assert!(trust_vc::ext_eq!(a.sub(b).add(b), a));
}}
"
    );
    let r = verify(&code, "ms_sub_add_cancel");
    assert!(
        counterexample(&r),
        "FALSE a.sub(b).add(b) =~= a must be a Counterexample, got {r:?}"
    );
}

/// The degenerate shared-operand shape: `a.add(b) =~= a`, false for non-empty
/// `b`. A structural keying that compared only the shared root would prove it.
#[test]
fn multiset_add_vs_own_operand_false_is_counterexample() {
    let code = format!(
        "{MS}
#[trust_vc::ensures(true)]
fn ms_add_vs_operand<V>(a: Multiset<V>, b: Multiset<V>) {{
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b), a));
}}
"
    );
    let r = verify(&code, "ms_add_vs_operand");
    assert!(
        counterexample(&r),
        "FALSE a.add(b) =~= a must be a Counterexample, got {r:?}"
    );
}

/// TRUE twin: commutativity. Must still verify.
#[test]
fn multiset_add_commutes_true_verifies() {
    let code = format!(
        "{MS}
#[trust_vc::ensures(true)]
fn ms_add_commutes<V>(a: Multiset<V>, b: Multiset<V>) {{
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b), b.add(a)));
}}
"
    );
    let r = verify(&code, "ms_add_commutes");
    assert!(
        verified(&r),
        "TRUE a.add(b) =~= b.add(a) must verify, got {r:?}"
    );
}

/// TRUE twin: `a.add(a) =~= a.add(a)`. The shape the liar differs from by ONE
/// operand, so a fix that refused on "shares an operand" would break it.
#[test]
fn multiset_self_add_reflexive_true_verifies() {
    let code = format!(
        "{MS}
#[trust_vc::ensures(true)]
fn ms_self_add_refl<V>(a: Multiset<V>) {{
    trust_vc::assert!(trust_vc::ext_eq!(a.add(a), a.add(a)));
}}
"
    );
    let r = verify(&code, "ms_self_add_refl");
    assert!(
        verified(&r),
        "TRUE a.add(a) =~= a.add(a) must verify, got {r:?}"
    );
}

/// TRUE twin: associativity.
#[test]
fn multiset_add_associative_true_verifies() {
    let code = format!(
        "{MS}
#[trust_vc::ensures(true)]
fn ms_add_assoc<V>(a: Multiset<V>, b: Multiset<V>, c: Multiset<V>) {{
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b.add(c)), a.add(b).add(c)));
}}
"
    );
    let r = verify(&code, "ms_add_assoc");
    assert!(
        verified(&r),
        "TRUE a.add(b.add(c)) =~= a.add(b).add(c) must verify, got {r:?}"
    );
}

/// TRUE twin: a genuine extensional equality proved ELEMENTWISE — the counts
/// agree by hypothesis and nothing structural relates the two operands.
#[test]
fn multiset_elementwise_hypothesis_true_verifies() {
    let code = format!(
        "{MS}
#[trust_vc::requires(forall(|v: V| a.count(v) == b.count(v)))]
#[trust_vc::ensures(true)]
fn ms_elementwise<V>(a: Multiset<V>, b: Multiset<V>) {{
    trust_vc::assert!(trust_vc::ext_eq!(a, b));
}}
"
    );
    let r = verify(&code, "ms_elementwise");
    assert!(
        verified(&r),
        "TRUE elementwise-equal multisets must verify, got {r:?}"
    );
}

// ══════════════════════════════════ Set ═══════════════════════════════════

const SET: &str = "use trust_vc_types::Set;\n";

/// `a.union(b) =~= a.union(a)` reduces to `a ∪ b == a`, false whenever `b` has
/// an element outside `a`. Today this refuses fail-closed WITHOUT a model
/// (quantifier incompleteness on the symbolic membership forall), so the pin is
/// "not verified"; that is a completeness residual, never a soundness one.
#[test]
fn set_union_shared_operand_false_does_not_verify() {
    let code = format!(
        "{SET}
#[trust_vc::ensures(true)]
fn set_union_shared<V>(a: Set<V>, b: Set<V>) {{
    trust_vc::assert!(trust_vc::ext_eq!(a.union(b), a.union(a)));
}}
"
    );
    let r = verify(&code, "set_union_shared");
    must_not_verify(&r, "a.union(b) =~= a.union(a)");
}

/// `a.difference(b) =~= a` is false whenever `a` and `b` overlap.
#[test]
fn set_difference_vs_own_operand_false_does_not_verify() {
    let code = format!(
        "{SET}
#[trust_vc::ensures(true)]
fn set_diff_vs_operand<V>(a: Set<V>, b: Set<V>) {{
    trust_vc::assert!(trust_vc::ext_eq!(a.difference(b), a));
}}
"
    );
    let r = verify(&code, "set_diff_vs_operand");
    must_not_verify(&r, "a.difference(b) =~= a");
}

/// TRUE twin: union commutes.
#[test]
fn set_union_commutes_true_verifies() {
    let code = format!(
        "{SET}
#[trust_vc::ensures(true)]
fn set_union_commutes<V>(a: Set<V>, b: Set<V>) {{
    trust_vc::assert!(trust_vc::ext_eq!(a.union(b), b.union(a)));
}}
"
    );
    let r = verify(&code, "set_union_commutes");
    assert!(
        verified(&r),
        "TRUE a.union(b) =~= b.union(a) must verify, got {r:?}"
    );
}

/// TRUE twin: syntactic reflexivity of a COMPOUND operand — the fail-closed
/// refusals above must not swallow this.
#[test]
fn set_compound_reflexive_true_verifies() {
    let code = format!(
        "{SET}
#[trust_vc::ensures(true)]
fn set_compound_refl<V>(a: Set<V>, b: Set<V>) {{
    trust_vc::assert!(trust_vc::ext_eq!(a.union(b), a.union(b)));
}}
"
    );
    let r = verify(&code, "set_compound_refl");
    assert!(
        verified(&r),
        "TRUE a.union(b) =~= a.union(b) must verify, got {r:?}"
    );
}

// ══════════════════════════════════ Map ═══════════════════════════════════

const MAP: &str = "use trust_vc_types::Map;\n";

/// Two inserts at the SAME key with DIFFERENT values share their whole base and
/// their key; only the value distinguishes them. Structural keying on the
/// receiver would prove this false claim.
#[test]
fn map_insert_differing_value_false_is_counterexample() {
    let code = format!(
        "{MAP}
#[trust_vc::ensures(true)]
fn map_insert_diff_value(a: Map<u64, u64>, k: u64, v: u64, w: u64) {{
    trust_vc::assert!(trust_vc::ext_eq!(a.insert(k, v), a.insert(k, w)));
}}
"
    );
    let r = verify(&code, "map_insert_diff_value");
    assert!(
        counterexample(&r),
        "FALSE a.insert(k,v) =~= a.insert(k,w) must be a Counterexample, got {r:?}"
    );
}

/// `a.insert(k, v) =~= a` is false whenever `k` is outside `a`'s domain.
#[test]
fn map_insert_vs_own_operand_false_is_counterexample() {
    let code = format!(
        "{MAP}
#[trust_vc::ensures(true)]
fn map_insert_vs_operand(a: Map<u64, u64>, k: u64, v: u64) {{
    trust_vc::assert!(trust_vc::ext_eq!(a.insert(k, v), a));
}}
"
    );
    let r = verify(&code, "map_insert_vs_operand");
    assert!(
        counterexample(&r),
        "FALSE a.insert(k,v) =~= a must be a Counterexample, got {r:?}"
    );
}

/// TRUE twin: syntactic reflexivity of a compound operand.
#[test]
fn map_compound_reflexive_true_verifies() {
    let code = format!(
        "{MAP}
#[trust_vc::ensures(true)]
fn map_compound_refl(a: Map<u64, u64>, k: u64, v: u64) {{
    trust_vc::assert!(trust_vc::ext_eq!(a.insert(k, v), a.insert(k, v)));
}}
"
    );
    let r = verify(&code, "map_compound_refl");
    assert!(
        verified(&r),
        "TRUE a.insert(k,v) =~= a.insert(k,v) must verify, got {r:?}"
    );
}

/// TRUE twin: a genuine equality between STRUCTURALLY DIFFERENT expressions —
/// the last write at a repeated key wins.
#[test]
fn map_insert_twice_last_write_wins_true_verifies() {
    let code = format!(
        "{MAP}
#[trust_vc::ensures(true)]
fn map_insert_twice(a: Map<u64, u64>, k: u64, v: u64, w: u64) {{
    trust_vc::assert!(trust_vc::ext_eq!(a.insert(k, v).insert(k, w), a.insert(k, w)));
}}
"
    );
    let r = verify(&code, "map_insert_twice");
    assert!(
        verified(&r),
        "TRUE a.insert(k,v).insert(k,w) =~= a.insert(k,w) must verify, got {r:?}"
    );
}

// ══════════════════════════════════ Seq ═══════════════════════════════════
//
// Seq is probed at CONCRETE lengths. The symbolic-operand form
// (`a.add(b) =~= a.add(a)` for two `Seq<V>` parameters) builds a quantifier over
// a pointer-width BITVECTOR index (`build_seq_ext_eq`), and measured on this
// machine it does not return within ~20 minutes even with `--timeout 240` — so
// it is left unpinned rather than pinned as a hang. Non-termination is
// fail-closed, never a false `Verified`; it is recorded as a residual.

const SEQ: &str = "use trust_vc_types::Seq;\n";

/// Shared PREFIX, differing tail: `[x, y] =~= [x, x]` is false when `y != x`.
/// The Seq analogue of the reported multiset shape — a structural keying that
/// stopped at the shared prefix would prove it.
#[test]
fn seq_shared_prefix_differing_tail_false_is_counterexample() {
    let code = format!(
        "{SEQ}
#[trust_vc::requires(x != y)]
#[trust_vc::ensures(true)]
fn seq_shared_prefix(x: u64, y: u64) {{
    trust_vc::assert!(trust_vc::ext_eq!(
        Seq::<u64>::empty().push(x).push(y),
        Seq::<u64>::empty().push(x).push(x)
    ));
}}
"
    );
    let r = verify(&code, "seq_shared_prefix");
    assert!(
        counterexample(&r),
        "FALSE [x, y] =~= [x, x] under x != y must be a Counterexample, got {r:?}"
    );
}

/// TRUE twin: the same two-element shape with matching tails.
#[test]
fn seq_shared_prefix_matching_tail_true_verifies() {
    let code = format!(
        "{SEQ}
#[trust_vc::ensures(true)]
fn seq_shared_prefix_ok(x: u64, y: u64) {{
    trust_vc::assert!(trust_vc::ext_eq!(
        Seq::<u64>::empty().push(x).push(y),
        Seq::<u64>::empty().push(x).push(y)
    ));
}}
"
    );
    let r = verify(&code, "seq_shared_prefix_ok");
    assert!(
        verified(&r),
        "TRUE [x, y] =~= [x, y] must verify, got {r:?}"
    );
}

/// TRUE twin: structurally DISTINCT operands whose elements agree by hypothesis.
#[test]
fn seq_elementwise_hypothesis_true_verifies() {
    let code = format!(
        "{SEQ}
#[trust_vc::requires(x == y)]
#[trust_vc::ensures(true)]
fn seq_elementwise(x: u64, y: u64) {{
    trust_vc::assert!(trust_vc::ext_eq!(
        Seq::<u64>::empty().push(x),
        Seq::<u64>::empty().push(y)
    ));
}}
"
    );
    let r = verify(&code, "seq_elementwise");
    assert!(
        verified(&r),
        "TRUE [x] =~= [y] under x == y must verify, got {r:?}"
    );
}
