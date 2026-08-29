//! Permanent soundness guards: the cardinality of a DERIVED **Multiset** is not
//! the SOURCE multiset's cardinality (FV-3, Multiset arm).
//!
//! `4cfa9b19` closed this for `Set`/`Map`/`Seq::to_set` by marking the derived
//! result with `decline_collection_len`. The `Multiset` arm of the SAME dispatch
//! survived: `encode_union` / `encode_intersect` / `encode_difference`
//! (`ir_encoder/collection_set_map_inline.rs`) branch on
//! `resolve_receiver_kind`, and only the `_ =>` (Set) branch reached the
//! declining `encode_trust_vc_set_binary_op`. A `Multiset` receiver routed to
//! `encode_multiset_union` / `_intersect` / `_difference`, which registered
//! `CollectionMeta { len_term: None, .. }` and stopped there — so
//! `lookup_collection_len` fell through to its name fallback and answered with
//! the SOURCE multiset's length (`lowered_receiver_name` walks a chained
//! `CollectionOp` down to its base receiver).
//!
//! Fully INVERTED, not merely incomplete: with `a.len() == 2` and `b.len() == 3`,
//! `a.union(b).len() == 2` VERIFIED while the true `== 5` did not. `remove`, and
//! `insert` over an already-derived receiver, shared the shape; `is_empty()`
//! leaked through the same term.
//!
//! The fix declines at the single funnel `register_multiset_meta`, which every
//! Multiset result term passes through, and supplies the ONE exactly-computable
//! cell — `|a.union(b)| == |a| + |b|` (total multiplicity, pointwise sum) — so
//! the capability moves forward rather than back.
//!
//! NARROWNESS PINS live here too (`pin_*`): base cardinality, `insert`'s exact
//! `+1`, the new union additivity, and derived-multiset `count` (always encoded
//! correctly, via the compositional provenance) must all keep verifying.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::path::Path;
use trust_vc_core::ir::TrustVcType;
use trust_vc_core::vc::{ProofObligation, VerificationContext};
use trust_vc_core::{TrustVcResult, VerifyResult};

/// Two multisets with KNOWN, DIFFERENT cardinalities. Every "must not verify"
/// case below claims the derived collection still has `a`'s cardinality (2).
const DECLS: &[(&str, &str)] = &[("a", "Multiset<i32>"), ("b", "Multiset<i32>"), ("x", "i32")];
const ASSUMES: &[(&str, &str)] = &[("a2", "a.len() == 2"), ("b3", "b.len() == 3")];

fn verdict(expr: &str) -> VerifyResult {
    let mut ctx = VerificationContext::new();
    for (name, ty) in DECLS {
        ctx.declare_var_typed(name, TrustVcType::parse_or_opaque(ty));
    }
    for (n, e) in ASSUMES {
        ctx.push_obligation(ProofObligation::assume(*n, *e));
    }
    ctx.push_obligation(ProofObligation::assert("goal", expr));
    ctx.verify()
}

fn refutes(expr: &str) {
    let r = verdict(expr);
    assert!(
        !matches!(r, VerifyResult::Verified),
        "SOUNDNESS: a derived multiset's len must not be the source's len — \
         `{expr}` (with a.len()==2, b.len()==3) must not verify: {r:?}"
    );
}

fn proves(expr: &str) {
    let r = verdict(expr);
    assert!(
        matches!(r, VerifyResult::Verified),
        "NARROWNESS: `{expr}` (with a.len()==2, b.len()==3) is TRUE and must \
         still verify — declining everything is a capability disaster: {r:?}"
    );
}

// ───────────── CARDINAL: derived-multiset cardinality (must refute) ─────────────

/// The reproducer. `|a ∪ b| == |a| + |b| == 5`, never 2.
#[test]
fn multiset_union_len_must_not_inherit_source_len() {
    refutes("a.union(b).len() == 2");
}

/// `add` is Verus's spelling of multiset union and routes to the same encoder.
#[test]
fn multiset_add_len_must_not_inherit_source_len() {
    refutes("a.add(b).len() == 2");
}

/// Pointwise `min`: the intersection can be empty even when both operands are
/// large, so `|a ∩ b| == |a|` is not entailed.
#[test]
fn multiset_intersect_len_must_not_inherit_source_len() {
    refutes("a.intersect(b).len() == 2");
}

/// Pointwise saturating subtraction: `a.difference(a)` is empty.
#[test]
fn multiset_difference_len_must_not_inherit_source_len() {
    refutes("a.difference(b).len() == 2");
}

/// `sub` is the upstream spelling of `difference` — same encoder, same hole.
#[test]
fn multiset_sub_len_must_not_inherit_source_len() {
    refutes("a.sub(b).len() == 2");
}

/// `remove` drops one copy when the element is present, so the length is
/// `|a| - ite(count(a,x) > 0, 1, 0)`, not `|a|`.
#[test]
fn multiset_remove_len_must_not_inherit_source_len() {
    refutes("a.remove(x).len() == 2");
}

/// `is_empty()` reads the same length term, so it leaked identically:
/// `a.difference(a)` IS empty, so "not empty" must not verify.
#[test]
fn multiset_difference_is_empty_must_not_inherit_source_len() {
    refutes("a.difference(b).is_empty() == false");
}

// ── chains: the decline must survive one more link, or the fallback re-acquires
//    the base receiver's length one level down (the `Set::mk_map` shape) ──

#[test]
fn multiset_union_then_insert_len_must_not_leak() {
    refutes("a.union(b).insert(x).len() == 2");
}

#[test]
fn multiset_union_then_remove_len_must_not_leak() {
    refutes("a.union(b).remove(x).len() == 2");
}

#[test]
fn multiset_union_then_union_len_must_not_leak() {
    refutes("a.union(b).union(b).len() == 2");
}

#[test]
fn multiset_difference_then_insert_len_must_not_leak() {
    refutes("a.difference(b).insert(x).len() == 2");
}

/// `insert` computes `old + 1`, so over a DECLINED receiver it must decline too
/// rather than resolve `old` through the base receiver's name.
#[test]
fn multiset_intersect_then_insert_len_must_not_leak() {
    refutes("a.intersect(b).insert(x).len() == 2");
}

// ─────────────────────── NARROWNESS PINS (must verify) ───────────────────────

/// Base cardinality — the fallback these tests must not break.
#[test]
fn pin_base_multiset_len_still_verifies() {
    proves("a.len() == 2");
}

/// `insert` keeps its exact `+1` cardinality.
#[test]
fn pin_multiset_insert_len_still_verifies() {
    proves("a.insert(x).len() == 3");
}

/// The capability this fix ADDS: union is the one derived cell whose exact
/// cardinality is computable. Before the fix `a.union(b).len()` was `a.len()`,
/// so this TRUE claim did NOT verify.
#[test]
fn pin_multiset_union_len_is_additive() {
    proves("a.union(b).len() == 5");
}

/// Additivity must compose down a chain.
#[test]
fn pin_multiset_union_then_insert_len_is_exact() {
    proves("a.union(b).insert(x).len() == 6");
}

/// MEMBERSHIP/multiplicity on a derived multiset is encoded compositionally and
/// was always correct — the decline must not regress it.
#[test]
fn pin_derived_multiset_count_stays_sound() {
    proves("a.union(b).count(x) == a.count(x) + b.count(x)");
}

/// …and stays refutable in the false direction (the pin above is not vacuous).
#[test]
fn pin_derived_multiset_count_false_claim_refutes() {
    refutes("a.union(b).count(x) == a.count(x)");
}

// ───────────────── end-to-end through the production surface ─────────────────

fn verify_source(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    let dir = Path::new("target/derived_multiset_cardinality_soundness");
    fs::create_dir_all(dir).unwrap();
    let f = dir.join(format!("{name}.rs"));
    fs::write(&f, code).unwrap();
    trust_vc_core::verify_function_from_file(f.to_str().unwrap(), name)
}

/// The same cardinal defect on real `#[trust_vc::requires]` source — this is the
/// form the independent verifier reproduced through `cargo trust-vc check`.
#[test]
fn source_level_multiset_union_len_must_not_inherit_source_len() {
    let code = r#"
use trust_vc_types::Multiset;

#[trust_vc::requires(a.len() == 2usize)]
#[trust_vc::requires(b.len() == 3usize)]
#[trust_vc::ensures(true)]
fn source_level_multiset_union_len_must_not_inherit_source_len(a: Multiset<i32>, b: Multiset<i32>) {
    let u = a.union(b);
    trust_vc::assert!(u.len() == 2usize);
}
"#;
    let r = verify_source(
        code,
        "source_level_multiset_union_len_must_not_inherit_source_len",
    );
    assert!(
        !matches!(r, Ok(VerifyResult::Verified)),
        "SOUNDNESS: `a.union(b).len() == a.len()` must not verify at source level: {r:?}"
    );
}

/// Source-level narrowness pin: the TRUE additive claim verifies, so the guard
/// above is not passing because multisets stopped working entirely.
#[test]
fn source_level_multiset_union_len_additive_still_verifies() {
    let code = r#"
use trust_vc_types::Multiset;

#[trust_vc::requires(a.len() == 2usize)]
#[trust_vc::requires(b.len() == 3usize)]
#[trust_vc::ensures(true)]
fn source_level_multiset_union_len_additive_still_verifies(a: Multiset<i32>, b: Multiset<i32>) {
    let u = a.union(b);
    trust_vc::assert!(u.len() == 5usize);
}
"#;
    let r = verify_source(
        code,
        "source_level_multiset_union_len_additive_still_verifies",
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "NARROWNESS: the TRUE `|a ∪ b| == |a| + |b|` must verify at source level: {r:?}"
    );
}
