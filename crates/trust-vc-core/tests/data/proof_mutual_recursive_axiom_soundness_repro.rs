// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Soundness probe (round-8, mutual-recursion broadcast/proof lemma class): two
// proof/broadcast lemmas with NO #[decreases] that call EACH OTHER publish
// contradictory defining `ensures` axioms. `la` proves `ensures op(i)` only by
// trusting `lb`'s (equally unproven) `ensures op(i)` and vice-versa; the cycle
// is ill-founded, so the postcondition `op(i)` is certified for ALL `i`. An
// external caller of `la` then trusts `op(3) = (3 > 100) = false` and verifies a
// false goal.
//
// The direct-self-recursion gate `self_recursive_body_axiom_unsound`
// (block_contains_self_call + !has_decreases) catches `la` calling `la`, but NOT
// the mutual cycle `la -> lb -> la`. The fix generalizes it to a full recursion
// CYCLE check (`ill_founded_recursive_function_names`): a function in a cycle
// where some member lacks `#[decreases]` may NOT publish its `ensures` or its
// single-return body axiom (treated uninterpreted / call is an opaque no-op).
//
// Verus rejects mutually-recursive proof fns lacking a discharged `decreases`.
// A WELL-FOUNDED cycle (every member carries `#[decreases]`) and any
// non-recursive lemma are unaffected (no over-rejection).
//
// See vc_extraction.rs `ill_founded_recursive_function_names` and its consumers
// (`collect_referenced_sibling_helper_contracts` for the call-site `ensures`,
// `SiblingHelperDef::from_item_fn_with_name` /
// `InherentMethodDef::from_impl_method` for the body axiom).

#[trust_vc::spec]
#[trust_vc::opaque]
fn op(i: u32) -> bool {
    i > 100u32
}

// ---- THE HOLE: ill-founded mutual recursion, no decreases ----

// Mutually-recursive BROADCAST lemma pair (findings 15-16).
#[trust_vc::broadcast]
#[trust_vc::trigger(op(i))]
#[trust_vc::ensures(op(i))]
fn la(i: u32) {
    lb(i);
}

#[trust_vc::broadcast]
#[trust_vc::trigger(op(i))]
#[trust_vc::ensures(op(i))]
fn lb(i: u32) {
    la(i);
}

// External caller: brings `la`'s (ill-founded) ensures into scope; op(3) is
// genuinely FALSE, so this must NOT verify.
#[trust_vc::ensures(true)]
fn exploit_broadcast_mutual() {
    la(3u32);
    trust_vc::assert!(op(3u32));
}

// Plain #[proof] (no #[broadcast]) mutual pair — same hole.
#[trust_vc::proof]
#[trust_vc::ensures(op(i))]
fn pa(i: u32) {
    pb(i);
}

#[trust_vc::proof]
#[trust_vc::ensures(op(i))]
fn pb(i: u32) {
    pa(i);
}

#[trust_vc::ensures(true)]
fn exploit_proof_mutual() {
    pa(3u32);
    trust_vc::assert!(op(3u32));
}

// Direct self-recursion, ensures, no decreases — its OWN postcondition already
// fails (existing gate), but an EXTERNAL caller used to still trust its ensures.
#[trust_vc::proof]
#[trust_vc::ensures(op(i))]
fn ps(i: u32) {
    ps(i);
}

#[trust_vc::ensures(true)]
fn exploit_self_external() {
    ps(3u32);
    trust_vc::assert!(op(3u32));
}

// Three-function cycle c1 -> c2 -> c3 -> c1 — the hole is not limited to 2-cycles.
#[trust_vc::proof]
#[trust_vc::ensures(op(i))]
fn c1(i: u32) {
    c2(i);
}

#[trust_vc::proof]
#[trust_vc::ensures(op(i))]
fn c2(i: u32) {
    c3(i);
}

#[trust_vc::proof]
#[trust_vc::ensures(op(i))]
fn c3(i: u32) {
    c1(i);
}

#[trust_vc::ensures(true)]
fn exploit_cycle3() {
    c1(3u32);
    trust_vc::assert!(op(3u32));
}

// Value-returning mutual recursion (sibling-helper BODY axiom):
// fa(n) == fb(n)+1, fb(n) == fa(n)  =>  fa(n) == fa(n)+1  =>  false.
#[trust_vc::proof]
fn fa(n: u32) -> u32 {
    fb(n) + 1u32
}

#[trust_vc::proof]
fn fb(n: u32) -> u32 {
    fa(n)
}

#[trust_vc::ensures(true)]
fn exploit_value_mutual() {
    let z = fa(3u32);
    trust_vc::assert!(z == fa(3u32) + 100u32);
}

// ---- CONTROL (causation, not vacuity): op(3) unprovable without a lemma ----
#[trust_vc::ensures(true)]
fn control_no_lemma() {
    trust_vc::reveal(op);
    trust_vc::assert!(op(3u32));
}

// ---- NO OVER-REJECTION: well-founded / non-recursive analogs MUST verify ----

// An OPAQUE predicate the caller can only learn via a trusted ensures.
#[trust_vc::spec]
#[trust_vc::opaque]
fn p(i: u32) -> bool {
    true
}

// Well-founded SELF-recursive lemma WITH #[decreases], opaque ensures: its
// ensures must STILL be trusted at an external caller (NOT suppressed).
#[trust_vc::proof]
#[trust_vc::decreases(i)]
#[trust_vc::ensures(p(i))]
fn wf_self(i: u32) {
    trust_vc::reveal(p);
    if i == 0u32 {
    } else {
        wf_self(i - 1u32);
    }
}

#[trust_vc::ensures(true)]
fn caller_wf_self() {
    wf_self(3u32);
    trust_vc::assert!(p(3u32));
}

// Well-founded MUTUAL pair WITH #[decreases] on both members (true ensures): the
// cycle is termination-guarded, so it must NOT be suppressed.
#[trust_vc::spec]
fn tt(i: u32) -> bool {
    true
}

#[trust_vc::proof]
#[trust_vc::decreases(i)]
#[trust_vc::ensures(tt(i))]
fn wa(i: u32) {
    if i == 0u32 {
    } else {
        wb(i - 1u32);
    }
}

#[trust_vc::proof]
#[trust_vc::decreases(i)]
#[trust_vc::ensures(tt(i))]
fn wb(i: u32) {
    if i == 0u32 {
    } else {
        wa(i - 1u32);
    }
}

#[trust_vc::ensures(true)]
fn caller_wellfounded_mutual() {
    wa(3u32);
    trust_vc::assert!(tt(3u32));
}

// ---- S1: bogus (non-shrinking) #[decreases] on a mutual cycle ----
// Both members carry #[decreases(i)] so the STRUCTURAL Stage-1 gate passes, but the
// measure does NOT shrink on the `bogus_b -> bogus_a` edge (it passes the SAME `i`),
// so it is NOT a valid per-edge termination measure — Verus rejects it. The semantic
// Stage-2 proof must catch this and suppress the circular `ensures op(i)`; otherwise
// `bogus_a(3)` publishes `op(3) = (3 > 100) = false` and the exploit verifies a false
// goal (the round-8 findings 15-16 hole, decreases-bearing variant).
#[trust_vc::proof]
#[trust_vc::decreases(i)]
#[trust_vc::ensures(op(i))]
fn bogus_a(i: u32) {
    bogus_b(i);
}

#[trust_vc::proof]
#[trust_vc::decreases(i)]
#[trust_vc::ensures(op(i))]
fn bogus_b(i: u32) {
    bogus_a(i);
}

#[trust_vc::ensures(true)]
fn exploit_bogus_decreases_mutual() {
    bogus_a(3u32);
    trust_vc::assert!(op(3u32));
}

// ---- S2: recursion cycle routed through function-item VALUES ----
// `fv_a` and `fv_b` call each other through `let f = partner; f(i)` rather than a
// direct call, so the direct-call recursion graph misses the edge. With NO
// #[decreases] the cycle is ill-founded; the exploit's DIRECT call to `fv_a` trusts
// its `ensures op(i)`, so unless `fv_a` is detected as an ill-founded cycle member (and
// its ensures cleared), op(3) = (3 > 100) = false verifies.
#[trust_vc::proof]
#[trust_vc::ensures(op(i))]
fn fv_a(i: u32) {
    let f = fv_b;
    f(i);
}

#[trust_vc::proof]
#[trust_vc::ensures(op(i))]
fn fv_b(i: u32) {
    let g = fv_a;
    g(i);
}

#[trust_vc::ensures(true)]
fn exploit_fnvalue_mutual() {
    fv_a(3u32);
    trust_vc::assert!(op(3u32));
}

// The outer binding must be restored after the nested block, and aliases (including
// a same-name shadow whose initializer sees the old binding) must resolve to the
// original function item. A flat binding map misses both cycle edges.
#[trust_vc::proof]
#[trust_vc::ensures(op(i))]
fn fv_shadow_alias_a(i: u32) {
    let f = fv_shadow_alias_b;
    {
        let f = fv_id;
        f(i);
    }
    let alias = f;
    alias(i);
}

#[trust_vc::proof]
#[trust_vc::ensures(op(i))]
fn fv_shadow_alias_b(i: u32) {
    let f = fv_shadow_alias_a;
    let f = f;
    f(i);
}

#[trust_vc::ensures(true)]
fn exploit_fnvalue_shadow_alias_mutual() {
    fv_shadow_alias_a(3u32);
    trust_vc::assert!(op(3u32));
}

// Assignment invalidates the statically-known function-item target. Here the
// initial harmless leaf is replaced by a recursive partner; retaining the stale
// leaf binding makes the real cycle disappear from the source graph.
#[trust_vc::proof]
#[trust_vc::ensures(op(i))]
fn fv_reassign_a(i: u32) {
    let mut f = fv_id;
    if i > 0u32 {
        f = fv_reassign_b;
    }
    f(i);
}

#[trust_vc::proof]
#[trust_vc::ensures(op(i))]
fn fv_reassign_b(i: u32) {
    fv_reassign_a(i);
}

#[trust_vc::ensures(true)]
fn exploit_fnvalue_reassignment() {
    fv_reassign_a(3u32);
    trust_vc::assert!(op(3u32));
}

// A source cycle whose signature cannot be reconstructed by the semantic
// termination checker must fail closed. Both members have a syntactic decreases
// marker, but reference parameters are intentionally outside MemberTermInfo's
// modeled surface; accepting `None` here publishes the circular false ensures.
#[trust_vc::proof]
#[trust_vc::decreases(i)]
#[trust_vc::ensures(op(3u32))]
fn ref_decreases_a(i: &u32) {
    ref_decreases_b(i);
}

#[trust_vc::proof]
#[trust_vc::decreases(i)]
#[trust_vc::ensures(op(3u32))]
fn ref_decreases_b(i: &u32) {
    ref_decreases_a(i);
}

#[trust_vc::ensures(true)]
fn exploit_unmodelable_ref_decreases(i: &u32) {
    ref_decreases_a(i);
    trust_vc::assert!(op(3u32));
}

// No over-rejection: a NON-cyclic call through a fn-item value must still be usable.
// `fv_id`'s opaque ensures must stay trusted at the caller (it is not recursive).
#[trust_vc::proof]
#[trust_vc::ensures(p(i))]
fn fv_id(i: u32) {
    trust_vc::reveal(p);
}

#[trust_vc::ensures(true)]
fn caller_fnvalue_noncyclic() {
    // A fn-item value bound and called (adds a caller -> fv_id graph edge) but fv_id is
    // a non-recursive leaf, so no cycle forms and nothing is suppressed. The DIRECT
    // call brings fv_id's ensures p(i) into scope (fn-value calls do not resolve
    // ensures — a separate, pre-existing capability gap).
    let f = fv_id;
    f(3u32);
    fv_id(3u32);
    trust_vc::assert!(p(3u32));
}

// Control for the scoped/alias collector: the same binding shapes used by the
// negative sentinel remain non-recursive when every resolved target is a leaf.
#[trust_vc::proof]
#[trust_vc::ensures(p(i))]
fn fv_alias_shadow_nonrecursive(i: u32) {
    trust_vc::reveal(p);
    let f = fv_id;
    {
        let f = fv_id;
        f(i);
    }
    let alias = f;
    alias(i);
}

#[trust_vc::ensures(true)]
fn caller_fnvalue_alias_shadow_nonrecursive() {
    fv_alias_shadow_nonrecursive(3u32);
    trust_vc::assert!(p(3u32));
}

// Non-recursive proof lemma proving an OPAQUE predicate: ensures stays live.
#[trust_vc::proof]
#[trust_vc::ensures(p(i))]
fn nr_lemma(i: u32) {
    trust_vc::reveal(p);
}

#[trust_vc::ensures(true)]
fn caller_nonrec_opaque() {
    nr_lemma(3u32);
    trust_vc::assert!(p(3u32));
}

// Control for the non-recursive opaque case: without the lemma, p(3) is unknown.
#[trust_vc::ensures(true)]
fn control_nonrec_opaque() {
    trust_vc::assert!(p(3u32));
}

// Non-recursive value-returning helper body axiom must stay live: inc(5) == 6.
#[trust_vc::proof]
fn inc(n: u32) -> u32 {
    n + 1u32
}

#[trust_vc::ensures(true)]
fn caller_value_nonrec() {
    let z = inc(5u32);
    trust_vc::assert!(z == 6u32);
}
