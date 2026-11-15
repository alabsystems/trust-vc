// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A collection reached through a STRUCT FIELD must answer the same queries a
//! collection reached through a PARAMETER answers.
//!
//! A field read in a SPEC expression never becomes a place: `lower_field_access`
//! emits `TrustVcExpr::FnCall { name: <selector UF>, .. }`, so the receiver never
//! travelled the `encode_place` route that mints dom/len companions
//! (`ensure_projected_collection_meta`). Before this change `s.m.contains_key(k)`
//! answered
//!
//!     contains_key() not supported without dom tracking for '_anon'
//!
//! while the identical `Map` passed as a parameter verified. The companion is now
//! minted at the end of `encode_fn_call` and carried across `AstExpressionParser`
//! instances by `VerificationState::projected_collection_meta`.
//!
//! SOUNDNESS SHAPE. The minted dom is a FRESH array with no axiom tying it to the
//! collection value, so it can only ever answer what this query's own assumptions
//! pinned through the very same term. Every positive case below is therefore
//! paired with a LIAR TWIN that must still refute, and the framing witnesses at
//! the bottom pin what happens when the struct is written to.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(name: &str, src: &str, target: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_fdom_{}_{}.rs", std::process::id(), name));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), target).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

fn assert_verified(name: &str, src: &str, why: &str) {
    let r = verify(name, src, "t");
    assert!(r.is_verified(), "{why}, got: {r:?}");
}

fn assert_refuted(name: &str, src: &str, why: &str) {
    let r = verify(name, src, "t");
    assert!(
        !r.is_verified(),
        "{why} — a false claim must never verify, got: {r:?}"
    );
}

// ============================================================ the decisive pair

const PARAM_MAP: &str = r#"
use trust_vc_types::Map;
#[trust_vc::requires(m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(m: Map<u32, u32>) { trust_vc::assert!(m.contains_key(1u32)); }
"#;

const FIELD_MAP: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S) { trust_vc::assert!(s.m.contains_key(1u32)); }
"#;

#[test]
fn param_held_map_contains_key_verifies() {
    assert_verified(
        "param",
        PARAM_MAP,
        "a Map as a PARAMETER must discharge its own precondition",
    );
}

/// The gap. This is the case that errored before the fix.
#[test]
fn field_held_map_contains_key_verifies() {
    assert_verified(
        "field",
        FIELD_MAP,
        "a Map as a STRUCT FIELD must discharge its own precondition, exactly as a parameter does",
    );
}

// ====================================================== liar twins (trap 2)

const FIELD_MAP_LIAR_OTHER_KEY: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S) { trust_vc::assert!(s.m.contains_key(2u32)); }
"#;

const FIELD_MAP_LIAR_NEGATION: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S) { trust_vc::assert!(!s.m.contains_key(1u32)); }
"#;

#[test]
fn field_held_map_liar_on_another_key_refutes() {
    assert_refuted(
        "field_liar_key",
        FIELD_MAP_LIAR_OTHER_KEY,
        "membership of key 1 says nothing about key 2",
    );
}

#[test]
fn field_held_map_liar_negation_refutes() {
    assert_refuted(
        "field_liar_neg",
        FIELD_MAP_LIAR_NEGATION,
        "the negation of the precondition",
    );
}

// ===================================== the same gap on a length-bearing field

const FIELD_SEQ_LEN: &str = r#"
use trust_vc_types::Seq;
struct S { q: Seq<u32> }
#[trust_vc::requires(v.q.len() == 3int)]
#[trust_vc::ensures(true)]
fn t(v: S) { trust_vc::assert!(v.q.len() == 3int); }
"#;

const FIELD_SEQ_LEN_LIAR: &str = r#"
use trust_vc_types::Seq;
struct S { q: Seq<u32> }
#[trust_vc::requires(v.q.len() == 3int)]
#[trust_vc::ensures(true)]
fn t(v: S) { trust_vc::assert!(v.q.len() == 4int); }
"#;

/// The dom half of the defect had a length twin: a `Seq` field answered
/// "collection `_anon` has no tracked length".
#[test]
fn field_held_seq_len_verifies() {
    assert_verified(
        "field_seq_len",
        FIELD_SEQ_LEN,
        "a Seq as a STRUCT FIELD must carry a length companion",
    );
}

#[test]
fn field_held_seq_len_liar_refutes() {
    assert_refuted(
        "field_seq_len_liar",
        FIELD_SEQ_LEN_LIAR,
        "len 3 is not len 4",
    );
}

// ============================================ term identity, end to end (trap 1)

const TWO_OCCURRENCES: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::ensures(true)]
fn t(s: S, k: u32) {
    if s.m.contains_key(k) { trust_vc::assert!(s.m.contains_key(k)); }
}
"#;

const NESTED_FIELD_MAP: &str = r#"
use trust_vc_types::Map;
struct Inner { m: Map<u32, u32> }
struct Outer { i: Inner }
#[trust_vc::requires(o.i.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(o: Outer) { trust_vc::assert!(o.i.m.contains_key(1u32)); }
"#;

const FORALL_FIELD_MAP: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(forall(|k: u32| s.m.contains_key(k)))]
#[trust_vc::ensures(true)]
fn t(s: S) { trust_vc::assert!(s.m.contains_key(7u32)); }
"#;

/// Two occurrences of one field place must share one dom array, or the
/// entailment `p ==> p` stops being provable. The unit twin of this — asserting
/// the two occurrences encode to the same `Term` — is
/// `encoder::tests::parser_state_coverage::collections::same_field_place_encodes_to_same_term_and_same_dom`.
#[test]
fn two_occurrences_of_one_field_place_share_one_dom() {
    assert_verified(
        "two_occ",
        TWO_OCCURRENCES,
        "the same field place twice in one query must denote one collection",
    );
}

#[test]
fn nested_field_map_verifies() {
    assert_verified(
        "nested",
        NESTED_FIELD_MAP,
        "a field of a field is still one place",
    );
}

#[test]
fn quantified_field_map_instantiates() {
    assert_verified(
        "forall",
        FORALL_FIELD_MAP,
        "a universal over a field-held Map must instantiate at a ground key",
    );
}

// ================================================== framing witnesses (trap 3)
//
// `frame_state.rs` frames `{name}_dom` BY NAME, and a field dom has no name.
// What actually happens, measured, is that the field dom is keyed by the
// selector application over the ROOT variable's term, so it cannot outlive a
// write to the root: any construct that re-keys or havocs the root yields a
// DIFFERENT carrier term and therefore a fresh, unconstrained companion. The
// direction of that failure is refusal, never a stale answer. These three
// witnesses pin it; if any of them ever starts VERIFYING, a stale dom is being
// read and the fix has become a false-verify factory.
//
// A write through a Map field CAN arise, so this does not rest on an upstream
// refusal of a projected Map receiver. Field ASSIGNMENT is not rejected:
// `s.m = other` lowers fine and the query simply REFUTES, as do a conditional write (`if c { s.m = other; }`) and a nested one
// (`o.i.m = other`) — NOT-VERIFIED, not an error. What vc_extraction rejects is a
// ghost METHOD RECEIVER that is not a direct variable ("Vec::remove receiver is
// unsupported in vc_extraction: `q`"), and that fires on a LET-LOCAL too, not only
// on a projection. So the reason is the carrier-term keying below, not an upstream
// refusal. The three witnesses are what actually pin it.

const MUT_REF_CLOBBER: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::ensures(true)]
fn clobber(s: &mut S) { }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S) {
    let mut s = s;
    clobber(&mut s);
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

const LOOP_REBIND: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S, other: S) {
    let mut s = s;
    let mut i = 0u32;
    while i < 3u32 { trust_vc::invariant!(i <= 3u32); s = other; i = i + 1u32; }
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

const STRUCT_REBUILD: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S) {
    let u = S { m: s.m };
    trust_vc::assert!(u.m.contains_key(1u32));
}
"#;

/// A call that may write the whole struct must NOT leave the pre-call dom
/// readable. `clobber` promises nothing about `s.m`.
#[test]
fn field_dom_does_not_survive_a_mut_ref_call() {
    assert_refuted(
        "clobber",
        MUT_REF_CLOBBER,
        "a &mut call that promises nothing about the field",
    );
}

/// A loop that reassigns the root must NOT leave the pre-loop dom readable.
#[test]
fn field_dom_does_not_survive_a_loop_that_rebinds_the_root() {
    assert_refuted(
        "loop_rebind",
        LOOP_REBIND,
        "the loop reassigns `s` from an unconstrained `other`",
    );
}

/// The honest cost of keying by carrier term: rebuilding the struct around the
/// SAME field value produces a different carrier, so the companion does not
/// follow. Refusal, not a wrong answer — pinned so the incompleteness is a
/// recorded decision rather than a surprise.
#[test]
fn field_dom_does_not_follow_a_struct_rebuild() {
    assert_refuted(
        "rebuild",
        STRUCT_REBUILD,
        "`S { m: s.m }` is a different carrier term",
    );
}

// ================================================== aliasing witnesses
//
// The file above pins that ONE place
// keeps ONE dom; these pin the converse, which is the worse failure: two DIFFERENT
// places must never share one. If any of them starts VERIFYING, the companion is
// being keyed by something coarser than the carrier term and the encoder is
// manufacturing equalities that do not hold.

const TWO_STRUCT_VALUES: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s1.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s1: S, s2: S) { trust_vc::assert!(s2.m.contains_key(1u32)); }
"#;

const TWO_FIELDS_ONE_VALUE: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32>, n: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S) { trust_vc::assert!(s.n.contains_key(1u32)); }
"#;

const TWO_NESTED_SIBLINGS: &str = r#"
use trust_vc_types::Map;
struct Inner { m: Map<u32, u32> }
struct Outer { i: Inner, j: Inner }
#[trust_vc::requires(o.i.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(o: Outer) { trust_vc::assert!(o.j.m.contains_key(1u32)); }
"#;

const FIELD_NAME_VS_PARAM_NAME: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S, m: Map<u32, u32>) { trust_vc::assert!(m.contains_key(1u32)); }
"#;

#[test]
fn two_struct_values_do_not_share_one_field_dom() {
    assert_refuted(
        "two_values",
        TWO_STRUCT_VALUES,
        "`s1.m` and `s2.m` are two carriers",
    );
}

#[test]
fn two_fields_of_one_value_do_not_share_one_dom() {
    assert_refuted(
        "two_fields",
        TWO_FIELDS_ONE_VALUE,
        "`s.m` and `s.n` are two selectors",
    );
}

#[test]
fn two_nested_siblings_do_not_share_one_dom() {
    assert_refuted(
        "two_nested",
        TWO_NESTED_SIBLINGS,
        "`o.i.m` and `o.j.m` differ in the inner selector",
    );
}

#[test]
fn a_field_dom_does_not_leak_into_a_parameter_of_the_same_name() {
    assert_refuted(
        "name_shadow",
        FIELD_NAME_VS_PARAM_NAME,
        "the companion is term-keyed; `lookup_collection_dom`'s `{name}_dom` \
         fallback must not be reached through the field's spelling",
    );
}

// =============================================== field WRITES
//
// A write through a Map field is not rejected by vc_extraction; it refutes.
// These three pin the REFUSAL so the paragraph above is a control and not
// just a note.

const FIELD_ASSIGN: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S, other: Map<u32, u32>) { let mut s = s; s.m = other; trust_vc::assert!(s.m.contains_key(1u32)); }
"#;

const FIELD_ASSIGN_CONDITIONAL: &str = r#"
use trust_vc_types::Map;
struct S { m: Map<u32, u32> }
#[trust_vc::requires(s.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(s: S, other: Map<u32, u32>, c: bool) {
    let mut s = s;
    if c { s.m = other; }
    trust_vc::assert!(s.m.contains_key(1u32));
}
"#;

const FIELD_ASSIGN_NESTED: &str = r#"
use trust_vc_types::Map;
struct Inner { m: Map<u32, u32> }
struct Outer { i: Inner }
#[trust_vc::requires(o.i.m.contains_key(1u32))]
#[trust_vc::ensures(true)]
fn t(o: Outer, other: Map<u32, u32>) { let mut o = o; o.i.m = other; trust_vc::assert!(o.i.m.contains_key(1u32)); }
"#;

#[test]
fn a_field_assignment_kills_the_field_dom() {
    assert_refuted(
        "field_assign",
        FIELD_ASSIGN,
        "`s.m = other` replaces the map with an unconstrained one",
    );
}

#[test]
fn a_conditional_field_assignment_kills_the_field_dom() {
    assert_refuted(
        "field_assign_cond",
        FIELD_ASSIGN_CONDITIONAL,
        "the write happens on one branch, so the fact does not survive the merge",
    );
}

#[test]
fn a_nested_field_assignment_kills_the_inner_dom() {
    assert_refuted(
        "field_assign_nested",
        FIELD_ASSIGN_NESTED,
        "`o.i.m = other` replaces the inner map",
    );
}
