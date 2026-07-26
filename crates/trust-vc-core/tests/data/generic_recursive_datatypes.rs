// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Source fixtures for GENERIC self-recursive datatype support + its soundness
// battery. See `generic_recursive_datatypes.rs` (the integration test) for the
// per-function expectations and their rationale.

#![allow(dead_code, unused_variables)]

// ── generic cons-list (self-recursive enum carrying a generic payload) ──────
enum GList<T> {
    GNil,
    GCons(T, Box<GList<T>>),
}

// ── generic binary tree (TWO self-recursive children) ───────────────────────
enum GTree<T> {
    GLeaf(T),
    GBranch(Box<GTree<T>>, Box<GTree<T>>),
}

// ── generic no-base-case enum: every variant recurses → FAIL-CLOSED ─────────
enum GStream<T> {
    GMore(T, Box<GStream<T>>),
}

// ── generic mutual recursion → FAIL-CLOSED (no cross RecursiveRef inlined) ──
enum GEven<T> {
    GEZero,
    GESucc(T, Box<GOdd<T>>),
}
enum GOdd<T> {
    GOSucc(T, Box<GEven<T>>),
}

// ── generic negative position (fn(Self) field) → FAIL-CLOSED ────────────────
enum GNegPos<T> {
    GBase,
    GFn(fn(GNegPos<T>) -> T),
}

// ══════════════════════════ spec functions ═════════════════════════════════

// Generic recursive spec fn over GList<T>, WITH a #[decreases] measure.
#[trust_vc::spec]
#[trust_vc::decreases(xs)]
fn glen<T>(xs: GList<T>) -> nat {
    match xs {
        GList::GNil => 0,
        GList::GCons(_, rest) => (1 + glen(*rest)) as nat,
    }
}

// Generic recursive spec fn over GList<T> WITHOUT #[decreases]: its defining
// axiom must stay SUPPRESSED (uninterpreted helper, no unsound equation).
#[trust_vc::spec]
fn glen_bad<T>(xs: GList<T>) -> nat {
    match xs {
        GList::GNil => 0,
        GList::GCons(_, rest) => (1 + glen_bad(*rest)) as nat,
    }
}

// Generic NON-recursive predicate over GList<T> (no decreases needed; trusted).
#[trust_vc::spec]
fn gis_empty<T>(xs: GList<T>) -> bool {
    match xs {
        GList::GNil => true,
        GList::GCons(_, _) => false,
    }
}

// Builtin List<i32> as a SOURCE-PARSED recursive spec-fn param (the monomorphic
// naming-bug fix).
#[trust_vc::spec]
#[trust_vc::decreases(xs)]
fn blen(xs: List<i32>) -> nat {
    match xs {
        List::Nil => 0,
        List::Cons(_, rest) => (1 + blen(*rest)) as nat,
    }
}

// Builtin Tree<i32> as a SOURCE-PARSED spec-fn param, NON-recursive (a branching
// tree-size diverges in ay's e-matching — a pre-existing solver limitation that
// `recursive_structural_decreases.rs` also avoids — so we exercise the carrier /
// naming fix without triggering it).
#[trust_vc::spec]
fn troot(t: Tree<i32>) -> i32 {
    match t {
        Tree::Leaf(v) => v,
        Tree::Branch(_, _) => 0,
    }
}

// Spec fns over the fail-closed generic datatypes (probe extraction errors).
#[trust_vc::spec]
fn gstream_probe(s: GStream<i32>) -> bool {
    true
}
#[trust_vc::spec]
fn geven_probe(e: GEven<i32>) -> bool {
    true
}
#[trust_vc::spec]
fn gnegpos_probe(n: GNegPos<i32>) -> bool {
    true
}

// ═══════════════════ TRUE generic goals (must Verify) ══════════════════════

#[trust_vc::ensures(true)]
fn t_glen_zero() {
    trust_vc::assert!(glen::<i32>(GList::GNil) == 0);
}

#[trust_vc::ensures(true)]
fn t_glen_one() {
    trust_vc::assert!(glen(GList::GCons(5i32, Box::new(GList::GNil))) == 1);
}

// Structural-descent over a GENERIC recursive datatype: needs the unfolding
// axiom to fire twice.
#[trust_vc::ensures(true)]
fn t_glen_two() {
    trust_vc::assert!(
        glen(GList::GCons(5i32, Box::new(GList::GCons(6i32, Box::new(GList::GNil))))) == 2
    );
}

// Same generic spec fn at a DIFFERENT instantiation (GList<bool>): distinct
// per-instantiation carrier, verifies independently.
#[trust_vc::ensures(true)]
fn t_glen_bool_one() {
    trust_vc::assert!(glen(GList::GCons(true, Box::new(GList::GNil))) == 1);
}

#[trust_vc::ensures(true)]
fn t_gis_empty_nil() {
    trust_vc::assert!(gis_empty::<i32>(GList::GNil) == true);
}

#[trust_vc::ensures(true)]
fn t_gis_empty_cons() {
    trust_vc::assert!(gis_empty(GList::GCons(9i32, Box::new(GList::GNil))) == false);
}

// Generic constructor/selector disjointness (native datatype theory, no axiom).
#[trust_vc::ensures(true)]
fn t_gtree_disjoint() {
    trust_vc::assert!(
        GTree::GBranch(Box::new(GTree::GLeaf(1i32)), Box::new(GTree::GLeaf(2i32)))
            != GTree::GLeaf(1i32)
    );
}

// Builtin List<i32> structural recursion as a source-parsed spec fn.
#[trust_vc::ensures(true)]
fn t_blen_one() {
    trust_vc::assert!(blen(List::Cons(5i32, Box::new(List::Nil))) == 1);
}

// Builtin Tree<i32> source-parsed spec fn (non-recursive).
#[trust_vc::ensures(true)]
fn t_troot_leaf() {
    trust_vc::assert!(troot(Tree::Leaf(7i32)) == 7);
}

// Generic acyclicity (positive dt_size witness): no GList<i32> equals its own
// GCons. VALID (UNSAT of `xs == GCons(h, xs)` via dt_size), so it must Verify.
#[trust_vc::ensures(true)]
fn t_gacyclic(xs: GList<i32>, h: i32) {
    trust_vc::assert!(xs != GList::GCons(h, Box::new(xs)));
}

// ═══════════════════ FALSE generic goals (never Verified) ══════════════════

#[trust_vc::ensures(true)]
fn f_glen_one_wrong() {
    trust_vc::assert!(glen(GList::GCons(5i32, Box::new(GList::GNil))) == 2);
}

#[trust_vc::ensures(true)]
fn f_glen_zero_wrong() {
    trust_vc::assert!(glen::<i32>(GList::GNil) == 1);
}

#[trust_vc::ensures(true)]
fn f_gis_empty_wrong() {
    trust_vc::assert!(gis_empty(GList::GCons(9i32, Box::new(GList::GNil))) == true);
}

// ═══════════ CYCLIC generic claim (never Verified — acyclicity) ═════════════
// `xs == GCons(h, xs)` holds for NO GList (dt_size). Asserting it must be
// REFUTED (Counterexample), never proved.
#[trust_vc::ensures(true)]
fn c_gassert_cycle(xs: GList<i32>, h: i32) {
    trust_vc::assert!(xs == GList::GCons(h, Box::new(xs)));
}

// Assume a cyclic generic structure, then try to prove a concrete arithmetic
// falsehood about an unrelated value. The engine must NOT build a cyclic model.
#[trust_vc::ensures(true)]
fn c_gcycle_assume_then_false(xs: GList<i32>, h: i32) {
    trust_vc::assume!(xs == GList::GCons(h, Box::new(xs)));
    trust_vc::assert!(0u64 == 1u64);
}

// ════════ ill-founded generic recursion: NO unsound axiom (no false) ════════
#[trust_vc::ensures(true)]
fn g_glen_bad_no_false() {
    trust_vc::assert!(glen_bad(GList::GCons(5i32, Box::new(GList::GNil))) == glen_bad(GList::GCons(5i32, Box::new(GList::GNil))));
    trust_vc::assert!(0u64 == 1u64);
}

// ════════ DISTINCT-instantiation conflict in ONE function → fail-closed ═════
// Constructing BOTH GList<i32> and GList<bool> and calling glen on each: the
// per-instantiation carrier cannot collapse to a single helper symbol, so glen
// is left uninterpreted and the structural goal does NOT verify (sound).
#[trust_vc::ensures(true)]
fn t_conflict_no_false() {
    trust_vc::assert!(glen(GList::GCons(5i32, Box::new(GList::GNil))) == 1);
    trust_vc::assert!(glen(GList::GCons(true, Box::new(GList::GNil))) == 1);
    trust_vc::assert!(0u64 == 1u64);
}

// ─────────── fail-closed generic datatypes (extraction/encoding error) ───────
#[trust_vc::ensures(true)]
fn use_gstream(s: GStream<i32>) {
    trust_vc::assert!(gstream_probe(s));
}
#[trust_vc::ensures(true)]
fn use_geven(e: GEven<i32>) {
    trust_vc::assert!(geven_probe(e));
}
#[trust_vc::ensures(true)]
fn use_gnegpos(n: GNegPos<i32>) {
    trust_vc::assert!(gnegpos_probe(n));
}
