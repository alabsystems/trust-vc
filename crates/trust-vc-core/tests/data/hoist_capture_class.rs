// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
//! Fixture for the ENCODE-THEN-CLOSE BINDER-CAPTURE CLASS.
//!
//! Not one bug — a CLASS. Every spec-fn defining axiom, broadcast lemma and
//! trait-method axiom is built the same way:
//!
//! ```text
//!   let body = encode(expr);                     // bound vars are TOP-LEVEL terms
//!   solver.try_assert_term(solver.try_forall(&var_terms, body));
//! ```
//!
//! During `encode` there is no live solver binder — `real_quantifier_depth` is
//! 0 and `quantifier_scopes` is EMPTY — so nothing the encoder can consult says
//! a binder is coming. Any helper reached from that encode which mints a fresh
//! const and asserts its defining equation at the SOLVER TOP LEVEL leaves that
//! equation OUTSIDE the `forall` while the const it returned sits INSIDE:
//!
//! ```text
//!   (assert (= __c (g x)))                       ; x FREE here
//!   (assert (forall ((x S)) (= (f x) __c)))      ; ... BOUND here  => f is CONSTANT
//! ```
//!
//! A static sweep of `crates/trust-vc-core/src/encoder` finds **47 helpers on
//! `AstExpressionParser`** that mint a fresh const and reach a
//! `try_assert_term` in the same function, i.e. 47 candidate instances of this
//! shape. Two were measured to be live CARDINAL false verifies; both are pinned
//! below. The rest are closed by the general backstop in
//! `encoder::binder_capture`, which declines the axiom outright when a hoist
//! made during the body encode mentions a term the pending `forall` will bind.
//!
//! Goal shapes are chosen so trust-vc's own concrete evaluator CANNOT decide
//! them: either a hypothesis is in scope (which switches off the closed-ground
//! override in `typed_assertions::goal_is_closed_ground`), or the goal is a
//! `Forall` (which `is_datatype_eq_goal` rejects). Every verdict below is
//! therefore genuinely the emitted axiom's.

#![allow(dead_code, unused_variables)]

// ═════════ SITE 1 — datatype-valued `match` (`bind_datatype_match_result`) ══
// CLOSED BY INLINING: the helper returns the `ite` tree instead of a hoisted
// const, so the definition survives and the power controls still verify.

enum Color {
    Red,
    Green,
    Blue,
}

#[trust_vc::spec]
fn next(c: Color) -> Color {
    match c {
        Color::Red => Color::Green,
        Color::Green => Color::Blue,
        Color::Blue => Color::Red,
    }
}

// CARDINAL. FALSE: next(Red)=Green but next(Green)=Blue. Only a collapsed
// `forall c. next(c) == <top-level const>` proves it. A `Forall` goal, so no
// evaluator override can reach this verdict.
#[trust_vc::ensures(true)]
fn f_match_forall_constant() {
    trust_vc::assert!(forall|c: Color, d: Color| next(c) == next(d));
}

// CARDINAL, ground form under a hypothesis.
#[trust_vc::ensures(true)]
fn f_match_red_neq_green(x: Color) {
    trust_vc::assume!(x == Color::Red);
    trust_vc::assert!(next(Color::Red) != Color::Green);
}

// POWER CONTROL: the definition must survive the fix.
#[trust_vc::ensures(true)]
fn t_match_red_is_green(x: Color) {
    trust_vc::assume!(x == Color::Red);
    trust_vc::assert!(next(Color::Red) == Color::Green);
}

// ═════════ SITE 2 — Euclidean `/` and `%` (`purified_euclidean_div_mod_*`) ══
// CLOSED BY INLINING: under a pending closure the native `bvsdiv`/`Int` div
// term is kept instead of the hoisted `__euclid_q` / `__euclid_r` pair.
//
// This one was strictly worse than site 1. The ground replay of the same body
// pins the hoisted const to a SECOND value, so the axiom set becomes
// CONTRADICTORY and every goal mentioning the function verifies vacuously —
// `half(2) == 5` verified in 0.03 s on pristine.

#[trust_vc::spec]
fn half(n: int) -> int {
    n / 2
}

// CARDINAL, and the sharpest one: 2/2 == 1, never 5. A `Verified` here means
// the CONTEXT IS INCONSISTENT, not merely that `half` collapsed.
#[trust_vc::ensures(true)]
fn f_euclid_two_is_five(x: int) {
    trust_vc::assume!(x == 0);
    trust_vc::assert!(half(2) == 5);
}

// CARDINAL. FALSE: half(0)=0, half(2)=1.
#[trust_vc::ensures(true)]
fn f_euclid_zero_two(x: int) {
    trust_vc::assume!(x == 0);
    trust_vc::assert!(half(0) == half(2));
}

// CARDINAL, quantified form — no ground evaluator can touch it.
#[trust_vc::ensures(true)]
fn f_euclid_forall_constant() {
    trust_vc::assert!(forall|a: int, b: int| half(a) == half(b));
}

// POWER CONTROL: `half(2) == 1` must still verify, so the fix cannot be
// "drop the definition".
#[trust_vc::ensures(true)]
fn t_euclid_two_is_one(x: int) {
    trust_vc::assume!(x == 0);
    trust_vc::assert!(half(2) == 1);
}

#[trust_vc::spec]
fn parity(n: int) -> int {
    n % 2
}

// CARDINAL. FALSE: parity(0)=0, parity(1)=1.
#[trust_vc::ensures(true)]
fn f_parity_zero_one(x: int) {
    trust_vc::assume!(x == 0);
    trust_vc::assert!(parity(0) == parity(1));
}

// POWER CONTROL.
#[trust_vc::ensures(true)]
fn t_parity_one_is_one(x: int) {
    trust_vc::assume!(x == 0);
    trust_vc::assert!(parity(1) == 1);
}

// ═════════ SITE 3 — signedness reinterpretation (`reinterpret_bv_signedness`)
// CLOSED BY THE GENERAL BACKSTOP, NOT by inlining. `cast.rs` mints
// `__trust_vc_signedness_cast_N` and asserts its defining equation at the top
// level, guarded only by `is_quantifier_bound_term` — which consults the EMPTY
// `quantifier_scopes` and so never fires during an encode-then-close. Inlining
// it needs width bookkeeping the current non-hoisting branch gets wrong (it
// stamps the inner term with the CAST's signedness, surfacing as
// "sort metadata mismatch: IR declared Uint{32}, tracked width=32
// signed=true"), so instead the backstop DECLINES the whole defining axiom and
// `sflip` is left uninterpreted for symbolic reasoning.
//
// MEASURED CONSEQUENCE, stated rather than assumed: none of the TRUE goals
// below lost their proof. The ground-pool replay path re-encodes the body per
// concrete instance — it builds no binder, so it cannot be captured and the
// backstop never touches it — and it still decides `t_cast_one_is_one`,
// `t_cast_symbolic` and `t_cast_nonneg`. What IS still open is that this site
// is fail-closed rather than repaired; that is pinned as the `#[ignore]`d
// `known_open_signedness_cast_hoist_is_declined_not_inlined` in
// `tests/hoist_capture_class.rs`, which asserts on the decline trace itself
// rather than on a verdict.

#[trust_vc::spec]
fn sflip(x: u32) -> i32 {
    x as i32
}

// CARDINAL. FALSE: sflip(0)=0, sflip(1)=1.
#[trust_vc::ensures(true)]
fn f_cast_zero_one(x: u32) {
    trust_vc::assume!(x == 0);
    trust_vc::assert!(sflip(0) == sflip(1));
}

// CARDINAL, quantified form.
#[trust_vc::ensures(true)]
fn f_cast_forall_constant() {
    trust_vc::assert!(forall|a: u32, b: u32| sflip(a) == sflip(b));
}

// POWER CONTROL: TRUE, and MEASURED to still verify even though the defining
// axiom is declined (the ground-pool replay decides it).
#[trust_vc::ensures(true)]
fn t_cast_one_is_one(x: u32) {
    trust_vc::assume!(x == 0);
    trust_vc::assert!(sflip(1) == 1);
}

// ═════════ ISOLATION CONTROL — a spec fn with NO hoisting helper ═══════════
// Pure linear arithmetic: nothing mints a const, nothing is hoisted, so this
// pair must be unaffected in EVERY arm. It isolates the hoist as the cause.

#[trust_vc::spec]
fn dbl2(n: int) -> int {
    n + n
}

// FALSE: dbl2(0)=0, dbl2(1)=2.
#[trust_vc::ensures(true)]
fn f_clean_collapse(x: int) {
    trust_vc::assume!(x == 0);
    trust_vc::assert!(dbl2(0) == dbl2(1));
}

// TRUE.
#[trust_vc::ensures(true)]
fn t_clean_one_is_two(x: int) {
    trust_vc::assume!(x == 0);
    trust_vc::assert!(dbl2(1) == 2);
}

// ═════════ SYMBOLIC power probes ══════════════════════════════════════════
// Ground goals are still decided through the ground-pool replay path (it
// re-encodes the body per concrete instance, so it cannot be captured and the
// backstop does not touch it). These goals are SYMBOLIC in the spec fn's
// argument, so only the universally-closed defining axiom can decide them.
// They are the true measure of what declining that axiom costs.

// Needs `forall a. sflip(a) == a as i32` — the axiom the backstop declines.
#[trust_vc::ensures(true)]
fn t_cast_symbolic(a: u32) {
    trust_vc::assume!(a < 100u32);
    trust_vc::assert!(sflip(a) == a as i32);
}

// Same shape on an INLINED site: `forall n. half(n) == n / 2` must survive.
#[trust_vc::ensures(true)]
fn t_euclid_symbolic(a: int) {
    trust_vc::assume!(a >= 0);
    trust_vc::assert!(half(a) == a / 2);
}

// Same shape on the datatype-match site.
#[trust_vc::ensures(true)]
fn t_match_symbolic(c: Color) {
    trust_vc::assume!(c == Color::Green);
    trust_vc::assert!(next(c) == Color::Blue);
}

// Clean control.
#[trust_vc::ensures(true)]
fn t_clean_symbolic(a: int) {
    trust_vc::assume!(a >= 0);
    trust_vc::assert!(dbl2(a) == a + a);
}

// Harder symbolic probes: these need the CONTENT of the defining axiom, not
// just congruence, and they are not decidable by ground replay.
#[trust_vc::ensures(true)]
fn t_cast_nonneg(a: u32) {
    trust_vc::assume!(a < 100u32);
    trust_vc::assert!(sflip(a) >= 0i32);
}

// NOT PINNED, and deliberately kept as documentation: this shape hits a
// PRE-EXISTING and unrelated encoder limitation — `sort mismatch in apply:
// expected matching domain sort, got Int` — identically on pristine 7eb96392,
// on A1+A2 and on this amendment. It is here so a future reader does not
// mistake that error for a consequence of the declined `sflip` axiom.
#[trust_vc::ensures(true)]
fn t_cast_forall_nonneg() {
    trust_vc::assert!(forall|a: u32| a < 100u32 ==> sflip(a) >= 0i32);
}

#[trust_vc::ensures(true)]
fn t_euclid_forall_bound() {
    trust_vc::assert!(forall|a: int| a >= 0 ==> half(a) <= a);
}

#[trust_vc::ensures(true)]
fn t_match_forall_not_red() {
    trust_vc::assert!(forall|c: Color| next(c) != c);
}

// ═════════ SITE 4 — `choose` Skolem-witness axiom (`ir_encoder/choose.rs`) ══
// A closure BOUNDARY, wired in the same change that adds these probes: the
// condition is re-encoded with the witness standing in as an ordinary
// top-level term, then closed under `forall witness`. The re-encode now runs
// with `pending_universal_closure` set (so the euclid helper INLINES its
// div instead of hoisting `__euclid_q`), and any hoist that still mentions
// the witness DECLINES the Skolem axiom outright.

// MEASURED ON BOTH ARMS (pristine = trust-vc main encoder + ay f1f93ed25):
// both false-goal probes below COUNTEREXAMPLE on pristine as well, so no live
// CARDINAL was demonstrated at this site — the wiring is prophylactic closure
// of the same encode-then-close shape the measured sites had.
//
// Probe: the condition is UNSAT over nat — every int solution of
// `(0 - q) / 2 == 1` is negative — so the correct guarded Skolem axiom
// `forall w. (w >= 0 && cond(w)) ==> cond(result)` is VACUOUS and the assert
// must counterexample. A captured hoist lets the witness's defining equation
// escape the `w >= 0` range guard through the unconstrained top-level const,
// which can force `cond(result)` — UNSAT over a nat result — and poison the
// context. `x` + assume keeps the closed-ground evaluator out of the verdict.
#[trust_vc::ensures(true)]
fn f_choose_unsat_nat(x: int) {
    trust_vc::assume!(x == 0);
    let q: nat = trust_vc::choose!(|q: nat| (0 - q) / 2 == 1);
    trust_vc::assert!(1 == 2);
}

// Same shape with a SATISFIABLE condition: the context must stay consistent.
#[trust_vc::ensures(true)]
fn f_choose_sat_consistency(x: int) {
    trust_vc::assume!(x == 0);
    let a: int = trust_vc::choose!(|q: int| q / 2 == 1);
    trust_vc::assert!(1 == 2);
}

// NOT PINNED, measured on BOTH arms and reported rather than asserted. This
// goal is TRUE (the condition has witnesses, so the chosen value satisfies
// it). Pristine answers a FALSE COUNTEREXAMPLE in 0.03s — the hoisted-and-
// captured axiom denies the chosen value its property. The wired arm answers
// NotProved (incomplete quantifier-cegqi, 14.2s) — the flag makes the euclid
// literal INLINE to a native Int division inside the `forall` body, which
// ay's cegqi lane does not decide. Neither arm proves it; the wired arm's
// honest refusal replaces pristine's fabricated refutation, and a lost proof
// is the backstop's documented failure mode.
#[trust_vc::ensures(true)]
fn t_choose_witness_property(x: int) {
    trust_vc::assume!(x == 0);
    let a: int = trust_vc::choose!(|q: int| q / 2 == 1);
    trust_vc::assert!(a / 2 == 1);
}
