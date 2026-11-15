// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! D1a `state_machine!` LIARS: none of these may ever be Verified.
//!
//! Each is one token away from a control in `sm_controls.rs`, so the pair is a
//! mutation-sensitive discriminator: if the relation compiler drops the frame,
//! a require, a branch guard or the implicit-else continuation, the matching
//! liar starts verifying.

#![allow(dead_code, unused_variables, non_snake_case)]

use trust_vc_types::{int, nat};

// ---------------------------------------------------------------------------
// (a') the inductiveness lemma of a transition that breaks the invariant.

trust_vc::state_machine! { LiarInd {
    fields {
        pub y: int,
        pub z: int,
    }

    transition! {
        tr1(n: int) {
            require pre.y <= pre.z;
            require n >= 0;
            update y = pre.y + 2;
        }
    }

    #[invariant]
    pub fn liar_inv(&self) -> bool {
        self.y <= self.z
    }

    #[inductive(tr1)]
    fn liar_tr1_inductive(pre: Self, post: Self, n: int) {}
} }

// (b') an init that sets `y > z` on one branch only.
trust_vc::state_machine! { LiarInit {
    fields {
        pub y: int,
        pub z: int,
    }

    init! {
        initialize(b: bool) {
            if b {
                init y = 0;
                init z = 1;
            } else {
                init y = 5;
                init z = 1;
            }
        }
    }

    #[invariant]
    pub fn liar_init_inv(&self) -> bool {
        self.y <= self.z
    }

    #[inductive(initialize)]
    fn liar_initialize_inductive(post: Self, b: bool) {}
} }

// (b'') the same init liar without a parameter: no existential binder is
// involved, so the refutation is a ground counterexample.
trust_vc::state_machine! { LiarInit2 {
    fields {
        pub y: int,
        pub z: int,
    }

    init! {
        initialize() {
            init y = 5;
            init z = 1;
        }
    }

    #[invariant]
    pub fn liar_init2_inv(&self) -> bool {
        self.y <= self.z
    }

    #[inductive(initialize)]
    fn liar_initialize2_inductive(post: Self) {}
} }

// (e') the implicit-else continuation: the update falls through the one-sided
// `if`, and only the fall-through breaks the invariant.
trust_vc::state_machine! { LiarImplicitElse {
    fields {
        pub y: int,
        pub z: int,
    }

    transition! {
        tr(c: bool) {
            if c {
                require pre.y + 1 <= pre.z;
            }
            update z = pre.z - 1;
        }
    }

    #[invariant]
    pub fn lie_inv(&self) -> bool {
        self.y <= self.z
    }

    #[inductive(tr)]
    fn liar_implicit_else_inductive(pre: Self, post: Self, c: bool) {}
} }

// (p1)/(p2) per-path liars: the else path alone breaks the invariant.
trust_vc::state_machine! { LiarPath {
    fields {
        pub y: int,
        pub z: int,
    }

    transition! {
        tr(b: bool) {
            if b {
                update z = pre.z + 1;
            } else {
                update z = pre.z - 1;
            }
        }
    }

    #[invariant]
    pub fn path_inv(&self) -> bool {
        self.y <= self.z
    }

    #[inductive(tr)]
    fn liar_path_inductive(pre: Self, post: Self, b: bool) {}
} }

/// The OTHER path verifies on its own: the liar is about one path, not about
/// the whole relation being useless.
#[trust_vc::proof]
#[trust_vc::requires(LiarPath::State::tr(pre, post, b) && b && pre.y <= pre.z)]
#[trust_vc::ensures(post.y <= post.z)]
fn path_then_branch_is_sound(pre: LiarPath::State, post: LiarPath::State, b: bool) {}

// (i') a let whose substitution a client gets wrong.
trust_vc::state_machine! { LetSub {
    fields {
        pub z: int,
    }

    transition! {
        tr() {
            let m = pre.z + 1;
            update z = m + 1;
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::requires(LetSub::State::tr(pre, post))]
#[trust_vc::ensures(post.z == pre.z + 2)]
fn letsub_control(pre: LetSub::State, post: LetSub::State) {}

#[trust_vc::proof]
#[trust_vc::requires(LetSub::State::tr(pre, post))]
#[trust_vc::ensures(post.z == pre.z + 1)]
fn letsub_liar(pre: LetSub::State, post: LetSub::State) {}

// (j') a lemma whose body assumes `false`.
trust_vc::state_machine! { AssumeFalse {
    fields {
        pub z: int,
    }

    transition! {
        tr() {
            update z = pre.z - 1;
        }
    }

    #[invariant]
    pub fn af_inv(&self) -> bool {
        self.z >= 0
    }

    #[inductive(tr)]
    fn assume_false_inductive(pre: Self, post: Self) {
        trust_vc::assume!(false);
    }
} }

// (m') a false lemma plus a client that calls it: the client verifies
// MODULARLY, which is exactly why the suite's lemma-conjunction rule exists.
trust_vc::state_machine! { FalseLemma {
    fields {
        pub z: int,
    }

    transition! {
        tr() {
            update z = pre.z - 1;
        }
    }

    #[invariant]
    pub fn fl_inv(&self) -> bool {
        self.z >= 0
    }

    #[inductive(tr)]
    fn false_lemma_inductive(pre: Self, post: Self) {}
} }

#[trust_vc::proof]
#[trust_vc::requires(pre.invariant() && FalseLemma::State::tr_strong(pre, post))]
#[trust_vc::ensures(post.z >= 0)]
fn calls_the_false_lemma(pre: FalseLemma::State, post: FalseLemma::State) {
    FalseLemma::State::false_lemma_inductive(pre, post);
}

// ---------------------------------------------------------------------------
// Client liars against the CONTROL machines' shapes, re-declared here so the
// two fixtures stay independently runnable.

trust_vc::state_machine! { Ctl2 {
    fields {
        pub x: int,
        pub y: int,
        pub z: int,
    }

    transition! {
        tr1(n: int) {
            require pre.y <= pre.z;
            require n >= 0;
            update z = pre.z + n;
        }
    }

    transition! {
        tr2(b: bool, c: bool) {
            if b {
                update z = pre.z + 1;
            }
            require c;
        }
    }

    readonly! {
        r() {
            require pre.y <= pre.z;
        }
    }
} }

// (d') the frame, off by one.
#[trust_vc::proof]
#[trust_vc::requires(Ctl2::State::tr1(pre, post, n))]
#[trust_vc::ensures(post.x == pre.x + 1)]
fn ctl2_frame_liar(pre: Ctl2::State, post: Ctl2::State, n: int) {}

// (d'') the then-branch effect claimed under the else condition.
#[trust_vc::proof]
#[trust_vc::requires(Ctl2::State::tr2(pre, post, b, c) && !b)]
#[trust_vc::ensures(post.z == pre.z + 1)]
fn ctl2_branch_liar(pre: Ctl2::State, post: Ctl2::State, b: bool, c: bool) {}

// (h') the dropped-require liar: the relation must be FALSE when the
// enabling condition fails.
#[trust_vc::proof]
#[trust_vc::requires(pre.y > pre.z)]
#[trust_vc::ensures(Ctl2::State::tr1(pre, post, n))]
fn ctl2_dropped_require_liar(pre: Ctl2::State, post: Ctl2::State, n: int) {}

// The control twin: the relation really is unsatisfiable there.
#[trust_vc::proof]
#[trust_vc::requires(pre.y > pre.z)]
#[trust_vc::ensures(!Ctl2::State::tr1(pre, post, n))]
fn ctl2_dropped_require_control(pre: Ctl2::State, post: Ctl2::State, n: int) {}

// (w') a witness twin with one post field wrong.
#[trust_vc::proof]
#[trust_vc::requires(pre.x == 1 && pre.y == 2 && pre.z == 5 && post.x == 9 && post.y == 2 && post.z == 8)]
#[trust_vc::ensures(Ctl2::State::tr1(pre, post, 3))]
fn ctl2_witness_liar(pre: Ctl2::State, post: Ctl2::State) {}

// The readonly frame, off by one.
#[trust_vc::proof]
#[trust_vc::requires(Ctl2::State::r(pre, post))]
#[trust_vc::ensures(post.z == pre.z + 1)]
fn ctl2_readonly_liar(pre: Ctl2::State, post: Ctl2::State) {}

// (n') a `next` introduction whose only witness would need a negative `nat`.
trust_vc::state_machine! { Natp2 {
    fields {
        pub i: int,
    }

    transition! {
        addk(k: nat) {
            update i = pre.i + k;
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::requires(post.i == pre.i - 1)]
#[trust_vc::ensures(Natp2::State::next(pre, post))]
fn natp2_negative_witness_liar(pre: Natp2::State, post: Natp2::State) {}

// (q') cross-machine: one machine's invariant must not be readable as
// another's.
#[trust_vc::proof]
#[trust_vc::requires(a.invariant())]
#[trust_vc::ensures(a.z >= 0)]
fn crosstalk_liar(a: LiarPath::State) {}

// ---------------------------------------------------------------------------
// Twins for the three controls under which ay logs a REJECTED UNSAT
// certificate while still publishing the result.
//
// MEASURED 2026-09-17, and PRE-EXISTING (not a D1a effect): while
// `hlp_scale_inductive`, `natp_monotone` and `user_state_is_untouched` run, ay
// prints `MODEL-UNCONFIRMED [UNCONFIRMED/published] … computed UNSAT rejected
// by mandatory strict certification: … EufCongruentPred: predicate symbols
// differ`, and trust-vc reports `Verified`. The HEAD lens (the untouched tree)
// prints the SAME lines, with the same counts (4 / 6 / 4), on HAND-WRITTEN
// Rust of the same shape and no `state_machine!` anywhere: a spec relation
// over struct fields combined with `*` on `int` or a `nat` parameter. The
// existing corpus simply never carried that shape, so D1a is the first
// material to reach it — it is not what introduced it, and refusing these
// shapes would hide a solver-side question behind a D1a restriction rather
// than answer it. `user_state_is_untouched` makes that plain without leaving
// the tree: its `State`, `tr1` and `invariant` are the USER's own hand-written
// items in `sm_controls.rs`, with no generated code anywhere in the obligation.
//
// What protects the claim meanwhile is the discriminator, so each of the three
// controls gets its twin here. If a published-but-uncertified UNSAT ever did
// become a false Verified, these are what turn red.

trust_vc::state_machine! { LiarCert {
    fields {
        pub v: int,
    }

    transition! {
        scale(k: int) {
            require pre.v >= 0;
            require k >= 1;
            update v = pre.v * k;
        }
    }

    // FALSE of the relation: `v * k` is unbounded above.
    #[invariant]
    pub fn liarcert_inv(&self) -> bool {
        self.v <= 10
    }

    #[inductive(scale)]
    fn liarcert_scale_inductive(pre: Self, post: Self, k: int) {}
} }

/// The GROUND half of the `hlp_scale_inductive` twin: concrete `pre.v` and
/// `k`, so the refutation needs no quantifier reasoning and comes back as a
/// counterexample rather than an incompleteness.
#[trust_vc::proof]
#[trust_vc::requires(pre.v == 2 && LiarCert::State::scale(pre, post, 3))]
#[trust_vc::ensures(post.v == 7)]
fn liarcert_scale_effect_liar(pre: LiarCert::State, post: LiarCert::State) {}

/// Its control: the RIGHT product.
#[trust_vc::proof]
#[trust_vc::requires(pre.v == 2 && LiarCert::State::scale(pre, post, 3))]
#[trust_vc::ensures(post.v == 6)]
fn liarcert_scale_effect_control(pre: LiarCert::State, post: LiarCert::State) {}

// The `natp_monotone` twin: `+ k` with `k: nat` is monotone, not STRICTLY so.
trust_vc::state_machine! { LiarCertNat {
    fields {
        pub i: int,
    }

    transition! {
        addk(k: nat) {
            update i = pre.i + k;
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::requires(LiarCertNat::State::addk(pre, post, k))]
#[trust_vc::ensures(post.i > pre.i)]
fn liarcert_natp_strict_liar(pre: LiarCertNat::State, post: LiarCertNat::State, k: nat) {}

// The `user_state_is_untouched` twin: a user struct and a free spec relation
// over `*`, with the wrong product claimed.
pub struct LiarCertState {
    pub u: int,
}

impl LiarCertState {
    #[trust_vc::spec]
    pub fn invariant(&self) -> bool {
        self.u == 7
    }
}

#[trust_vc::spec]
pub fn liarcert_tr1(pre: LiarCertState, post: LiarCertState) -> bool {
    post.u == pre.u * 2
}

#[trust_vc::proof]
#[trust_vc::requires(liarcert_tr1(pre, post) && pre.invariant())]
#[trust_vc::ensures(post.u == 15)]
fn liarcert_user_state_liar(pre: LiarCertState, post: LiarCertState) {}

/// The other half of that pair: the same premises with the RIGHT product.
#[trust_vc::proof]
#[trust_vc::requires(liarcert_tr1(pre, post) && pre.invariant())]
#[trust_vc::ensures(post.u == 14)]
fn liarcert_user_state_control(pre: LiarCertState, post: LiarCertState) {}
