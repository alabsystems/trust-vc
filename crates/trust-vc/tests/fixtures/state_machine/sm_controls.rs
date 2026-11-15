// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! D1a `state_machine!` CONTROLS: every case here must be Verified.
//!
//! Each control has a one-token-away twin in `sm_liars.rs` that must never
//! verify, and every transition/init has a satisfiability WITNESS here (a
//! concrete pre/post pair that satisfies the relation), so an always-false
//! relation — which would make the inductiveness lemmas vacuous — is caught.

#![allow(dead_code, unused_variables, non_snake_case)]

use trust_vc_types::{int, nat};

pub mod modes {
    use trust_vc_types::int;

    #[derive(PartialEq, Eq)]
    pub enum Mode {
        Idle,
        Busy(int),
    }
}

/// A datatype with NO `PartialEq` impl at all: spec `==` on it is structural.
pub enum Cmd {
    Nop,
    Set(int),
}

/// (h) A user item named `State`, with its own `invariant` method, plus a free
/// `tr1` — the names two generated machines would otherwise collide on.
pub struct State {
    pub u: int,
}

impl State {
    #[trust_vc::spec]
    pub fn invariant(&self) -> bool {
        self.u == 7
    }
}

#[trust_vc::spec]
pub fn tr1(pre: State, post: State) -> bool {
    post.u == pre.u * 2
}

/// (c) A file-root helper lemma an inductiveness proof calls.
#[trust_vc::proof]
#[trust_vc::requires(a >= 0 && b >= 1)]
#[trust_vc::ensures(a * b >= a)]
pub fn helper_mul_ge(a: int, b: int) {}

#[trust_vc::spec]
pub fn bump(v: int) -> int {
    v + 1
}

// ---------------------------------------------------------------------------
// (a)/(b)/(g)/(k) the main machine: the upstream `relation_codegen` shapes.

trust_vc::state_machine! { Ctl {
    fields {
        pub x: int,
        pub y: int,
        pub z: int,
    }

    init! {
        initialize(x: int, y: int, z: int) {
            require(y <= z);
            init x = x;
            init y = y;
            if x == y {
                init z = z;
            } else {
                init z = z + 1;
            }
        }
    }

    transition! {
        tr1(n: int) {
            require pre.y <= pre.z;
            require n >= 0;
            update z = pre.z + n;
        }
    }

    // (k) `require` AFTER an update is legal upstream and is conjoined.
    transition! {
        tr2(b: bool, c: bool) {
            if b {
                update z = pre.z + 1;
            }
            require c;
        }
    }

    // (g) a readonly transition: the frame is `post == pre` on every field.
    readonly! {
        r() {
            require pre.y <= pre.z;
        }
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        self.y <= self.z
    }

    #[inductive(initialize)]
    fn ctl_initialize_inductive(post: Self, x: int, y: int, z: int) {}

    #[inductive(tr1)]
    fn ctl_tr1_inductive(pre: Self, post: Self, n: int) {}

    #[inductive(tr2)]
    fn ctl_tr2_inductive(pre: Self, post: Self, b: bool, c: bool) {}
} }

// (d) the frame is visible to a client.
#[trust_vc::proof]
#[trust_vc::requires(Ctl::State::tr1(pre, post, n))]
#[trust_vc::ensures(post.x == pre.x && post.y == pre.y)]
fn ctl_frame(pre: Ctl::State, post: Ctl::State, n: int) {}

#[trust_vc::proof]
#[trust_vc::requires(Ctl::State::tr1(pre, post, n))]
#[trust_vc::ensures(post.z == pre.z + n && n >= 0 && pre.y <= pre.z)]
fn ctl_tr1_effect(pre: Ctl::State, post: Ctl::State, n: int) {}

// (b) the upstream `initialize` relation, read by a client.
#[trust_vc::proof]
#[trust_vc::requires(Ctl::State::initialize(post, 1, 2, 5))]
#[trust_vc::ensures(post.x == 1 && post.y == 2 && post.z == 6)]
fn ctl_init_branch(post: Ctl::State) {}

#[trust_vc::proof]
#[trust_vc::requires(Ctl::State::initialize(post, 3, 3, 5))]
#[trust_vc::ensures(post.z == 5)]
fn ctl_init_same_branch(post: Ctl::State) {}

// (g) the readonly frame.
#[trust_vc::proof]
#[trust_vc::requires(Ctl::State::r(pre, post))]
#[trust_vc::ensures(post.x == pre.x && post.y == pre.y && post.z == pre.z)]
fn ctl_readonly_frame(pre: Ctl::State, post: Ctl::State) {}

// (e) `next` elimination and introduction.
#[trust_vc::proof]
#[trust_vc::requires(Ctl::State::next(pre, post) && pre.y <= pre.z)]
#[trust_vc::ensures(post.x == pre.x && post.y == pre.y)]
fn ctl_next_elim(pre: Ctl::State, post: Ctl::State) {}

#[trust_vc::proof]
#[trust_vc::requires(pre.y <= pre.z && post.x == pre.x && post.y == pre.y && post.z == pre.z + 4)]
#[trust_vc::ensures(Ctl::State::next(pre, post))]
fn ctl_next_intro(pre: Ctl::State, post: Ctl::State) {}

// (k) the require-after-update relation.
#[trust_vc::proof]
#[trust_vc::requires(Ctl::State::tr2(pre, post, b, c) && b)]
#[trust_vc::ensures(c && post.z == pre.z + 1)]
fn ctl_tr2_effect(pre: Ctl::State, post: Ctl::State, b: bool, c: bool) {}

#[trust_vc::proof]
#[trust_vc::requires(Ctl::State::tr2(pre, post, b, c) && !b)]
#[trust_vc::ensures(c && post.z == pre.z)]
fn ctl_tr2_else_effect(pre: Ctl::State, post: Ctl::State, b: bool, c: bool) {}

// `_enabled` drops the postconditions.
#[trust_vc::proof]
#[trust_vc::requires(Ctl::State::tr1_enabled(pre, n))]
#[trust_vc::ensures(pre.y <= pre.z && n >= 0)]
fn ctl_enabled(pre: Ctl::State, n: int) {}

// SATISFIABILITY WITNESSES: a concrete pre/post pair per transition and init.
#[trust_vc::proof]
#[trust_vc::requires(pre.x == 1 && pre.y == 2 && pre.z == 5 && post.x == 1 && post.y == 2 && post.z == 8)]
#[trust_vc::ensures(Ctl::State::tr1(pre, post, 3))]
fn ctl_witness_tr1(pre: Ctl::State, post: Ctl::State) {}

#[trust_vc::proof]
#[trust_vc::requires(pre.x == 1 && pre.y == 2 && pre.z == 5 && post.x == 1 && post.y == 2 && post.z == 6)]
#[trust_vc::ensures(Ctl::State::tr2(pre, post, true, true))]
fn ctl_witness_tr2(pre: Ctl::State, post: Ctl::State) {}

#[trust_vc::proof]
#[trust_vc::requires(post.x == 1 && post.y == 2 && post.z == 6)]
#[trust_vc::ensures(Ctl::State::initialize(post, 1, 2, 5))]
fn ctl_witness_initialize(post: Ctl::State) {}

#[trust_vc::proof]
#[trust_vc::requires(pre.x == 1 && pre.y == 2 && pre.z == 5 && post.x == 1 && post.y == 2 && post.z == 5)]
#[trust_vc::ensures(Ctl::State::r(pre, post))]
fn ctl_witness_r(pre: Ctl::State, post: Ctl::State) {}

// ---------------------------------------------------------------------------
// (c) a lemma whose body calls a file-root helper lemma.

trust_vc::state_machine! { Hlp {
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

    #[invariant]
    pub fn hlp_inv(&self) -> bool {
        self.v >= 0
    }

    #[inductive(scale)]
    fn hlp_scale_inductive(pre: Self, post: Self, k: int) {
        helper_mul_ge(pre.v, k);
    }
} }

#[trust_vc::proof]
#[trust_vc::requires(pre.v == 3 && post.v == 12)]
#[trust_vc::ensures(Hlp::State::scale(pre, post, 4))]
fn hlp_witness_scale(pre: Hlp::State, post: Hlp::State) {}

// ---------------------------------------------------------------------------
// (f) datatype fields: a derived-PartialEq enum in an inline module and an
// enum with no `PartialEq` impl at all.

trust_vc::state_machine! { Dt {
    fields {
        pub m: modes::Mode,
        pub c: Cmd,
        pub n: int,
    }

    init! {
        start() {
            init m = modes::Mode::Idle;
            init c = Cmd::Nop;
            init n = 0;
        }
    }

    transition! {
        busy(v: int) {
            require v >= 0;
            update m = modes::Mode::Busy(v);
            update n = v;
        }
    }

    transition! {
        setc(v: int) {
            require v >= 0;
            update c = Cmd::Set(v);
            update n = bump(v);
        }
    }

    #[invariant]
    pub fn dt_inv(&self) -> bool {
        self.n >= 0
    }

    #[inductive(start)]
    fn dt_start_inductive(post: Self) {}

    #[inductive(busy)]
    fn dt_busy_inductive(pre: Self, post: Self, v: int) {}

    #[inductive(setc)]
    fn dt_setc_inductive(pre: Self, post: Self, v: int) {}
} }

#[trust_vc::proof]
#[trust_vc::requires(Dt::State::busy(pre, post, v))]
#[trust_vc::ensures(post.m == modes::Mode::Busy(v) && post.c == pre.c)]
fn dt_busy_effect(pre: Dt::State, post: Dt::State, v: int) {}

#[trust_vc::proof]
#[trust_vc::requires(Dt::State::setc(pre, post, v))]
#[trust_vc::ensures(post.c == Cmd::Set(v) && post.m == pre.m && post.n == v + 1)]
fn dt_setc_effect(pre: Dt::State, post: Dt::State, v: int) {}

#[trust_vc::proof]
#[trust_vc::requires(pre.n == 0 && post.n == 7 && post.m == modes::Mode::Busy(7) && post.c == pre.c)]
#[trust_vc::ensures(Dt::State::busy(pre, post, 7))]
fn dt_witness_busy(pre: Dt::State, post: Dt::State) {}

#[trust_vc::proof]
#[trust_vc::requires(post.n == 0 && post.m == modes::Mode::Idle && post.c == Cmd::Nop)]
#[trust_vc::ensures(Dt::State::start(post))]
fn dt_witness_start(post: Dt::State) {}

// ---------------------------------------------------------------------------
// (j) a `nat` transition parameter carries its range fact.

trust_vc::state_machine! { Natp {
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
#[trust_vc::requires(Natp::State::addk(pre, post, k))]
#[trust_vc::ensures(post.i >= pre.i)]
fn natp_monotone(pre: Natp::State, post: Natp::State, k: nat) {}

#[trust_vc::proof]
#[trust_vc::requires(Natp::State::next(pre, post))]
#[trust_vc::ensures(post.i >= pre.i)]
fn natp_next_monotone(pre: Natp::State, post: Natp::State) {}

#[trust_vc::proof]
#[trust_vc::requires(pre.i == 1 && post.i == 4)]
#[trust_vc::ensures(Natp::State::addk(pre, post, 3))]
fn natp_witness_addk(pre: Natp::State, post: Natp::State) {}

// ---------------------------------------------------------------------------
// (i) a machine with no invariant: `invariant()` is `true` and no
// inductiveness lemma is required.

trust_vc::state_machine! { NoInv {
    fields {
        pub q: int,
    }

    transition! {
        bumpq() {
            update q = pre.q + 1;
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::requires(NoInv::State::bumpq(pre, post))]
#[trust_vc::ensures(post.q == pre.q + 1 && post.invariant())]
fn noinv_true_invariant(pre: NoInv::State, post: NoInv::State) {}

// ---------------------------------------------------------------------------
// (h) a SECOND machine declaring the same transition and invariant names.

trust_vc::state_machine! { Two {
    fields {
        pub x: int,
        pub y: int,
        pub z: int,
    }

    transition! {
        tr1(n: int) {
            require n <= 0;
            update z = pre.z + n;
        }
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        self.z <= self.y
    }

    #[inductive(tr1)]
    fn two_tr1_inductive(pre: Self, post: Self, n: int) {}
} }

#[trust_vc::proof]
#[trust_vc::requires(Two::State::tr1(pre, post, n))]
#[trust_vc::ensures(post.z <= pre.z)]
fn two_tr1_effect(pre: Two::State, post: Two::State, n: int) {}

#[trust_vc::proof]
#[trust_vc::requires(a.invariant() && b.invariant())]
#[trust_vc::ensures(a.y <= a.z && b.z <= b.y)]
fn two_invariants_are_distinct(a: Ctl::State, b: Two::State) {}

#[trust_vc::proof]
#[trust_vc::requires(tr1(pre, post) && pre.invariant())]
#[trust_vc::ensures(post.u == 14)]
fn user_state_is_untouched(pre: State, post: State) {}

#[trust_vc::proof]
#[trust_vc::requires(pre.z == 1 && post.z == 0 && post.x == pre.x && post.y == pre.y)]
#[trust_vc::ensures(Two::State::tr1(pre, post, -1))]
fn two_witness_tr1(pre: Two::State, post: Two::State) {}
