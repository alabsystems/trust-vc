// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! D1a `state_machine!` GATED cases: every machine here is refused, and every
//! client that mentions one fails closed with the pinned message.
//!
//! The clients are what the suite addresses: a refused machine is replaced by
//! a marker item, so the file still parses and every OTHER function in it is
//! still verified.

#![allow(dead_code, unused_variables, non_snake_case)]

use trust_vc_types::{int, nat};

pub struct Liar {
    pub a: int,
}

impl PartialEq for Liar {
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}

pub struct Holder {
    pub inner: Liar,
}

pub enum Rec {
    Nil,
    Cons(Rec),
}

pub struct Gen<T> {
    pub a: T,
}

pub struct Floaty {
    pub a: f64,
}

// --- field types ----------------------------------------------------------

trust_vc::state_machine! { FNat {
    fields { pub t: nat }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_nat_field(s: FNat::State) {}

trust_vc::state_machine! { FU32 {
    fields { pub t: u32 }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_u32_field(s: FU32::State) {}

trust_vc::state_machine! { FUsize {
    fields { pub t: usize }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_usize_field(s: FUsize::State) {}

trust_vc::state_machine! { FF64 {
    fields { pub t: f64 }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_f64_field(s: FF64::State) {}

trust_vc::state_machine! { FSeq {
    fields { pub t: Seq<int> }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_seq_field(s: FSeq::State) {}

trust_vc::state_machine! { FMap {
    fields { pub t: Map<int, int> }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_map_field(s: FMap::State) {}

trust_vc::state_machine! { FEq {
    fields { pub t: Liar }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_manual_eq_field(s: FEq::State) {}

trust_vc::state_machine! { FEqHolder {
    fields { pub t: Holder }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_manual_eq_via_holder(s: FEqHolder::State) {}

trust_vc::state_machine! { FRec {
    fields { pub t: Rec }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_recursive_field(s: FRec::State) {}

trust_vc::state_machine! { FGen {
    fields { pub t: Gen }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_generic_field(s: FGen::State) {}

trust_vc::state_machine! { FFloat {
    fields { pub t: Floaty }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_float_bearing_field(s: FFloat::State) {}

// --- statements and expressions -------------------------------------------

trust_vc::state_machine! { SAssert {
    fields { pub t: int }

    transition! {
        tr() {
            assert pre.t >= 0;
            update t = pre.t + 1;
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_assert(s: SAssert::State) {}

trust_vc::state_machine! { SMatch {
    fields { pub t: int }

    transition! {
        tr(b: bool) {
            match b {
                _ => { update t = 1; }
            }
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_match(s: SMatch::State) {}

trust_vc::state_machine! { SProperty {
    fields { pub t: int }

    property! {
        p() {
            require pre.t >= 0;
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_property(s: SProperty::State) {}

trust_vc::state_machine! { SRequireLet {
    fields { pub t: int }

    transition! {
        tr(b: bool) {
            require let true = b;
            update t = 1;
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_require_let(s: SRequireLet::State) {}

trust_vc::state_machine! { SBirdsEye {
    fields { pub t: int }

    transition! {
        tr() {
            birds_eye let x = 5;
            update t = x;
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_birds_eye(s: SBirdsEye::State) {}

trust_vc::state_machine! { SSharding {
    fields { pub t: int }

    transition! {
        tr() {
            add t += (1);
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_sharding_op(s: SSharding::State) {}

trust_vc::state_machine! { SSubUpdate {
    fields { pub t: int }

    transition! {
        tr() {
            update t.g = 1;
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_sub_update(s: SSubUpdate::State) {}

trust_vc::state_machine! { SDivision {
    fields { pub t: int }

    transition! {
        tr() {
            update t = pre.t / 2;
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_division(s: SDivision::State) {}

trust_vc::state_machine! { SCast {
    fields { pub t: int }

    transition! {
        tr(x: int) {
            update t = x as int;
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_cast(s: SCast::State) {}

trust_vc::state_machine! { SBarePre {
    fields { pub t: int }

    transition! {
        tr() {
            update t = pre;
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_bare_pre(s: SBarePre::State) {}

trust_vc::state_machine! { SUnknownCall {
    fields { pub t: int }

    transition! {
        tr() {
            update t = unknown_helper(1);
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_unknown_call(s: SUnknownCall::State) {}

// --- lemma / invariant attribute attacks ----------------------------------

trust_vc::state_machine! { ARequiresFalse {
    fields { pub t: int }

    transition! {
        tr() {
            update t = pre.t + 1;
        }
    }

    #[invariant]
    pub fn inv(&self) -> bool {
        self.t == 5
    }

    #[inductive(tr)]
    #[trust_vc::requires(false)]
    fn a_requires_false_inductive(pre: Self, post: Self) {}
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_lemma_requires_false(s: ARequiresFalse::State) {}

trust_vc::state_machine! { ASatisfiableRequires {
    fields { pub t: int }

    transition! {
        tr() {
            update t = pre.t + 1;
        }
    }

    #[invariant]
    pub fn inv(&self) -> bool {
        self.t == 5
    }

    #[inductive(tr)]
    #[trust_vc::requires(pre.t < 0)]
    fn a_satisfiable_requires_inductive(pre: Self, post: Self) {}
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_lemma_satisfiable_requires(s: ASatisfiableRequires::State) {}

trust_vc::state_machine! { AExternalBody {
    fields { pub t: int }

    transition! {
        tr() {
            update t = pre.t + 1;
        }
    }

    #[invariant]
    pub fn inv(&self) -> bool {
        self.t == 5
    }

    #[inductive(tr)]
    #[trust_vc::external_body]
    fn a_external_body_inductive(pre: Self, post: Self) {}
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_lemma_external_body(s: AExternalBody::State) {}

trust_vc::state_machine! { AVerifierExternalBody {
    fields { pub t: int }

    transition! {
        tr() {
            update t = pre.t + 1;
        }
    }

    #[invariant]
    pub fn inv(&self) -> bool {
        self.t == 5
    }

    #[inductive(tr)]
    #[verifier::external_body]
    fn a_verifier_external_body_inductive(pre: Self, post: Self) {}
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_lemma_verifier_external_body(s: AVerifierExternalBody::State) {}

trust_vc::state_machine! { ACfgAttr {
    fields { pub t: int }

    transition! {
        tr() {
            update t = pre.t + 1;
        }
    }

    #[invariant]
    pub fn inv(&self) -> bool {
        self.t == 5
    }

    #[inductive(tr)]
    #[cfg_attr(any(), trust_vc::requires(false))]
    fn a_cfg_attr_inductive(pre: Self, post: Self) {}
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_lemma_cfg_attr(s: ACfgAttr::State) {}

trust_vc::state_machine! { ARequiresMacro {
    fields { pub t: int }

    transition! {
        tr() {
            update t = pre.t + 1;
        }
    }

    #[invariant]
    pub fn inv(&self) -> bool {
        self.t == 5
    }

    #[inductive(tr)]
    fn a_requires_macro_inductive(pre: Self, post: Self) {
        trust_vc::requires!(false);
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_lemma_requires_macro(s: ARequiresMacro::State) {}

trust_vc::state_machine! { AInvariantAttr {
    fields { pub t: int }

    #[invariant]
    #[trust_vc::opaque]
    pub fn inv(&self) -> bool {
        self.t == 5
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_invariant_attr(s: AInvariantAttr::State) {}

trust_vc::state_machine! { AInvariantStmts {
    fields { pub t: int }

    #[invariant]
    pub fn inv(&self) -> bool {
        let x = 5;
        self.t == x
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_invariant_statements(s: AInvariantStmts::State) {}

// --- structure ------------------------------------------------------------

trust_vc::state_machine! { SHelper {
    fields { pub t: int }

    fn helper() -> int {
        3
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_helper_fn(s: SHelper::State) {}

trust_vc::state_machine! { SLabel {
    fields { pub t: int }

    pub struct Label {}
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_label(s: SLabel::State) {}

trust_vc::state_machine! { SPreParam {
    fields { pub t: int }

    transition! {
        tr(pre: int) {
            update t = 1;
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_pre_param(s: SPreParam::State) {}

trust_vc::state_machine! { SGenerated {
    fields { pub __TvcSm_x: int }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_generated_prefix(s: SGenerated::State) {}

trust_vc::tokenized_state_machine! { TokMachine {
    fields {
        #[sharding(variable)]
        pub t: int,
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_tokenized(s: TokMachine::State) {}

// --- ungenerated paths on an ADMITTED machine -----------------------------

trust_vc::state_machine! { Ok1 {
    fields { pub t: int }

    transition! {
        tr() {
            update t = pre.t + 1;
        }
    }

    #[invariant]
    pub fn ok_inv(&self) -> bool {
        self.t >= 0
    }

    #[inductive(tr)]
    fn ok1_tr_inductive(pre: Self, post: Self) {}
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_step_path(s: Ok1::Step) {}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_show_path(s: Ok1::State) {
    Ok1::show::tr(s);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_ufcs_invariant(s: Ok1::State) {
    let _b = Ok1::State::invariant(s);
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn gate_next_by(s: Ok1::State) {
    let _b = Ok1::State::next_by(s, s);
}

/// The admitted machine in this file still verifies: a refused sibling does
/// not take the whole file down.
#[trust_vc::proof]
#[trust_vc::requires(Ok1::State::tr(pre, post))]
#[trust_vc::ensures(post.t == pre.t + 1)]
fn refusals_file_still_verifies_ok1(pre: Ok1::State, post: Ok1::State) {}

// --- an INDIRECT reference: a helper whose BODY mentions a refused machine --
//
// The client never spells the machine itself, so it carries no poison ident of
// its own; it fails closed one level down, when the helper's body axiom cannot
// be lowered. Pinned because "fails closed" is the property, not the message.

#[trust_vc::spec]
pub fn helper_mentioning_a_refused_machine(a: int) -> bool {
    FNat::State::tr_enabled(a)
}

#[trust_vc::proof]
#[trust_vc::requires(helper_mentioning_a_refused_machine(a))]
#[trust_vc::ensures(a >= 0)]
fn gate_indirect_reference(a: int) {}
