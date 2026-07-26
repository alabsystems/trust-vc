// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Soundness probe (round-4, proof/exec self-recursion class): a self-recursive
// #[trust_vc::proof] inherent method (or free proof fn) with a VALUE return and
// NO termination measure must NOT publish a usable single-return body axiom. The
// axiom `m(s,n) == m(s,n) + 1` is arithmetically `0 == 1`; published raw it lets
// ANY goal mentioning `m` verify vacuously.
//
// Verus admits a recursive definition's defining axiom only after discharging a
// `#[decreases]` termination proof. trust-vc fails closed structurally: a
// self-recursive body with no `#[decreases]` is registered uninterpreted (UF),
// emitting no body axiom. A well-founded recursive function WITH `#[decreases]`,
// and any non-recursive function, are unaffected.
//
// See vc_extraction.rs `self_recursive_body_axiom_unsound` and its two call sites
// (InherentMethodDef::from_impl_method, SiblingHelperDef::from_item_fn_with_name).

struct S;

impl S {
    // Ill-founded self-recursive inherent method, value return, NO decreases.
    #[trust_vc::proof]
    fn m(&self, n: u32) -> u32 {
        self.m(n) + 1u32
    }

    // Non-recursive inherent method: body axiom MUST still be published.
    #[trust_vc::proof]
    fn inc(&self, n: u32) -> u32 {
        n + 1u32
    }

    // Well-founded recursive inherent method WITH #[decreases]: body axiom MUST
    // still be published (valid termination measure annotated).
    #[trust_vc::proof]
    #[trust_vc::decreases(n)]
    fn cnt(&self, n: u32) -> u32 {
        if n == 0u32 {
            0u32
        } else {
            self.cnt(n - 1u32)
        }
    }
}

// Ill-founded self-recursive FREE proof fn, value return, NO decreases.
#[trust_vc::proof]
fn freem(n: u32) -> u32 {
    freem(n) + 1u32
}

// Non-recursive free helper: body axiom MUST still be published.
#[trust_vc::proof]
fn g(n: u32) -> u32 {
    n + 1u32
}

// Well-founded recursive FREE proof fn WITH #[decreases]: body axiom MUST publish.
#[trust_vc::proof]
#[trust_vc::decreases(n)]
fn fcnt(n: u32) -> u32 {
    if n == 0u32 {
        0u32
    } else {
        fcnt(n - 1u32)
    }
}

// ---- EXPLOITS: false goals that must NOT verify ----

// s.m(0) brings the contradictory axiom into scope; assert!(false) must NOT verify.
#[trust_vc::ensures(true)]
fn exploit_false(s: S) {
    let _z = s.m(0u32);
    trust_vc::assert!(false);
}

// Derived arithmetic false fact via the inherent-method axiom.
#[trust_vc::ensures(true)]
fn exploit_plus_100(s: S) {
    trust_vc::assert!(s.m(3u32) == s.m(3u32) + 100u32);
}

// Free self-recursive proof fn (sibling-helper body-axiom path).
#[trust_vc::ensures(true)]
fn exploit_free_false() {
    let _z = freem(0u32);
    trust_vc::assert!(false);
}

// ---- CONTROL: false goal with no recursive call (proves causation, not vacuity) ----

#[trust_vc::ensures(true)]
fn control_false_no_call() {
    trust_vc::assert!(false);
}

// ---- POSITIVE / NO-OVER-REJECTION: valid analogs that MUST still verify ----

// Non-recursive inherent-method definition is usable.
#[trust_vc::ensures(true)]
fn pos_inc(s: S) {
    trust_vc::assert!(s.inc(5u32) == 6u32);
}

// Well-founded recursive inherent method (base case) reduces.
#[trust_vc::ensures(true)]
fn pos_cnt_base(s: S) {
    trust_vc::assert!(s.cnt(0u32) == 0u32);
}

// Non-recursive free helper definition is usable.
#[trust_vc::ensures(true)]
fn pos_g() {
    let z = g(5u32);
    trust_vc::assert!(z == 6u32);
}

// Well-founded recursive free fn (base case) reduces.
#[trust_vc::ensures(true)]
fn pos_fcnt_base() {
    let z = fcnt(0u32);
    trust_vc::assert!(z == 0u32);
}

// A FALSE fact about the non-recursive free helper must NOT verify — proves g's
// body axiom is live (the positive verdicts are not vacuous).
#[trust_vc::ensures(true)]
fn neg_g_false() {
    let z = g(5u32);
    trust_vc::assert!(z == 7u32);
}
