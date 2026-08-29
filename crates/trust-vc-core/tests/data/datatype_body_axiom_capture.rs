// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixture for the BINDER-CAPTURE defect in the spec-fn defining axiom.
//
// `add_typed_broadcast` (and `fuel::encode_fuel_axioms`) encode a spec fn's
// body FIRST — with every bound variable resolved as an ordinary top-level
// term — and only then close a `forall` over those terms. While that encode
// runs there is no live solver binder, so `real_quantifier_depth` is 0 and
// nothing in the encoder could tell that a binder was coming. Any helper that
// hoisted a derived fact to the SOLVER TOP LEVEL therefore had that fact
// captured by the `forall` built afterwards.
//
// `ir_encoder::match_encode::bind_datatype_match_result` did exactly that for a
// datatype-valued `match`: it minted a fresh top-level const `m`, asserted
// `m == ite(..)` plus every tester/selector link at the top level, and returned
// `m` as the match's value. The emitted defining axiom therefore came out as
//
//     (assert (forall ((c Color)) (= (next c) __trust_vc_match_dt_N)))
//
// with `__trust_vc_match_dt_N` a top-level `declare-const` — i.e. "next is a
// CONSTANT FUNCTION". That is a CARDINAL false verify: it proves
// `next(Red) == next(Green)`, which is false (`Green` vs `Blue`).
//
// Every goal below is stated UNDER A HYPOTHESIS on purpose. A bare goal is
// closed and ground, so `typed_assertions::goal_is_closed_ground` lets the
// concrete-evaluator refutation/upgrade override whatever the SMT said — which
// would mask an axiom defect entirely. With a hypothesis in scope those
// overrides are withheld and the verdict is the solver's, resting on the body
// axiom alone. These are therefore genuine axiom-shape pins.
//
// SCOPE. This fixture covers ONE instance of the class. `add_typed_broadcast`
// makes every helper that hoists a fresh const's defining equation to the
// solver top level capturable the same way — 47 such helpers exist on
// `AstExpressionParser`, and `purified_euclidean_div_mod_literal` was a second
// measured CARDINAL false verify. See `tests/data/hoist_capture_class.rs` for
// the class-level fixture and `encoder::binder_capture` for the class-level fix.
//
// The datatype is deliberately NON-RECURSIVE and the spec fn NON-RECURSIVE:
// that keeps the pin off the `decreases` well-foundedness lane and off datatype
// acyclicity, so it stays cheap while still exercising the exact hoist.

#![allow(dead_code, unused_variables)]

enum Color {
    Red,
    Green,
    Blue,
}

// Datatype-VALUED spec fn whose body is a multi-arm `match`, i.e. an `ite` tree
// of constructor leaves — precisely the shape `bind_datatype_match_result` fires
// on, encoded inside the `forall` of its own defining axiom.
#[trust_vc::spec]
fn next(c: Color) -> Color {
    match c {
        Color::Red => Color::Green,
        Color::Green => Color::Blue,
        Color::Blue => Color::Red,
    }
}

// CARDINAL. `next(Red) == Green` and `next(Green) == Blue`, so this equality is
// FALSE. Only a body axiom that says `next` is constant can prove it. The
// hypothesis is irrelevant to the goal; it exists solely to switch off the
// closed-ground concrete-evaluator override so the SMT verdict stands.
#[trust_vc::ensures(true)]
fn f_next_constant_collapse(x: Color) {
    trust_vc::assume!(x == Color::Red);
    trust_vc::assert!(next(Color::Red) == next(Color::Green));
}

// CARDINAL, disequality direction: a constant `next` equally proves the FALSE
// `next(Red) != Green`.
#[trust_vc::ensures(true)]
fn f_next_red_neq_green(x: Color) {
    trust_vc::assume!(x == Color::Red);
    trust_vc::assert!(next(Color::Red) != Color::Green);
}

// NO-OVER-REJECTION control: with the correct body axiom
// `forall c. next(c) == match c { .. }` this is TRUE and must still Verify, so
// the fix cannot be "emit nothing and lose the definition". (Measured: this one
// verifies under the captured axiom too — an unconstrained constant is still
// free to equal `Green` — so it is a control, not a second discriminator. The
// discriminating direction is the FALSE-goal pair above, which reported
// `Verified` with the capture in place.)
#[trust_vc::ensures(true)]
fn t_next_red_is_green(x: Color) {
    trust_vc::assume!(x == Color::Red);
    trust_vc::assert!(next(Color::Red) == Color::Green);
}
