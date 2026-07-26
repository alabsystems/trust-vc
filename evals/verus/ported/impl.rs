// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream Verus
// `rust_verify_test/tests/impl.rs`.
//
// This scout covers Rust-valid inherent impl bodies that TrustVc can execute
// directly: `Bike::new()`-shaped constructors, explicit concrete and borrowed
// self receivers, generic impl method bodies, generic-parameter return shapes,
// concrete `TemplateCar`-style field witnesses, stable false-field
// counterexamples, receiver method calls (`recv.method()`), and — over a
// concrete impl — implicit `self` receivers, `-> Self` return types, and
// `Self::method(..)` associated calls (`Self` resolves to the enclosing impl's
// concrete type at target lifting; see `function_discovery::SelfTypeSubstituter`),
// and a GENERIC inherent method called on a concrete receiver instantiation
// (`ImplWrapper::<u64>`, monomorphized `A -> u64`; see `admit_generic_inherent_impl`
// / `collect_concrete_receiver_carriers`). Full upstream parity is not claimed.
// Verus spec/proof modes, visibility diagnostics, external trait impl
// diagnostics, and unsafe impl diagnostics remain unsupported or outside this
// executable slice.

#![allow(dead_code)]

pub const IMPL_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("new_bike_verified", "test_impl_no_self", "verified", 1),
    (
        "explicit_self_hard_tail_verified",
        "test_generic_struct",
        "verified",
        1,
    ),
    (
        "explicit_borrow_self_hard_tail_verified",
        "test_impl_1",
        "verified",
        1,
    ),
    (
        "associated_identity_verified",
        "test_impl_no_self",
        "verified",
        1,
    ),
    (
        "generic_wrapper_take_verified",
        "test_impl_generic_pass",
        "verified",
        1,
    ),
    (
        "concrete_wrapper_take_with_param_verified",
        "test_impl_generic_param",
        "verified",
        1,
    ),
    (
        "template_new_u64_verified",
        "test_generic_struct",
        "verified",
        1,
    ),
    (
        "template_get_passengers_explicit_self_verified",
        "test_generic_struct",
        "verified",
        1,
    ),
    (
        "template_get_v_explicit_self_verified",
        "test_generic_struct",
        "verified",
        1,
    ),
    (
        "associated_assert_false_counterexample",
        "test_impl_generic_fail",
        "counterexample",
        1,
    ),
    (
        "concrete_wrapper_field_wrong_counterexample",
        "test_impl_generic_fail",
        "counterexample",
        1,
    ),
    (
        "template_field_projection_wrong_counterexample",
        "test_generic_struct",
        "counterexample",
        1,
    ),
    (
        "associated_function_call_currently_blocked",
        "test_impl_mod_1",
        "verified",
        1,
    ),
    (
        "method_call_verified",
        "test_impl_1",
        "verified",
        1,
    ),
    (
        "implicit_self_hard_tail_verified",
        "test_generic_struct",
        "verified",
        1,
    ),
    (
        "self_return_type_verified",
        "test_impl_with_self",
        "verified",
        1,
    ),
    (
        "self_associated_call_verified",
        "test_resolve_self_ty",
        "verified",
        1,
    ),
    (
        "generic_method_call_verified",
        "test_impl_generic_pass",
        "verified",
        1,
    ),
];

pub fn impl_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    IMPL_RS_EXPECTED_CASES
}

// All impl.rs scout cases now resolve (verified/counterexample); no fail-closed
// boundary remains in this slice after Phase A2-generic.
pub const IMPL_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[];

pub fn impl_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])] {
    IMPL_RS_EXPECTED_ERROR_PATTERNS
}

struct ImplBike {
    hard_tail: bool,
}

impl ImplBike {
    #[trust_vc::ensures(result == self.hard_tail)]
    fn explicit_self_hard_tail_verified(self: ImplBike) -> bool {
        self.hard_tail
    }

    #[trust_vc::ensures(result == self.hard_tail)]
    fn explicit_borrow_self_hard_tail_verified(self: &ImplBike) -> bool {
        self.hard_tail
    }

    // De-surrogated 2026-07-15 (Phase A, Self-substitution): when a method is
    // lifted to a verification target, `Self` now resolves to the enclosing
    // impl's concrete type (`ImplBike`) — so a bare `self` receiver types as
    // `ImplBike` (field projection lowers), a `-> Self` return types the result
    // as `ImplBike`, and a `Self::method(..)` associated call resolves to the
    // concrete method (return type carried through). Faithful to upstream
    // test_resolve_self_ty (`bar(self) -> Self`, `bar2` calling `Self::bar`,
    // ensures `equal(self, result)`) and test_impl_with_self; all three verify.
    #[trust_vc::ensures(result == self.hard_tail)]
    fn implicit_self_hard_tail_verified(self) -> bool {
        self.hard_tail
    }

    #[trust_vc::ensures(result.hard_tail == self.hard_tail)]
    fn self_return_type_verified(self: ImplBike) -> Self {
        self
    }

    #[trust_vc::ensures(result.hard_tail == self.hard_tail)]
    fn self_associated_call_verified(self: ImplBike) -> Self {
        Self::self_return_type_verified(self)
    }
}

struct ImplWitness;

impl ImplWitness {
    #[trust_vc::ensures(result.hard_tail)]
    fn new_bike_verified() -> ImplBike {
        ImplBike { hard_tail: true }
    }

    #[trust_vc::ensures(result == value)]
    fn associated_identity_verified(value: u64) -> u64 {
        value
    }

    #[trust_vc::ensures(true)]
    fn associated_assert_false_counterexample() {
        trust_vc::assert!(false);
    }
}

struct ImplWrapper<A> {
    value: A,
}

impl<A> ImplWrapper<A> {
    #[trust_vc::ensures(result == self.value)]
    fn generic_wrapper_take_verified(self: ImplWrapper<A>) -> A {
        self.value
    }
}

struct ImplU64Wrapper {
    value: u64,
}

struct ImplU64BoolPair {
    a: u64,
    b: bool,
}

impl ImplU64Wrapper {
    #[trust_vc::ensures(result.a == self.value && result.b == b)]
    fn concrete_wrapper_take_with_param_verified(self: ImplU64Wrapper, b: bool) -> ImplU64BoolPair {
        ImplU64BoolPair { a: self.value, b }
    }
}

#[trust_vc::ensures(true)]
fn concrete_wrapper_field_wrong_counterexample() {
    trust_vc::assert_by_compute!(ImplU64Wrapper { value: 7u64 }.value == 8u64; compute_only);
}

struct ImplTemplateCarU64 {
    four_doors: bool,
    passengers: u64,
    the_v: u64,
}

impl ImplTemplateCarU64 {
    #[trust_vc::ensures(result.passengers == 205u64 && result.the_v == v)]
    fn template_new_u64_verified(v: u64) -> ImplTemplateCarU64 {
        ImplTemplateCarU64 {
            four_doors: false,
            passengers: 205u64,
            the_v: v,
        }
    }

    #[trust_vc::ensures(result == self.passengers)]
    fn template_get_passengers_explicit_self_verified(self: ImplTemplateCarU64) -> u64 {
        self.passengers
    }

    #[trust_vc::ensures(result == self.the_v)]
    fn template_get_v_explicit_self_verified(self: ImplTemplateCarU64) -> u64 {
        self.the_v
    }
}

#[trust_vc::ensures(true)]
fn template_field_projection_wrong_counterexample() {
    trust_vc::assert_by_compute!(
        ImplTemplateCarU64 {
            four_doors: false,
            passengers: 205u64,
            the_v: 7u64,
        }
        .the_v == 8u64;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn associated_function_call_currently_blocked() {
    trust_vc::assert!(ImplWitness::new_bike_verified().hard_tail);
}

// De-surrogated 2026-07-15 (Phase A): inherent method-call resolution works on
// the file path — `bike.explicit_self_hard_tail_verified()` resolves to the
// method's contract (`result == self.hard_tail`), so under `requires(bike.hard_tail)`
// the assertion verifies. (Was a stale "unknown return type" fail-closed boundary;
// the engine already resolves the call — the port lagged the engine.)
#[trust_vc::requires(bike.hard_tail)]
#[trust_vc::ensures(true)]
fn method_call_verified(bike: ImplBike) {
    trust_vc::assert!(bike.explicit_self_hard_tail_verified());
}

// De-surrogated 2026-07-20 (Phase A2-generic, un-quarantine #2): a generic
// inherent method (`impl<A> ImplWrapper<A> { fn take(self) -> A }`) called on a
// CONCRETE receiver (`ImplWrapper::<u64>`) is now monomorphized (`A -> u64`) and
// its conformance-checked contract (`result == self.value`) applied at the call
// site, so `wrapped.generic_wrapper_take_verified() == value` verifies. Upstream
// test_impl_generic_pass shape.
#[trust_vc::ensures(true)]
fn generic_method_call_verified(value: u64) {
    let wrapped = ImplWrapper::<u64> { value };

    trust_vc::assert!(wrapped.generic_wrapper_take_verified() == value);
}
