// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc evidence for upstream
// `source/rust_verify_test/tests/inline.rs`.
//
// This file intentionally covers only a small Rust-valid inline/spec-function
// contract surface. Upstream Verus exercises `#[verifier(inline)]` across
// private/open spec visibility, proof-mode assertions, generic spec functions,
// uninterpreted specs, hide/reveal, default trait implementations, and exact
// diagnostics. TrustVc does not claim that full replacement here.
//
// This scout records inline-marked source spec helpers used from executable
// contracts and assertions, including arithmetic wrapper/argument-renaming/
// local-binding bodies shaped after upstream test1, generic source-spec calls,
// opaque-wrapper/reveal behavior, a struct-field getter shaped after
// test_ensures_type_inference, stable false facts against those helpers, and
// current fail-closed boundaries for executable-helper, hide, and trait/default
// implementation surfaces.

use trust_vc_types::{int, Set};

pub const INLINE_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "inline_spec_contract_surface_verified",
        "test1",
        "verified",
        1,
    ),
    ("inline_spec_assertion_verified", "test1", "verified", 1),
    (
        "inline_local_binding_spec_contract_verified",
        "test1",
        "verified",
        1,
    ),
    (
        "inline_test1_arithmetic_assertions_verified",
        "test1",
        "verified",
        1,
    ),
    (
        "inline_test1_arithmetic_contract_verified",
        "test1",
        "verified",
        1,
    ),
    (
        "inline_test1_generic_identity_verified",
        "test1",
        "verified",
        1,
    ),
    (
        "inline_test1_opaque_wrapper_requires_verified",
        "test1",
        "verified",
        1,
    ),
    (
        "inline_test1_opaque_wrapper_reveal_verified",
        "test1",
        "verified",
        1,
    ),
    (
        "inline_ensures_type_inference_direct_field_verified",
        "test_ensures_type_inference",
        "verified",
        1,
    ),
    (
        "inline_test1_arithmetic_body_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "inline_bool_negate_body_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "inline_exec_helper_in_contract_fails_closed",
        "test_nonspec_fails",
        "error",
        0,
    ),
    (
        // Legacy name (kept for pin stability). hide! is supported (#2785):
        // upstream inline.rs `test_spec_fn` marks f1/f2 #[verifier(inline)] and
        // hide(f2) is accepted (it opaques the inline fn). Here hiding
        // `inline_less_than` with no reveal leaves `inline_less_than(0, 1)`
        // provable only via the hidden body → Counterexample, matching Verus.
        "inline_hide_macro_boundary_fails_closed",
        "test_spec_fn",
        "counterexample",
        1,
    ),
    (
        // Legacy case_id (kept for pin stability). File-path `#[trust_vc::inline]`
        // functions are now call-site-substituted (#2777): the local-binding
        // call-through body `let za=a+1; let zb=b+1; plain_arith_formula(za-1,
        // zb-1)` inlines to `a+2b`, so `f(33,44)==121` verifies — matching
        // upstream test1's f4 local-binding case. Was a fail-closed
        // "undefined variable za" placeholder before inline substitution.
        "inline_test1_local_binding_call_plain_fails_closed",
        "test1",
        "verified",
        1,
    ),
    (
        // Legacy case_id (kept for pin stability). Generic tuple-returning inline
        // spec fns are now call-site-substituted (#2777): `inline_generic_swap::
        // <u8, bool>(10u8, true)` inlines to the concrete tuple `(true, 10u8)`,
        // renormalized to the `(bool, u8)` carrier, so `swapped.0` and `swapped.1
        // == 10u8` verify — matching upstream test1's `fg` assertion. Was a
        // fail-closed "conflicting variant metadata" placeholder before generic
        // inline substitution + tuple-carrier renormalization.
        "inline_test1_generic_swap_return_type_fails_closed",
        "test1",
        "verified",
        1,
    ),
    (
        // Legacy case_id (kept for pin stability). This is the faithful port of
        // upstream `test_ensures_type_inference` (`test1() -> Foo ensures
        // get_b(b)` returning `Foo{b:true}` => Ok). Datatype-parameter inline
        // spec functions now encode (#2777), so `inline_get_b(result)` inlines
        // to `result.b == true` and verifies. Was a fail-closed
        // "unsupported parameter type InlineFoo" placeholder.
        "inline_ensures_type_inference_getter_fails_closed",
        "test_ensures_type_inference",
        "verified",
        1,
    ),
    (
        // Legacy case_id (kept for pin stability). trust-vc-authored negative
        // probe (no upstream analog; upstream test_ensures_type_inference is
        // positive-only). Returns `Foo{b:false}` so the inlined postcondition
        // `result.b` is false → Counterexample, exactly like the direct-field
        // `inline_ensures_type_inference_direct_field_counterexample` control.
        // Was a fail-closed "unsupported parameter type" placeholder (#2777).
        "inline_ensures_type_inference_getter_wrong_fails_closed",
        "test_ensures_type_inference",
        "counterexample",
        1,
    ),
    (
        "inline_default_impl_trait_boundary_fails_closed",
        "default_impl_issue1407",
        "error",
        0,
    ),
    (
        // Faithful port of upstream `inline_poly` (assert_one_fails): a generic
        // `#[inline]` spec fn `forall|a: A| s.contains(a)` at `Set<int>` is false
        // for a general set => Counterexample. The generic inline body is
        // monomorphized to `A = int` at the call site (#2777).
        "inline_poly_all_contains_counterexample",
        "inline_poly",
        "counterexample",
        1,
    ),
    (
        // Faithful port of upstream `test_rec_fails1`: inline + `decreases` =>
        // fail-closed "'inline' functions cannot be recursive".
        "inline_rec_decreases_diagnostic",
        "test_rec_fails1",
        "error",
        0,
    ),
    (
        // Faithful port of upstream `test_rec_fails2`: inline + self-call + no
        // `decreases` => fail-closed "recursive function must have a decreases
        // clause".
        "inline_rec_no_decreases_diagnostic",
        "test_rec_fails2",
        "error",
        0,
    ),
    (
        // Faithful port of upstream `test_nonspec_fails`: `#[inline]` on a PROOF
        // fn => fail-closed "'inline' is only allowed for 'spec' functions".
        "inline_nonspec_proof_diagnostic",
        "test_nonspec_fails",
        "error",
        0,
    ),
    (
        // Faithful port of upstream `test_private_fails`: `#[inline]` on a `closed`
        // (opaque, body-hidden) spec fn => fail-closed
        // "'inline' is only allowed for private or 'open spec' functions".
        "inline_private_closed_diagnostic",
        "test_private_fails",
        "error",
        0,
    ),
];

pub const INLINE_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "inline_exec_helper_in_contract_fails_closed",
        &["Unsupported call to sibling helper"],
    ),
    // inline_hide_macro_boundary_fails_closed is a Counterexample now (hide!
    // supported, #2785), not a fail-closed error — no error patterns, absent here.
    // inline_test1_local_binding_call_plain_fails_closed, getter, and
    // getter_wrong are no longer fail-closed errors (file-path inline
    // substitution, #2777): the first two verify and getter_wrong is a
    // Counterexample — absent here, pinned in VERIFIED/COUNTEREXAMPLE metadata.
    // inline_test1_generic_swap_return_type_fails_closed now VERIFIES (generic
    // inline substitution + tuple-carrier renormalization, #2777) — no longer a
    // fail-closed error, so it carries no error patterns and is absent here.
    (
        "inline_default_impl_trait_boundary_fails_closed",
        &[
            "unsupported",
            "inline_default_value",
            "InlineDefaultOverride",
        ],
    ),
    (
        "inline_rec_decreases_diagnostic",
        &["'inline' functions cannot be recursive"],
    ),
    (
        "inline_rec_no_decreases_diagnostic",
        &["recursive function must have a decreases clause"],
    ),
    (
        "inline_nonspec_proof_diagnostic",
        &["'inline' is only allowed for 'spec' functions"],
    ),
    (
        "inline_private_closed_diagnostic",
        &["'inline' is only allowed for private or 'open spec' functions"],
    ),
];

pub fn inline_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    INLINE_RS_EXPECTED_CASES
}

pub fn inline_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])] {
    INLINE_RS_EXPECTED_ERROR_PATTERNS
}

#[derive(Clone, Copy)]
struct InlineFoo {
    b: bool,
}

#[trust_vc::spec]
#[trust_vc::inline]
fn inline_negate(input: bool) -> bool {
    !input
}

#[trust_vc::spec]
#[trust_vc::inline]
fn inline_let_roundtrip(input: bool) -> bool {
    let flipped = !input;
    !flipped
}

#[trust_vc::spec]
#[trust_vc::inline]
fn inline_arith_formula(x: int, y: int) -> int {
    x + 2 * y
}

#[trust_vc::spec]
fn plain_arith_formula(x: int, y: int) -> int {
    x + 2 * y
}

#[trust_vc::spec]
#[trust_vc::inline]
fn inline_arith_wrapper(x: int, y: int) -> int {
    plain_arith_formula(x, y)
}

#[trust_vc::spec]
#[trust_vc::inline]
fn inline_arith_renamed(a: int, b: int) -> int {
    plain_arith_formula(a, b)
}

#[trust_vc::spec]
#[trust_vc::inline]
fn inline_arith_local_bindings(a: int, b: int) -> int {
    let za = a + 1;
    let zb = b + 1;
    (za - 1) + 2 * (zb - 1)
}

#[trust_vc::spec]
#[trust_vc::inline]
fn inline_arith_local_bindings_call_plain(a: int, b: int) -> int {
    let za = a + 1;
    let zb = b + 1;
    plain_arith_formula(za - 1, zb - 1)
}

#[trust_vc::spec]
#[trust_vc::inline]
fn inline_generic_identity<T>(value: T) -> T {
    value
}

// Faithful port of upstream inline.rs `inline_poly`: a generic `#[inline]` spec
// fn whose body is a `forall` over `Set<A>`. Called at `Set<int>`, the claim
// "the set contains every int" is false for a general set, so the assertion
// fails => Counterexample (upstream `assert_one_fails`). The generic inline body
// is monomorphized to `A = int` at the call site (#2777) so the `forall|a: A|`
// binder and the `contains` select take the concrete `int` element sort; without
// that the encoder returns Unknown on a `Poly` sort mismatch instead.
#[trust_vc::spec]
#[trust_vc::inline]
fn inline_all_contains<A>(s1: Set<A>) -> bool {
    forall(|a: A| s1.contains(a))
}

#[trust_vc::ensures(true)]
fn inline_poly_all_contains_counterexample(s: Set<int>) {
    trust_vc::assert!(inline_all_contains(s));
}

// Faithful port of upstream `test_rec_fails1`: an `#[inline]` spec fn with a
// `decreases` clause DECLARES recursion, which inline substitution cannot
// support => fail-closed "'inline' functions cannot be recursive". The
// definition-level rejection surfaces when the diagnostic case (below) resolves
// the inline body of this fn.
#[trust_vc::spec]
#[trust_vc::inline]
#[trust_vc::decreases(n)]
fn inline_rec_decreases(n: int) -> int {
    0
}

#[trust_vc::ensures(true)]
fn inline_rec_decreases_diagnostic(n: int) {
    trust_vc::assert!(inline_rec_decreases(n) == 0);
}

// Faithful port of upstream `test_rec_fails2`: an `#[inline]` spec fn with a
// genuine self-call and NO `decreases` clause => fail-closed "recursive function
// must have a decreases clause".
#[trust_vc::spec]
#[trust_vc::inline]
fn inline_rec_no_decreases(n: int) -> int {
    if n == 0 {
        0
    } else {
        inline_rec_no_decreases(n - 1)
    }
}

#[trust_vc::ensures(true)]
fn inline_rec_no_decreases_diagnostic(n: int) {
    trust_vc::assert!(inline_rec_no_decreases(n) == 0);
}

// Faithful port of upstream `test_nonspec_fails`: `#[inline]` is only permitted
// on SPEC functions; an `#[inline]` PROOF fn is rejected at definition time with
// the verbatim Verus message. Verified directly (the bad definition IS the
// case) => fail-closed Error.
#[trust_vc::proof]
#[trust_vc::inline]
fn inline_nonspec_proof_diagnostic() {}

// Faithful port of upstream `test_private_fails`: `#[verifier(inline)] pub closed
// spec fn f`. `#[inline]` is only permitted on a spec fn whose body is VISIBLE
// (private or `open spec`); a `closed` spec fn hides its body, which inline
// substitution cannot see, so Verus rejects the definition with
// "'inline' is only allowed for private or 'open spec' functions". In trust-vc,
// `#[trust_vc::opaque]` is the faithful analog of Verus `closed` (the body is
// uninterpreted until `reveal!`), so `inline` + `opaque` reproduces the same
// rejection. Fail-closed at definition time; the error surfaces when the
// diagnostic caller below resolves this fn's inline body.
#[trust_vc::spec]
#[trust_vc::opaque]
#[trust_vc::inline]
fn inline_private_closed_spec(x: int, y: int) -> int {
    x + 2 * y
}

#[trust_vc::ensures(true)]
fn inline_private_closed_diagnostic(x: int, y: int) {
    trust_vc::assert!(inline_private_closed_spec(x, y) == x + 2 * y);
}

#[trust_vc::spec]
#[trust_vc::inline]
fn inline_generic_swap<A, B>(a: A, b: B) -> (B, A) {
    (b, a)
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn inline_opaque_int_predicate(x: int) -> bool {
    x == x
}

#[trust_vc::spec]
#[trust_vc::inline]
fn inline_opaque_predicate_wrapper(x: int) -> bool {
    inline_opaque_int_predicate(x)
}

#[trust_vc::spec]
#[trust_vc::inline]
fn inline_less_than(i: int, j: int) -> bool {
    i < j
}

#[trust_vc::spec]
#[trust_vc::inline]
fn inline_get_b(foo: InlineFoo) -> bool {
    foo.b
}

trait InlineDefaultTrait {
    fn inline_default_value(&self) -> bool {
        true
    }
}

struct InlineDefaultOverride {}

impl InlineDefaultTrait for InlineDefaultOverride {
    fn inline_default_value(&self) -> bool {
        false
    }
}

#[trust_vc::spec]
#[trust_vc::inline]
fn inline_trait_default_wrapper<T: InlineDefaultTrait>(value: T) -> bool {
    value.inline_default_value()
}

#[trust_vc::contract(
    ensures(result == inline_negate(input)),
    returns(result),
)]
fn inline_spec_contract_surface_verified(input: bool) -> bool {
    !input
}

#[trust_vc::contract(
    ensures(result == inline_negate(true)),
    returns(result),
)]
fn inline_spec_contract_surface_wrong_counterexample() -> bool {
    trust_vc::assume!(inline_negate(true) == false);
    true
}

#[trust_vc::requires(input)]
#[trust_vc::ensures(true)]
fn inline_spec_assertion_verified(input: bool) {
    trust_vc::assert!(inline_negate(!input));
}

#[trust_vc::ensures(true)]
fn inline_spec_assertion_wrong_counterexample() {
    trust_vc::assume!(inline_negate(true) == false);
    trust_vc::assert!(inline_negate(true));
}

#[trust_vc::contract(
    ensures(result == inline_let_roundtrip(input)),
    returns(result),
)]
fn inline_local_binding_spec_contract_verified(input: bool) -> bool {
    input
}

#[trust_vc::ensures(true)]
fn inline_local_binding_spec_false_counterexample() {
    trust_vc::assume!(inline_let_roundtrip(true));
    trust_vc::assert!(inline_let_roundtrip(true) == false);
}

#[trust_vc::ensures(true)]
fn inline_test1_arithmetic_assertions_verified() {
    let za: int = 44;

    trust_vc::assert!(inline_arith_formula(33, 44) == 121);
    trust_vc::assert!(plain_arith_formula(33, 44) == 121);
    trust_vc::assert!(inline_arith_wrapper(33, 44) == 121);
    trust_vc::assert!(inline_arith_renamed(33, 44) == 121);
    trust_vc::assert!(inline_arith_local_bindings(33, za) == 121);
}

#[trust_vc::contract(
    ensures(result == inline_arith_local_bindings(x, y)),
    returns(result),
)]
fn inline_test1_arithmetic_contract_verified(x: int, y: int) -> int {
    x + 2 * y
}

#[trust_vc::ensures(true)]
fn inline_test1_arithmetic_wrong_counterexample() {
    trust_vc::assume!(inline_arith_formula(33, 44) == 121);
    trust_vc::assert!(inline_arith_formula(33, 44) == 122);
}

#[trust_vc::ensures(true)]
fn inline_test1_arithmetic_body_counterexample() {
    trust_vc::assert_by_compute!(
        (33 as int) + (2 as int) * (44 as int) == (122 as int);
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn inline_bool_negate_body_counterexample() {
    trust_vc::assert_by_compute!(
        !true;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn inline_test1_generic_identity_verified() {
    trust_vc::assert!(inline_generic_identity::<u64>(10u64) == 10u64);
    trust_vc::assert!(inline_generic_identity::<bool>(true));
}

#[trust_vc::ensures(true)]
fn inline_test1_generic_identity_wrong_counterexample() {
    trust_vc::assume!(inline_generic_identity::<u64>(10u64) == 10u64);
    trust_vc::assert!(inline_generic_identity::<u64>(10u64) == 11u64);
}

#[trust_vc::ensures(true)]
fn inline_test1_generic_swap_return_type_fails_closed() {
    let swapped = inline_generic_swap::<u8, bool>(10u8, true);

    trust_vc::assert!(swapped.0);
    trust_vc::assert!(swapped.1 == 10u8);
}

#[trust_vc::requires(forall(|i: int| inline_opaque_predicate_wrapper(i)))]
#[trust_vc::ensures(true)]
fn inline_test1_opaque_wrapper_requires_verified() {
    trust_vc::assert!(inline_opaque_predicate_wrapper(6));
}

#[trust_vc::ensures(true)]
fn inline_test1_opaque_wrapper_reveal_verified(x: int) {
    trust_vc::reveal!(inline_opaque_int_predicate);
    trust_vc::assert!(inline_opaque_predicate_wrapper(x));
}

#[trust_vc::ensures(true)]
fn inline_test1_opaque_wrapper_without_reveal_counterexample(x: int) {
    trust_vc::assert!(inline_opaque_predicate_wrapper(x));
}

#[trust_vc::ensures(result.b)]
fn inline_ensures_type_inference_direct_field_verified() -> InlineFoo {
    InlineFoo { b: true }
}

#[trust_vc::ensures(result.b)]
fn inline_ensures_type_inference_direct_field_counterexample() -> InlineFoo {
    InlineFoo { b: false }
}

#[trust_vc::contract(ensures(inline_get_b(result)), returns(result))]
fn inline_ensures_type_inference_getter_fails_closed() -> InlineFoo {
    InlineFoo { b: true }
}

#[trust_vc::contract(ensures(inline_get_b(result)), returns(result))]
fn inline_ensures_type_inference_getter_wrong_fails_closed() -> InlineFoo {
    InlineFoo { b: false }
}

#[trust_vc::contract(
    ensures(result == inline_spec_contract_surface_verified(input)),
    returns(result),
)]
fn inline_exec_helper_in_contract_fails_closed(input: bool) -> bool {
    !input
}

#[trust_vc::ensures(true)]
fn inline_test1_local_binding_call_plain_fails_closed() {
    trust_vc::assert!(inline_arith_local_bindings_call_plain(33, 44) == 121);
}

// Legacy name (kept for pin stability). hide! is supported (#2785): hiding the
// inline fn (Verus accepts hide of #[verifier(inline)], opaquing it) with no
// reveal leaves `inline_less_than(0, 1)` provable only via the hidden body →
// Counterexample, matching upstream Verus.
#[trust_vc::ensures(true)]
fn inline_hide_macro_boundary_fails_closed() {
    trust_vc::hide!(inline_less_than);
    trust_vc::assert!(inline_less_than(0, 1));
}

#[trust_vc::ensures(true)]
fn inline_default_impl_trait_boundary_fails_closed() {
    let value = InlineDefaultOverride {};

    trust_vc::assert!(inline_trait_default_wrapper::<InlineDefaultOverride>(value));
}
