// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Partial direct TrustVc port for the supported executable core of upstream
// returns_postcondition.rs.
//
// Verus `returns expr` is represented with a TrustVc postcondition over the
// canonical direct-source return binding `result`. This intentionally covers
// ordinary function/proof-function return-value obligations plus narrow
// direct-expression and trait/default inheritance witnesses. Verus-only
// diagnostics and broader trait dispatch remain unsupported.

fn returns_basic_helper() -> u8 {
    20u8
}

#[trust_vc::contract(
    ensures(result == 20u8),
    returns(result),
)]
fn returns_basic_value() -> u8 {
    20u8
}

#[trust_vc::contract(
    ensures(result == 20u8),
    returns(result),
)]
#[trust_vc::proof]
fn proof_returns_basic_value() -> u8 {
    20u8
}

#[trust_vc::ensures(true)]
fn returns_basic_call_uses_return_value() {
    let j = returns_basic_helper();
    trust_vc::assert!(j == 20u8);
}

#[trust_vc::contract(
    ensures(result == 20u8),
    returns(result),
)]
fn returns_basic_wrong_value() -> u8 {
    19u8
}

#[trust_vc::contract(
    ensures(result == 20u8),
    returns(result),
)]
fn returns_basic_wrong_explicit_return() -> u8 {
    return 19u8;
}

#[trust_vc::contract(
    requires(a < 256u16),
    requires(b < 256u16),
    requires(a + b < 256u16),
    ensures(result == a + b),
    returns(result),
)]
fn returns_basic_wrong_sum_return(a: u16, b: u16) -> u16 {
    a
}

#[trust_vc::contract(
    requires(a < 256u16),
    requires(b < 256u16),
    requires(a + b < 256u16),
    ensures(a + b < 250u16),
    ensures(result == a + b),
    returns(result),
)]
fn returns_basic_stronger_ensures_fails(a: u16, b: u16) -> u16 {
    a + b
}

#[trust_vc::contract(
    requires(a < 256u16),
    requires(b < 256u16),
    requires(a + b < 256u16),
    ensures(result == a + b),
    returns(result),
)]
#[trust_vc::proof]
fn proof_returns_basic_wrong_sum_return(a: u16, b: u16) -> u16 {
    a
}

#[trust_vc::contract(
    requires(a < 256u16),
    requires(b < 256u16),
    requires(a + b < 256u16),
    ensures(a + b < 250u16),
    ensures(result == a + b),
    returns(result),
)]
#[trust_vc::proof]
fn proof_returns_basic_stronger_ensures_fails(a: u16, b: u16) -> u16 {
    a + b
}

#[trust_vc::contract(
    requires(a < 200u64),
    requires(b < 50u64),
    ensures(result == a + b),
    returns(result),
)]
fn returns_basic_explicit_sum_return_value(a: u64, b: u64) -> u64 {
    return a + b;
}

#[trust_vc::contract(
    requires(a < 200u64),
    requires(b > 0u64 && b < 50u64),
    ensures(result == a + b),
    returns(result),
)]
fn returns_basic_explicit_sum_return_wrong(a: u64, b: u64) -> u64 {
    let _ = b;
    return a;
}

#[trust_vc::returns(20u8)]
fn returns_basic_direct_attr_value() -> u8 {
    20u8
}

#[trust_vc::returns(20u8)]
#[trust_vc::proof]
fn proof_returns_basic_direct_attr_value() -> u8 {
    20u8
}

#[trust_vc::returns(20u8)]
fn returns_basic_direct_attr_explicit_return_value() -> u8 {
    return 20u8;
}

#[trust_vc::ensures(ret == x)]
#[trust_vc::returns(ret)]
fn returns_basic_direct_attr_legacy_ident_binding(x: u8) -> u8 {
    x
}

#[trust_vc::returns(20u8)]
fn returns_basic_direct_attr_wrong_value() -> u8 {
    19u8
}

#[trust_vc::returns(20u8)]
fn returns_basic_direct_attr_wrong_explicit_return() -> u8 {
    return 19u8;
}

// The `requires` bounds keep `a + b` inside u8, matching how every other sum case
// in this file guards its arithmetic (`requires(a < 256u16)` above). Without them
// the exec addition genuinely overflows at a = b = 255 and the case fails on
// "possible addition overflow" — which Verus would also reject — so the point of
// the case (a direct `returns` attribute carrying a sum) never got tested.
#[trust_vc::requires(a < 100u8)]
#[trust_vc::requires(b < 100u8)]
#[trust_vc::returns((a + b) as u8)]
fn returns_basic_direct_attr_sum_value(a: u8, b: u8) -> u8 {
    a + b
}

// `b > 0` makes `a` differ from `a + b`, so this fails on the WRONG RETURN VALUE
// (the property under test) rather than incidentally on overflow.
#[trust_vc::requires(a < 100u8)]
#[trust_vc::requires(b > 0u8 && b < 100u8)]
#[trust_vc::returns((a + b) as u8)]
fn returns_basic_direct_attr_wrong_sum_return(a: u8, b: u8) -> u8 {
    let _ = b;
    a
}

#[trust_vc::requires(x == 3u8)]
#[trust_vc::returns(x == 3u8)]
fn returns_basic_direct_attr_bool_expression_value(x: u8) -> bool {
    true
}

#[trust_vc::requires(x == 3u8)]
#[trust_vc::returns(x == 3u8)]
fn returns_basic_direct_attr_bool_expression_wrong(x: u8) -> bool {
    false
}

#[trust_vc::returns((a + b) as u8)]
fn returns_basic_direct_attr_unresolved_sum_return(a: u8, _b: u8) -> u8 {
    a
}

#[trust_vc::contract(ensures(result == x), returns(result))]
fn returns_direct_attr_unknown_ret_param_rejected() -> u8 {
    20u8
}

#[trust_vc::returns(20u8)]
fn returns_basic_direct_attr_literal_type_mismatch() -> bool {
    true
}

#[trust_vc::contract(
    ensures(result == ()),
    returns(result),
)]
fn returning_unit_value_ok() -> () {}

#[trust_vc::contract(ensures(false), returns(result))]
fn returning_unit_value_fails() {}

#[trust_vc::returns(())]
fn returning_unit_value_direct_attr_ok() {}

#[trust_vc::contract(
    ensures(*result == *x),
    returns(result),
)]
fn returns_reference_postcondition<'a>(x: &'a u64) -> &'a u64 {
    x
}

#[trust_vc::contract(
    ensures(*result == *x),
    returns(result),
)]
fn returns_reference_postcondition_wrong<'a>(x: &'a u64, y: &'a u64) -> &'a u64 {
    let _ = x;
    y
}

#[trust_vc::returns(x)]
fn returns_reference_direct_attr_postcondition<'a>(x: &'a u64) -> &'a u64 {
    x
}

#[trust_vc::returns(x)]
fn returns_reference_direct_attr_postcondition_wrong<'a>(x: &'a u64, y: &'a u64) -> &'a u64 {
    let _ = x;
    y
}

#[trust_vc::returns(x)]
fn returns_reference_direct_attr_char_referent_rejected<'a>(x: &'a char) -> &'a char {
    x
}

#[trust_vc::returns(*x)]
fn returns_mut_ref_bool_current_value_currently_rejected(x: &mut bool) -> bool {
    *x
}

#[trust_vc::spec]
#[trust_vc::recommends(x < 10u64)]
fn returns_recommends_identity(x: u64) -> u64 {
    x
}

#[trust_vc::spec]
#[trust_vc::recommends(x < 10u64)]
#[trust_vc::recommends(y < 10u64)]
fn returns_recommends_product(x: u64, y: u64) -> u64 {
    x * y
}

#[trust_vc::spec]
#[trust_vc::returns(result)]
fn spec_direct_returns_clause_rejected(x: u8) -> bool {
    x == 3u8
}

#[trust_vc::spec]
#[trust_vc::contract(ensures(result == x), returns(result))]
fn spec_grouped_returns_clause_rejected(x: u8) -> u8 {
    x
}

#[trust_vc::spec]
#[trust_vc::returns(x == 3u8)]
fn spec_direct_returns_expression_rejected(x: u8) -> bool {
    x == 3u8
}

#[trust_vc::ensures(true)]
fn returns_recommends_body_call_positive(x: u64) {
    trust_vc::assume!(x < 10u64);
    let returned = returns_recommends_identity(x);
    trust_vc::assert!(returned == x);
}

#[trust_vc::ensures(true)]
fn returns_recommends_body_call_violates() {
    let returned = returns_recommends_identity(10u64);
    trust_vc::assert!(returned == 10u64);
}

#[trust_vc::ensures(true)]
fn returns_recommends_multi_arg_body_call_positive() {
    let returned = returns_recommends_product(2u64, 3u64);
    trust_vc::assert!(returned == 6u64);
}

#[trust_vc::ensures(true)]
fn returns_recommends_multi_arg_body_call_violates() {
    let returned = returns_recommends_product(10u64, 3u64);
    trust_vc::assert!(returned == 30u64);
}

#[trust_vc::trait_spec]
trait DefaultTraitReturnsPostcondition: Sized {
    #[trust_vc::returns(true)]
    fn default_returns_true(self) -> bool {
        true
    }
}

#[trust_vc::trait_impl]
impl DefaultTraitReturnsPostcondition for bool {}

#[trust_vc::ensures(true)]
fn default_trait_returns_inherited_positive<T: DefaultTraitReturnsPostcondition>(value: T) {
    let returned = value.default_returns_true();
    trust_vc::assert!(returned);
}

#[trust_vc::trait_spec]
trait DefaultTraitReturnsParamPostcondition {
    #[trust_vc::contract(ensures(result == input), returns(result))]
    fn default_returns_input(input: u8) -> u8 {
        input
    }
}

#[trust_vc::trait_impl]
impl DefaultTraitReturnsParamPostcondition for bool {}

#[trust_vc::trait_spec]
trait DefaultTraitReturnsPostconditionMismatch {
    #[trust_vc::returns(true)]
    fn default_returns_false() -> bool {
        false
    }
}

#[trust_vc::trait_impl]
impl DefaultTraitReturnsPostconditionMismatch for bool {}

#[trust_vc::trait_spec]
trait DefaultTraitReturnsParamPostconditionMismatch {
    #[trust_vc::contract(ensures(result == input), returns(result))]
    fn default_returns_wrong_input(input: u8) -> u8 {
        let _ = input;
        0u8
    }
}

#[trust_vc::trait_impl]
impl DefaultTraitReturnsParamPostconditionMismatch for bool {}

#[trust_vc::trait_spec]
trait TraitReturnsInheritedPostconditionPositive {
    #[trust_vc::returns(true)]
    fn inherited_returns_true_positive() -> bool;
}

#[trust_vc::trait_impl]
impl TraitReturnsInheritedPostconditionPositive for bool {
    fn inherited_returns_true_positive() -> bool {
        true
    }
}

#[trust_vc::trait_spec]
trait TraitReturnsInheritedPostcondition {
    #[trust_vc::returns(true)]
    fn inherited_returns_true() -> bool;
}

#[trust_vc::trait_impl]
impl TraitReturnsInheritedPostcondition for bool {
    fn inherited_returns_true() -> bool {
        false
    }
}

#[trust_vc::trait_spec]
trait TraitImplReturnsPostcondition {
    fn impl_returns_true() -> bool;
}

#[trust_vc::trait_impl]
impl TraitImplReturnsPostcondition for bool {
    #[trust_vc::returns(true)]
    fn impl_returns_true() -> bool {
        true
    }
}

#[trust_vc::trait_spec]
trait TraitImplReturnsPostconditionMismatch {
    fn impl_returns_false() -> bool;
}

#[trust_vc::trait_impl]
impl TraitImplReturnsPostconditionMismatch for bool {
    #[trust_vc::returns(true)]
    fn impl_returns_false() -> bool {
        false
    }
}

#[trust_vc::trait_spec]
trait TraitReturnsConflictPostcondition {
    #[trust_vc::returns(true)]
    fn conflicting_returns_clause() -> bool;
}

#[trust_vc::trait_impl]
impl TraitReturnsConflictPostcondition for bool {
    #[trust_vc::returns(false)]
    fn conflicting_returns_clause() -> bool {
        false
    }
}

#[trust_vc::trait_spec]
trait TraitReturnsGroupedConflictPostcondition {
    #[trust_vc::returns(true)]
    fn conflicting_grouped_returns_clause() -> bool;
}

#[trust_vc::trait_impl]
impl TraitReturnsGroupedConflictPostcondition for bool {
    #[trust_vc::contract(ensures(result == false), returns(result))]
    fn conflicting_grouped_returns_clause() -> bool {
        false
    }
}

pub const RETURNS_POSTCONDITION_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("returns_basic_value", "returns_basic", "verified", 1),
    ("proof_returns_basic_value", "returns_basic", "verified", 1),
    (
        "returns_basic_call_uses_return_value",
        "returns_basic",
        "verified",
        2,
    ),
    (
        "returns_basic_wrong_value",
        "returns_basic",
        "counterexample",
        1,
    ),
    (
        "returns_basic_wrong_explicit_return",
        "returns_basic",
        "counterexample",
        1,
    ),
    (
        "returns_basic_wrong_sum_return",
        "returns_basic",
        "counterexample",
        1,
    ),
    (
        "returns_basic_stronger_ensures_fails",
        "returns_basic",
        "counterexample",
        1,
    ),
    (
        "proof_returns_basic_wrong_sum_return",
        "returns_basic",
        "counterexample",
        1,
    ),
    (
        "proof_returns_basic_stronger_ensures_fails",
        "returns_basic",
        "counterexample",
        1,
    ),
    (
        "returns_basic_explicit_sum_return_value",
        "returns_basic",
        "verified",
        1,
    ),
    (
        "returns_basic_explicit_sum_return_wrong",
        "returns_basic",
        "counterexample",
        1,
    ),
    (
        "returns_basic_direct_attr_value",
        "returns_basic",
        "verified",
        1,
    ),
    (
        "proof_returns_basic_direct_attr_value",
        "returns_basic",
        "verified",
        1,
    ),
    (
        "returns_basic_direct_attr_explicit_return_value",
        "returns_basic",
        "verified",
        1,
    ),
    (
        "returns_basic_direct_attr_legacy_ident_binding",
        "returns_basic",
        "verified",
        1,
    ),
    (
        "returns_basic_direct_attr_wrong_value",
        "returns_basic",
        "counterexample",
        1,
    ),
    (
        "returns_basic_direct_attr_wrong_explicit_return",
        "returns_basic",
        "counterexample",
        1,
    ),
    (
        "returns_basic_direct_attr_sum_value",
        "returns_basic",
        "verified",
        1,
    ),
    (
        "returns_basic_direct_attr_wrong_sum_return",
        "returns_basic",
        "counterexample",
        1,
    ),
    (
        "returns_basic_direct_attr_bool_expression_value",
        "returns_basic",
        "verified",
        1,
    ),
    (
        "returns_basic_direct_attr_bool_expression_wrong",
        "returns_basic",
        "counterexample",
        1,
    ),
    (
        "returns_basic_direct_attr_unresolved_sum_return",
        "returns_basic",
        "error",
        0,
    ),
    (
        "returns_direct_attr_unknown_ret_param_rejected",
        "spec_fn_returns_references_ret_param",
        "error",
        0,
    ),
    (
        "returns_basic_direct_attr_literal_type_mismatch",
        "wrong_type",
        "error",
        0,
    ),
    (
        "returning_unit_value_ok",
        "returning_unit_value",
        "verified",
        1,
    ),
    (
        "returning_unit_value_fails",
        "returning_unit_value",
        "counterexample",
        1,
    ),
    (
        "returning_unit_value_direct_attr_ok",
        "returning_unit_value",
        "verified",
        1,
    ),
    (
        "returns_reference_postcondition",
        "returns references ret param",
        "verified",
        1,
    ),
    (
        "returns_reference_postcondition_wrong",
        "returns references ret param",
        "counterexample",
        1,
    ),
    (
        "returns_reference_direct_attr_postcondition",
        "returns references ret param",
        "verified",
        1,
    ),
    (
        "returns_reference_direct_attr_postcondition_wrong",
        "returns references ret param",
        "counterexample",
        1,
    ),
    (
        "returns_reference_direct_attr_char_referent_rejected",
        "returns references ret param",
        "error",
        0,
    ),
    (
        "returns_mut_ref_bool_current_value_currently_rejected",
        "allow_in_spec_mut_ref",
        "error",
        0,
    ),
    (
        "spec_direct_returns_clause_rejected",
        "spec_fn_returns",
        "error",
        0,
    ),
    (
        "spec_grouped_returns_clause_rejected",
        "spec_fn_returns",
        "error",
        0,
    ),
    (
        "spec_direct_returns_expression_rejected",
        "spec_fn_returns",
        "error",
        0,
    ),
    (
        "returns_recommends_body_call_positive",
        "returns_and_recommends_issue1834",
        "verified",
        1,
    ),
    (
        "returns_recommends_body_call_violates",
        "returns_and_recommends_issue1834",
        "verified",
        1,
    ),
    (
        "returns_recommends_multi_arg_body_call_positive",
        "returns_and_recommends_issue1834",
        "verified",
        1,
    ),
    (
        "returns_recommends_multi_arg_body_call_violates",
        "returns_and_recommends_issue1834",
        "verified",
        1,
    ),
    (
        "default_trait_returns_inherited_positive",
        "default_trait_fn_with_returns",
        "verified",
        1,
    ),
    (
        "default_returns_input",
        "default_trait_fn_with_returns",
        "verified",
        1,
    ),
    (
        "default_returns_false",
        "default_trait_fn_with_returns2",
        "counterexample",
        1,
    ),
    (
        "default_returns_wrong_input",
        "default_trait_fn_with_returns2",
        "counterexample",
        1,
    ),
    (
        "inherited_returns_true_positive",
        "trait_returns_on_trait_method_decl",
        "verified",
        1,
    ),
    (
        "inherited_returns_true",
        "trait_returns_on_trait_method_decl",
        "counterexample",
        1,
    ),
    (
        "impl_returns_true",
        "trait_returns_on_trait_method_impl",
        "verified",
        1,
    ),
    (
        "impl_returns_false",
        "trait_returns_on_trait_method_impl",
        "counterexample",
        1,
    ),
    (
        "conflicting_returns_clause",
        "default_trait_fn_with_returns_conflict",
        "error",
        0,
    ),
    (
        "conflicting_grouped_returns_clause",
        "trait_returns_conflict",
        "error",
        0,
    ),
];

pub fn returns_postcondition_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    RETURNS_POSTCONDITION_RS_EXPECTED_CASES
}
