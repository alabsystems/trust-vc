// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_types::{SpecFn, int, nat};

pub const FUNCTIONS_RS_EXPECTED_CASES: &[(&str, &str, &str, &str, usize)] = &[
    (
        "test_use_fun_ext",
        "test_use_fun_ext",
        "evals/verus/ported/functions.rs",
        "verified",
        2,
    ),
    (
        "test_use_fun_ext2",
        "test_use_fun_ext2",
        "evals/verus/ported/functions.rs",
        "verified",
        2,
    ),
    (
        "test_ensures_returns_default_regression_392_1",
        "test_ensures_returns_default_regression_392_1",
        "evals/verus/ported/functions.rs",
        "verified",
        2,
    ),
    (
        "test_ensures_returns_default_regression_497",
        "test_ensures_returns_default_regression_497",
        "evals/verus/ported/functions.rs",
        "verified",
        1,
    ),
    (
        "test_ensures_returns_default_regression_392_2",
        "test_ensures_returns_default_regression_392_2",
        "evals/verus/ported/functions.rs",
        "verified",
        2,
    ),
    (
        "test_ensures_returns_default_regression_392_3",
        "test_ensures_returns_default_regression_392_3",
        "evals/verus/ported/functions.rs",
        "verified",
        2,
    ),
    (
        "test_returns_named_unit",
        "test_returns_named_unit",
        "evals/verus/ported/functions.rs",
        "verified",
        1,
    ),
    (
        "test_async_external_fn_accepted",
        "test_async_external_fn_accepted",
        "evals/verus/ported/functions.rs",
        "verified",
        1,
    ),
    (
        "test_non_async_opaque_types_disallowed",
        "test_non_async_opaque_types_disallowed",
        "evals/verus/ported/functions_invalid_opaque_type",
        "error",
        0,
    ),
    (
        "test_ensures_name_collision",
        "test_ensures_name_collision",
        "evals/verus/ported/functions.rs",
        "verified",
        1,
    ),
];

pub fn functions_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, &'static str, usize)] {
    FUNCTIONS_RS_EXPECTED_CASES
}

pub const FUNCTIONS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[(
    "test_non_async_opaque_types_disallowed",
    &["`impl Trait` in type aliases is unstable"],
)];

pub fn functions_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    FUNCTIONS_RS_EXPECTED_ERROR_PATTERNS
}

fn functions_drop<A>(f: SpecFn<int, A>, k: nat) -> SpecFn<int, A> {
    SpecFn::new(|n: int| f.call(n + (k as int)))
}

#[trust_vc::ensures(true)]
fn test_use_fun_ext(_f: SpecFn<int, int>) {
    trust_vc::assert!(trust_vc::ext_eq!(
        SpecFn::new(|i: int| i + 1),
        SpecFn::new(|j: int| 1 + j)
    ));
}

#[trust_vc::ensures(true)]
fn test_use_fun_ext2<A>(f: SpecFn<int, A>, k1: nat, k2: nat) {
    trust_vc::assert!(trust_vc::ext_eq!(
        SpecFn::new(|n: int| f.call((n + (k2 as int)) + (k1 as int))),
        SpecFn::new(|n: int| f.call(n + ((k1 as int) + (k2 as int))))
    ));
}

fn returns_nothing(_a: u8, _b: u8) {}

#[trust_vc::ensures(true)]
fn test_ensures_returns_default_regression_392_1() {
    let x: () = returns_nothing(0u8, 0u8);
    trust_vc::assert!(x == ());
}

trait FunctionsFoo {
    fn foo(&self);
}

struct FunctionsX;

impl FunctionsFoo for FunctionsX {
    fn foo(&self) {}
}

#[trust_vc::ensures(true)]
fn test_ensures_returns_default_regression_497() {
    let z = FunctionsX;
    let x: () = z.foo();
    let _ = x;
}

#[trust_vc::spec]
fn functions_foo() -> bool {
    true
}

fn returns_unit() {}

#[trust_vc::ensures(true)]
fn test_ensures_returns_default_regression_392_2(b: bool) {
    trust_vc::assert!(functions_foo());
    let mut x: () = ();
    if b {
        x = returns_unit();
    }
    let _ = x;
}

fn takes_unit(_u: ()) {}

#[trust_vc::ensures(true)]
fn test_ensures_returns_default_regression_392_3(_b: bool) {
    trust_vc::assert!(functions_foo());
    takes_unit(returns_unit());
}

#[trust_vc::contract(
    ensures(u == ()),
    returns(u),
)]
#[trust_vc::proof]
fn test_returns_named_unit() -> () {}

#[trust_vc::external]
#[trust_vc::ensures(true)]
async fn test_async_external_fn_accepted(_c: usize) -> Result<usize, ()> {
    Ok(21usize)
}

// Upstream Verus expects rustc to reject a non-async `type OT = impl Foo`;
// evals/verus/ported/functions_invalid_opaque_type carries that cargo fixture.
trait FunctionsOpaqueFoo {
    fn bar(&self) -> bool;
}

#[allow(dead_code)]
fn test_non_async_opaque_types_disallowed_marker<T: FunctionsOpaqueFoo>(_value: &T) {}

#[trust_vc::contract(
    ensures(test_ensures_name_collision == 42i32),
    returns(test_ensures_name_collision),
)]
fn test_ensures_name_collision() -> i32 {
    42i32
}
