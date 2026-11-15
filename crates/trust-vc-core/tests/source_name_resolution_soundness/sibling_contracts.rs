// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Adversarial controls for the narrow opaque-unit-sibling exception.

use super::{verify, VerifyResult};

const OPAQUE_UNIT_SIBLING_WITH_FALSE_REQUIRES: &str = r#"
mod nested {
    pub fn external_effect() {}
}

#[trust_vc::requires(false)]
fn guarded_unit_helper() {
    use nested::*;
    external_effect();
}

#[trust_vc::ensures(true)]
fn caller_must_still_establish_helper_requires() {
    guarded_unit_helper();
}
"#;

#[test]
fn opaque_unit_sibling_still_enforces_its_contract() {
    let result = verify(
        OPAQUE_UNIT_SIBLING_WITH_FALSE_REQUIRES,
        "caller_must_still_establish_helper_requires",
    );
    assert!(
        !matches!(result, Ok(VerifyResult::Verified)),
        "omitting an unresolved unit body must not omit its false requires clause, got {result:?}"
    );
}

const MUTATING_UNIT_SIBLING_WITH_BLOCK_GLOB: &str = r#"
mod nested {
    pub fn external_effect() {}
}

fn mutating_helper(value: &mut u32) {
    use nested::*;
    external_effect();
    *value = 1;
}

#[trust_vc::ensures(true)]
fn caller_exposes_helper_mutation(value: &mut u32) {
    mutating_helper(value);
}
"#;

#[test]
fn unresolved_glob_in_mutating_unit_sibling_still_fails_closed() {
    let result = verify(
        MUTATING_UNIT_SIBLING_WITH_BLOCK_GLOB,
        "caller_exposes_helper_mutation",
    );
    assert!(
        result.is_err(),
        "a sibling with caller-visible mutation must not be made opaque, got {result:?}"
    );
}
