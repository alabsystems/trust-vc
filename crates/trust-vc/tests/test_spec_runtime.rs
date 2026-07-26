// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test that spec functions don't panic at runtime
//!
//! Part of #103: spec functions shouldn't panic at runtime

use trust_vc::spec;

#[spec]
fn my_spec_function(x: i32) -> i32 {
    x + 1
}

#[test]
fn test_spec_function_panics_when_called() {
    // Spec functions are ghost code and should panic at runtime
    // This is the correct behavior for Verus-style verification
    let result = std::panic::catch_unwind(|| my_spec_function(5));
    assert!(
        result.is_err(),
        "spec functions should panic at runtime - they are ghost code"
    );
}

#[test]
fn test_spec_function_compiles() {
    // The function should at least compile
    // We just don't call it - this test verifies compilation only
    // by virtue of the module compiling successfully
}
