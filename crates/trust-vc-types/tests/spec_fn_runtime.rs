// SpecFn runtime behavior tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_types::SpecFn;

#[test]
fn spec_fn_new_does_not_execute_closure() {
    let result = std::panic::catch_unwind(|| {
        let _ = SpecFn::new(|_x: i32| -> i32 { panic!("SpecFn closure executed") });
    });
    assert!(result.is_ok(), "SpecFn::new should not execute the closure");
}

#[test]
fn spec_fn_call_panics() {
    let spec = SpecFn::new(|x: i32| x + 1);
    let result = std::panic::catch_unwind(|| {
        let _ = spec.call(1);
    });
    assert!(
        result.is_err(),
        "SpecFn::call should panic if executed at runtime"
    );
}
