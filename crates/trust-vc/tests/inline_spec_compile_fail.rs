// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Focused compile-fail coverage for inline spec proc-macro validation.

#[path = "common/trybuild_env.rs"]
mod trybuild_env;

#[test]
fn inline_spec_compile_fail_tests() {
    trybuild_env::pin_no_trust_verify();
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/compile-fail/inline_*.rs");
}
