// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Compile-fail coverage for the reserved-keyword spec op `final(..)` on the
//! RUNTIME proc-macro surfaces.
//!
//! `final(..)` is parseable (`trust_vc_core`'s
//! `MUT_REF_FINAL_MARKER` rewrite). The marker has no runtime function behind
//! it, so any surface that expands an obligation into a runtime `assert!` must
//! refuse it BY NAME; otherwise rustc reports `error[E0425]: cannot find
//! function \`__trust_vc_mut_ref_final\``, a symbol the author never wrote.

#[path = "common/trybuild_env.rs"]
mod trybuild_env;

#[test]
fn mut_ref_final_runtime_surfaces_compile_fail_tests() {
    trybuild_env::pin_no_trust_verify();
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/compile-fail/mut_ref_final_*.rs");
}
