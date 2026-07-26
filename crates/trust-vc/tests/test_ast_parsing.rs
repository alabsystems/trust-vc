//! Test that AST-based parsing works for the assert macro
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;

mod common;

#[test]
fn test_assert_macro_with_ast_parsing() {
    common::with_clean_verification(|| {
        // #[proof] auto-verifies internally; success = no panic (#2274)
        #[trust_vc::proof]
        fn test_simple_assert() {
            trust_vc::assert!(5 < 10);
        }

        // Proof function auto-verifies via ay — no panic means success
        test_simple_assert();
    })
}

#[test]
fn test_assert_macro_with_complex_expression() {
    common::with_clean_verification(|| {
        // #[proof] auto-verifies internally; success = no panic (#2274)
        #[trust_vc::proof]
        fn test_complex_assert() {
            trust_vc::assert!(3 * 3 + 4 * 4 == 5 * 5);
        }

        // Proof function auto-verifies via ay — no panic means success
        test_complex_assert();
    })
}
