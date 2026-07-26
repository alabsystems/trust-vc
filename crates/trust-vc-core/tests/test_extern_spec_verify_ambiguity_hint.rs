// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use trust_vc_core::{clear_extern_contracts, register_extern_spec_from_source};

#[test]
fn test_register_extern_spec_from_source_surfaces_ambiguity_hint() {
    clear_extern_contracts();

    let error = register_extern_spec_from_source(
        "register_ambiguous.rs",
        r#"
            trust_vc::extern_spec! {
                impl Vec::<u8> {
                    #[requires(false)]
                    fn pop(&mut self) -> Option<u8>;
                }
            }

            trust_vc::extern_spec! {
                impl Vec::<u16> {
                    #[requires(true)]
                    fn pop(&mut self) -> Option<u16>;
                }
            }
        "#,
        "Vec::pop",
    )
    .expect_err("ambiguous shorthand lookup should fail closed")
    .to_string();

    assert!(
        error.contains("Vec::pop"),
        "error should identify the ambiguous target, got: {error}"
    );
    assert!(
        error.contains("2 entries match"),
        "error should report the number of conflicting matches, got: {error}"
    );
    assert!(
        error.contains("use explicit generic arguments to disambiguate"),
        "error should tell the caller how to fix the ambiguity, got: {error}"
    );
}
