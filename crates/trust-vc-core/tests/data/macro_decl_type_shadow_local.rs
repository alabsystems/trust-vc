// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! NARROWNESS, the third condition: a macro can only do harm when some
//! declaration exists STRICTLY OUTSIDE its module for the expansion to shadow.
//! Here every type is declared in the same module as the invocation, so the
//! outward walk never steps past the macro's scope to reach an answer — and a
//! name bound only by the expansion is carried by no registry, so its own use
//! sites already fail closed as unrecognized types.

mod inner {
    macro_rules! decl_fn {
        () => {
            pub fn helper() -> u64 {
                7u64
            }
        };
    }
    decl_fn!();

    pub struct Local {
        pub x: u8,
    }

    /// TRUE: `Local` is declared right here, beside the invocation. Nothing is
    /// declared outside this module, so there is nothing to shadow.
    #[trust_vc::ensures(true)]
    pub fn local_type_beside_macro_verifies(l: Local) -> u64 {
        trust_vc::assert!(l.x <= 255u8);
        0u64
    }
}
