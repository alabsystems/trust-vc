// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! IMPORT-FLIP control for `module_type_shadow_use_import.rs`: the SAME two
//! declarations in the SAME order, only the `use` points at `beta` instead of
//! `alpha`. The verdict must follow the import, not the source position of the
//! declarations.

mod alpha {
    pub struct T {
        pub v: u8,
    }
}

mod beta {
    pub struct T {
        pub v: u64,
    }
}

use beta::T;

/// FALSE for `beta::T` (`v` is a `u64`, so it may exceed 255). Verifying this
/// would mean the first-declared `alpha::T` (`u8`) had been adopted for a use
/// site that names `beta::T`.
#[trust_vc::ensures(true)]
fn use_binding_selects_declaration(t: T) -> u64 {
    trust_vc::assert!(t.v <= 255u64);
    0u64
}
