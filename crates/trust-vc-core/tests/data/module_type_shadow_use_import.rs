// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Scope-relative resolution through a `use` binding: neither declaration of
//! `T` is at top level, so the bare `T` at the use site is named by the `use`
//! and by nothing else.
//!
//! `alpha` is declared FIRST here and in the `_flip` companion; only the `use`
//! differs. That is what proves the answer comes from the import and not from
//! declaration order.

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

use alpha::T;

/// RESOLVABLE: `use alpha::T` names the `u8` declaration, so `t.v <= 255u8`
/// must VERIFY.
#[trust_vc::ensures(true)]
fn use_binding_selects_declaration(t: T) -> u64 {
    trust_vc::assert!(t.v <= 255u8);
    0u64
}
