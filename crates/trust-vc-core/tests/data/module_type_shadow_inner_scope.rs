// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Scope-relative resolution INWARD: the use site lives inside `inner`, which
//! declares its own `R`, so the innermost declaration wins over the top-level
//! one. Only `inner` holds code here, so `inner` is the sole scope that has to
//! agree.

pub struct R {
    pub v: u64,
}

mod inner {
    pub struct R {
        pub v: u8,
    }

    /// RESOLVABLE: the enclosing module declares `R` as a `u8` carrier, so
    /// `r.v <= 255u8` must VERIFY.
    #[trust_vc::ensures(true)]
    pub fn inner_scope_declaration_wins(r: R) -> u64 {
        trust_vc::assert!(r.v <= 255u8);
        0u64
    }
}
