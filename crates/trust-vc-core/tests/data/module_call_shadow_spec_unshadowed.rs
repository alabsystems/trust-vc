// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! NARROWNESS PIN for the bare-spec strike: with NO nested re-declaration of
//! `v`, the top-level spec fn still answers a bare `v()` written inside a
//! module. Must VERIFY — the strike may only fire on a genuine shadow.

#[trust_vc::spec]
fn v() -> bool {
    true
}

mod inner {
    #[trust_vc::proof]
    #[trust_vc::ensures(result)]
    pub fn uses_top() -> bool {
        v()
    }
}
