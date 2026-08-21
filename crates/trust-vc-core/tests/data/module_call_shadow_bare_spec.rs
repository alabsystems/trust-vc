// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! FV-A, bare-spelling half — the MINIMAL form, no sub-module needed. The spec
//! catalog keys a top-level spec fn by its bare ident and answers a bare `v()`
//! written anywhere in the file, but `mod inner`'s own `v` shadows it for every
//! call written inside `inner`.
//!
//! Ground truth (rustc): `inner::bare_shadow() == false`, against
//! `ensures(result)`. `bare_shadow` must NOT verify.

#[trust_vc::spec]
fn v() -> bool {
    true
}

mod inner {
    #[trust_vc::spec]
    pub fn v() -> bool {
        false
    }

    #[trust_vc::proof]
    #[trust_vc::ensures(result)]
    pub fn bare_shadow() -> bool {
        v()
    }
}
