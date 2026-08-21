// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! NARROWNESS PIN for the bare-spec strike: the shadow is present, but the use
//! site writes the MODULE-QUALIFIED spelling `inner::v()`, which the catalog's
//! module-keyed entry resolves unambiguously. Must VERIFY, and must verify
//! `!result` — `inner::v()` is `false`, so this also discriminates against the
//! top-level `v` being substituted.

#[trust_vc::spec]
fn v() -> bool {
    true
}

mod inner {
    #[trust_vc::spec]
    pub fn v() -> bool {
        false
    }
}

#[trust_vc::proof]
#[trust_vc::ensures(!result)]
fn qualified_shadowed() -> bool {
    inner::v()
}
