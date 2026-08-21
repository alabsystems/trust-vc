// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ORDER-FLIP CONTROL for `module_call_shadow_bare_spec.rs`: `mod inner` is
//! written FIRST. The verdict must be identical — the strike depends on the SET
//! of declarations, never on which one the file writes first.

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

#[trust_vc::spec]
fn v() -> bool {
    true
}
