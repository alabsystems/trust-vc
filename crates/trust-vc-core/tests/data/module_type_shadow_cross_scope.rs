// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! DECLINE PIN: two code-bearing scopes in one file resolve the same bare name
//! to DIFFERENT declarations.
//!
//! Resolution installs exactly one shape per bare name, because the carrier
//! name, the `StructDef` name and the SMT sort name are all the bare name. A
//! contract, body or axiom lowered from `coded` can land in the same
//! verification context as a top-level function's, and both would be typed
//! against that single sort. Picking the verified function's own scope would
//! therefore mis-type the other scope's facts, so disagreement declines for
//! BOTH scopes.

mod coded {
    pub struct D {
        pub v: u8,
    }

    #[trust_vc::ensures(true)]
    pub fn inner_reads_d(d: D) -> u64 {
        trust_vc::assert!(d.v <= 255u8);
        0u64
    }
}

pub struct D {
    pub v: u64,
}

#[trust_vc::ensures(true)]
fn top_level_reads_d(d: D) -> u64 {
    trust_vc::assert!(d.v <= 255u64);
    0u64
}
