// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! An allowlist of QUALIFIER ROOTS is only worth anything if the file has not
//! rebound the root: `mod trust_vc { .. }` makes `trust_vc::` name the local
//! module, not the crate.

mod trust_vc {
    macro_rules! assume {
        ($e:expr) => {};
    }
    pub(crate) use assume;
}

/// FALSE: `trust_vc::assume!` here is the LOCAL module's no-op macro.
#[::trust_vc::ensures(true)]
fn rebound_root_must_not_verify(x: u64) -> u64 {
    trust_vc::assume!(x == 0u64);
    ::trust_vc::assert!(x <= 255u64);
    0u64
}
