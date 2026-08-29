// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! The qualifier was discarded outright: `path_last_segment` threw away every
//! segment but the last, so `m::assume!` was read as trust-vc's `assume!`.

mod m {
    macro_rules! assume {
        ($e:expr) => {};
    }
    pub(crate) use assume;

    /// FALSE: inside `m`, the bare name IS the user's no-op macro.
    #[trust_vc::ensures(true)]
    pub fn module_local_assume_must_not_verify(x: u64) -> u64 {
        assume!(x == 0u64);
        trust_vc::assert!(x <= 255u64);
        0u64
    }
}

/// FALSE: `m::assume!` is the user's NO-OP macro, not a trust-vc assumption.
#[trust_vc::ensures(true)]
fn qualified_user_assume_must_not_verify(x: u64) -> u64 {
    m::assume!(x == 0u64);
    trust_vc::assert!(x <= 255u64);
    0u64
}

/// NARROWNESS PIN: a `macro_rules!` inside `mod m` is not in scope in the
/// PARENT module, so the top-level `assume!` is still trust-vc's and this must
/// keep verifying exactly as it did before.
#[trust_vc::ensures(true)]
fn top_level_assume_is_unaffected(x: u64) -> u64 {
    assume!(x == 0u64);
    trust_vc::assert!(x <= 255u64);
    0u64
}
