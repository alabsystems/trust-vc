// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! A `use` RENAME binds a special name to a different macro without a
//! `macro_rules!` of that name appearing anywhere.

mod util {
    macro_rules! noop {
        ($e:expr) => {};
    }
    pub(crate) use noop as assume;
}
use util::assume;

/// FALSE: `assume` here is a `use`-ALIAS of the user's no-op macro.
#[trust_vc::ensures(true)]
fn use_aliased_assume_must_not_verify(x: u64) -> u64 {
    assume!(x == 0u64);
    trust_vc::assert!(x <= 255u64);
    0u64
}
