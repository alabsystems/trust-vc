// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! The binding points INTO trust-vc, so a check of "where does this name come
//! from" passes — but it renames a DIFFERENT trust-vc macro onto the name.

use trust_vc::hide as assume;

/// FALSE: `assume!` is bound to `trust_vc::hide!`, which asserts nothing and
/// assumes nothing about `x`.
#[trust_vc::ensures(true)]
fn trust_vc_rename_must_not_verify(x: u64) -> u64 {
    assume!(x == 0u64);
    trust_vc::assert!(x <= 255u64);
    0u64
}
