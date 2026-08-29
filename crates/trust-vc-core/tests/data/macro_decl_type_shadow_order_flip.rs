// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Declaration ORDER must not decide soundness. Unlike the visible-collision
//! family — where first-declaration-wins made the verdict flip with order — this
//! defect is order-INDEPENDENT: the macro-declared type is invisible in either
//! order, so the single visible declaration answers every scope. Both orders
//! were measured verifying the false claim before the fix.

mod inner {
    macro_rules! decl_s {
        () => {
            pub struct S {
                pub x: u64,
            }
        };
    }
    decl_s!();

    /// FALSE: `S` here is the macro-declared `u64` struct.
    #[trust_vc::ensures(true)]
    pub fn macro_decl_shadow_must_not_verify(s: S) -> u64 {
        trust_vc::assert!(s.x <= 255u64);
        0u64
    }
}

pub struct S {
    pub x: u8,
}

/// TRUE, and at the file root: unaffected in this order too.
#[trust_vc::ensures(true)]
fn top_level_narrow_is_true(s: S) -> u64 {
    trust_vc::assert!(s.x <= 255u8);
    0u64
}
