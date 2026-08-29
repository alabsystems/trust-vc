// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! RESIDUAL B, the one `a10aea13` recorded and left open: "a macro that declares
//! a type is invisible to this walk".
//!
//! The scope walk resolves a bare type name by stepping OUTWARD from the use
//! site's module, and it is sound only while it can see every binding each step
//! holds. An item-macro INVOCATION defeats that — `decl_s!()` below expands to
//! `struct S { x: u64 }` and binds `S` inside `inner`, so every use site in
//! `inner` names THAT struct. The walk, seeing no `S` in `inner`, stepped past
//! it and answered with the top-level `u8` shape: a confident WRONG answer.
//!
//! Ground truth, `rustc --edition 2021`, this exact shape compiled and run:
//!   top S::x = 255 (u8)
//!   inner S::x = 18446744073709551615 (u64) -- exceeds 255: true
//!   top S::v = 1   inner S::v = 2
//!
//! Both registries were exposed, and the inverted-pair signature was present in
//! both: the FALSE claim verified while the TRUE one was rejected against the
//! same wrong shape.

pub struct S {
    pub x: u8,
}

impl S {
    pub fn v(&self) -> u64 {
        1u64
    }
}

mod inner {
    macro_rules! decl_s {
        () => {
            pub struct S {
                pub x: u64,
            }
            impl S {
                pub fn v(&self) -> u64 {
                    2u64
                }
            }
        };
    }
    decl_s!();

    /// FALSE: `S` here is the macro-declared struct, whose `x` is a `u64` and
    /// may hold 18446744073709551615. Verifying this requires the top-level
    /// `u8` shape to have answered for a value of a different type.
    #[trust_vc::ensures(true)]
    pub fn macro_decl_shadow_must_not_verify(s: S) -> u64 {
        trust_vc::assert!(s.x <= 255u64);
        0u64
    }

    /// TRUE: `x` really is a `u64`, so it may hold 1000. The other half of the
    /// inverted pair — this was REJECTED against the `u8` sort.
    #[trust_vc::ensures(true)]
    pub fn macro_decl_wide_construct_is_true() -> u64 {
        let s = S { x: 1000u64 };
        trust_vc::assert!(s.x == 1000u64);
        0u64
    }

    /// FALSE through the METHOD registry: `S::v` here is the macro-declared one,
    /// which returns 2. This verified, keyed by the bare receiver name.
    #[trust_vc::ensures(true)]
    pub fn macro_decl_method_must_not_verify(s: S) -> u64 {
        trust_vc::assert!(s.v() == 1u64);
        0u64
    }

    /// TRUE: the real answer is 2. This was refuted with a model showing the
    /// 8-bit carrier `(S_S #x00)` — the top-level struct's shape.
    #[trust_vc::ensures(true)]
    pub fn macro_decl_method_true_is_two(s: S) -> u64 {
        trust_vc::assert!(s.v() == 2u64);
        0u64
    }
}

// ---- NARROWNESS PIN: the use site OUTSIDE the macro's module is unaffected ----

/// TRUE: this function is at the file root, so `inner`'s macro is not on its
/// outward walk path and cannot bind anything it reads. It must still VERIFY,
/// in the very same file as the reproducers above.
#[trust_vc::ensures(true)]
fn top_level_narrow_is_true(s: S) -> u64 {
    trust_vc::assert!(s.x <= 255u8);
    0u64
}
