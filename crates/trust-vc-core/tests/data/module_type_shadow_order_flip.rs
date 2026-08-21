// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! FV-1 ORDER-FLIP control: the SAME two declarations as
//! `module_type_shadow_soundness.rs`, only swapped. Before the fix the verdict
//! flipped with declaration order (narrow-first verified, wide-first refuted),
//! which is what proved the registry was guessing. Both orders must now decline.

pub struct S {
    pub x: u64,
}

mod helper {
    pub struct S {
        pub x: u8,
    }
}

#[trust_vc::ensures(true)]
fn collided_field_width_must_not_verify(s: S) -> u64 {
    trust_vc::assert!(s.x <= 255u64);
    0u64
}
