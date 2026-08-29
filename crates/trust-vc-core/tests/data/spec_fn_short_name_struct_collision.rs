// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! FV-1 COLLISION PROBE for the short-name struct spec-fn parameter fix.
//!
//! FV-1 (`module_type_shadow_soundness.rs`) was a cardinal false-verify in which
//! a bare type name that two declarations claim resolved first-declaration-wins.
//! The short-name fix resolves a `TypeParam` leaf against the SAME source-type
//! registry the `Opaque` leaf arm already used, so it inherits that registry's
//! collision policy — and must inherit its protection too, not route around it.
//!
//! `SP` is declared twice with different field widths. `narrow_inv` is asserted
//! as an UNCONDITIONAL postcondition, so nothing in the contract makes it true:
//! `s.a <= 255` holds for every `u8` value but not for every `u64` one. A
//! verdict of `Verified` therefore means the engine adopted the `u8` declaration
//! on no grounds.

pub struct SP {
    pub a: u64,
}

mod helper {
    pub struct SP {
        pub a: u8,
    }
}

#[trust_vc::spec]
fn narrow_inv(s: SP) -> bool {
    s.a <= 255
}

#[trust_vc::ensures(narrow_inv(p))]
fn collided_short_name_must_not_verify(p: SP) -> u64 {
    0
}
