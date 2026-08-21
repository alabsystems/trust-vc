// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! FV-1 reproducer + narrowness pins for the bare-name source-type registry.
//!
//! The registry keys structs/enums/aliases by BARE identifier and recurses into
//! inline modules, so a nested `mod helper { struct S }` used to silently supply
//! the field types of a top-level `struct S` (first declaration wins). The fix
//! detects the collision and fails closed; the pins below hold the line against
//! that degenerating into blanket rejection of module-declared types.

mod helper {
    pub struct S {
        pub x: u8,
    }
}

pub struct S {
    pub x: u64,
}

/// FALSE: `s.x` is a `u64`, so it may exceed 255. Verifying this requires the
/// engine to have adopted `helper::S`'s `u8` field for a top-level `S` value.
#[trust_vc::ensures(true)]
fn collided_field_width_must_not_verify(s: S) -> u64 {
    trust_vc::assert!(s.x <= 255u64);
    0u64
}

// ---- cross-kind collision: a nested enum shadowing a top-level struct ----

mod kinds {
    pub enum Shape {
        Round,
    }
}

pub struct Shape {
    pub w: u64,
}

/// FALSE for the same reason, through the struct/enum registry split.
#[trust_vc::ensures(true)]
fn cross_kind_collision_must_not_verify(sh: Shape) -> u64 {
    trust_vc::assert!(sh.w <= 255u64);
    0u64
}

// ---- PIN 1: a nested-module type that collides with nothing still works ----

mod widgets {
    pub struct Widget {
        pub weight: u8,
    }
}

use widgets::Widget;

/// TRUE: `weight` really is a `u8`. A non-colliding module-declared type must
/// still resolve to its real fields, so this must VERIFY.
#[trust_vc::ensures(true)]
fn module_type_without_collision_verifies(w: Widget) -> u64 {
    trust_vc::assert!(w.weight <= 255u8);
    0u64
}

/// TRUE: a top-level type that shares the file with (non-colliding) module
/// types must be unaffected.
#[trust_vc::ensures(true)]
fn top_level_type_verifies(s2: Other) -> u64 {
    trust_vc::assert!(s2.x <= 18446744073709551615u64);
    0u64
}

pub struct Other {
    pub x: u64,
}

// ---- PIN 2: token-identical re-declarations are NOT a collision ----

mod left {
    pub struct Twin {
        pub v: u8,
    }
}

mod right {
    pub struct Twin {
        pub v: u8,
    }
}

use left::Twin;

/// TRUE, and BOTH declarations agree on the shape, so declining here would be
/// pure over-rejection: this must still VERIFY.
#[trust_vc::ensures(true)]
fn identical_redeclaration_still_verifies(t: Twin) -> u64 {
    trust_vc::assert!(t.v <= 255u8);
    0u64
}
