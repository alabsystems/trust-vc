// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Scope-relative resolution of a colliding bare type name: the case a bare
//! name is written at TOP LEVEL while a same-named type also exists inside an
//! inline module. Rust resolves that to the top-level declaration, and so does
//! the source-type registry — no declaration-order tiebreak involved.
//!
//! The two declarations are deliberately NARROW-INSIDE / WIDE-OUTSIDE inverted
//! relative to the FV-1 reproducer so that the positive direction discriminates:
//! `p.x <= 255u8` is provable ONLY for the top-level `u8` field. Resolving to
//! `narrow_inner::P` yields a counterexample; declining yields an error.

mod narrow_inner {
    pub struct P {
        pub x: u64,
    }
}

pub struct P {
    pub x: u8,
}

/// RESOLVABLE: a top-level use site names the top-level `P` (`u8`), so this
/// must VERIFY rather than decline.
#[trust_vc::ensures(true)]
fn top_level_declaration_wins(p: P) -> u64 {
    trust_vc::assert!(p.x <= 255u8);
    0u64
}

/// RESOLVABLE: `self::P` spells the SAME declaration the bare name resolves to,
/// so the explicit qualifier is accepted and this must VERIFY.
#[trust_vc::ensures(true)]
fn qualified_path_naming_the_winner_resolves(p: self::P) -> u64 {
    trust_vc::assert!(p.x <= 255u8);
    0u64
}

/// DECLINE PIN: `narrow_inner::P` names the OTHER declaration. The registry
/// carries one shape per bare name — the carrier name, the `StructDef` name and
/// the SMT sort name are all `P` — so the loser's shape is unrepresentable in
/// this verification context and the use site must fail closed instead of
/// silently receiving the top-level `u8` field.
#[trust_vc::ensures(true)]
fn qualified_path_naming_the_loser_declines(p: narrow_inner::P) -> u64 {
    trust_vc::assert!(p.x <= 255u64);
    0u64
}
