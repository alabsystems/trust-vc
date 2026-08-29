// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Fixture for `const_pattern_scope_soundness.rs`.
//!
//! `const_pattern_desugar` decides a bare pattern ident by DECLARATION rather
//! than by spelling — but only for declarations it SEES. Its first collector
//! descended into `Item::Mod` content and the top-level statement items of an
//! `Item::Fn` block, and nowhere else, so a `const` (or a `use` alias) declared
//! in an `impl` method body, a trait DEFAULT method body, or ANY nested block
//! was invisible. The name stayed a bare lowercase ident,
//! `arm_pattern_match_condition` answered `Always`, and the sibling arm's
//! prior-negation `!(true)` — FALSE — vacuously discharged it.
//!
//! Every `*_must_not_verify` function below is a container shape that reached
//! `Verified` before the whole-tree scan; every `*_still_binds` function is the
//! narrowness pin that must survive it, because declining to bind is the
//! overwhelmingly common case and turning the feature off passes every cardinal
//! probe.
//!
//! Each route uses its OWN const name: the registry is file-wide, so a shared
//! name would let one route's declaration mask another's and the pins would
//! stop discriminating.
#![allow(non_upper_case_globals)]
#![allow(dead_code)]
#![allow(unused_imports)]

/// Fold sources for the `use`-alias routes. Each is aliased from exactly one
/// nested scope, so the ALIAS is what changes verdict, not the const.
pub const src_impl_body: u64 = 5;
pub const src_nested_block: u64 = 5;
pub const src_trait_default: u64 = 5;

/// The capability source: aliased at FILE scope, where the fold is legitimate.
pub const src_capability: u64 = 5;
pub use crate::src_capability as alias_capability;

pub struct Holder;

// ---- ROUTE 1: `const` in an `impl` method body -----------------------------

impl Holder {
    #[trust_vc::requires(n < 100)]
    pub fn impl_body_const_sibling_must_not_verify(n: u64) {
        const k_impl_body: u64 = 5;
        match n {
            k_impl_body => {}
            _ => {
                assert!(false);
            }
        }
    }

    /// ROUTE 4: a nested block INSIDE an `impl` method body — the shape a
    /// three-arm `Item::Impl`/`Item::Trait` patch would still have missed.
    #[trust_vc::requires(n < 100)]
    pub fn impl_nested_block_const_sibling_must_not_verify(n: u64) {
        {
            const k_impl_nested: u64 = 5;
            match n {
                k_impl_nested => {}
                _ => {
                    assert!(false);
                }
            }
        }
    }

    /// ROUTE 7: a `static`, not a `const`. Same value namespace, same hole.
    #[trust_vc::requires(n < 100)]
    pub fn impl_body_static_sibling_must_not_verify(n: u64) {
        static k_impl_static: u64 = 5;
        match n {
            k_impl_static => {}
            _ => {
                assert!(false);
            }
        }
    }

    /// ROUTE 8: a `use` ALIAS in an `impl` method body. The alias defeats the
    /// spelling heuristic on its own; being in an unwalked scope defeated the
    /// declaration registry too.
    #[trust_vc::requires(n < 100)]
    pub fn impl_body_use_alias_sibling_must_not_verify(n: u64) {
        use crate::src_impl_body as alias_impl_body;
        match n {
            alias_impl_body => {}
            _ => {
                assert!(false);
            }
        }
    }

    /// NARROWNESS PIN. An ordinary lowercase binder inside an `impl` method
    /// still BINDS — this is the common case and the thing a blanket rejection
    /// would destroy.
    #[trust_vc::requires(n < 100)]
    #[trust_vc::ensures(result == n)]
    pub fn impl_body_binder_still_binds(n: u64) -> u64 {
        match n {
            bound_impl => bound_impl,
        }
    }

    /// The DISCRIMINATOR for the pin above: a binder binds, it does not
    /// constrain, so the false claim of the same shape must still refute.
    #[trust_vc::requires(n < 100)]
    #[trust_vc::ensures(result == n + 1)]
    pub fn impl_body_binder_liar_must_not_verify(n: u64) -> u64 {
        match n {
            bound_impl_liar => bound_impl_liar,
        }
    }

    /// NARROWNESS PIN. A binder inside a nested block inside an `impl` method.
    #[trust_vc::requires(n < 100)]
    #[trust_vc::ensures(result == n)]
    pub fn impl_nested_block_binder_still_binds(n: u64) -> u64 {
        {
            match n {
                bound_impl_nested => bound_impl_nested,
            }
        }
    }
}

/// NARROWNESS PIN. An ASSOCIATED const is not a bare-name pattern (`Assoc::v`
/// is required), so walking `impl` bodies must NOT start collecting them —
/// doing so would convert a genuine binder into a fail-closed marker.
pub struct Assoc;

impl Assoc {
    pub const bound_assoc: u64 = 5;

    #[trust_vc::requires(n < 100)]
    #[trust_vc::ensures(result == n)]
    pub fn binder_colliding_with_impl_assoc_const_still_binds(n: u64) -> u64 {
        match n {
            bound_assoc => bound_assoc,
        }
    }
}

// ---- ROUTE 2: `const` in a trait DEFAULT method body ------------------------

pub trait Defaults {
    /// NARROWNESS PIN. A trait ASSOCIATED const is a `TraitItem::Const`, not an
    /// `Item::Const`, and must stay uncollected.
    const bound_trait_assoc: u64 = 5;

    #[trust_vc::requires(n < 100)]
    fn trait_default_const_sibling_must_not_verify(n: u64) {
        const k_trait_default: u64 = 5;
        match n {
            k_trait_default => {}
            _ => {
                assert!(false);
            }
        }
    }

    /// ROUTE 10: a `use` alias in a trait default body.
    #[trust_vc::requires(n < 100)]
    fn trait_default_use_alias_sibling_must_not_verify(n: u64) {
        use crate::src_trait_default as alias_trait_default;
        match n {
            alias_trait_default => {}
            _ => {
                assert!(false);
            }
        }
    }

    /// NARROWNESS PIN in a trait default body.
    #[trust_vc::requires(n < 100)]
    #[trust_vc::ensures(result == n)]
    fn trait_default_binder_still_binds(n: u64) -> u64 {
        match n {
            bound_trait => bound_trait,
        }
    }

    #[trust_vc::requires(n < 100)]
    #[trust_vc::ensures(result == n)]
    fn binder_colliding_with_trait_assoc_const_still_binds(n: u64) -> u64 {
        match n {
            bound_trait_assoc => bound_trait_assoc,
        }
    }
}

// ---- ROUTE 3: `const` in a nested block ------------------------------------

#[trust_vc::requires(n < 100)]
pub fn nested_block_const_sibling_must_not_verify(n: u64) {
    {
        const k_nested_block: u64 = 5;
        match n {
            k_nested_block => {}
            _ => {
                assert!(false);
            }
        }
    }
}

/// ROUTE 9: a `use` alias in a nested block.
#[trust_vc::requires(n < 100)]
pub fn nested_block_use_alias_sibling_must_not_verify(n: u64) {
    {
        use crate::src_nested_block as alias_nested_block;
        match n {
            alias_nested_block => {}
            _ => {
                assert!(false);
            }
        }
    }
}

/// ROUTE 5: an `if` block.
#[trust_vc::requires(n < 100)]
pub fn if_block_const_sibling_must_not_verify(n: u64) {
    if n < 200 {
        const k_if_block: u64 = 5;
        match n {
            k_if_block => {}
            _ => {
                assert!(false);
            }
        }
    }
}

/// ROUTE 6: a `while`-loop body block.
#[trust_vc::requires(n < 100)]
pub fn loop_body_const_sibling_must_not_verify(n: u64) {
    let mut i: u64 = 0;
    while i < 1 {
        const k_loop_body: u64 = 5;
        match n {
            k_loop_body => {}
            _ => {
                assert!(false);
            }
        }
        i = i + 1;
    }
}

/// ROUTE 11: a match-ARM block — a scope with no item list of its own at all.
#[trust_vc::requires(n < 100)]
pub fn match_arm_const_sibling_must_not_verify(n: u64) {
    match n {
        _ => {
            const k_match_arm: u64 = 5;
            match n {
                k_match_arm => {}
                _ => {
                    assert!(false);
                }
            }
        }
    }
}

/// ROUTE 12: an `impl` inside an inline `mod` — nesting the container shapes.
pub mod inner {
    pub struct Deep;

    impl Deep {
        #[trust_vc::requires(n < 100)]
        pub fn mod_impl_const_sibling_must_not_verify(n: u64) {
            const k_mod_impl: u64 = 5;
            match n {
                k_mod_impl => {}
                _ => {
                    assert!(false);
                }
            }
        }
    }
}

// ---- NARROWNESS PINS at file scope -----------------------------------------

#[trust_vc::requires(n < 100)]
#[trust_vc::ensures(result == n)]
pub fn nested_block_binder_still_binds(n: u64) -> u64 {
    {
        match n {
            bound_nested => bound_nested,
        }
    }
}

/// NARROWNESS PIN. A `use` that resolves to a FUNCTION leaves an ordinary
/// binder: only const-like imports may change behaviour, and the newly walked
/// scopes must not change that. The alias lives in one method, the binder of
/// the same name in another.
pub fn plain_helper(x: u64) -> u64 {
    x
}

pub struct AliasHolder;

impl AliasHolder {
    pub fn uses_the_fn_alias(y: u64) -> u64 {
        use crate::plain_helper as bound_fn_alias;
        bound_fn_alias(y)
    }

    #[trust_vc::requires(n < 100)]
    #[trust_vc::ensures(result == n)]
    pub fn fn_alias_leaves_a_binder_alone(n: u64) -> u64 {
        match n {
            bound_fn_alias => bound_fn_alias,
        }
    }
}

// ---- CAPABILITY PINS -------------------------------------------------------
// Proving less is not a fix. A FILE-SCOPE const alias must still FOLD and
// supply `n == 5`, which is also the pin on the collector's top-level `use`
// bookkeeping: entering a top-level alias twice would demote it to the
// fail-closed marker and silently retire this capability.

#[trust_vc::requires(n < 100)]
pub fn top_level_alias_arm_still_folds(n: u64) {
    match n {
        alias_capability => {
            assert!(n == 5);
        }
        _ => {}
    }
}

#[trust_vc::requires(n < 100)]
pub fn top_level_alias_arm_liar_must_not_verify(n: u64) {
    match n {
        alias_capability => {
            assert!(n == 6);
        }
        _ => {}
    }
}

pub const cap_direct: u64 = 7;

#[trust_vc::requires(n < 100)]
pub fn top_level_const_arm_still_folds(n: u64) {
    match n {
        cap_direct => {
            assert!(n == 7);
        }
        _ => {}
    }
}

#[trust_vc::requires(n < 100)]
pub fn top_level_const_arm_liar_must_not_verify(n: u64) {
    match n {
        cap_direct => {
            assert!(n == 8);
        }
        _ => {}
    }
}
