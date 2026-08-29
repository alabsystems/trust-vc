// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Fixture for `const_pattern_use_alias_soundness.rs`.
//!
//! A `use` introduces a second NAME for a const. The declaration decides what a
//! bare pattern ident means, so both names must reach the same verdict — and an
//! import that names a fn/type/struct must leave an ordinary binder alone.
#![allow(non_upper_case_globals)]
#![allow(dead_code)]
#![allow(unused_imports)]

pub const lower_k: u64 = 5;

pub mod helpers {
    pub const limit: u64 = 5;
    pub const MAXV: u64 = 5;
    pub fn helper_fn(x: u64) -> u64 {
        x
    }
    pub struct Payload {
        pub a: u64,
    }
    pub type Scalar = u64;
}

/// An out-of-line module: this file cannot see what it declares.
pub mod out_of_line;

use crate::helpers::limit;
use crate::helpers::helper_fn as min;
use crate::helpers::Payload as payload;
use crate::helpers::Scalar as scalar;
use crate::helpers::MAXV as maxv;
use crate::lower_k as alias_k;
use crate::out_of_line::unresolvable_k;

// ---- THE CARDINAL FALSE VERIFY --------------------------------------------
// Same const, same file, two names. `under_own_name` always refuted; the
// aliased spelling VERIFIED, because the registry was keyed on declaration
// idents and never saw the alias.

#[trust_vc::requires(n < 100)]
pub fn own_name_sibling_must_not_verify(n: u64) {
    match n {
        lower_k => {}
        _ => {
            assert!(false);
        }
    }
}

#[trust_vc::requires(n < 100)]
pub fn alias_sibling_must_not_verify(n: u64) {
    match n {
        alias_k => {}
        _ => {
            assert!(false);
        }
    }
}

/// An UPPERCASE const renamed to a lowercase local: the alias defeats the
/// registry regardless of spelling, so this is not a case-heuristic residual.
#[trust_vc::requires(n < 100)]
pub fn upper_const_aliased_to_lower_must_not_verify(n: u64) {
    match n {
        maxv => {}
        _ => {
            assert!(false);
        }
    }
}

/// A cross-module import under its own (lowercase) name.
#[trust_vc::requires(n < 100)]
pub fn cross_module_import_must_not_verify(n: u64) {
    match n {
        limit => {}
        _ => {
            assert!(false);
        }
    }
}

/// THE DISCRIMINATOR. The literal twin of all four: the same Rust program.
#[trust_vc::requires(n < 100)]
pub fn literal_twin_must_not_verify(n: u64) {
    match n {
        5 => {}
        _ => {
            assert!(false);
        }
    }
}

// ---- LIAR PINS -------------------------------------------------------------
// The aliased arm now SUPPLIES `n == 5`. Proving more is only progress if
// nothing FALSE became provable.

#[trust_vc::requires(n < 100)]
pub fn alias_arm_liar_must_not_verify(n: u64) {
    match n {
        alias_k => {
            assert!(n == 6);
        }
        _ => {}
    }
}

#[trust_vc::requires(n < 100)]
pub fn alias_wildcard_liar_must_not_verify(n: u64) {
    match n {
        alias_k => {}
        _ => {
            assert!(n == 5);
        }
    }
}

// ---- CAPABILITY ------------------------------------------------------------

#[trust_vc::requires(n < 100)]
pub fn alias_arm_supplies_its_value(n: u64) {
    match n {
        alias_k => {
            assert!(n == 5);
        }
        _ => {}
    }
}

#[trust_vc::requires(n < 100)]
pub fn alias_wildcard_knows_the_negation(n: u64) {
    match n {
        alias_k => {}
        _ => {
            assert!(n != 5);
        }
    }
}

// ---- NARROWNESS PINS -------------------------------------------------------
// Only CONST aliases may change behaviour. An import naming a fn, a type or a
// struct leaves the local name an ordinary BINDER — `use std::cmp::min;` must
// not stop `match n { min => .. }` from binding.

#[trust_vc::requires(n < 100)]
pub fn ordinary_binder_still_binds_among_imports(n: u64) -> u64 {
    match n {
        m => {
            assert!(m == n);
            m
        }
    }
}

#[trust_vc::requires(n < 100)]
pub fn fn_alias_binder_still_binds(n: u64) -> u64 {
    match n {
        min => {
            assert!(min == n);
            min
        }
    }
}

#[trust_vc::requires(n < 100)]
pub fn fn_alias_binder_liar_must_not_verify(n: u64) {
    match n {
        min => {
            assert!(min == 5);
        }
    }
}

#[trust_vc::requires(n < 100)]
pub fn type_alias_binder_still_binds(n: u64) -> u64 {
    match n {
        scalar => {
            assert!(scalar == n);
            scalar
        }
    }
}

#[trust_vc::requires(n < 100)]
pub fn struct_alias_binder_still_binds(n: u64) -> u64 {
    match n {
        payload => {
            assert!(payload == n);
            payload
        }
    }
}

// ---- NESTED SCOPES ---------------------------------------------------------
// A function inside an inline module is verified too, so a `use` in that module
// cannot be invisible. Its value is not folded (this pass does not model scope);
// it fails closed.

pub mod nested {
    use crate::helpers::helper_fn as nested_min;
    use crate::lower_k as nested_alias;

    #[trust_vc::requires(n < 100)]
    pub fn nested_alias_sibling_must_not_verify(n: u64) {
        match n {
            nested_alias => {}
            _ => {
                assert!(false);
            }
        }
    }

    /// `lower_k` is declared at FILE top level, which is not in scope here —
    /// Rust items do not nest lexically — so this is an ordinary BINDER and the
    /// claim is false. Folding it to `5` narrowed the arm and verified.
    #[trust_vc::requires(n < 100)]
    pub fn nested_top_level_const_is_a_binder_must_not_verify(n: u64) {
        match n {
            lower_k => {
                assert!(n == 5);
            }
        }
    }

    /// The pin holds at depth: a nested fn import still leaves a binder.
    #[trust_vc::requires(n < 100)]
    pub fn nested_fn_alias_binder_still_binds(n: u64) -> u64 {
        match n {
            nested_min => {
                assert!(nested_min == n);
                nested_min
            }
        }
    }
}

// ---- FAIL CLOSED, NOT GUESSED ----------------------------------------------

/// The import names an item in an out-of-line module, so this file cannot say
/// what it is. Declining is sound; guessing is not.
#[trust_vc::requires(n < 100)]
pub fn unresolvable_import_must_not_verify(n: u64) {
    match n {
        unresolvable_k => {}
        _ => {
            assert!(false);
        }
    }
}
