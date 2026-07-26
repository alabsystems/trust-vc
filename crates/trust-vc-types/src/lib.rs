//! TrustVc types - Spec-only ghost collections
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Provides ghost types for specification:
//! - `Seq<T>` - Mathematical sequences (ay array theory)
//! - `Set<T>` - Mathematical sets (ay set theory)
//! - `Multiset<T>` - Mathematical bags with multiplicity counts
//! - `Map<K, V>` - Mathematical maps (ay array theory)
//! - `SpecFn<Args, Ret>` - Spec-only closures for higher-order specs
//! - `Ghost<T>` - Zero-sized wrapper for proof values (always Copy)
//! - `Tracked<T>` - Linear ghost ownership wrapper (Copy only if T: Copy)
//! - `Snapshot<T>` - Captures value at program point for postconditions
//! - `Proph<T>` - Prophecy variable for future-value reasoning
//! - `View` trait - Convert runtime types to spec types
//!
//! These types exist only for verification and are erased at runtime.
//!
//! # Formal Contracts
//!
//! Collection methods with preconditions use `trust_vc::ghost_requires!` for formal
//! verification. The verifier (trust_vc) checks these at call sites.
//!
//! **Important:** `ghost_requires!` is verification-only and adds no runtime
//! precondition checks. These APIs are for specification, not runtime use: a
//! failed precondition does not itself trigger a runtime check, but ghost
//! accessors such as `Seq::index`, `Seq::last`, `Seq::first`, and `Map::get`
//! still panic unconditionally if executed.

/// Builds a ghost [`Map`] by inserting key/value pairs from left to right.
///
/// This mirrors the Verus `map![k => v, ...]` literal surface for ordinary Rust
/// key/value expressions. Verus-specific value implication syntax such as
/// `a ==> b` should be written with the corresponding TrustVc boolean expression
/// before it is used as a macro value.
#[macro_export]
macro_rules! map {
    () => {
        $crate::Map::empty()
    };
    ($($key:expr => $value:expr),+ $(,)?) => {{
        let __trust_vc_map = $crate::Map::empty();
        $(
            let __trust_vc_map = __trust_vc_map.insert($key, $value);
        )+
        __trust_vc_map
    }};
}

/// Builds a ghost [`Set`] by inserting elements from left to right.
///
/// `cargo-trust_vc` lowers non-empty literals directly in proof contexts, so
/// literals such as `set![1i32, 2, 3]` carry finite set facts.
#[macro_export]
macro_rules! set {
    () => {
        $crate::Set::empty()
    };
    ($first:expr $(, $rest:expr)* $(,)?) => {{
        let set = $crate::Set::empty().insert($first);
        $(
            let set = set.insert($rest);
        )*
        set
    }};
}

/// Compatibility shims for neighboring ghost/spec APIs (e.g., trust_wp).
pub mod compat;

mod runtime_boundary;

mod ghost;
mod invariant;
mod list;
mod map;
mod multiset;
mod proph;
mod seq;
mod set;
mod snapshot;
mod spec_fn;
mod tracked;
mod tree;
mod view;

pub use ghost::Ghost;
pub use invariant::{InvariantBinding, InvariantPredicate, LocalInvariant};
pub use list::List;
pub use map::Map;
pub use multiset::Multiset;
pub use proph::Proph;
pub use seq::Seq;
pub use set::Set;
pub use snapshot::Snapshot;
pub use spec_fn::SpecFn;
pub use tracked::Tracked;
pub use tree::Tree;
pub use view::View;

/// Rust-side placeholder for Verus-style spec `int`.
///
/// TrustVc maps the source type name `int` to unbounded mathematical integer
/// semantics during verification. The alias exists so proof/spec code using
/// `int` can still type-check as Rust.
#[allow(non_camel_case_types)]
pub type int = i128;

/// Rust-side placeholder for Verus-style spec `nat`.
///
/// TrustVc maps the source type name `nat` to non-negative mathematical integer
/// semantics during verification. The alias exists so proof/spec code using
/// `nat` can still type-check as Rust.
#[allow(non_camel_case_types)]
pub type nat = u128;

/// Builds a finite ghost [`Seq`] literal.
///
/// `cargo-trust_vc` lowers this macro directly in proof contexts, so finite
/// literals such as `seq![1i32, 2, 3]` and literal repeats such as
/// `seq![5i32; 10]` carry exact logical length and element facts.
#[macro_export]
macro_rules! seq {
    () => {
        $crate::Seq::empty()
    };
    ($elem:expr; 0) => {
        $crate::Seq::empty()
    };
    ($elem:expr; 1) => {
        $crate::seq![$elem]
    };
    ($elem:expr; 2) => {
        $crate::seq![$elem, $elem]
    };
    ($elem:expr; 3) => {
        $crate::seq![$elem, $elem, $elem]
    };
    ($elem:expr; 4) => {
        $crate::seq![$elem, $elem, $elem, $elem]
    };
    ($elem:expr; 5) => {
        $crate::seq![$elem, $elem, $elem, $elem, $elem]
    };
    ($elem:expr; 6) => {
        $crate::seq![$elem, $elem, $elem, $elem, $elem, $elem]
    };
    ($elem:expr; 7) => {
        $crate::seq![$elem, $elem, $elem, $elem, $elem, $elem, $elem]
    };
    ($elem:expr; 8) => {
        $crate::seq![$elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem]
    };
    ($elem:expr; 9) => {
        $crate::seq![$elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem]
    };
    ($elem:expr; 10) => {
        $crate::seq![
            $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem
        ]
    };
    ($elem:expr; 11) => {
        $crate::seq![
            $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem
        ]
    };
    ($elem:expr; 12) => {
        $crate::seq![
            $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem
        ]
    };
    ($elem:expr; 13) => {
        $crate::seq![
            $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem,
            $elem
        ]
    };
    ($elem:expr; 14) => {
        $crate::seq![
            $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem,
            $elem, $elem
        ]
    };
    ($elem:expr; 15) => {
        $crate::seq![
            $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem,
            $elem, $elem, $elem
        ]
    };
    ($elem:expr; 16) => {
        $crate::seq![
            $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem, $elem,
            $elem, $elem, $elem, $elem
        ]
    };
    ($elem:expr; $len:expr) => {
        compile_error!("trust_vc_types::seq![value; len] currently supports literal len 0 through 16")
    };
    ($first:expr $(, $rest:expr)* $(,)?) => {{
        let seq = $crate::Seq::empty().push($first);
        $(
            let seq = seq.push($rest);
        )*
        seq
    }};
}

#[cfg(test)]
mod seq_macro_tests {
    use super::{Seq, Set};

    #[test]
    fn seq_macro_list_type_checks() {
        let _: Seq<i32> = crate::seq![1i32, 2i32, 3i32];
    }

    #[test]
    fn seq_macro_repeat_type_checks() {
        let _: Seq<i32> = crate::seq![5i32; 10];
    }

    #[test]
    fn set_macro_list_type_checks() {
        let _: Set<i32> = crate::set![1i32, 2i32, 3i32,];
    }
}
