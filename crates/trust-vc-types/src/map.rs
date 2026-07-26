// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{marker::PhantomData, ops::Index};

use crate::runtime_boundary::ghost_runtime_panic;
use crate::{Set, SpecFn};

/// A mathematical map for specifications.
///
/// `Map<K, V>` represents an immutable mapping from keys to values.
/// It maps to ay's array theory for verification.
///
/// # Example
/// ```text
/// #[trust_vc::spec]
/// fn lookup(m: Map<i32, String>, key: i32) -> String {
///     m.get(key)
/// }
/// ```
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Map<K, V> {
    pub(crate) _marker: PhantomData<(K, V)>,
}

impl<K, V> Map<K, V> {
    /// Creates an empty map.
    #[must_use]
    pub const fn empty() -> Self {
        Map {
            _marker: PhantomData,
        }
    }

    /// TrustWp compatibility alias for [`Map::empty`].
    ///
    /// The underlying TrustVc model remains a total map rather than TrustWp's
    /// partial-map API surface.
    #[must_use]
    pub const fn new() -> Self {
        Self::empty()
    }

    /// Returns the number of entries in the map.
    #[must_use]
    pub const fn len(&self) -> usize {
        0 // Ghost - verified via ay
    }

    /// Returns true if the map is empty.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        true // Ghost - verified via ay
    }

    /// Returns true if the map contains the key.
    #[must_use]
    pub fn contains_key(&self, _key: K) -> bool {
        false // Ghost - verified via ay
    }

    /// Returns true if any key in the map's domain maps to the given value.
    #[must_use]
    pub fn contains_value(&self, _value: V) -> bool {
        false // Ghost - verified via ay
    }

    /// TrustWp compatibility alias for [`Map::contains_key`].
    #[must_use]
    pub fn contains(&self, key: K) -> bool {
        self.contains_key(key)
    }

    /// Returns the value for the given key.
    ///
    /// # Panics
    /// Always panics at runtime (ghost method). Requires: `self.contains_key(key)`.
    #[must_use]
    pub fn get(&self, _key: K) -> V {
        // Formal contract: trust_vc verifies this precondition
        trust_vc::ghost_requires!(self.contains_key(_key));
        ghost_runtime_panic("Map", "get")
    }

    /// Verus compatibility alias for [`Map::get`].
    ///
    /// # Panics
    /// Always panics at runtime (ghost method). Requires: `self.contains_key(key)`.
    #[must_use]
    pub fn index(&self, key: K) -> V {
        self.get(key)
    }

    /// TrustWp compatibility alias for [`Map::get`].
    ///
    /// This still follows TrustVc total-map semantics and therefore returns `V`
    /// directly rather than `Option<V>`.
    #[must_use]
    pub fn lookup(&self, key: K) -> V {
        self.get(key)
    }

    /// Inserts a key-value pair into the map.
    #[must_use]
    pub fn insert(self, _key: K, _value: V) -> Self {
        Map {
            _marker: PhantomData,
        }
    }

    /// Removes a key from the map.
    #[must_use]
    pub fn remove(self, _key: K) -> Self {
        Map {
            _marker: PhantomData,
        }
    }

    /// Returns the domain (set of keys) of the map.
    ///
    /// This is useful for iterating over keys or checking membership.
    #[must_use]
    pub fn dom(&self) -> Set<K> {
        Set::empty() // Ghost - verified via ay
    }

    /// Maps each value through a spec-only closure, preserving keys.
    #[must_use]
    pub fn map_values<U>(self, _f: SpecFn<V, U>) -> Map<K, U> {
        Map {
            _marker: PhantomData,
        }
    }

    /// Maps each `(key, value)` pair through a spec-only closure, preserving keys.
    #[must_use]
    pub fn map_entries<U>(self, _f: SpecFn<(K, V), U>) -> Map<K, U> {
        Map {
            _marker: PhantomData,
        }
    }

    /// Filters the map by a predicate on keys.
    #[must_use]
    pub fn filter_keys(self, _pred: SpecFn<K, bool>) -> Self {
        Map {
            _marker: PhantomData,
        }
    }
}

impl<K, V> Index<K> for Map<K, V> {
    type Output = V;

    fn index(&self, _key: K) -> &Self::Output {
        trust_vc::ghost_requires!(self.contains_key(_key));
        ghost_runtime_panic("Map", "index")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_map_empty() {
        let _map = Map::<String, i32>::empty();
    }

    #[test]
    fn test_map_insert() {
        let map1 = Map::<i32, String>::empty();
        let _map2 = map1.insert(42, "value".to_string());
    }

    #[test]
    fn test_map_dom() {
        let map = Map::<i32, String>::empty().insert(1, "a".to_string());
        let _domain = map.dom();
    }
}
