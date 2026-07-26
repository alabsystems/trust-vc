// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::marker::PhantomData;

use crate::runtime_boundary::ghost_runtime_panic;
use crate::{Map, SpecFn};

/// A mathematical set for specifications.
///
/// `Set<T>` represents an immutable set of elements.
/// It maps to ay's set theory for verification.
///
/// # Example
/// ```text
/// #[trust_vc::spec]
/// fn contains_zero(s: Set<i32>) -> bool {
///     s.contains(0)
/// }
/// ```
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Set<T> {
    _marker: PhantomData<T>,
}

impl<T> Set<T> {
    /// Creates an empty set.
    #[must_use]
    pub const fn empty() -> Self {
        Set {
            _marker: PhantomData,
        }
    }

    /// TrustWp compatibility alias for [`Set::empty`].
    ///
    /// TrustVc keeps its zero-sized runtime representation and existing set
    /// theory encoding behind this shim.
    #[must_use]
    pub const fn new() -> Self {
        Self::empty()
    }

    /// Returns the cardinality of the set.
    #[must_use]
    pub const fn len(&self) -> usize {
        0 // Ghost - verified via ay
    }

    /// Returns true if the set is empty.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        true // Ghost - verified via ay
    }

    /// Returns true when the set has finite cardinality.
    ///
    /// TrustVc tracks set cardinality for ghost reasoning through `len`.
    #[must_use]
    pub const fn finite(&self) -> bool {
        true // Ghost - verified via ay
    }

    /// Returns true if the set contains the element.
    #[must_use]
    pub fn contains(&self, _value: T) -> bool {
        false // Ghost - verified via ay
    }

    /// Returns an arbitrary element from the set.
    ///
    /// Verification may use the result as a member only when `self.len() != 0`.
    ///
    /// # Panics
    /// Always panics at runtime (ghost method).
    #[must_use]
    pub fn choose(&self) -> T {
        ghost_runtime_panic("Set", "choose")
    }

    /// Inserts an element into the set.
    #[must_use]
    pub fn insert(self, _value: T) -> Self {
        // Return a new instance to represent the modified state
        Set {
            _marker: PhantomData,
        }
    }

    /// Removes an element from the set.
    #[must_use]
    pub fn remove(self, _value: T) -> Self {
        Set {
            _marker: PhantomData,
        }
    }

    /// Returns the union of two sets.
    #[must_use]
    pub fn union(self, _other: Self) -> Self {
        Set {
            _marker: PhantomData,
        }
    }

    /// Returns the intersection of two sets.
    #[must_use]
    pub fn intersect(self, _other: Self) -> Self {
        Set {
            _marker: PhantomData,
        }
    }

    /// TrustWp compatibility alias for [`Set::intersect`].
    #[must_use]
    pub fn intersection(self, other: Self) -> Self {
        self.intersect(other)
    }

    /// Returns the difference of two sets (elements in self but not in other).
    #[must_use]
    pub fn difference(self, _other: Self) -> Self {
        Set {
            _marker: PhantomData,
        }
    }

    /// Returns true if self is a subset of other.
    #[must_use]
    pub fn subset(&self, _other: &Self) -> bool {
        true // Ghost - verified via ay
    }

    /// TrustWp compatibility alias for [`Set::subset`].
    #[must_use]
    pub fn is_subset(self, other: Self) -> bool {
        self.subset(&other)
    }

    /// Returns true if self is a superset of other.
    #[must_use]
    pub fn superset(&self, _other: &Self) -> bool {
        true // Ghost - verified via ay
    }

    /// TrustWp compatibility alias for [`Set::superset`].
    #[must_use]
    pub fn is_superset(self, other: Self) -> bool {
        self.superset(&other)
    }

    /// Filters elements by a spec-only predicate.
    #[must_use]
    pub fn filter(self, _pred: SpecFn<T, bool>) -> Self {
        Set {
            _marker: PhantomData,
        }
    }

    /// Maps each element through a spec-only closure.
    #[must_use]
    pub fn map<U>(self, _f: SpecFn<T, U>) -> Set<U> {
        Set {
            _marker: PhantomData,
        }
    }

    /// Builds a map whose domain is exactly this set.
    #[must_use]
    pub fn mk_map<V>(self, _f: SpecFn<T, V>) -> Map<T, V> {
        Map {
            _marker: PhantomData,
        }
    }

    /// Folds over the set elements with a spec-only accumulator step.
    ///
    /// The step function must be order-insensitive: the result must be the
    /// same regardless of the order in which elements are visited.
    #[must_use]
    pub fn fold<U>(self, init: U, _f: SpecFn<(U, T), U>) -> U {
        init
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_set_empty() {
        let set = Set::<i32>::empty();
        assert!(set.is_empty());
    }

    #[test]
    fn test_set_insert() {
        let set1 = Set::<i32>::empty();
        let _set2 = set1.insert(42);
    }

    #[test]
    fn test_set_union() {
        let set1 = Set::<i32>::empty().insert(1);
        let set2 = Set::<i32>::empty().insert(2);
        let _set3 = set1.union(set2);
    }

    #[test]
    fn test_set_contains() {
        let set = Set::<i32>::empty().insert(42);
        assert!(!set.contains(42));
    }

    #[test]
    fn test_set_difference() {
        let set1 = Set::<i32>::empty().insert(1).insert(2).insert(3);
        let set2 = Set::<i32>::empty().insert(2);
        let _diff = set1.difference(set2);
    }

    #[test]
    #[should_panic(expected = "Set::choose called at runtime")]
    fn test_set_choose_runtime_boundary() {
        let _ = Set::<i32>::empty().choose();
    }
}
