// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::marker::PhantomData;

use crate::runtime_boundary::ghost_runtime_panic;

/// A mathematical multiset (bag) for specifications.
///
/// `Multiset<T>` represents an immutable bag of elements with multiplicity
/// counts. It maps to ay array theory from elements to mathematical integers.
///
/// # Example
/// ```text
/// #[trust_vc::spec]
/// fn has_duplicate_42(ms: Multiset<i32>) -> bool {
///     ms.count(42) >= 2
/// }
/// ```
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Multiset<T> {
    _marker: PhantomData<T>,
}

impl<T> Multiset<T> {
    /// Creates an empty multiset.
    #[must_use]
    pub const fn empty() -> Self {
        Multiset {
            _marker: PhantomData,
        }
    }

    /// Creates a singleton multiset.
    #[must_use]
    pub fn singleton(_value: T) -> Self {
        Self::empty()
    }

    /// Returns the total element count.
    #[must_use]
    pub const fn len(&self) -> usize {
        0 // Ghost - verified via ay
    }

    /// Returns true if the multiset is empty.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        true // Ghost - verified via ay
    }

    /// Returns the multiplicity of the element.
    #[must_use]
    pub fn count(&self, _value: T) -> usize {
        0 // Ghost - verified via ay
    }

    /// Returns true if the multiset contains at least one copy of the element.
    #[must_use]
    pub fn contains(&self, _value: T) -> bool {
        false // Ghost - verified via ay
    }

    /// Returns an arbitrary element from the multiset.
    ///
    /// Verification may use the result as a member only when `self.len() != 0`.
    ///
    /// # Panics
    /// Always panics at runtime (ghost method).
    #[must_use]
    pub fn choose(&self) -> T {
        ghost_runtime_panic("Multiset", "choose")
    }

    /// Inserts one copy of the element.
    #[must_use]
    pub fn insert(self, _value: T) -> Self {
        Multiset {
            _marker: PhantomData,
        }
    }

    /// Removes one copy of the element, saturating at zero multiplicity.
    #[must_use]
    pub fn remove(self, _value: T) -> Self {
        self.sub(Self::singleton(_value))
    }

    /// Returns the difference of two multisets (pointwise saturating subtraction).
    #[must_use]
    #[allow(clippy::should_implement_trait)]
    pub fn sub(self, _other: Self) -> Self {
        Multiset {
            _marker: PhantomData,
        }
    }

    /// Readable alias for [`Multiset::sub`].
    #[must_use]
    pub fn difference(self, other: Self) -> Self {
        self.sub(other)
    }

    /// Returns the pointwise sum of two multisets.
    ///
    /// Verus spells multiset union as `add`; keep `union` as the readable
    /// TrustVc alias while accepting the upstream surface directly.
    #[must_use]
    #[allow(clippy::should_implement_trait)]
    pub fn add(self, other: Self) -> Self {
        self.union(other)
    }

    /// Returns the union (pointwise sum) of two multisets.
    #[must_use]
    pub fn union(self, _other: Self) -> Self {
        Multiset {
            _marker: PhantomData,
        }
    }

    /// Returns the intersection (pointwise minimum) of two multisets.
    #[must_use]
    pub fn intersect(self, _other: Self) -> Self {
        Multiset {
            _marker: PhantomData,
        }
    }

    /// Returns true iff every element count in `self` is less than or equal to
    /// the corresponding count in `other`.
    #[must_use]
    pub fn subset_of(self, _other: Self) -> bool {
        true // Ghost - verified via ay
    }

    /// Alias for [`Multiset::subset_of`].
    #[must_use]
    pub fn subset(self, other: Self) -> bool {
        self.subset_of(other)
    }

    /// Alias for [`Multiset::subset_of`].
    #[must_use]
    pub fn is_subset(self, other: Self) -> bool {
        self.subset_of(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_multiset_empty() {
        let multiset = Multiset::<i32>::empty();
        assert!(multiset.is_empty());
    }

    #[test]
    fn test_multiset_insert_and_union() {
        let multiset1 = Multiset::<i32>::empty().insert(1);
        let multiset2 = Multiset::<i32>::singleton(2);
        let _multiset3 = multiset1.union(multiset2);
        let _multiset4 = multiset1.add(multiset2);
    }

    #[test]
    fn test_multiset_count_and_contains() {
        let multiset = Multiset::<i32>::empty().insert(42);
        assert_eq!(multiset.count(42), 0);
        assert!(!multiset.contains(42));
    }

    #[test]
    #[should_panic(expected = "Multiset::choose")]
    fn test_multiset_choose_runtime_boundary() {
        let _ = Multiset::<i32>::empty().choose();
    }

    #[test]
    fn test_multiset_subtraction_surface() {
        let multiset1 = Multiset::<i32>::empty().insert(1).insert(2);
        let multiset2 = Multiset::<i32>::singleton(2);
        let _subtracted = multiset1.sub(multiset2);
        let _difference = multiset1.difference(multiset2);
        let _removed = multiset1.remove(1);
    }

    #[test]
    fn test_multiset_subset_surface() {
        let multiset1 = Multiset::<i32>::empty().insert(1);
        let multiset2 = multiset1.insert(2);
        assert!(multiset1.subset_of(multiset2));
        assert!(multiset1.subset(multiset2));
        assert!(multiset1.is_subset(multiset2));
    }
}
