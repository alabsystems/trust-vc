// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::marker::PhantomData;

use crate::runtime_boundary::ghost_runtime_panic;
use crate::SpecFn;

/// A mathematical sequence for specifications.
///
/// `Seq<T>` represents an immutable, indexed sequence of elements.
/// It maps to ay's array theory for verification.
///
/// # Example
/// ```text
/// #[trust_vc::spec]
/// fn first_element(s: Seq<i32>) -> i32 {
///     s.index(0)
/// }
/// ```
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Seq<T> {
    _marker: PhantomData<T>,
}

impl<T> Seq<T> {
    /// Creates an empty sequence.
    #[must_use]
    pub const fn empty() -> Self {
        Seq {
            _marker: PhantomData,
        }
    }

    /// TrustWp compatibility alias for [`Seq::empty`].
    ///
    /// This retains TrustVc semantics: `Seq` stays `usize`-indexed and
    /// zero-sized at runtime.
    #[must_use]
    pub const fn new() -> Self {
        Self::empty()
    }

    /// Returns the length of the sequence.
    #[must_use]
    pub const fn len(&self) -> usize {
        0 // Ghost - verified via ay
    }

    /// Returns true if the sequence is empty.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        true // Ghost - verified via ay
    }

    /// Creates a sequence of length `len` whose element at index `i` is `f(i)`.
    #[must_use]
    pub fn from_fn(_len: usize, _f: SpecFn<usize, T>) -> Self {
        Seq {
            _marker: PhantomData,
        }
    }

    /// Returns the element at the given index.
    ///
    /// # Panics
    /// Always panics at runtime (ghost method). Requires: `i < self.len()`.
    #[must_use]
    pub fn index(&self, _i: usize) -> T {
        // Formal contract: trust_vc verifies this precondition
        trust_vc::ghost_requires!(_i < self.len());
        ghost_runtime_panic("Seq", "index")
    }

    /// Verus-compatible alias for [`Seq::index`].
    ///
    /// # Panics
    /// Always panics at runtime (ghost method). Requires: `i < self.len()`.
    #[must_use]
    pub fn get(&self, i: usize) -> T {
        trust_vc::ghost_requires!(i < self.len());
        self.index(i)
    }

    /// Appends an element to the sequence.
    #[must_use]
    pub fn push(self, _value: T) -> Self {
        // Return a new instance to represent the modified sequence
        // The runtime representation is still PhantomData, but ay tracks the logical change
        Seq {
            _marker: PhantomData,
        }
    }

    /// TrustWp compatibility alias for [`Seq::push`].
    #[must_use]
    pub fn push_back(self, value: T) -> Self {
        self.push(value)
    }

    /// Updates the element at the given index.
    ///
    /// # Runtime behavior
    /// Returns a new ghost sequence placeholder at runtime. Verification
    /// requires: `i < self.len()`, but `ghost_requires!` adds no runtime check.
    #[must_use]
    pub fn update(self, _i: usize, _value: T) -> Self {
        // Formal contract: trust_vc verifies this precondition
        trust_vc::ghost_requires!(_i < self.len());
        // Return a new instance to represent the modified sequence
        Seq {
            _marker: PhantomData,
        }
    }

    /// TrustWp compatibility alias for [`Seq::update`].
    #[must_use]
    pub fn set(self, index: usize, value: T) -> Self {
        trust_vc::ghost_requires!(index < self.len());
        self.update(index, value)
    }

    /// Returns the last element of the sequence.
    ///
    /// # Panics
    /// Always panics at runtime (ghost method). Requires: `!self.is_empty()`.
    #[must_use]
    pub fn last(&self) -> T {
        // Formal contract: trust_vc verifies this precondition
        trust_vc::ghost_requires!(!self.is_empty());
        ghost_runtime_panic("Seq", "last")
    }

    /// Returns the sequence without its last element.
    ///
    /// # Runtime behavior
    /// Returns a new ghost sequence placeholder at runtime. Verification
    /// requires: `!self.is_empty()`, but `ghost_requires!` adds no runtime
    /// check.
    #[must_use]
    pub fn drop_last(self) -> Self {
        // Formal contract: trust_vc verifies this precondition
        trust_vc::ghost_requires!(!self.is_empty());
        // Return a new instance to represent the modified state
        Seq {
            _marker: PhantomData,
        }
    }

    /// TrustWp compatibility alias for [`Seq::drop_last`].
    #[must_use]
    pub fn pop_back(self) -> Self {
        trust_vc::ghost_requires!(!self.is_empty());
        self.drop_last()
    }

    /// Returns a subsequence from `start` (inclusive) to `end` (exclusive).
    ///
    /// # Runtime behavior
    /// Returns a new ghost sequence placeholder at runtime. Verification
    /// requires: `start <= end && end <= self.len()`, but `ghost_requires!`
    /// adds no runtime check.
    #[must_use]
    pub fn subrange(self, _start: usize, _end: usize) -> Self {
        // Formal contract: trust_vc verifies these preconditions
        trust_vc::ghost_requires!(_start <= _end && _end <= self.len());
        // Return a new instance to represent the modified state
        Seq {
            _marker: PhantomData,
        }
    }

    /// TrustWp compatibility alias for [`Seq::subrange`].
    #[must_use]
    pub fn subsequence(self, start: usize, end: usize) -> Self {
        trust_vc::ghost_requires!(start <= end && end <= self.len());
        self.subrange(start, end)
    }

    /// Concatenates two sequences (canonical API).
    ///
    /// This is the standard Verus-compatible concatenation method.
    /// Also available via `+` operator (`std::ops::Add`).
    #[must_use]
    #[allow(clippy::should_implement_trait)]
    pub fn add(self, _other: Self) -> Self {
        Seq {
            _marker: PhantomData,
        }
    }

    /// Deprecated alias for [`Seq::add`]. Use `add` or `+` instead.
    #[must_use]
    #[deprecated(since = "0.1.0", note = "use `Seq::add` or `+` operator instead")]
    pub fn concat(self, _other: Self) -> Self {
        self.add(_other)
    }

    /// Returns the first element of the sequence.
    ///
    /// # Panics
    /// Always panics at runtime (ghost method). Requires: `!self.is_empty()`.
    #[must_use]
    pub fn first(&self) -> T {
        // Formal contract: trust_vc verifies this precondition
        trust_vc::ghost_requires!(!self.is_empty());
        ghost_runtime_panic("Seq", "first")
    }

    /// Returns the sequence without its first element.
    ///
    /// # Runtime behavior
    /// Returns a new ghost sequence placeholder at runtime. Verification
    /// requires: `!self.is_empty()`, but `ghost_requires!` adds no runtime
    /// check.
    #[must_use]
    pub fn drop_first(self) -> Self {
        // Formal contract: trust_vc verifies this precondition
        trust_vc::ghost_requires!(!self.is_empty());
        // Return a new instance to represent the modified state
        Seq {
            _marker: PhantomData,
        }
    }

    /// Returns the first `n` elements.
    ///
    /// # Runtime behavior
    /// Returns a new ghost sequence placeholder at runtime. Verification
    /// requires: `n <= self.len()`, but `ghost_requires!` adds no runtime
    /// check.
    #[must_use]
    pub fn take(self, _n: usize) -> Self {
        // Formal contract: trust_vc verifies this precondition
        trust_vc::ghost_requires!(_n <= self.len());
        // Return a new instance to represent the modified state
        Seq {
            _marker: PhantomData,
        }
    }

    /// Returns the sequence without the first `n` elements.
    ///
    /// # Runtime behavior
    /// Returns a new ghost sequence placeholder at runtime. Verification
    /// requires: `n <= self.len()`, but `ghost_requires!` adds no runtime
    /// check.
    #[must_use]
    pub fn skip(self, _n: usize) -> Self {
        // Formal contract: trust_vc verifies this precondition
        trust_vc::ghost_requires!(_n <= self.len());
        // Return a new instance to represent the modified state
        Seq {
            _marker: PhantomData,
        }
    }

    /// Returns true if the sequence contains the given element.
    #[must_use]
    pub fn contains(&self, _value: T) -> bool {
        false // Ghost - verified via ay
    }

    /// Maps each sequence element through a spec-only closure.
    #[must_use]
    pub fn map_values<U>(self, _f: SpecFn<T, U>) -> Seq<U> {
        Seq {
            _marker: PhantomData,
        }
    }

    /// Maps each sequence element with its index through a spec-only closure.
    #[must_use]
    pub fn map<U>(self, _f: SpecFn<(usize, T), U>) -> Seq<U> {
        Seq {
            _marker: PhantomData,
        }
    }

    /// Returns the subsequence of elements satisfying the predicate.
    ///
    /// All elements in the result satisfy `pred`, and every source element
    /// satisfying `pred` appears in the result. The result length is at most
    /// `self.len()`.
    #[must_use]
    pub fn filter(self, _pred: SpecFn<T, bool>) -> Self {
        Seq {
            _marker: PhantomData,
        }
    }

    /// Maps each element to a sequence and concatenates the results.
    #[must_use]
    pub fn flat_map<U>(self, _f: SpecFn<T, Seq<U>>) -> Seq<U> {
        Seq {
            _marker: PhantomData,
        }
    }

    /// Folds the sequence from left to right with a spec-only accumulator step.
    #[must_use]
    pub fn fold_left<U>(self, init: U, _f: SpecFn<(U, T), U>) -> U {
        init
    }

    /// Folds the sequence from right to left with a spec-only accumulator step.
    #[must_use]
    pub fn fold_right<U>(self, init: U, _f: SpecFn<(T, U), U>) -> U {
        init
    }

    /// Converts the sequence to a set of its elements.
    #[must_use]
    pub fn to_set(&self) -> crate::Set<T> {
        crate::Set::empty() // Ghost - verified via ay
    }

    /// Converts the sequence to a multiset of its elements.
    #[must_use]
    pub fn to_multiset(&self) -> crate::Multiset<T> {
        crate::Multiset::empty() // Ghost - verified via ay
    }

    /// Returns the sequence with elements in reverse order.
    #[must_use]
    pub fn reverse(self) -> Self {
        Seq {
            _marker: PhantomData,
        }
    }

    /// Returns true if all elements in the sequence are distinct.
    #[must_use]
    pub fn no_duplicates(&self) -> bool {
        false // Ghost - verified via ay
    }
}

impl<T> std::ops::Add for Seq<T> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Seq::add(self, rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_seq_empty() {
        let seq = Seq::<String>::empty();
        assert!(seq.is_empty());
    }

    #[test]
    fn test_seq_push() {
        let seq1 = Seq::<i32>::empty();
        let _seq2 = seq1.push(42);
    }

    #[test]
    fn test_seq_len() {
        let seq = Seq::<i32>::empty();
        assert_eq!(seq.len(), 0);
    }

    #[test]
    fn test_seq_from_fn_typechecks() {
        let _seq = Seq::from_fn(4, SpecFn::new(|i: usize| i + 1));
    }

    #[test]
    fn test_seq_index() {
        let _seq = Seq::<i32>::empty().push(42);
    }

    #[test]
    fn test_seq_subrange() {
        let seq = Seq::<i32>::empty().push(1).push(2).push(3);
        let _sub = seq.subrange(1, 2);
    }
}
