// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

/// Spec-only linked list for inductive proofs.
///
/// `List<T>` is a recursive algebraic datatype for structural induction.
/// Unlike `Seq<T>` (array-backed), `List<T>` has constructors (`Nil`, `Cons`)
/// that the solver can pattern-match on, enabling inductive proof strategies.
///
/// # ay Encoding
///
/// Encoded as a UF datatype with constructors, selectors, testers, and
/// well-foundedness axioms (`dt_size`). `RecursiveRef` in the `Cons` tail
/// field maps to the `Sort::Int` carrier sort.
///
/// # Example
/// ```text
/// #[trust_vc::decreases(list)]
/// #[trust_vc::spec]
/// fn sum(list: List<i32>) -> i32 {
///     match list {
///         List::Nil => 0,
///         List::Cons(h, t) => h + sum(*t),
///     }
/// }
/// ```
#[derive(Clone, Debug, Default)]
pub enum List<T> {
    /// Empty list (base case).
    #[default]
    Nil,
    /// Cons cell: head element and tail list.
    Cons(T, Box<List<T>>),
}

impl<T> List<T> {
    /// Returns true if the list is empty.
    #[must_use]
    pub fn is_nil(&self) -> bool {
        matches!(self, List::Nil)
    }

    /// Returns true if the list is non-empty.
    #[must_use]
    pub fn is_cons(&self) -> bool {
        matches!(self, List::Cons(_, _))
    }

    /// Returns the head element, or `None` on `Nil`.
    ///
    /// Total: a selector that panicked on the wrong variant was a reachable
    /// panic the verifier refuted, and Trust's contract language cannot yet
    /// state a variant precondition on `&self`, so the wrong variant is `None`.
    #[must_use]
    pub fn head(&self) -> Option<&T> {
        match self {
            List::Cons(h, _) => Some(h),
            List::Nil => None,
        }
    }

    /// Returns the tail list, or `None` on `Nil`.
    ///
    /// Total: a selector that panicked on the wrong variant was a reachable
    /// panic the verifier refuted, and Trust's contract language cannot yet
    /// state a variant precondition on `&self`, so the wrong variant is `None`.
    #[must_use]
    pub fn tail(&self) -> Option<&List<T>> {
        match self {
            List::Cons(_, t) => Some(t),
            List::Nil => None,
        }
    }

    /// Returns the length of the list.
    #[must_use]
    pub fn len(&self) -> usize {
        match self {
            List::Nil => 0,
            List::Cons(_, t) => 1 + t.len(),
        }
    }

    /// Returns true if the list is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.is_nil()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_list_nil_is_empty() {
        let list: List<i32> = List::Nil;
        assert!(list.is_nil());
        assert!(!list.is_cons());
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn test_list_cons_construction() {
        let list = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
        assert!(list.is_cons());
        assert!(!list.is_nil());
        assert_eq!(list.len(), 2);
        assert_eq!(list.head(), Some(&1));
        assert_eq!(list.tail().map(List::len), Some(1));
        assert_eq!(list.tail().and_then(List::head), Some(&2));
        assert!(list.tail().and_then(List::tail).is_some_and(List::is_nil));
    }

    #[test]
    fn test_list_default_is_nil() {
        let list: List<String> = List::default();
        assert!(list.is_nil());
    }

    /// Regression: the selectors are total; `Nil` has no head or tail
    /// (they used to panic, a reachable panic the verifier refuted).
    #[test]
    fn test_list_selectors_on_nil_are_none() {
        let list: List<i32> = List::Nil;
        assert_eq!(list.head(), None);
        assert!(list.tail().is_none());
    }
}
