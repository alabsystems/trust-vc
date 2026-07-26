// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::runtime_boundary::variant_accessor_panic;

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

    /// Returns the head element. Panics on `Nil`.
    #[must_use]
    pub fn head(&self) -> &T {
        match self {
            List::Cons(h, _) => h,
            List::Nil => variant_accessor_panic("List", "head", "Nil"),
        }
    }

    /// Returns the tail list. Panics on `Nil`.
    #[must_use]
    pub fn tail(&self) -> &List<T> {
        match self {
            List::Cons(_, t) => t,
            List::Nil => variant_accessor_panic("List", "tail", "Nil"),
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
        assert_eq!(*list.head(), 1);
        assert_eq!(list.tail().len(), 1);
    }

    #[test]
    fn test_list_default_is_nil() {
        let list: List<String> = List::default();
        assert!(list.is_nil());
    }

    #[test]
    #[should_panic(expected = "List::head called on Nil")]
    fn test_list_head_panics_on_nil() {
        let list: List<i32> = List::Nil;
        let _ = list.head();
    }

    #[test]
    #[should_panic(expected = "List::tail called on Nil")]
    fn test_list_tail_panics_on_nil() {
        let list: List<i32> = List::Nil;
        let _ = list.tail();
    }
}
