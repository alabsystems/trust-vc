// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::runtime_boundary::variant_accessor_panic;

/// Spec-only binary tree for structural induction.
///
/// `Tree<T>` is a recursive algebraic datatype for tree-structured
/// inductive proofs. Each leaf stores a value; branches have two children.
///
/// # ay Encoding
///
/// Encoded as a UF datatype with well-foundedness axioms. Both children
/// of `Branch` use `RecursiveRef` mapped to `Sort::Int`.
///
/// # Example
/// ```text
/// #[trust_vc::decreases(tree)]
/// #[trust_vc::spec]
/// fn depth(tree: Tree<i32>) -> nat {
///     match tree {
///         Tree::Leaf(_) => 0,
///         Tree::Branch(l, r) => 1 + max(depth(*l), depth(*r)),
///     }
/// }
/// ```
#[derive(Clone, Debug)]
pub enum Tree<T> {
    /// Leaf node containing a value (base case).
    Leaf(T),
    /// Branch node with two children.
    Branch(Box<Tree<T>>, Box<Tree<T>>),
}

impl<T> Tree<T> {
    /// Returns true if this is a leaf node.
    #[must_use]
    pub fn is_leaf(&self) -> bool {
        matches!(self, Tree::Leaf(_))
    }

    /// Returns true if this is a branch node.
    #[must_use]
    pub fn is_branch(&self) -> bool {
        matches!(self, Tree::Branch(_, _))
    }

    /// Returns the leaf value. Panics on `Branch`.
    #[must_use]
    pub fn value(&self) -> &T {
        match self {
            Tree::Leaf(v) => v,
            Tree::Branch(_, _) => variant_accessor_panic("Tree", "value", "Branch"),
        }
    }

    /// Returns the left child. Panics on `Leaf`.
    #[must_use]
    pub fn left(&self) -> &Tree<T> {
        match self {
            Tree::Branch(l, _) => l,
            Tree::Leaf(_) => variant_accessor_panic("Tree", "left", "Leaf"),
        }
    }

    /// Returns the right child. Panics on `Leaf`.
    #[must_use]
    pub fn right(&self) -> &Tree<T> {
        match self {
            Tree::Branch(_, r) => r,
            Tree::Leaf(_) => variant_accessor_panic("Tree", "right", "Leaf"),
        }
    }

    /// Returns the depth of the tree.
    #[must_use]
    pub fn depth(&self) -> usize {
        match self {
            Tree::Leaf(_) => 0,
            Tree::Branch(l, r) => 1 + l.depth().max(r.depth()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tree_leaf() {
        let tree = Tree::Leaf(42);
        assert!(tree.is_leaf());
        assert!(!tree.is_branch());
        assert_eq!(*tree.value(), 42);
        assert_eq!(tree.depth(), 0);
    }

    #[test]
    fn test_tree_branch_construction() {
        let tree = Tree::Branch(Box::new(Tree::Leaf(1)), Box::new(Tree::Leaf(2)));
        assert!(tree.is_branch());
        assert!(!tree.is_leaf());
        assert_eq!(tree.depth(), 1);
        assert!(tree.left().is_leaf());
        assert!(tree.right().is_leaf());
    }

    #[test]
    fn test_tree_nested_depth() {
        let tree = Tree::Branch(
            Box::new(Tree::Branch(
                Box::new(Tree::Leaf(1)),
                Box::new(Tree::Leaf(2)),
            )),
            Box::new(Tree::Leaf(3)),
        );
        assert_eq!(tree.depth(), 2);
    }

    #[test]
    #[should_panic(expected = "Tree::value called on Branch")]
    fn test_tree_value_panics_on_branch() {
        let tree = Tree::Branch(Box::new(Tree::Leaf(1)), Box::new(Tree::Leaf(2)));
        let _ = tree.value();
    }

    #[test]
    #[should_panic(expected = "Tree::left called on Leaf")]
    fn test_tree_left_panics_on_leaf() {
        let tree = Tree::Leaf(42);
        let _ = tree.left();
    }
}
