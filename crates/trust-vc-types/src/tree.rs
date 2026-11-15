// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

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

    /// Returns the leaf value, or `None` on `Branch`.
    ///
    /// Total: a selector that panicked on the wrong variant was a reachable
    /// panic the verifier refuted, and Trust's contract language cannot yet
    /// state a variant precondition on `&self`, so the wrong variant is `None`.
    #[must_use]
    pub fn value(&self) -> Option<&T> {
        match self {
            Tree::Leaf(v) => Some(v),
            Tree::Branch(_, _) => None,
        }
    }

    /// Returns the left child, or `None` on `Leaf`.
    ///
    /// Total: a selector that panicked on the wrong variant was a reachable
    /// panic the verifier refuted, and Trust's contract language cannot yet
    /// state a variant precondition on `&self`, so the wrong variant is `None`.
    #[must_use]
    pub fn left(&self) -> Option<&Tree<T>> {
        match self {
            Tree::Branch(l, _) => Some(l),
            Tree::Leaf(_) => None,
        }
    }

    /// Returns the right child, or `None` on `Leaf`.
    ///
    /// Total: a selector that panicked on the wrong variant was a reachable
    /// panic the verifier refuted, and Trust's contract language cannot yet
    /// state a variant precondition on `&self`, so the wrong variant is `None`.
    #[must_use]
    pub fn right(&self) -> Option<&Tree<T>> {
        match self {
            Tree::Branch(_, r) => Some(r),
            Tree::Leaf(_) => None,
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
        assert_eq!(tree.value(), Some(&42));
        assert_eq!(tree.depth(), 0);
    }

    #[test]
    fn test_tree_branch_construction() {
        let tree = Tree::Branch(Box::new(Tree::Leaf(1)), Box::new(Tree::Leaf(2)));
        assert!(tree.is_branch());
        assert!(!tree.is_leaf());
        assert_eq!(tree.depth(), 1);
        assert_eq!(tree.left().and_then(Tree::value), Some(&1));
        assert_eq!(tree.right().and_then(Tree::value), Some(&2));
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

    /// Regression: the selectors are total; the wrong variant gives `None`
    /// (they used to panic, a reachable panic the verifier refuted).
    #[test]
    fn test_tree_value_on_branch_is_none() {
        let tree = Tree::Branch(Box::new(Tree::Leaf(1)), Box::new(Tree::Leaf(2)));
        assert_eq!(tree.value(), None);
    }

    #[test]
    fn test_tree_children_on_leaf_are_none() {
        let tree = Tree::Leaf(42);
        assert!(tree.left().is_none());
        assert!(tree.right().is_none());
    }
}
