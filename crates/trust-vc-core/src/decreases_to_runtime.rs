// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Runtime evaluation for `decreases_to!` macro.
//!
//! Provides the lexicographic comparison function used in test mode
//! to verify that decrease relations actually hold (#1548).

/// Evaluates whether `lhs` lexicographically decreases to `rhs`.
///
/// The relation holds when there exists an index `k` such that:
/// - `lhs[k] > rhs[k]` (element at position k strictly decreases)
/// - For all `i < k`: `lhs[i] == rhs[i]` (all earlier elements are equal)
///
/// Returns `false` if all elements are equal (no decrease) or if any
/// earlier element increases.
///
/// # Panics
/// Panics if `lhs` and `rhs` have different lengths.
pub fn lexicographic_decreases(lhs: &[i128], rhs: &[i128]) -> bool {
    assert_eq!(
        lhs.len(),
        rhs.len(),
        "decreases_to! LHS and RHS must have equal length"
    );

    for (l, r) in lhs.iter().zip(rhs.iter()) {
        if *l > *r {
            return true; // Found a decrease at this position
        }
        if *l < *r {
            return false; // Found an increase — not decreasing
        }
        // l == r, continue to next position
    }
    false // All equal — no decrease
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_decrease() {
        assert!(lexicographic_decreases(&[10], &[5]));
    }

    #[test]
    fn test_simple_increase() {
        assert!(!lexicographic_decreases(&[1], &[100]));
    }

    #[test]
    fn test_equal() {
        assert!(!lexicographic_decreases(&[5], &[5]));
    }

    #[test]
    fn test_lex_second_decreases() {
        assert!(lexicographic_decreases(&[5, 10], &[5, 3]));
    }

    #[test]
    fn test_lex_first_decreases() {
        assert!(lexicographic_decreases(&[10, 1], &[5, 100]));
    }

    #[test]
    fn test_lex_first_increases() {
        assert!(!lexicographic_decreases(&[3, 10], &[5, 3]));
    }

    #[test]
    fn test_three_element() {
        assert!(lexicographic_decreases(&[5, 5, 10], &[5, 5, 3]));
    }

    #[test]
    fn test_ackermann_case1() {
        // (3, 0) => (2, 1): first decreases
        assert!(lexicographic_decreases(&[3, 0], &[2, 1]));
    }

    #[test]
    fn test_ackermann_case2() {
        // (2, 5) => (2, 4): first equal, second decreases
        assert!(lexicographic_decreases(&[2, 5], &[2, 4]));
    }
}
