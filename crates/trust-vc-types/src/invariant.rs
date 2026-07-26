// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use core::fmt;
use core::ops::{Deref, DerefMut};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

use crate::runtime_boundary::ghost_runtime_panic;

/// Predicate trait for local invariants.
///
/// Implement this trait to specify the invariant predicate that must hold
/// whenever a `LocalInvariant` is opened and closed.
///
/// # Example
///
/// ```text
/// struct CounterPred;
///
/// impl InvariantPredicate<(), u32> for CounterPred {
///     fn inv(_k: (), v: u32) -> bool {
///         v < 100
///     }
/// }
/// ```
///
/// # ay Encoding
///
/// The `inv` function is encoded as a boolean SMT expression. When an
/// invariant is opened, `inv(k, inner)` is assumed; when closed, it
/// is asserted.
pub trait InvariantPredicate<K, V> {
    /// The invariant predicate. Must hold whenever the invariant is
    /// in a closed state.
    fn inv(k: K, v: V) -> bool;
}

/// Placeholder mutable binding returned by `open_local_invariant!`.
///
/// The proc macro symbolically rewrites supported `*inner` uses before the body
/// executes in test mode, so the `Deref`/`DerefMut` impls are a fail-closed
/// fallback for unsupported runtime evaluation paths.
#[doc(hidden)]
pub struct InvariantBinding<T>(PhantomData<T>);

impl<T> InvariantBinding<T> {
    #[must_use]
    pub const fn new() -> Self {
        Self(PhantomData)
    }
}

impl<T> Default for InvariantBinding<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Deref for InvariantBinding<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        ghost_runtime_panic("InvariantBinding", "deref")
    }
}

impl<T> DerefMut for InvariantBinding<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        ghost_runtime_panic("InvariantBinding", "deref_mut")
    }
}

/// A local (single-threaded) invariant over tracked ghost state.
///
/// `LocalInvariant<K, V, Pred>` stores a tracked `V` value that satisfies
/// `Pred::inv(k, v)`. Opening the invariant gives mutable access to the
/// inner value; closing it re-asserts the predicate.
///
/// # Type Parameters
///
/// - `K` — constant data associated with the invariant (namespace key)
/// - `V` — the tracked inner value type
/// - `Pred` — the predicate type, must implement `InvariantPredicate<K, V>`
///
/// # Example
///
/// ```text
/// use trust_vc_types::{LocalInvariant, InvariantPredicate};
///
/// struct BoundedPred;
/// impl InvariantPredicate<(), i32> for BoundedPred {
///     fn inv(_k: (), v: i32) -> bool { v >= 0 && v < 100 }
/// }
///
/// // inv: LocalInvariant<(), i32, BoundedPred>
/// // open_local_invariant!(&inv => inner => {
/// //     *inner += 1;
/// //     // Pred::inv((), *inner) is asserted on close
/// // });
/// ```
///
/// # ay Encoding
///
/// The invariant block generates:
/// 1. Havoc the inner variable (fresh symbolic value)
/// 2. `assume(pred(k, inner))` — invariant holds at entry
/// 3. Encode body (may modify `inner`)
/// 4. `assert(pred(k, inner))` — invariant must hold at exit
pub struct LocalInvariant<K, V, Pred: InvariantPredicate<K, V>> {
    _phantom: PhantomData<(K, V, Pred)>,
}

impl<K, V, Pred: InvariantPredicate<K, V>> LocalInvariant<K, V, Pred> {
    /// Create a new local invariant with the given constant and initial value.
    ///
    /// The initial value must satisfy `Pred::inv(k, v)`.
    ///
    /// # Panics
    /// Always panics at runtime — invariants exist only in verification context.
    #[must_use]
    pub fn new(_k: K, _v: V) -> Self {
        ghost_runtime_panic("LocalInvariant", "new")
    }

    /// Returns the constant data associated with this invariant.
    ///
    /// # Panics
    /// Always panics at runtime.
    #[must_use]
    pub fn constant(&self) -> K {
        ghost_runtime_panic("LocalInvariant", "constant")
    }

    /// Returns the namespace identifier for mask-based access control.
    ///
    /// MVP namespace identity is type-scoped: the namespace is a stable hash of
    /// `(K, V, Pred)`. This makes `namespace()` runtime-safe so proc-macro
    /// expansion can enforce `#[opens_invariants(...)]` without panicking.
    #[must_use]
    pub fn namespace(&self) -> i64 {
        let mut hasher = DefaultHasher::new();
        std::any::type_name::<(K, V, Pred)>().hash(&mut hasher);
        hasher.finish() as i64
    }

    /// Returns the inner value type name for symbolic invariant-body lowering.
    #[doc(hidden)]
    #[must_use]
    pub fn binding_type_name(&self) -> &'static str {
        std::any::type_name::<V>()
    }

    /// Creates a placeholder mutable binding for `open_local_invariant!`.
    ///
    /// The binding never carries a runtime value; supported body expressions are
    /// rewritten symbolically by the proc macro before execution.
    #[doc(hidden)]
    #[must_use]
    pub fn open_binding(&self) -> InvariantBinding<V> {
        InvariantBinding::new()
    }
}

impl<K, V, Pred: InvariantPredicate<K, V>> fmt::Debug for LocalInvariant<K, V, Pred> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LocalInvariant").finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestPred;
    impl InvariantPredicate<(), i32> for TestPred {
        fn inv(_k: (), v: i32) -> bool {
            (0..100).contains(&v)
        }
    }

    #[test]
    fn test_invariant_predicate_trait() {
        assert!(TestPred::inv((), 0));
        assert!(TestPred::inv((), 99));
        assert!(!TestPred::inv((), -1));
        assert!(!TestPred::inv((), 100));
    }

    #[test]
    fn test_local_invariant_is_zero_sized() {
        assert_eq!(
            std::mem::size_of::<LocalInvariant<(), i32, TestPred>>(),
            0,
            "LocalInvariant should be zero-sized"
        );
    }

    #[test]
    #[should_panic(expected = "LocalInvariant::new called at runtime")]
    fn test_local_invariant_new_panics_at_runtime() {
        let _ = LocalInvariant::<(), i32, TestPred>::new((), 42);
    }

    #[test]
    fn test_local_invariant_debug() {
        fn assert_debug<T: std::fmt::Debug>() {}
        assert_debug::<LocalInvariant<(), i32, TestPred>>();
    }

    struct KeyedPred;
    impl InvariantPredicate<u64, String> for KeyedPred {
        fn inv(k: u64, v: String) -> bool {
            v.len() < k as usize
        }
    }

    #[test]
    fn test_keyed_invariant_predicate() {
        assert!(KeyedPred::inv(10, "short".to_string()));
        assert!(!KeyedPred::inv(3, "toolong".to_string()));
    }

    #[test]
    fn test_local_invariant_namespace_is_runtime_safe_and_stable() {
        let inv_a = LocalInvariant::<(), i32, TestPred> {
            _phantom: PhantomData,
        };
        let inv_b = LocalInvariant::<(), i32, TestPred> {
            _phantom: PhantomData,
        };

        assert_eq!(inv_a.namespace(), inv_b.namespace());
    }

    #[test]
    fn test_local_invariant_namespace_distinguishes_predicates() {
        let test_inv = LocalInvariant::<(), i32, TestPred> {
            _phantom: PhantomData,
        };
        let keyed_inv = LocalInvariant::<u64, String, KeyedPred> {
            _phantom: PhantomData,
        };

        assert_ne!(test_inv.namespace(), keyed_inv.namespace());
    }

    #[test]
    fn test_local_invariant_binding_helpers_expose_value_metadata() {
        let inv = LocalInvariant::<(), i32, TestPred> {
            _phantom: PhantomData,
        };

        assert_eq!(inv.binding_type_name(), std::any::type_name::<i32>());
        assert_eq!(
            std::mem::size_of_val(&inv.open_binding()),
            0,
            "InvariantBinding should stay zero-sized"
        );
    }
}
