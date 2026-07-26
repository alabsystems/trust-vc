// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use core::fmt;
use std::marker::PhantomData;

use crate::runtime_boundary::ghost_runtime_panic;

/// Prophecy variable — represents a value determined in the future.
///
/// A prophecy variable is ghost state that "predicts" a future execution
/// choice. The value is unconstrained at creation and becomes fixed when
/// `resolve()` is called.
///
/// # ay Encoding
///
/// - `Proph::new()` creates a fresh unconstrained ay constant of sort T.
/// - `view()` returns the prophecy term directly.
/// - `resolve(value)` emits `(assert (= prophecy_term (encode value)))`.
///
/// Part of #2519.
#[repr(transparent)]
pub struct Proph<T>(PhantomData<T>);

impl<T: Copy> Copy for Proph<T> {}

impl<T: Copy> Clone for Proph<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Proph<T> {
    /// Create a fresh prophecy variable.
    ///
    /// The prophecy value is unconstrained until `resolve()` is called.
    /// Only valid in verification context (ghost code).
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Proph(PhantomData)
    }

    /// View the prophecy's value (ghost/spec reasoning only).
    ///
    /// Returns the future value that the prophecy will be resolved to.
    /// Before resolution, this is an unconstrained symbolic value.
    ///
    /// # Panics
    ///
    /// Always panics at runtime. Only valid in verification context.
    pub fn view(&self) -> T {
        ghost_runtime_panic("Proph", "view")
    }

    /// Resolve the prophecy to a concrete value.
    ///
    /// Constrains the prophecy to equal `value`, retroactively making all
    /// prior reasoning about `view()` consistent with the resolved value.
    ///
    /// # Panics
    ///
    /// Always panics at runtime. Only valid in verification context.
    #[allow(clippy::needless_pass_by_value)]
    pub fn resolve(self, value: T) {
        let _ = value;
        ghost_runtime_panic("Proph", "resolve")
    }
}

impl<T> Default for Proph<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> fmt::Debug for Proph<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Proph").finish_non_exhaustive()
    }
}

// SAFETY: Proph<T> contains no actual data (PhantomData only), so it is
// trivially Send regardless of T.
unsafe impl<T> Send for Proph<T> {}
// SAFETY: Proph<T> contains no actual data (PhantomData only), so it is
// trivially Sync regardless of T.
unsafe impl<T> Sync for Proph<T> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proph_new() {
        let _p: Proph<i32> = Proph::new();
    }

    #[test]
    fn test_proph_is_zero_sized() {
        assert_eq!(
            std::mem::size_of::<Proph<i32>>(),
            0,
            "Proph<T> should be zero-sized"
        );
        assert_eq!(
            std::mem::size_of::<Proph<String>>(),
            0,
            "Proph<T> should be zero-sized regardless of T"
        );
    }

    #[test]
    fn test_proph_copy_when_t_is_copy() {
        let p1: Proph<i32> = Proph::new();
        let p2 = p1;
        let p3 = p1; // still valid because i32: Copy => Proph<i32>: Copy
        let _ = (p2, p3);
    }

    #[test]
    #[should_panic(expected = "Proph::view called at runtime")]
    fn test_proph_view_panics_at_runtime() {
        let p: Proph<i32> = Proph::new();
        let _ = p.view();
    }

    #[test]
    #[should_panic(expected = "Proph::resolve called at runtime")]
    fn test_proph_resolve_panics_at_runtime() {
        let p: Proph<i32> = Proph::new();
        p.resolve(42);
    }

    #[test]
    fn test_proph_debug() {
        let p: Proph<i32> = Proph::new();
        let debug = format!("{:?}", p);
        assert!(debug.contains("Proph"), "Debug output should mention Proph");
    }

    #[test]
    fn test_proph_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Proph<i32>>();
        assert_send_sync::<Proph<String>>();
    }
}
