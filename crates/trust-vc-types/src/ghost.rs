// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use core::fmt;
use std::marker::PhantomData;

use crate::runtime_boundary::ghost_runtime_panic;

/// A ghost value that exists only for verification.
///
/// At runtime, `Ghost<T>` is zero-sized (`PhantomData`).
/// The verifier treats it as containing a T value.
///
/// # Properties
///
/// - Zero-sized at runtime (no memory overhead)
/// - Always `Copy` (regardless of whether `T` is `Copy`)
/// - Cannot be dereferenced at runtime (panics)
/// - Value is available to the verifier
///
/// # Example
///
/// ```text
/// use trust_vc_types::Ghost;
///
/// fn sum_with_ghost(n: i32) -> i32 {
///     let mut sum = 0;
///     // Ghost variable tracks partial sums for proof
///     let _ghost_partial = Ghost::new(vec![0i32]);
///     for i in 0..n {
///         sum += i;
///     }
///     sum
/// }
/// ```
///
/// # ay Encoding
///
/// In ay, `Ghost<T>` is treated as `T`. The wrapper only affects
/// Rust type checking - the SMT solver sees the underlying value.
#[repr(transparent)]
pub struct Ghost<T>(PhantomData<T>);

// Ghost<T> is always Copy regardless of T (it contains no actual data)
impl<T> Copy for Ghost<T> {}

impl<T> Clone for Ghost<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Ghost<T> {
    /// Create a new ghost value.
    ///
    /// The value is consumed logically for verification but not stored
    /// at runtime. The resulting `Ghost<T>` is zero-sized.
    ///
    /// # Example
    ///
    /// ```text
    /// use trust_vc_types::Ghost;
    ///
    /// let x = 42;
    /// let ghost_x = Ghost::new(x);
    /// // x is consumed, ghost_x is zero-sized
    /// ```
    #[inline]
    #[must_use]
    #[allow(clippy::needless_pass_by_value)]
    pub fn new(value: T) -> Self {
        let _ = value; // Consume but don't store
        Ghost(PhantomData)
    }

    /// Get the inner value (ghost context only).
    ///
    /// # Panics
    ///
    /// Always panics at runtime. This method is only valid in verification
    /// context where the verifier intercepts the call.
    #[doc(hidden)]
    pub fn inner(&self) -> &T {
        ghost_runtime_panic("Ghost", "inner")
    }

    /// Get the inner value mutably (ghost context only).
    ///
    /// # Panics
    ///
    /// Always panics at runtime. This method is only valid in verification
    /// context where the verifier intercepts the call.
    #[doc(hidden)]
    pub fn inner_mut(&mut self) -> &mut T {
        ghost_runtime_panic("Ghost", "inner_mut")
    }

    /// Get the logical value carried by this ghost wrapper.
    ///
    /// # Panics
    ///
    /// Always panics at runtime. This method is only valid in verification
    /// context where the verifier intercepts the call.
    #[doc(hidden)]
    pub fn view(&self) -> T {
        ghost_runtime_panic("Ghost", "view")
    }
}

impl<T> Default for Ghost<T>
where
    T: Default,
{
    fn default() -> Self {
        Ghost::new(T::default())
    }
}

impl<T> fmt::Debug for Ghost<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Ghost").finish_non_exhaustive()
    }
}

// SAFETY: Ghost<T> contains no actual data (PhantomData only), so it is
// trivially Send regardless of T.
unsafe impl<T> Send for Ghost<T> {}
// SAFETY: Ghost<T> contains no actual data (PhantomData only), so it is
// trivially Sync regardless of T.
unsafe impl<T> Sync for Ghost<T> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ghost_new() {
        let _ghost = Ghost::new(42);
        // Zero-sized wrapper
    }
}
