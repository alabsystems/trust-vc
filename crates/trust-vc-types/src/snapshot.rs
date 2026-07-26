// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use core::fmt;
use std::marker::PhantomData;

use crate::runtime_boundary::ghost_runtime_panic;

/// A snapshot of a value captured for proof purposes.
///
/// At runtime, `Snapshot<T>` is zero-sized (`PhantomData`).
/// The verifier treats it as an immutable copy of the value at capture time.
///
/// # Key Differences from `Ghost<T>`
///
/// | Property | `Ghost<T>` | `Snapshot<T>` |
/// |----------|------------|---------------|
/// | Mutable | Yes (in ghost context) | No |
/// | Copy | Always Copy | Always Copy |
/// | Use case | Auxiliary proof state | Capturing values at program points |
///
/// # Example
///
/// ```text
/// use trust_vc_types::Snapshot;
///
/// fn sort(v: &mut Vec<i32>) {
///     // Capture the length before modification
///     let original_len = Snapshot::capture(&v.len());
///     v.push(42);
///     // In verification: use explicit snapshot access, e.g. original_len.inner() == v.len() - 1
/// }
/// ```
/// # ay Encoding
///
/// In ay, `Snapshot<T>` is treated as `T`. The snapshot captures
/// the value at a specific program point for postcondition reasoning.
#[repr(transparent)]
pub struct Snapshot<T: ?Sized>(PhantomData<T>);

// Snapshot<T> is always Copy regardless of T (it contains no actual data)
impl<T: ?Sized> Copy for Snapshot<T> {}

impl<T: ?Sized> Clone for Snapshot<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Snapshot<T> {
    /// Capture a snapshot of a value for proof purposes.
    ///
    /// The value is captured logically for verification but the snapshot
    /// contains no runtime data. The resulting `Snapshot<T>` is zero-sized.
    ///
    /// # Example
    ///
    /// ```text
    /// use trust_vc_types::Snapshot;
    ///
    /// let x = 42;
    /// let snap = Snapshot::capture(&x);
    /// // x is NOT consumed - only a logical copy is made
    /// assert_eq!(x, 42);
    /// ```
    ///
    /// ```compile_fail
    /// use trust_vc_types::Snapshot;
    ///
    /// fn takes_ref(_: &i32) {}
    ///
    /// let x = 1;
    /// let snap = Snapshot::capture(&x);
    /// takes_ref(&snap);
    /// ```
    #[must_use = "captured snapshots should be bound and used in proof/spec conditions"]
    #[inline]
    pub fn capture(_value: &T) -> Self {
        Snapshot(PhantomData)
    }

    /// Get the captured value (verification context only).
    ///
    /// # Panics
    ///
    /// Always panics at runtime. This method is only valid in verification
    /// context where the verifier intercepts the call.
    #[doc(hidden)]
    pub fn inner(&self) -> &T {
        ghost_runtime_panic("Snapshot", "inner")
    }
}

impl<T: ?Sized> fmt::Debug for Snapshot<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Snapshot").finish_non_exhaustive()
    }
}

// SAFETY: Snapshot<T> contains no actual data (PhantomData only), so it is
// trivially Send regardless of T.
unsafe impl<T: ?Sized> Send for Snapshot<T> {}
// SAFETY: Snapshot<T> contains no actual data (PhantomData only), so it is
// trivially Sync regardless of T.
unsafe impl<T: ?Sized> Sync for Snapshot<T> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_snapshot_capture() {
        let value = vec![1, 2, 3];
        let _snapshot = Snapshot::capture(&value);
        // Captures value at point - zero-sized at runtime
    }
}
