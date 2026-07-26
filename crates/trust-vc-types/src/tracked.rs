// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use core::fmt;
use std::marker::PhantomData;

use crate::runtime_boundary::ghost_runtime_panic;

/// Linear ghost ownership wrapper.
///
/// Unlike `Ghost<T>` which is always `Copy`, `Tracked<T>` is NOT `Copy`
/// (unless `T: Copy`). Rust's move semantics enforce linear consumption —
/// a `Tracked<T>` value must be used exactly once when `T` is not `Copy`.
///
/// # Key Difference from `Ghost<T>`
///
/// | Property | `Ghost<T>` | `Tracked<T>` |
/// |----------|------------|--------------|
/// | Copy | Always Copy | Only if `T: Copy` |
/// | Use case | Spec-mode ghost state | Proof-mode linear resources |
/// | Linearity | None (freely duplicable) | Rust move semantics |
///
/// # ay Encoding
///
/// In ay, `Tracked<T>` is treated as `T`. The wrapper only affects
/// Rust type checking — the SMT solver sees the underlying value.
#[repr(transparent)]
pub struct Tracked<T>(PhantomData<T>);

// NOT Copy unless T: Copy — this is the key difference from Ghost<T>.
// No blanket Clone: non-Copy T has no Clone at all, so Rust move semantics
// enforce linearity automatically.
impl<T: Copy> Copy for Tracked<T> {}

impl<T: Copy> Clone for Tracked<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Tracked<T> {
    /// Wrap a proof-mode value in Tracked.
    ///
    /// The value is consumed logically for verification but not stored
    /// at runtime. The resulting `Tracked<T>` is zero-sized.
    #[inline]
    #[must_use]
    #[allow(clippy::needless_pass_by_value)]
    pub fn new(value: T) -> Self {
        let _ = value;
        Tracked(PhantomData)
    }

    /// Extract the inner value, consuming the Tracked wrapper.
    ///
    /// # Panics
    ///
    /// Always panics at runtime. This method is only valid in verification
    /// context where the verifier intercepts the call.
    pub fn get(self) -> T {
        ghost_runtime_panic("Tracked", "get")
    }

    /// Borrow the inner value immutably (proof context only).
    ///
    /// # Panics
    ///
    /// Always panics at runtime. This method is only valid in verification
    /// context where the verifier intercepts the call.
    #[doc(hidden)]
    #[allow(clippy::should_implement_trait)]
    pub fn borrow(&self) -> &T {
        ghost_runtime_panic("Tracked", "borrow")
    }

    /// Borrow the inner value mutably (proof context only).
    ///
    /// # Panics
    ///
    /// Always panics at runtime. This method is only valid in verification
    /// context where the verifier intercepts the call.
    #[doc(hidden)]
    #[allow(clippy::should_implement_trait)]
    pub fn borrow_mut(&mut self) -> &mut T {
        ghost_runtime_panic("Tracked", "borrow_mut")
    }
}

impl<T> fmt::Debug for Tracked<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Tracked").finish_non_exhaustive()
    }
}

// Send/Sync are intentionally NOT implemented here: Tracked<T> is a newtype over
// PhantomData<T>, so the compiler auto-derives `Send iff T: Send` and `Sync iff
// T: Sync` — i.e. it inherits thread-safety from the tracked type, matching Verus
// (builtin `Tracked<A>` provides no explicit impl either). An unconditional
// `unsafe impl<T> Send/Sync` would let the verifier accept sending a Tracked<A>
// where A is a non-Send permission token, which Verus rejects.

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tracked_new_i32() {
        let t = Tracked::new(42i32);
        let _ = t;
    }

    #[test]
    fn test_tracked_copy_when_t_is_copy() {
        let t1 = Tracked::new(42i32);
        let t2 = t1; // move
        let t3 = t1; // still valid because i32: Copy => Tracked<i32>: Copy
        let _ = (t2, t3);
    }

    #[test]
    fn test_tracked_move_when_t_not_copy() {
        let t1 = Tracked::new(String::from("hello"));
        let t2 = t1; // move — t1 is consumed
                     // t1 is no longer accessible (enforced by Rust type system)
        let _ = t2;
    }

    #[test]
    #[should_panic(expected = "Tracked::get called at runtime")]
    fn test_tracked_get_panics_at_runtime() {
        let t = Tracked::new(42i32);
        let _ = t.get(); // panics: verification-only
    }

    #[test]
    #[should_panic(expected = "Tracked::borrow called at runtime")]
    fn test_tracked_borrow_panics_at_runtime() {
        let t = Tracked::new(42i32);
        let _ = t.borrow(); // panics: verification-only
    }

    #[test]
    #[should_panic(expected = "Tracked::borrow_mut called at runtime")]
    fn test_tracked_borrow_mut_panics_at_runtime() {
        let mut t = Tracked::new(42i32);
        let _ = t.borrow_mut(); // panics: verification-only
    }

    #[test]
    fn test_tracked_debug() {
        let t = Tracked::new(42i32);
        let debug = format!("{:?}", t);
        assert!(
            debug.contains("Tracked"),
            "Debug output should mention Tracked"
        );
    }

    #[test]
    fn test_tracked_is_zero_sized() {
        assert_eq!(
            std::mem::size_of::<Tracked<i32>>(),
            0,
            "Tracked<T> should be zero-sized"
        );
        assert_eq!(
            std::mem::size_of::<Tracked<String>>(),
            0,
            "Tracked<T> should be zero-sized regardless of T"
        );
    }

    #[test]
    fn test_tracked_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Tracked<i32>>();
        assert_send_sync::<Tracked<String>>();
    }
}
