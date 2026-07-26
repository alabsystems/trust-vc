// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::marker::PhantomData;

use crate::runtime_boundary::ghost_runtime_panic;

/// A spec-only closure type for higher-order specification functions.
///
/// `SpecFn<Args, Ret>` is a concrete, ghost-only type that represents
/// a specification closure. It never executes at runtime; use it for
/// higher-order spec helpers like sequence constructors.
///
/// # Example
/// ```text
/// use trust_vc_types::SpecFn;
///
/// #[trust_vc::spec]
/// fn make_doubler() -> SpecFn<i32, i32> {
///     SpecFn::new(|i: i32| i * 2)
/// }
/// ```
#[derive(Clone, Copy, Debug)]
pub struct SpecFn<Args, Ret> {
    _marker: PhantomData<fn(Args) -> Ret>,
}

impl<Args, Ret> PartialEq for SpecFn<Args, Ret> {
    fn eq(&self, _other: &Self) -> bool {
        ghost_runtime_panic("SpecFn", "eq")
    }
}

impl<Args, Ret> Eq for SpecFn<Args, Ret> {}

impl<Args, Ret> SpecFn<Args, Ret> {
    /// Constructs a spec closure from a Rust closure.
    ///
    /// The closure is only type-checked; it is never executed.
    #[allow(unused_variables)]
    pub fn new<F>(_f: F) -> Self
    where
        F: Fn(Args) -> Ret,
    {
        // Ensure the closure is type-checked without executing it.
        if false {
            let _ = &_f;
        }
        SpecFn {
            _marker: PhantomData,
        }
    }

    /// Applies the spec closure.
    ///
    /// This function should never execute at runtime; it exists so
    /// spec code can type-check closure application.
    #[doc(hidden)]
    #[allow(dead_code)]
    pub fn call(&self, _args: Args) -> Ret {
        ghost_runtime_panic("SpecFn", "call")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spec_fn_new() {
        let _spec_fn = SpecFn::<i32, i32>::new(|x| x * 2);
        // Spec-only closure
    }
}
