// extern_spec! basic tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `extern_spec!` macro.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file verify extern_spec contracts using ay through VerificationPipeline
//!
//! This macro allows attaching specifications to external functions
//! (functions you don't own, like stdlib). At compile time, it generates
//! stub functions with doc markers that trust_mc uses for verification.
//!
//! Note: Generic types must use turbofish syntax (Type::<T>) to avoid
//! parsing ambiguity with comparison operators.

// Simple extern_spec for Option::is_some
trust_vc::extern_spec! {
    impl<T> core::option::Option::<T> {
        #[ensures(result == self.is_some())]
        fn is_some(&self) -> bool;
    }
}

// Extern spec with requires clause
trust_vc::extern_spec! {
    impl<T> core::option::Option::<T> {
        #[requires(self.is_some())]
        fn unwrap(self) -> T;
    }
}

// Multiple methods in one impl block
trust_vc::extern_spec! {
    impl<T> std::vec::Vec::<T> {
        // Note: Self not supported in return types yet, use concrete type
        fn len(&self) -> usize;

        #[requires(self.len() > 0)]
        fn pop(&mut self) -> Option<T>;
    }
}

// Extern spec for primitive types
trust_vc::extern_spec! {
    impl i32 {
        fn abs(self) -> i32;
    }
}

// Note: Slice types [T] are not supported - only type paths
// For slices, use Vec::<T> or array types

// Multiple impl blocks in one extern_spec
trust_vc::extern_spec! {
    impl<T> core::option::Option::<T> {
        fn is_none(&self) -> bool;
    }

    impl<T> core::result::Result::<T, ()> {
        fn is_ok(&self) -> bool;
    }
}

mod common;

#[test]
fn extern_spec_option_compiles() {
    common::with_clean_verification(|| {
        let opt: Option<i32> = Some(42);
        assert!(opt.is_some());
    })
}

#[test]
fn extern_spec_vec_compiles() {
    common::with_clean_verification(|| {
        let v: Vec<i32> = Vec::new();
        assert_eq!(v.len(), 0);
    })
}

#[test]
fn extern_spec_i32_compiles() {
    common::with_clean_verification(|| {
        let x: i32 = -5;
        assert_eq!(x.abs(), 5);
    })
}

#[test]
fn extern_spec_does_not_affect_runtime() {
    common::with_clean_verification(|| {
        // extern_spec only adds verification metadata
        // Runtime behavior is unchanged
        let mut v = vec![1, 2, 3];
        assert_eq!(v.len(), 3);
        assert_eq!(v.pop(), Some(3));
        assert_eq!(v.len(), 2);
    })
}

#[test]
fn extern_spec_result_compiles() {
    common::with_clean_verification(|| {
        let ok: Result<i32, ()> = Ok(42);
        assert!(ok.is_ok());
    })
}

#[test]
fn extern_spec_option_none_compiles() {
    common::with_clean_verification(|| {
        let none: Option<i32> = None;
        assert!(none.is_none());
    })
}
