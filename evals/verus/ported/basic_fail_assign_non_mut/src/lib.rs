// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Mirrors upstream basic.rs `test_fail_assign_non_mut`:
//
//     fn test1() {
//         let x: u64 = 10;
//         x = 20;
//     }
//
// Upstream this is an `assert_rust_error_msg` case: the error comes from the
// ordinary Rust compiler channel (E0384), not from the verifier. The evidence
// gate's cargo-fixture rust-error channel runs a real `cargo check` on this
// crate and matches "cannot assign twice to immutable variable" against the
// emitted diagnostic.
pub fn test1() {
    let x: u64 = 10;
    x = 20;
}
