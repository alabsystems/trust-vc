// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Faithful reproduction of upstream Verus
// `source/rust_verify_test/tests/overflow.rs::test_literal_out_of_range`
// (pin a40d57c73650cd3648b09386bfdb96ab5c270626):
//
//     const C: u8 = 256 - 1;  // => Err: assert_rust_error_msg(err,
//         "attempt to compute `0_u8 - 1_u8`, which would overflow")
//
// This is a genuine RUSTC const-evaluation error (E0080), emitted by the real
// compiler when this crate is built — not a string trust-vc reconstructs. The
// `256` literal reduces to `0_u8`, and `0_u8 - 1_u8` underflows.

pub const C: u8 = 256 - 1;
