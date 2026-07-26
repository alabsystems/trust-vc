// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end coverage for `for i in lo..hi` loop invariant inference.
//!
//! This exercises the real `#[trust_vc::proof]` path:
//! - proc-macro range-loop folding
//! - iterator variable registration
//! - auto-applied loop metadata
//! - VerificationPipeline-backed proof verification
//!
//! Part of #2502.

mod common;

#[test]
fn test_for_range_loop_auto_inference_verifies_end_to_end() {
    let _ = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn inferred_range_loop() {
            let bound: usize = 1;
            let mut sum: usize = 0;
            for i in 0..bound {
                trust_vc::invariant!(bound == 1);
                sum += i;
            }
            let _ = sum;
        }

        inferred_range_loop();
    });
}
