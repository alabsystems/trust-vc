// Test: #[trust_vc::liveness] without protocol name should error
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Case 1: fairness-only form (no protocol name)
#[trust_vc::liveness(fairness = "weak")]
fn liveness_no_protocol() {}

fn main() {}
