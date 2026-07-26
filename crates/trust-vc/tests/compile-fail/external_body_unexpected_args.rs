// Test: #[trust_vc::external_body] with unexpected arguments should error
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::external_body(verbose)]
fn external_body_with_args() {}

fn main() {}
