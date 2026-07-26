// Test: #[trust_vc::via_fn] with unexpected arguments should error
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::via_fn(verbose)]
fn via_fn_with_args(_n: u64) {}

fn main() {}
