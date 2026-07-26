// Test: #[trust_vc::broadcast] with unexpected arguments should error
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::broadcast(verbose)]
fn broadcast_with_args() {}

fn main() {}
