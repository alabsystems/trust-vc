// Test: #[trust_vc::proof] with unexpected arguments should error
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::proof(verbose)]
fn proof_with_args() {}

fn main() {}
