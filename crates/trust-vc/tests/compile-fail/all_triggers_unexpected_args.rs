// Test: #[trust_vc::all_triggers] with unexpected arguments should error
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::all_triggers(verbose)]
fn all_triggers_with_args() {}

fn main() {}
