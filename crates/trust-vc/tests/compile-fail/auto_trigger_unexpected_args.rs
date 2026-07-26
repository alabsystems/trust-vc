// Test: #[trust_vc::auto_trigger] with unexpected arguments should error
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::auto_trigger(verbose)]
fn auto_trigger_with_args() {}

fn main() {}
