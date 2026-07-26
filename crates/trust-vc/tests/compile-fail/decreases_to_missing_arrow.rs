// Test: decreases_to! without `=>` separator should error
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

fn main() {
    trust_vc::decreases_to!(1, 2, 3);
}
