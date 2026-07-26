// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

fn regression_114_get_bool() -> bool {
    true
}

fn regression_114_require_false() -> bool {
    false
}

#[trust_vc::ensures(true)]
fn regression_114_unrelated_precondition() {
    let x = 6i32;

    if !regression_114_get_bool() {
        let _ = regression_114_require_false(); // INCORRECT CONTEXT
    }

    trust_vc::assert!(x == 7i32);
}

// The upstream harness checks that the reported diagnostic context excludes the
// dead branch marked above.
