// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Basic runtime coverage for the track_let! proc macro wrapper.

use trust_vc::track_let;

#[test]
fn test_track_let_executes_initializer_in_runtime_block() {
    let seed = 41;
    let mut observed = seed;

    track_let! {
        let _tracked: i32 = {
            observed += 1;
            observed
        };
    }

    assert_eq!(observed, 42);
}

#[test]
fn test_track_let_binding_does_not_escape_macro_scope() {
    let shadowed = 7;

    track_let! {
        let _shadowed: i32 = 42;
    }

    assert_eq!(shadowed, 7);
}
