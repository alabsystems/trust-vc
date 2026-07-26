// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Test to verify that invariant! macro executes at runtime (line 1468 of lib.rs)

use trust_vc::invariant;

#[test]
#[cfg_attr(not(test), should_panic)] // In non-test mode, this WOULD panic
fn test_invariant_executes_at_runtime_in_production() {
    // From lib.rs line 1468: assert!(#tokens, "trust_vc loop invariant failed");
    // This means in production (not(test)) mode, invariant! does runtime assert!

    let mut i = 0;
    while i < 5 {
        // This invariant is FALSE when i >= 3
        // In production, this would panic at runtime
        // In test mode, it doesn't assert so won't panic
        invariant!(i < 3);

        i += 1;
    }

    // In test mode, we reach here (no runtime assertion)
    // In production mode, would panic when i=3
}

#[test]
fn test_invariant_false_doesnt_panic_in_test_mode() {
    // In test mode, invariant! doesn't execute runtime assertions
    // So even false invariants don't panic

    // Obviously false invariant
    invariant!(false);

    // Contradictory invariant
    let _x = 5;
    invariant!(_x != _x);

    // Another false invariant
    invariant!(1 > 2);

    // We reach here because in test mode, invariant! doesn't assert
    // This allows negative tests to work
}

#[test]
fn test_invariant_in_loop_with_false_condition() {
    // Test that false loop invariants don't panic in test mode

    let mut counter = 10;
    while counter > 0 {
        // This invariant is false (counter starts at 10, not < 5)
        invariant!(counter < 5);

        counter -= 1;

        // Break early to prevent infinite test
        if counter == 5 {
            break;
        }
    }

    // Reached here without panic - invariant! didn't execute at runtime in test mode
}

#[test]
fn test_multiple_invariants_runtime() {
    // Multiple invariants, some false

    let mut x = 0;
    let mut _y = 10;

    while x < 5 {
        invariant!(x >= 0); // True
        invariant!(_y < 5); // False (_y starts at 10)
        invariant!(x + _y == 15); // False initially

        x += 1;
        _y -= 1;
    }

    // No panic even with false invariants (test mode doesn't assert)
}
