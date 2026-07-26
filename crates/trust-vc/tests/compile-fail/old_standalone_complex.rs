// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test: standalone old!(state.field) outside ensures!() rejects complex
// expressions instead of silently evaluating them in the current state.

use trust_vc::old;

struct DummyState {
    field: i32,
}

fn reject_standalone_field_access(state: DummyState) -> i32 {
    old!(state.field)
}

fn main() {
    let s = DummyState { field: 42 };
    let _ = reject_standalone_field_access(s);
}
