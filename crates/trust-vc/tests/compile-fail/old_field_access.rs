// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test: ensures!(old!(state.field)) rejects field access instead of silently
// evaluating it in the post-state.

use trust_vc::ensures;

struct DummyState {
    field: i32,
}

fn reject_field_access(state: DummyState) {
    ensures!(state.field == old!(state.field));
}

fn main() {
    let _ = reject_field_access as fn(DummyState);
}
