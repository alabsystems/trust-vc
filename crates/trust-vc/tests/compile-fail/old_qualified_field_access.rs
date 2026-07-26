// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test: ensures!(trust_vc::old!(state.field)) rejects qualified field access
// instead of silently evaluating it in the post-state.

use trust_vc::ensures;

struct DummyState {
    field: i32,
}

fn reject_qualified_field_access(state: DummyState) {
    ensures!(state.field == trust_vc::old!(state.field));
}

fn main() {
    let _ = reject_qualified_field_access as fn(DummyState);
}
