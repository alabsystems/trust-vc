// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// A FOREIGN namespaced attribute (`#[some_crate::widget]`, two segments but not
// `trust_vc`) carries no contract, so the dropped-clause gate must not reject
// it. It can be an attribute macro from another crate, which can rewrite the
// item it sits on or emit an impl, so the unread-item rule refuses a
// `Verified` answer for this file instead.

#[must_use]
#[allow(dead_code)]
#[some_crate::widget(anything)]
#[trust_vc::ensures(result == 1u64)]
fn foreign_attribute_is_not_a_dropped_clause(x: u64) -> u64 {
    trust_vc::assert!(1u64 == 1u64);
    1u64
}
