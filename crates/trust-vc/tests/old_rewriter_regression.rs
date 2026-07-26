// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression coverage for supported old!() token rewriting in ensures!().
//!
//! SOUNDNESS: #1836 now fails closed for complex `old!()` expressions via
//! trybuild coverage in `tests/compile-fail/old_*.rs`.

use trust_vc::ensures;
use trust_vc_core::verify_macro;

mod common;

fn collected_conditions() -> Vec<String> {
    verify_macro::get_context()
        .map(|ctx| {
            ctx.obligations()
                .iter()
                .map(|obligation| obligation.condition().to_string())
                .collect()
        })
        .unwrap_or_default()
}

#[test]
fn test_old_simple_identifier_rewrites_in_ensures_1836_control() {
    common::with_clean_verification(|| {
        let x = 10;
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        assert_eq!(x, 10);

        ensures!(x == old!(x));

        let conditions = collected_conditions();
        assert!(
            conditions
                .iter()
                .any(|condition| condition.contains("__trust_vc_old_x")),
            "control: old!(x) should be rewritten to a synthetic old variable, got {:?}",
            conditions
        );
        assert!(
            !conditions
                .iter()
                .any(|condition| condition.contains("old!")),
            "control: rewritten conditions should not retain raw old!(x), got {:?}",
            conditions
        );
    });
}
