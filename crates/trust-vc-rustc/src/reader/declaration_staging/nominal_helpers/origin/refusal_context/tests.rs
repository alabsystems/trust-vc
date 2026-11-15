// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Observation-only controls; no synthetic macro or helper authority is minted.

use super::*;

const REASON: &str = "impl source cannot be attributed to authored code or enum synthesis";

fn refusal(context: Value) -> Value {
    Failure::UnknownWithContext {
        reason: REASON.into(),
        context,
    }
    .observation()
}

#[test]
fn context_never_changes_the_unknown_state_or_reason() {
    // Even a nested value with these fields cannot overwrite the outer result.
    let observed = refusal(finish(Ok(
        json!({"state": "Checked", "reason": "another reason",
        "import_authorized": true}),
    )));
    assert_eq!(observed["state"], "Unknown");
    assert_eq!(observed["reason"], REASON);
    assert_eq!(observed["origin_refusal_context"]["state"], "Checked");
    assert!(observed.get("import_authorized").is_none());
    let missing = refusal(finish(Err("the source observation is unavailable")));
    assert_eq!(missing["state"], "Unknown");
    assert_eq!(missing["reason"], REASON);
    assert_eq!(missing["origin_refusal_context"]["state"], "Unknown");
}

#[test]
fn observation_budget_refusal_is_sticky_and_separate() {
    let qualification = Work::new();
    let original_work = qualification.remaining;
    let mut work = Budget::new();
    assert!(work.charge(WORK + 1, 0).is_err());
    assert!(work.charge(0, 0).is_err());
    assert_eq!(qualification.remaining, original_work);
    let mut bytes = Budget::new();
    assert!(bytes.charge(0, TEXT_BYTES + 1).is_err());
    assert!(bytes.charge(0, 0).is_err());
    let mut text = Budget::new();
    assert!(attributes::copy_text(&"x".repeat(TEXT_BYTES + 1), &mut text).is_err());
    assert_eq!(
        text.bytes, TEXT_BYTES,
        "text is charged before its owned copy"
    );
    assert!(text.charge(0, 0).is_err());
}

#[test]
fn exact_bound_anchors_and_oversized_contexts_remain_observations() {
    let anchor = AuthoredSpan {
        relative_file: "source/set.rs".into(),
        file_sha256: [0xab; 32],
        original_file_len: 400,
        bytes: (31, 37),
    };
    let encoded = bound_anchor(&anchor, &mut Budget::new()).unwrap();
    assert_eq!(encoded["relative_file"], "source/set.rs");
    assert_eq!(encoded["file_sha256"], "ab".repeat(32));
    assert_eq!(encoded["original_lo"], 31);
    assert_eq!(encoded["original_hi"], 37);
    let oversized = refusal(finish(Ok(json!({"payload": "x".repeat(JSON_BYTES)}))));
    assert_eq!(oversized["state"], "Unknown");
    assert_eq!(oversized["reason"], REASON);
    assert_eq!(oversized["origin_refusal_context"]["state"], "Unknown");
    assert_eq!(
        oversized["origin_refusal_context"]["reason"],
        "origin observation JSON exceeds its byte bound"
    );
}
