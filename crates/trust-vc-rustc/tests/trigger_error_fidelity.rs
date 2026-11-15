//! Trigger failures preserve source diagnostics and their phase precedence.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

const TRIGGER: &str = "Could not automatically infer triggers for this quantifier.  Use #[trigger] annotations to manually mark trigger terms instead.";
const INLINE: &str = "'inline' is only allowed for 'spec' functions";

fn rejected(
    name: &str,
    source: &str,
    message: &str,
    line: usize,
    erase: Option<i32>,
    code: Option<&str>,
) {
    let actual = common::run(name, source, &[]);
    assert_eq!(actual.exit, 1, "{actual:?}");
    assert_eq!(
        actual.outcome(),
        if code.is_some() {
            "erase-rejected"
        } else {
            "verus-rejected"
        },
        "{actual:?}"
    );
    assert!(actual.raw.is_empty(), "{actual:?}");
    assert_eq!(
        actual.record["crate_refusals"],
        serde_json::json!([]),
        "{actual:?}"
    );
    assert_eq!(
        actual.record.get("erase_exit"),
        Some(&serde_json::json!(erase)),
        "{actual:?}"
    );
    let errors = actual.errors();
    assert_eq!(errors.len(), 1, "{actual:?}");
    assert_eq!(errors[0].message, message, "{actual:?}");
    assert_eq!(errors[0].code.as_deref(), code, "{actual:?}");
    assert_eq!(errors[0].primary_lines, [line], "{actual:?}");
    for function in actual.record["functions"]
        .as_array()
        .expect("actual functions")
    {
        assert_ne!(function["verdict"], "verified", "{actual:?}");
        for field in ["sites_proved", "sites_failed"] {
            assert_eq!(
                function.get(field),
                Some(&serde_json::Value::Null),
                "{actual:?}"
            );
        }
    }
    let dump = actual.vcir.as_deref().expect("actual typed source IR");
    assert!(dump.contains("untriggered-"), "{dump}");
}

#[test]
fn generic_choice_reports_the_original_trigger_error() {
    rejected("source_choice_trigger", "verus! {\n#[verifier::inline]\nspec fn pick<A>(x: A) -> A { choose |y: A| y == x }\nproof fn test(x: u8) { assert(pick::<u8>(x) == x); }\n}\n", TRIGGER, 3, Some(0), None);
}

#[test]
fn forall_keeps_its_actual_typed_condition_after_inference_fails() {
    rejected(
        "source_forall_trigger",
        "verus! {\nproof fn test() {\n    assert(forall |x: u8| x == 0);\n}\n}\n",
        TRIGGER,
        3,
        Some(0),
        None,
    );
}

#[test]
fn sst_construction_error_precedes_choice_trigger_elaboration() {
    rejected("source_choice_earlier_sst", "verus! {\n#[verifier::inline]\nspec fn pick<A>(x: A) -> A { choose |y: A| y == x }\nproof fn test() { verus_builtin::assert_bitvector_by({ ensures(true); assert(true); }); }\n}\n", "assert_bitvector_by cannot contain a proof block", 4, Some(0), None);
}

#[test]
fn used_inline_choice_does_not_change_the_sst_stage_order() {
    rejected("source_choice_used_earlier_sst", "verus! {\n#[verifier::inline]\nspec fn pick<A>(x: A) -> A { choose |y: A| y == x }\nproof fn test(x: u8) { assert(pick::<u8>(x) == x); verus_builtin::assert_bitvector_by({ ensures(true); assert(true); }); }\n}\n", "assert_bitvector_by cannot contain a proof block", 4, Some(0), None);
}

#[test]
fn an_independent_earlier_header_is_still_checked() {
    rejected("source_choice_earlier_header", "verus! {\n#[verifier::inline]\nspec fn pick<A>(x: A) -> A { choose |y: A| y == x }\n#[verifier::inline]\nproof fn wrong() {}\nproof fn test() {}\n}\n", INLINE, 5, None, None);
}

#[test]
fn genuine_erase_move_failure_precedes_sst_trigger_reporting() {
    rejected("source_choice_erase_move", "verus! {\n#[verifier::inline]\nspec fn pick<A>(x: A) -> A { choose |y: A| y == x }\nstruct MoveCell { value: u8 }\nfn bad() { let x = MoveCell { value: 0 }; let _y = x; let _z = x; }\nproof fn test() {}\n}\n", "use of moved value: `x`", 5, Some(1), Some("E0382"));
}

#[test]
fn a_rejected_used_generic_function_keeps_its_own_header() {
    rejected("source_choice_same_owner", "verus! {\n#[verifier::inline]\nproof fn pick<A>(x: A) { let ghost y = choose |z: A| z == x; }\nproof fn test(x: u8) { pick::<u8>(x); }\n}\n", INLINE, 3, None, None);
}

#[test]
fn earlier_header_is_preserved_with_an_actual_closed_choice_caller() {
    rejected("source_choice_used_header", "verus! {\n#[verifier::inline]\nproof fn wrong() {}\n#[verifier::inline]\nspec fn pick<A>(x: A) -> A { choose |z: A| z == x }\nproof fn test(x: u8) { assert(pick::<u8>(x) == x); }\n}\n", INLINE, 3, None, None);
}

#[test]
fn modules_keep_their_own_first_error_across_both_sst_stages() {
    let source = "verus! {\nmod left {\nuse super::*;\n#[verifier::inline]\nspec fn pick<A>(x: A) -> A { choose |y: A| y == x }\nproof fn test() { verus_builtin::assert_bitvector_by({ ensures(true); assert(true); }); }\n}\nmod right {\nuse super::*;\n#[verifier::inline]\nspec fn pick<A>(x: A) -> A { choose |y: A| y == x }\nproof fn test() {}\n}\n}\n";
    let actual = common::run("source_choice_mixed_modules", source, &[]);
    assert_eq!(actual.exit, 1, "{actual:?}");
    assert_eq!(actual.outcome(), "verus-rejected", "{actual:?}");
    assert_eq!(actual.record["erase_exit"], 0, "{actual:?}");
    assert_eq!(
        actual.record["crate_refusals"],
        serde_json::json!([]),
        "{actual:?}"
    );
    assert!(actual.raw.is_empty(), "{actual:?}");
    let mut errors = actual
        .errors()
        .into_iter()
        .map(|error| {
            assert!(error.code.is_none(), "{actual:?}");
            (error.primary_lines.clone(), error.message.as_str())
        })
        .collect::<Vec<_>>();
    errors.sort();
    assert_eq!(
        errors,
        vec![
            (vec![6], "assert_bitvector_by cannot contain a proof block"),
            (vec![11], TRIGGER),
        ],
        "{actual:?}"
    );
    for function in actual.record["functions"]
        .as_array()
        .expect("actual functions")
    {
        assert_ne!(function["verdict"], "verified", "{actual:?}");
        assert_eq!(
            function.get("sites_proved"),
            Some(&serde_json::Value::Null),
            "{actual:?}"
        );
        assert_eq!(
            function.get("sites_failed"),
            Some(&serde_json::Value::Null),
            "{actual:?}"
        );
    }
}
