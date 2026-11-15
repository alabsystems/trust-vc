//! Native discriminators for rigid type/decorations and quantified Nat domains.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

fn check(name: &str, source: &str, proved: u64, failure_line: Option<usize>) {
    let result = common::run(name, source, &[]);
    assert!(result.raw.is_empty(), "{result:?}");
    let functions = result.record["functions"].as_array().unwrap();
    let proof = functions
        .iter()
        .find(|function| function["def_path"] == "test")
        .expect("the original proof");
    assert_eq!(proof["sites_proved"], proved, "{result:?}");
    if let Some(line) = failure_line {
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "verification-failed", "{result:?}");
        assert_eq!(proof["verdict"], "failed", "{result:?}");
        assert_eq!(proof["sites_failed"], 1, "{result:?}");
        let errors = result.errors();
        assert_eq!(errors.len(), 1, "{result:?}");
        assert_eq!(errors[0].message, "assertion failed");
        assert_eq!(errors[0].primary_lines, vec![line], "{errors:?}");
    } else {
        assert_eq!(result.exit, 0, "{result:?}");
        assert_eq!(result.outcome(), "checked", "{result:?}");
        assert_eq!(proof["verdict"], "verified", "{result:?}");
        assert_eq!(proof["sites_failed"], 0, "{result:?}");
        assert!(result.errors().is_empty(), "{result:?}");
    }
}

#[test]
fn nat_material_call_licenses_its_same_type_trigger() {
    check(
        "nat_material_type",
        include_str!("concrete_quantifier_domains/nat-type-positive.body.rs"),
        2,
        None,
    );
}

#[test]
fn int_material_call_does_not_license_a_nat_trigger() {
    check(
        "int_material_type",
        include_str!("concrete_quantifier_domains/nat-type-negative.body.rs"),
        1,
        Some(5),
    );
}

#[test]
fn owned_material_call_licenses_its_same_decoration_trigger() {
    check(
        "owned_material_decoration",
        include_str!("concrete_quantifier_domains/decoration-positive.body.rs"),
        2,
        None,
    );
}

#[test]
fn shared_reference_call_does_not_license_an_owned_trigger() {
    check(
        "reference_material_decoration",
        include_str!("concrete_quantifier_domains/decoration-negative.body.rs"),
        1,
        Some(5),
    );
}

#[test]
fn zero_int_trigger_can_instantiate_a_nat_domain() {
    check(
        "zero_int_nat_domain",
        include_str!("concrete_quantifier_domains/nat-domain-positive.body.rs"),
        1,
        None,
    );
}

#[test]
fn negative_int_trigger_does_not_create_nat_membership() {
    check(
        "negative_int_nat_domain",
        include_str!("concrete_quantifier_domains/nat-domain-negative.body.rs"),
        0,
        Some(7),
    );
}
