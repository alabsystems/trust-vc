// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;

#[test]
fn test_extract_mutable_parameter() {
    let code = r#"
        #[requires(x > 0)]
        fn with_mut(mut x: i32) {
            x += 1;
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "with_mut").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert!(vc.variables.iter().any(|v| v.name == "x"));
}

#[test]
fn test_extract_reference_parameter() {
    let code = r#"
        #[requires(x > 0)]
        fn with_ref(x: &i32) {
            let _ = *x;
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "with_ref").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert!(
        vc.variables.iter().any(|v| v.name == "x"),
        "should extract 'x' from reference parameter"
    );
}

#[test]
fn test_extract_ghost_parameter_marks_erased_wrapper() {
    let code = r#"
        fn with_ghost(t: Ghost<Option<u64>>) {
            let _ = t;
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "with_ghost").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert!(
        vc.variables.iter().any(|v| {
            v.name == "t" && v.ty == crate::ir::TrustVcType::parse_or_opaque("Option<u64>")
        }),
        "Ghost<Option<u64>> should erase to Option<u64>"
    );
    assert!(
        vc.is_erased_ghost_var("t"),
        "Ghost<T> parameters should be tracked separately from plain T"
    );
}

#[test]
fn test_extract_tuple_destructuring_parameter() {
    let code = r#"
        #[requires(a > 0)]
        fn with_tuple((a, b): (i32, i32)) {
            let _ = a + b;
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "with_tuple").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert!(
        vc.variables.iter().any(|v| v.name == "a"),
        "should extract 'a' from tuple destructuring"
    );
    assert!(
        vc.variables.iter().any(|v| v.name == "b"),
        "should extract 'b' from tuple destructuring"
    );
}
