//! Regression tests for malformed source-extraction markers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

use trust_vc_core::verify_macro::verify_markers_impl;

#[test]
fn malformed_marker_is_not_silently_dropped_when_other_marker_is_valid() {
    common::with_clean_verification(|| {
        use std::fs;
        use std::path::Path;

        let test_dir = Path::new("target/test_marker_extraction_malformed");
        fs::create_dir_all(test_dir).unwrap();
        let test_file = test_dir.join("malformed_with_valid.rs");

        fs::write(
            &test_file,
            r#"
            #[__trust_vc_requires = 123]
            #[__trust_vc_ensures = "true"]
            fn malformed_with_valid_marker(x: i32) -> i32 {
                x
            }
        "#,
        )
        .unwrap();

        let result = verify_markers_impl("test::module", test_file.to_str().unwrap());

        fs::remove_file(&test_file).ok();

        assert!(
            result.is_err(),
            "malformed marker must fail source extraction, got: {:?}",
            result
        );
        let err_msg = result.unwrap_err();
        assert!(
            err_msg.contains("Malformed marker #[__trust_vc_requires]"),
            "error should identify malformed marker, got: {}",
            err_msg
        );
    })
}
