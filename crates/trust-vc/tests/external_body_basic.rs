// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the #[external_body] attribute.
//!
//! Tests that the external_body attribute correctly marks function
//! implementations as trusted (not verified) while still checking
//! contracts at call sites.

use syn::parse_quote;
use trust_vc_core::expand_external_body;

#[test]
fn test_expand_external_body_basic() {
    let input = parse_quote! {
        fn read_from_socket(buf: &mut [u8]) -> usize {
            trust_vc::requires!(buf.len() > 0);
            trust_vc::ensures!(|result: usize| result <= buf.len());

            // Implementation is trusted, not verified
            unsafe {
                // System call or FFI here
                std::ptr::write_bytes(buf.as_mut_ptr(), 0, buf.len());
                buf.len()
            }
        }
    };

    let expanded = expand_external_body(input);
    let expanded_str = expanded.to_string();

    // Verify external_body marker is added
    assert!(
        expanded_str.contains("__trust_vc_external_body"),
        "external_body should add external body marker"
    );

    // Verify function signature is preserved
    assert!(
        expanded_str.contains("fn read_from_socket"),
        "Function name should be preserved"
    );

    // Verify contracts are preserved for call-site checking
    assert!(
        expanded_str.contains("requires") || expanded_str.contains("buf.len() > 0"),
        "Precondition should be preserved"
    );

    assert!(
        expanded_str.contains("ensures") || expanded_str.contains("result <= buf.len()"),
        "Postcondition should be preserved"
    );

    // Test that expansion succeeds - this ensures the expansion is valid
    // Note: We don't actually verify external_body functions as they're trusted
}

#[test]
fn test_expand_external_body_ffi_wrapper() {
    let input = parse_quote! {
        fn get_system_time() -> u64 {
            trust_vc::ensures!(|result: u64| result > 0);

            extern "C" {
                fn time(t: *mut i64) -> i64;
            }

            unsafe {
                time(std::ptr::null_mut()) as u64
            }
        }
    };

    let expanded = expand_external_body(input);
    let expanded_str = expanded.to_string();

    // Verify external_body marker is added
    assert!(
        expanded_str.contains("__trust_vc_external_body"),
        "external_body should add external body marker"
    );

    // Verify FFI call is preserved but not verified
    assert!(
        expanded_str.contains("unsafe"),
        "Unsafe block should be preserved"
    );

    // Test that expansion succeeds - this ensures the expansion is valid
    // Note: We don't actually verify external_body functions as they're trusted
}

#[test]
fn test_expand_external_body_with_complex_contracts() {
    let input = parse_quote! {
        fn parse_config(data: &str) -> Result<Config, String> {
            trust_vc::requires!(data.len() > 0);
            trust_vc::requires!(!data.is_empty());
            trust_vc::ensures!(|result: &Result<Config, String>|
                result.is_ok() ==> result.as_ref().unwrap().is_valid()
            );

            // Complex parsing logic that we trust but don't verify
            serde_json::from_str(data).map_err(|e| e.to_string())
        }
    };

    let expanded = expand_external_body(input);
    let expanded_str = expanded.to_string();

    // Verify external_body marker is added
    assert!(
        expanded_str.contains("__trust_vc_external_body"),
        "external_body should add external body marker"
    );

    // Verify multiple preconditions are preserved
    assert!(
        expanded_str.contains("data.len() > 0") || expanded_str.contains("requires"),
        "First precondition should be preserved"
    );

    // Test that expansion succeeds - this ensures the expansion is valid
    // Note: We don't actually verify external_body functions as they're trusted
}

#[test]
fn test_expand_external_body_generic_function() {
    let input = parse_quote! {
        fn serialize_to_bytes<T: serde::Serialize>(value: &T) -> Vec<u8> {
            trust_vc::ensures!(|result: &Vec<u8>| result.len() > 0);

            // Trust serialization library
            bincode::serialize(value).unwrap_or_else(|_| vec![0])
        }
    };

    let expanded = expand_external_body(input);
    let expanded_str = expanded.to_string();

    // Verify external_body marker is added
    assert!(
        expanded_str.contains("__trust_vc_external_body"),
        "external_body should add external body marker"
    );

    // Verify generic parameter and trait bound are preserved
    assert!(
        expanded_str.contains("<T") || expanded_str.contains("< T"),
        "Generic parameter should be preserved"
    );

    // Test that expansion succeeds - this ensures the expansion is valid
    // Note: We don't actually verify external_body functions as they're trusted
}

#[test]
fn test_expand_external_body_async_function() {
    let input = parse_quote! {
        async fn fetch_data(url: &str) -> Result<String, Error> {
            trust_vc::requires!(url.starts_with("https://"));
            trust_vc::ensures!(|result: &Result<String, Error>|
                result.is_ok() ==> result.as_ref().unwrap().len() > 0
            );

            // Async HTTP call - trusted implementation
            reqwest::get(url).await?.text().await
        }
    };

    let expanded = expand_external_body(input);
    let expanded_str = expanded.to_string();

    // Verify external_body marker is added
    assert!(
        expanded_str.contains("__trust_vc_external_body"),
        "external_body should add external body marker"
    );

    // Verify async function is preserved
    assert!(
        expanded_str.contains("async"),
        "Async keyword should be preserved"
    );

    // Test that expansion succeeds - this ensures the expansion is valid
    // Note: We don't actually verify external_body functions as they're trusted
}

#[test]
fn test_expand_external_body_hardware_interaction() {
    let input = parse_quote! {
        fn read_sensor_value(sensor_id: u32) -> Option<f64> {
            trust_vc::requires!(sensor_id < 256);
            trust_vc::ensures!(|result: &Option<f64>|
                result.is_some() ==> result.unwrap() >= -273.15  // Above absolute zero
            );

            // Direct hardware register access - cannot be verified
            unsafe {
                let addr = 0x4000_0000 + (sensor_id as usize * 4);
                let value = std::ptr::read_volatile(addr as *const f32);
                if value.is_finite() {
                    Some(value as f64)
                } else {
                    None
                }
            }
        }
    };

    let expanded = expand_external_body(input);
    let expanded_str = expanded.to_string();

    // Verify external_body marker is added
    assert!(
        expanded_str.contains("__trust_vc_external_body"),
        "external_body should add external body marker"
    );

    // Verify hardware interaction code is preserved but not verified
    assert!(
        expanded_str.contains("read_volatile") || expanded_str.contains("unsafe"),
        "Hardware interaction should be preserved"
    );

    // Test that expansion succeeds - this ensures the expansion is valid
    // Note: We don't actually verify external_body functions as they're trusted
}
