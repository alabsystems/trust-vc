// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_lookup_extern_spec_source_parses_single_block() {
    let source = r#"
        trust_vc::extern_spec! {
            impl i32 {
                #[requires(false)]
                fn abs(self) -> i32;
            }
        }
    "#;

    let entry = lookup_extern_spec_source("single.rs", source, "i32::abs")
        .expect("lookup should succeed")
        .expect("entry should exist");

    assert_eq!(entry.target_path, "i32::abs");
    assert!(entry.param_names.is_empty());
    assert_eq!(entry.requires, vec!["false"]);
}

#[test]
fn test_lookup_extern_spec_source_parses_multiple_blocks() {
    let source = r#"
        trust_vc::extern_spec! {
            impl i32 {
                fn abs(self) -> i32;
            }
        }

        trust_vc::extern_spec! {
            impl bool {
                #[ensures(true)]
                fn then(self) -> bool;
            }
        }
    "#;

    let entry = lookup_extern_spec_source("multi.rs", source, "bool::then")
        .expect("lookup should succeed")
        .expect("entry should exist");

    assert_eq!(entry.target_path, "bool::then");
    assert!(entry.param_names.is_empty());
    assert_eq!(entry.ensures, vec!["true"]);
}

#[test]
fn test_lookup_extern_spec_source_walks_inline_modules() {
    let source = r#"
        mod nested {
            trust_vc::extern_spec! {
                impl i32 {
                    #[requires(true)]
                    fn abs(self) -> i32;
                }
            }
        }
    "#;

    let entry = lookup_extern_spec_source("nested.rs", source, "i32::abs")
        .expect("lookup should succeed")
        .expect("entry should exist");

    assert_eq!(entry.target_path, "i32::abs");
    assert!(entry.param_names.is_empty());
    assert_eq!(entry.requires, vec!["true"]);
}

#[test]
fn test_lookup_extern_spec_source_accepts_external_spec_alias() {
    let source = r#"
        trust_vc::external_spec! {
            impl i32 {
                #[requires(false)]
                fn abs(self) -> i32;
            }
        }
    "#;

    let entry = lookup_extern_spec_source("single.rs", source, "i32::abs")
        .expect("lookup should succeed")
        .expect("entry should exist");

    assert_eq!(entry.target_path, "i32::abs");
    assert!(entry.param_names.is_empty());
    assert_eq!(entry.requires, vec!["false"]);
}

#[test]
fn test_normalize_extern_spec_path_erases_generics_for_lookup() {
    let with_generics = normalize_extern_spec_path("core::option::Option::<i32>::unwrap")
        .expect("normalization should succeed");
    let without_generics = normalize_extern_spec_path("core::option::Option::unwrap")
        .expect("normalization should succeed");

    assert_eq!(with_generics, without_generics);
    assert_eq!(with_generics, "core::option::Option::unwrap");
}

#[test]
fn test_lookup_extern_spec_source_keeps_lexical_paths_distinct() {
    let source = r#"
        trust_vc::extern_spec! {
            impl std::vec::Vec::<T> {
                fn pop(&mut self) -> Option<T>;
            }
        }
    "#;

    let entry = lookup_extern_spec_source("lexical.rs", source, "Vec::<i32>::pop")
        .expect("lookup should succeed");

    assert!(entry.is_none(), "lookup must stay lexical for #1802");
}

#[test]
fn test_normalize_full_preserves_concrete_generics() {
    let u8_path =
        normalize_extern_spec_path_full("Vec::<u8>::pop").expect("normalization should succeed");
    let u16_path =
        normalize_extern_spec_path_full("Vec::<u16>::pop").expect("normalization should succeed");

    assert_ne!(
        u8_path, u16_path,
        "distinct concrete specializations must differ"
    );
    assert_eq!(u8_path, "Vec::<u8>::pop");
    assert_eq!(u16_path, "Vec::<u16>::pop");
}

#[test]
fn test_normalize_full_preserves_type_params() {
    let generic = normalize_extern_spec_path_full("Option::<T>::unwrap")
        .expect("normalization should succeed");
    let concrete = normalize_extern_spec_path_full("Option::<i32>::unwrap")
        .expect("normalization should succeed");

    assert_ne!(
        generic, concrete,
        "T and i32 must produce distinct full paths"
    );
}

#[test]
fn test_lookup_disambiguates_concrete_specializations() {
    let source = r#"
        trust_vc::extern_spec! {
            impl Vec::<u8> {
                #[requires(false)]
                fn pop(&mut self) -> Option<u8>;
            }
        }

        trust_vc::extern_spec! {
            impl Vec::<u16> {
                #[requires(true)]
                fn pop(&mut self) -> Option<u16>;
            }
        }
    "#;

    let u16_entry = lookup_extern_spec_source("specialize.rs", source, "Vec::<u16>::pop")
        .expect("lookup should succeed")
        .expect("entry should exist");
    assert_eq!(
        u16_entry.requires,
        vec!["true"],
        "should return u16 contract"
    );

    let u8_entry = lookup_extern_spec_source("specialize.rs", source, "Vec::<u8>::pop")
        .expect("lookup should succeed")
        .expect("entry should exist");
    assert_eq!(
        u8_entry.requires,
        vec!["false"],
        "should return u8 contract"
    );
}

#[test]
fn test_lookup_ambiguous_erased_fails_closed() {
    let source = r#"
        trust_vc::extern_spec! {
            impl Vec::<u8> {
                #[requires(false)]
                fn pop(&mut self) -> Option<u8>;
            }
        }

        trust_vc::extern_spec! {
            impl Vec::<u16> {
                #[requires(true)]
                fn pop(&mut self) -> Option<u16>;
            }
        }
    "#;

    let result = lookup_extern_spec_source("ambiguous.rs", source, "Vec::pop");
    assert!(
        result.is_err(),
        "bare lookup with multiple specializations must fail"
    );
    let err = result.unwrap_err().to_string();
    assert!(
        err.contains("ambiguous"),
        "error must mention ambiguity: {err}"
    );
}

#[test]
fn test_lookup_generic_spec_matches_concrete_target() {
    let source = r#"
        trust_vc::extern_spec! {
            impl Vec::<T> {
                #[requires(true)]
                fn pop(&mut self) -> Option<T>;
            }
        }
    "#;

    let entry = lookup_extern_spec_source("generic_match.rs", source, "Vec::<i32>::pop")
        .expect("lookup should succeed")
        .expect("generic spec should match concrete target via erased fallback");
    assert_eq!(entry.requires, vec!["true"]);
}

// --- Resolution scope tests (#2392) ---

#[test]
fn test_entry_carries_file_local_resolution_scope() {
    let source = r#"
        trust_vc::extern_spec! {
            impl i32 {
                #[requires(false)]
                fn abs(self) -> i32;
            }
        }
    "#;

    let entry = lookup_extern_spec_source("scope_local.rs", source, "i32::abs")
        .expect("lookup should succeed")
        .expect("entry should exist");
    assert_eq!(
        entry.resolution_scope,
        ResolutionScope::FileLocal,
        "file-local discovery must tag entries as FileLocal"
    );
}

#[test]
fn test_classify_target_scope_detects_external_crates() {
    assert_eq!(classify_target_scope("std::vec::Vec::pop"), Some("std::"));
    assert_eq!(
        classify_target_scope("core::option::Option::unwrap"),
        Some("core::")
    );
    assert_eq!(
        classify_target_scope("alloc::string::String::new"),
        Some("alloc::")
    );
}

#[test]
fn test_classify_target_scope_returns_none_for_local_paths() {
    assert_eq!(classify_target_scope("i32::abs"), None);
    assert_eq!(classify_target_scope("Vec::<u8>::pop"), None);
    assert_eq!(classify_target_scope("MyType::method"), None);
}
