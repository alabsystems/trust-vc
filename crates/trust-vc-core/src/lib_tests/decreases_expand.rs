// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_has_decreases_metadata_accepts_raw_attr_and_doc_marker_2574() {
    let raw_attr_fn: syn::ItemFn = syn::parse2(quote! {
        #[trust_vc::decreases(n)]
        fn countdown(n: u64) {}
    })
    .expect("raw decreases attr should parse");
    assert!(has_decreases_metadata(&raw_attr_fn.attrs));

    let doc_attr_fn: syn::ItemFn = syn::parse2(quote! {
        #[doc = "trust_vc:decreases:entry=n"]
        fn countdown_doc(n: u64) {}
    })
    .expect("decreases doc metadata should parse");
    assert!(has_decreases_metadata(&doc_attr_fn.attrs));
}

#[test]
fn test_expand_decreases_with_clauses_emits_doc_attrs_2569() {
    let input = quote! {
        fn countdown(n: u64) -> u64 {
            if n == 0 { 0 } else { countdown(n - 1) }
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).expect("parse decreases fn");
    let result = expand_decreases_with_clauses(ast, quote!(n, when = n > 0, via = prove_countdown));
    let generated: syn::ItemFn =
        syn::parse2(result).expect("decreases expansion should produce a valid function");

    let metadata = crate::attr_doc_metadata::extract_decreases_doc_metadata(&generated.attrs)
        .expect("decreases metadata extraction should succeed")
        .expect("decreases metadata should be present");

    assert_eq!(metadata.entry, "n");
    assert_eq!(metadata.when.as_deref(), Some("n > 0"));
    assert_eq!(metadata.via.as_deref(), Some("prove_countdown"));
}

#[test]
fn test_expand_decreases() {
    let measures: proc_macro2::TokenStream = quote! { n };
    let item = quote! {
        fn recursive_fn(n: u64) -> u64 {
            if n == 0 { 0 } else { recursive_fn(n - 1) }
        }
    };

    let item_fn: syn::ItemFn = syn::parse2(item).unwrap();
    let result = expand_decreases(item_fn, measures);

    // Parse the result to verify structure
    let generated: syn::ItemFn = syn::parse2(result).expect("Should generate valid Rust function");

    // Verify function name is preserved
    assert_eq!(generated.sig.ident, "recursive_fn");

    // Verify the function has the correct return type
    match &generated.sig.output {
        syn::ReturnType::Type(_, ty) => {
            let ty_str = quote!(#ty).to_string();
            assert_eq!(ty_str, "u64");
        }
        _ => panic!("Expected a return type"),
    }
}

#[test]
fn test_expand_decreases_with_clauses_parse_error() {
    let attr_tokens = quote! { n when n > 0 };
    let input = quote! {
        fn conditional_decrease(n: u64) -> u64 {
            if n > 0 { conditional_decrease(n - 1) } else { 0 }
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_decreases_with_clauses(ast, attr_tokens);

    let result_str = result.to_string();
    // The input "n when n > 0" is not valid comma-separated syntax
    // so we expect a parse error
    assert!(
        result_str.contains("compile_error"),
        "Expected compile_error for malformed decreases clause, got: {}",
        result_str
    );
    // Verify it's the expected parse error
    assert!(
        result_str.contains("expected `,`"),
        "Expected 'expected ,' parse error, got: {}",
        result_str
    );
}

#[test]
fn test_expand_decreases_with_clauses_valid() {
    // Test with valid decreases syntax
    let attr_tokens = quote! { n };
    let input = quote! {
        fn recursive_fn(n: u64) -> u64 {
            if n > 0 { recursive_fn(n - 1) } else { 0 }
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_decreases_with_clauses(ast, attr_tokens);

    let result_str = result.to_string();
    // Should include termination measure markers for valid input
    assert!(
        result_str.contains("__trust_vc_measures_entry"),
        "Expected __trust_vc_measures_entry marker for valid decreases, got: {}",
        result_str
    );
    assert!(
        result_str.contains("recursive_fn"),
        "Function name should be preserved"
    );
    assert!(
        result_str.contains("MeasureNonNegative"),
        "Expected MeasureNonNegative obligation in test-mode expansion, got: {}",
        result_str
    );
    assert!(
        result_str.contains("n >= 0"),
        "Expected non-negativity condition in expansion, got: {}",
        result_str
    );
}

#[test]
fn test_expand_decreases_tuple_measure_generates_nonneg_per_component() {
    let attr_tokens = quote! { m, n };
    let input = quote! {
        fn lex_recursive(m: u64, n: u64) -> u64 {
            if m == 0 {
                n
            } else if n == 0 {
                lex_recursive(m - 1, 1)
            } else {
                lex_recursive(m - 1, n - 1)
            }
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_decreases_with_clauses(ast, attr_tokens);
    let result_str = result.to_string();

    assert!(
        result_str.contains("m >= 0"),
        "Expected first tuple component non-negativity, got: {}",
        result_str
    );
    assert!(
        result_str.contains("n >= 0"),
        "Expected second tuple component non-negativity, got: {}",
        result_str
    );
}

#[test]
fn test_expand_decreases_with_when_clause() {
    let attr_tokens = quote! { n, when = n > 0 };
    let input = quote! {
        fn conditional_decrease(n: u64) -> u64 {
            if n > 0 { conditional_decrease(n - 1) } else { 0 }
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_decreases_with_clauses(ast, attr_tokens);

    let result_str = result.to_string();
    assert!(
        result_str.contains("__trust_vc_measures_entry"),
        "Expected measures entry marker, got: {}",
        result_str
    );
    assert!(
        result_str.contains("__trust_vc_decreases_when"),
        "Expected when condition marker, got: {}",
        result_str
    );
    assert!(
        !result_str.contains("__trust_vc_decreases_via"),
        "Should NOT contain via marker when only when is specified"
    );
    // Content assertion: when condition body must contain the actual expression
    assert!(
        result_str.contains("n > 0"),
        "When clause content 'n > 0' must appear in output, got: {}",
        result_str
    );
}

#[test]
fn test_expand_decreases_with_via_clause() {
    let attr_tokens = quote! { n, via = proof_decrease };
    let input = quote! {
        fn delegated_decrease(n: u64) -> u64 {
            if n > 0 { delegated_decrease(n - 1) } else { 0 }
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_decreases_with_clauses(ast, attr_tokens);

    let result_str = result.to_string();
    assert!(
        result_str.contains("__trust_vc_measures_entry"),
        "Expected measures entry marker, got: {}",
        result_str
    );
    assert!(
        result_str.contains("__trust_vc_decreases_via"),
        "Expected via function marker, got: {}",
        result_str
    );
    assert!(
        result_str.contains("proof_decrease"),
        "Expected via function name in output, got: {}",
        result_str
    );
    assert!(
        !result_str.contains("__trust_vc_decreases_when"),
        "Should NOT contain when marker when only via is specified"
    );
}

#[test]
fn test_expand_decreases_with_when_and_via_clauses() {
    let attr_tokens = quote! { n, when = n > 0, via = proof_decrease };
    let input = quote! {
        fn full_clause_decrease(n: u64) -> u64 {
            if n > 0 { full_clause_decrease(n - 1) } else { 0 }
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_decreases_with_clauses(ast, attr_tokens);

    let result_str = result.to_string();
    assert!(
        result_str.contains("__trust_vc_measures_entry"),
        "Expected measures entry marker, got: {}",
        result_str
    );
    assert!(
        result_str.contains("__trust_vc_decreases_when"),
        "Expected when condition marker, got: {}",
        result_str
    );
    assert!(
        result_str.contains("__trust_vc_decreases_via"),
        "Expected via function marker, got: {}",
        result_str
    );
    // Content assertions: when condition and via function name
    assert!(
        result_str.contains("n > 0"),
        "When clause content 'n > 0' must appear in output, got: {}",
        result_str
    );
    assert!(
        result_str.contains("proof_decrease"),
        "Via function name 'proof_decrease' must appear in output, got: {}",
        result_str
    );
}

#[test]
fn test_expand_decreases_with_when_via_no_comma() {
    // Test the #1739 fix: when = cond via = fn (no comma separator)
    let attr_tokens = quote! { n, when = n > 0 via = proof_fn };
    let input = quote! {
        fn commaless_clause(n: u64) -> u64 {
            if n > 0 { commaless_clause(n - 1) } else { 0 }
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_decreases_with_clauses(ast, attr_tokens);

    let result_str = result.to_string();
    assert!(
        result_str.contains("__trust_vc_decreases_when"),
        "Expected when marker even without comma separator (#1739), got: {}",
        result_str
    );
    assert!(
        result_str.contains("__trust_vc_decreases_via"),
        "Expected via marker even without comma separator (#1739), got: {}",
        result_str
    );
    // Content assertions: verify correct boundary split between when and via
    assert!(
        result_str.contains("n > 0"),
        "When clause content 'n > 0' must survive no-comma parsing (#1739), got: {}",
        result_str
    );
    assert!(
        result_str.contains("proof_fn"),
        "Via function name 'proof_fn' must survive no-comma parsing (#1739), got: {}",
        result_str
    );
}

#[test]
fn test_expand_decreases_lexicographic_with_when() {
    // Test lexicographic tuple measure with when clause
    let attr_tokens = quote! { (x, y), when = x > 0 || y > 0 };
    let input = quote! {
        fn lex_decrease(x: u64, y: u64) -> u64 {
            if x > 0 { lex_decrease(x - 1, y) }
            else if y > 0 { lex_decrease(x, y - 1) }
            else { 0 }
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_decreases_with_clauses(ast, attr_tokens);

    let result_str = result.to_string();
    assert!(
        result_str.contains("__trust_vc_measures_entry"),
        "Expected measures entry for lexicographic measure, got: {}",
        result_str
    );
    assert!(
        result_str.contains("__trust_vc_decreases_when"),
        "Expected when marker for lex+when combo, got: {}",
        result_str
    );
    // Content assertion: when condition expression in lexicographic context
    assert!(
        result_str.contains("x > 0"),
        "When clause content 'x > 0' must appear in lex+when output, got: {}",
        result_str
    );
}

// ---------- New tests for expand.rs coverage ----------

#[test]
fn test_expand_decreases_empty_measures_emits_compile_error() {
    // #[decreases()] with no measure expressions must produce a compile error.
    let measures: proc_macro2::TokenStream = quote! {};
    let item = quote! {
        fn empty_measure() -> u64 { 0 }
    };

    let item_fn: syn::ItemFn = syn::parse2(item).unwrap();
    let result = expand_decreases(item_fn, measures);
    let result_str = result.to_string();

    assert!(
        result_str.contains("compile_error"),
        "Empty measures must produce compile_error, got: {}",
        result_str
    );
    assert!(
        result_str.contains("requires at least one measure expression"),
        "Error message must mention 'requires at least one measure expression', got: {}",
        result_str
    );
}

#[test]
fn test_expand_decreases_with_clauses_empty_measures_emits_compile_error() {
    // expand_decreases_with_clauses also rejects empty measures.
    let attr_tokens: proc_macro2::TokenStream = quote! {};
    let input = quote! {
        fn empty_clause() -> u64 { 0 }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_decreases_with_clauses(ast, attr_tokens);
    let result_str = result.to_string();

    assert!(
        result_str.contains("compile_error"),
        "Empty measures in clause form must produce compile_error, got: {}",
        result_str
    );
    assert!(
        result_str.contains("requires at least one measure expression"),
        "Error message must mention 'requires at least one measure expression', got: {}",
        result_str
    );
}

#[test]
fn test_expand_decreases_tuple_measure_produces_valid_entry_expr() {
    // Lexicographic (multi-measure) via the simpler expand_decreases path.
    let measures = quote! { m, n };
    let item = quote! {
        fn lex_fn(m: u64, n: u64) -> u64 {
            if m == 0 && n == 0 { 0 } else { lex_fn(m, n - 1) }
        }
    };

    let item_fn: syn::ItemFn = syn::parse2(item).unwrap();
    let result = expand_decreases(item_fn, measures);
    let generated: syn::ItemFn = syn::parse2(result)
        .expect("lexicographic expand_decreases should produce a valid function");

    assert_eq!(generated.sig.ident, "lex_fn");
    // The doc attr encodes the measure tuple representation.
    let metadata = crate::attr_doc_metadata::extract_decreases_doc_metadata(&generated.attrs)
        .expect("metadata extraction should succeed")
        .expect("decreases metadata should be present");
    assert_eq!(metadata.entry, "(m , n)");
}

#[test]
fn test_expand_via_fn_produces_valid_function() {
    // expand_via_fn wraps a proof function with the via-fn marker.
    let input = quote! {
        fn prove_termination(n: u64) {
            // proof body
        }
    };

    let item_fn: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_via_fn(item_fn);
    let generated: syn::ItemFn =
        syn::parse2(result).expect("expand_via_fn should produce a valid function");

    assert_eq!(generated.sig.ident, "prove_termination");
    // Check the function retains dead_code/unused_variables allow attrs
    let allow_attrs: Vec<_> = generated
        .attrs
        .iter()
        .filter(|attr| attr.path().is_ident("allow"))
        .collect();
    assert!(
        !allow_attrs.is_empty(),
        "Via function should have #[allow(...)] attributes"
    );
}

#[test]
fn test_expand_via_fn_contains_runtime_unreachable_guard() {
    // In production mode (#[cfg(not(any(trust_mc, test)))]), a via function must
    // be unreachable at runtime since it is ghost code.
    let input = quote! {
        fn ghost_proof(x: i32) {
            // proof body
        }
    };

    let item_fn: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_via_fn(item_fn);
    let result_str = result.to_string();

    assert!(
        result_str.contains("unreachable"),
        "Via function production mode must contain unreachable guard, got: {}",
        result_str
    );
    assert!(
        result_str.contains("__trust_vc_via_fn"),
        "Via function must contain __trust_vc_via_fn marker, got: {}",
        result_str
    );
    assert!(
        result_str.contains("ghost code"),
        "Unreachable message must mention 'ghost code', got: {}",
        result_str
    );
}

#[test]
fn test_expand_via_fn_emits_param_declarations_in_test_mode() {
    // In test mode, via functions emit collect_variable calls for each parameter.
    let input = quote! {
        fn proof_with_params(x: u64, y: i32) {
            // proof body
        }
    };

    let item_fn: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_via_fn(item_fn);
    let result_str = result.to_string();

    // The test-mode block should contain collect_variable for each param.
    assert!(
        result_str.contains("collect_variable"),
        "Via function test mode must emit collect_variable calls, got: {}",
        result_str
    );
}

#[test]
fn test_expand_decreases_with_clauses_when_guards_nonneg_obligations() {
    // When a `when` condition is present, non-negativity obligations should be
    // guarded by `(!(when_cond)) || (measure >= 0)`, meaning if the condition
    // doesn't hold, non-negativity isn't required (#1188).
    let attr_tokens = quote! { n, when = is_valid(n) };
    let input = quote! {
        fn guarded_decrease(n: u64) -> u64 {
            if is_valid(n) { guarded_decrease(n - 1) } else { 0 }
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_decreases_with_clauses(ast, attr_tokens);
    let result_str = result.to_string();

    // Non-negativity should be guarded: (!(is_valid(n))) || (n >= 0)
    assert!(
        result_str.contains("is_valid"),
        "When condition 'is_valid' must appear in output for guarded nonneg, got: {}",
        result_str
    );
    assert!(
        result_str.contains("n >= 0"),
        "Non-negativity 'n >= 0' must appear in output, got: {}",
        result_str
    );
    assert!(
        result_str.contains("MeasureNonNegative"),
        "Must emit MeasureNonNegative obligation kind, got: {}",
        result_str
    );
}

#[test]
fn test_expand_decreases_with_via_uses_original_body_not_transformed() {
    // When a via_fn is present, the test-mode body should use the ORIGINAL
    // function body (not the recursive-call-transformed body), because the via
    // function provides the termination proof including branch guards.
    // This is the fix for #2658 Category G1.
    let attr_tokens = quote! { n, via = prove_it };
    let input = quote! {
        fn via_guarded(n: u64) -> u64 {
            if n > 0 { via_guarded(n - 1) } else { 0 }
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_decreases_with_clauses(ast, attr_tokens);
    let result_str = result.to_string();

    // With via_fn, the test block should NOT contain MeasureDecreases
    // (which would come from the transformed body). It should contain
    // the via call instead.
    assert!(
        result_str.contains("prove_it"),
        "Via function name 'prove_it' must appear, got: {}",
        result_str
    );
    // The original body content should appear as-is (not wrapped with obligations)
    assert!(
        !result_str.contains("MeasureDecreases"),
        "Via-guarded expansion must NOT contain MeasureDecreases \
         (via_fn provides the proof instead), got: {}",
        result_str
    );
}

#[test]
fn test_expand_decreases_with_clauses_mutual_with_peers() {
    // mutual_with(peer_a, peer_b) should not pollute measures and should
    // be reflected in the transformation (all_peers includes them).
    let attr_tokens = quote! { n, mutual_with(is_odd) };
    let input = quote! {
        fn is_even(n: u64) -> bool {
            if n == 0 { true } else { is_odd(n - 1) }
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_decreases_with_clauses(ast, attr_tokens);
    let result_str = result.to_string();

    assert!(
        result_str.contains("__trust_vc_measures_entry"),
        "Mutual recursion expansion must contain measures entry marker, got: {}",
        result_str
    );
    // The is_odd call should get a MeasureDecreases obligation injected
    // because it is listed as a mutual peer.
    assert!(
        result_str.contains("MeasureDecreases"),
        "Mutual peer call should trigger MeasureDecreases obligation, got: {}",
        result_str
    );
    assert!(
        result_str.contains("MeasureNonNegative"),
        "Must still emit MeasureNonNegative for self measure, got: {}",
        result_str
    );
}

#[test]
fn test_expand_decreases_preserves_function_visibility() {
    // pub/pub(crate)/private visibility must survive expansion.
    let measures = quote! { n };
    let pub_fn = quote! {
        pub fn public_countdown(n: u64) -> u64 {
            if n == 0 { 0 } else { public_countdown(n - 1) }
        }
    };

    let item_fn: syn::ItemFn = syn::parse2(pub_fn).unwrap();
    let result = expand_decreases(item_fn, measures);
    let generated: syn::ItemFn =
        syn::parse2(result).expect("pub function expansion should produce valid Rust");

    assert!(
        matches!(generated.vis, syn::Visibility::Public(_)),
        "Public visibility must be preserved after expansion"
    );
}

#[test]
fn test_expand_decreases_single_measure_doc_metadata() {
    // Single measure should produce entry doc attr without tuple wrapping.
    let measures = quote! { depth };
    let item = quote! {
        fn tree_walk(depth: u64) -> u64 {
            if depth == 0 { 1 } else { tree_walk(depth - 1) }
        }
    };

    let item_fn: syn::ItemFn = syn::parse2(item).unwrap();
    let result = expand_decreases(item_fn, measures);
    let generated: syn::ItemFn =
        syn::parse2(result).expect("single measure expansion should produce valid function");

    let metadata = crate::attr_doc_metadata::extract_decreases_doc_metadata(&generated.attrs)
        .expect("metadata extraction should succeed")
        .expect("decreases metadata should be present");

    // Single measure should NOT be wrapped in tuple parens.
    assert_eq!(
        metadata.entry, "depth",
        "Single measure entry should be 'depth', not a tuple"
    );
}
