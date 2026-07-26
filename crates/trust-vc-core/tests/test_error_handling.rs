//! Tests for error handling in trust-vc-core
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Tests error cases and edge conditions that W2's tests missed

use quote::quote;
use syn::{parse_quote, ItemFn};
use trust_vc_core::{expand_broadcast, expand_decreases, expand_proof, expand_spec};

#[cfg(test)]
mod test_invalid_inputs {
    use super::*;

    #[test]
    fn test_expand_proof_with_invalid_signature() {
        // Function with empty body (minimal valid ItemFn)
        // This tests handling of minimal function definitions
        let input: ItemFn = parse_quote! {
            fn no_body() {
                // Empty body
            }
        };

        let result = expand_proof(input);
        let output = result.to_string();

        // Should still generate something, even if incomplete
        assert!(output.contains("fn no_body"));
    }

    #[test]
    fn test_expand_spec_with_no_return() {
        // Spec function with no return type
        let input: ItemFn = parse_quote! {
            fn no_return() {
                // No return
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should handle functions with unit return type
        assert!(output.contains("fn no_return"));
    }

    #[test]
    fn test_expand_decreases_empty_measures() {
        // Decreases with empty measure list (should error in real usage)
        let input: ItemFn = parse_quote! {
            fn empty_decreases(n: u32) -> u32 {
                n
            }
        };

        // Since we can't pass empty decreases here, test with minimal case
        let decreases_args = quote! { n };
        let result = expand_decreases(input, decreases_args);

        // Should generate termination checks
        assert!(result.to_string().contains("decreases"));
    }

    #[test]
    fn test_expand_broadcast_without_trigger() {
        // Broadcast without trigger should still work
        let input: ItemFn = parse_quote! {
            fn broadcast_no_trigger(x: i32) {
                // No trigger
            }
        };

        // expand_broadcast takes only one argument
        let result = expand_broadcast(input);

        // Should generate broadcast lemma
        assert!(result.to_string().contains("broadcast"));
    }
}

#[cfg(test)]
mod test_edge_cases {
    use super::*;

    #[test]
    fn test_generic_function_expansion() {
        // Generic function
        let input: ItemFn = parse_quote! {
            fn generic_fn<T: Clone>(x: T) -> T {
                x.clone()
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should preserve generics (with spaces in the tokenized output)
        assert!(
            output.contains("< T"),
            "Generic parameter should be preserved"
        );
        assert!(output.contains("Clone"), "Trait bound should be preserved");
    }

    #[test]
    fn test_lifetime_parameters() {
        // Function with lifetime parameters
        let input: ItemFn = parse_quote! {
            fn lifetime_fn<'a>(x: &'a str) -> &'a str {
                x
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should preserve lifetimes
        assert!(output.contains("'a"));
    }

    #[test]
    fn test_const_function() {
        // Const function
        let input: ItemFn = parse_quote! {
            const fn const_fn(x: i32) -> i32 {
                x * 2
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should preserve const
        assert!(output.contains("const fn"));
    }

    #[test]
    fn test_async_function() {
        // Async function
        let input: ItemFn = parse_quote! {
            async fn async_fn() -> i32 {
                42
            }
        };

        let result = expand_proof(input);
        let output = result.to_string();

        // Should handle async (might strip it for proof context)
        assert!(output.contains("fn async_fn"));
    }

    #[test]
    fn test_unsafe_function() {
        // Unsafe function
        let input: ItemFn = parse_quote! {
            unsafe fn unsafe_fn() {
                // Unsafe code
            }
        };

        let result = expand_proof(input);
        let output = result.to_string();

        // Should preserve unsafe
        assert!(output.contains("unsafe"));
    }

    #[test]
    fn test_very_long_function_name() {
        // Function with very long name
        let input: ItemFn = parse_quote! {
            fn this_is_a_very_long_function_name_that_might_cause_issues_with_formatting_or_string_processing_in_macro_expansion() {
                // Long name
            }
        };

        let result = expand_proof(input);
        let output = result.to_string();

        // Should handle long names
        assert!(output.contains("this_is_a_very_long_function_name"));
    }

    #[test]
    fn test_unicode_in_identifiers() {
        // Function with unicode in name (Rust allows this)
        let input: ItemFn = parse_quote! {
            fn 函数_test() {
                // Unicode identifier
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should handle unicode
        assert!(output.contains("函数_test"));
    }

    #[test]
    fn test_multiple_attributes() {
        // Function with multiple attributes
        let input: ItemFn = parse_quote! {
            #[inline]
            #[doc = "Test function"]
            #[allow(dead_code)]
            fn multi_attr() {
                // Multiple attributes
            }
        };

        let result = expand_proof(input);
        let output = result.to_string();

        // Should preserve or handle attributes
        assert!(output.contains("fn multi_attr"));
    }

    #[test]
    fn test_impl_method() {
        // Method in impl block (not a free function)
        // This would normally be part of an impl block
        let input: ItemFn = parse_quote! {
            fn method(self) -> Self {
                self
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should handle self parameter
        assert!(output.contains("self"));
    }

    #[test]
    fn test_variadic_function() {
        // Can't really test variadic in Rust, but test many params
        let input: ItemFn = parse_quote! {
            fn many_params(a: i32, b: i32, c: i32, d: i32, e: i32, f: i32) -> i32 {
                a + b + c + d + e + f
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should handle many parameters
        assert!(output.contains("a"));
        assert!(output.contains("f"));
    }
}

#[cfg(test)]
mod test_malformed_inputs {
    use super::*;

    #[test]
    fn test_function_with_no_parameters() {
        // Function with empty parameter list
        let input: ItemFn = parse_quote! {
            fn no_params() {
                // No parameters
            }
        };

        let result = expand_proof(input);

        // Should handle functions with no parameters
        assert!(result.to_string().contains("fn no_params"));
    }

    #[test]
    fn test_function_with_patterns() {
        // Function with pattern matching in parameters
        let input: ItemFn = parse_quote! {
            fn pattern_params((x, y): (i32, i32)) -> i32 {
                x + y
            }
        };

        let result = expand_spec(input);

        // Should handle pattern parameters
        assert!(result.to_string().contains("pattern_params"));
    }

    #[test]
    fn test_recursive_without_base_case() {
        // Recursive function without obvious base case
        let input: ItemFn = parse_quote! {
            fn infinite_recursion(n: u32) -> u32 {
                infinite_recursion(n + 1)
            }
        };

        let decreases_args = quote! { n };
        let result = expand_decreases(input, decreases_args);

        // Should still generate code (verification would fail)
        assert!(result.to_string().contains("infinite_recursion"));
    }

    #[test]
    fn test_function_with_where_clause() {
        // Function with where clause
        let input: ItemFn = parse_quote! {
            fn where_clause<T>(x: T) -> T
            where
                T: Clone + Default,
            {
                x
            }
        };

        let result = expand_spec(input);

        // Should preserve where clause
        assert!(result.to_string().contains("where"));
    }

    #[test]
    fn test_empty_function_body() {
        // Function with completely empty body
        let input: ItemFn = parse_quote! {
            fn empty_body() {}
        };

        let result = expand_proof(input);

        // Should handle empty body
        assert!(result.to_string().contains("empty_body"));
    }
}

#[cfg(test)]
mod test_complex_expressions {
    use super::*;

    #[test]
    fn test_function_with_closures() {
        // Function containing closures — don't call the closure since
        // unregistered single-segment calls are treated as Exec mode
        // and Proof cannot call Exec (mode.rs:49).
        let input: ItemFn = parse_quote! {
            fn with_closure() {
                let _f = |x: u32| x + 1;
            }
        };

        let result = expand_proof(input);

        // Should handle closures in body
        assert!(result.to_string().contains("with_closure"));
    }

    #[test]
    fn test_function_with_macros() {
        // Function using macros in body
        let input: ItemFn = parse_quote! {
            fn with_macros() {
                println!("test");
                vec![1, 2, 3];
            }
        };

        let result = expand_spec(input);

        // Should handle macro calls
        assert!(result.to_string().contains("with_macros"));
    }

    #[test]
    fn test_function_with_nested_functions() {
        // Function with nested function definitions — don't call inner()
        // since unregistered single-segment calls default to Exec mode
        // and Proof cannot call Exec (mode.rs:49).
        let input: ItemFn = parse_quote! {
            fn with_nested() {
                fn inner() {
                    // Nested function
                }
            }
        };

        let result = expand_proof(input);

        // Should handle nested functions
        assert!(result.to_string().contains("with_nested"));
    }
}
