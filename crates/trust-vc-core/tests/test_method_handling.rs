//! Tests for method and trait handling in trust-vc-core
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Tests for methods (self parameters) and trait implementations

use quote::quote;
use syn::{parse_quote, ItemFn};
use trust_vc_core::{expand_decreases, expand_proof, expand_spec};

#[cfg(test)]
mod test_methods {
    use super::*;

    #[test]
    fn test_method_with_self_parameter() {
        // Method with self parameter
        let input: ItemFn = parse_quote! {
            fn method(self) -> Self {
                self
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should handle self parameter
        assert!(output.contains("self"));
        assert!(output.contains("Self"));
    }

    #[test]
    fn test_method_with_ref_self() {
        // Method with &self parameter
        let input: ItemFn = parse_quote! {
            fn get_value(&self) -> i32 {
                42
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should handle &self - normalize whitespace for consistent testing
        let normalized = output.replace(" ", "");
        assert!(
            normalized.contains("&self"),
            "Expected &self in output: {}",
            output
        );
    }

    #[test]
    fn test_method_with_mut_self() {
        // Method with &mut self parameter
        let input: ItemFn = parse_quote! {
            fn set_value(&mut self, value: i32) {
                // Set value
            }
        };

        let result = expand_proof(input);
        let output = result.to_string();

        // Should handle &mut self - normalize whitespace for consistent testing
        let normalized = output.replace(" ", "");
        assert!(
            normalized.contains("&mutself"),
            "Expected &mut self in output: {}",
            output
        );
    }

    #[test]
    fn test_static_method() {
        // Associated function without self
        let input: ItemFn = parse_quote! {
            fn new() -> Self {
                Self::default()
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should handle associated functions
        assert!(output.contains("fn new"));
        assert!(output.contains("Self"));
    }

    #[test]
    fn test_method_with_lifetime_on_self() {
        // Method with lifetime on self reference
        let input: ItemFn = parse_quote! {
            fn borrow<'a>(&'a self) -> &'a str {
                "test"
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should preserve lifetimes - normalize whitespace for consistent testing
        let normalized = output.replace(" ", "");
        assert!(
            normalized.contains("'a"),
            "Expected lifetime 'a in output: {}",
            output
        );
        assert!(
            normalized.contains("&'aself"),
            "Expected &'a self in output: {}",
            output
        );
    }

    #[test]
    fn test_recursive_method_with_decreases() {
        // Recursive method with decreases
        let input: ItemFn = parse_quote! {
            fn count_down(&self, n: u32) -> u32 {
                if n == 0 {
                    0
                } else {
                    self.count_down(n - 1)
                }
            }
        };

        let decreases_args = quote! { n };
        let result = expand_decreases(input, decreases_args);

        // Should handle recursive methods
        assert!(result.to_string().contains("count_down"));
        assert!(result.to_string().contains("self"));
    }

    #[test]
    fn test_method_with_complex_receiver() {
        // Method with complex receiver type
        let input: ItemFn = parse_quote! {
            fn complex(self: Box<Self>) -> i32 {
                42
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should handle complex receivers
        assert!(output.contains("Box"));
        assert!(output.contains("Self"));
    }
}

#[cfg(test)]
mod test_error_conditions {
    use super::*;

    #[test]
    fn test_function_with_invalid_self_outside_impl() {
        // Function with self outside impl block (invalid in real Rust)
        let input: ItemFn = parse_quote! {
            fn invalid_self(self, x: i32) -> i32 {
                x
            }
        };

        let result = expand_proof(input);

        // Should still process even though it's technically invalid
        assert!(result.to_string().contains("invalid_self"));
    }

    #[test]
    fn test_method_missing_self_type() {
        // Method where Self type is unknown
        let input: ItemFn = parse_quote! {
            fn returns_self() -> Self {
                todo!()
            }
        };

        let result = expand_spec(input);

        // Should handle Self even without context
        assert!(result.to_string().contains("Self"));
    }

    #[test]
    fn test_method_with_generic_self() {
        // Method with generic parameters on self
        let input: ItemFn = parse_quote! {
            fn generic_method<T>(&self, value: T) -> T {
                value
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should preserve generics with methods - normalize whitespace for consistent testing
        let normalized = output.replace(" ", "");
        assert!(
            normalized.contains("<T"),
            "Expected generic <T in output: {}",
            output
        );
        assert!(
            normalized.contains("&self"),
            "Expected &self in output: {}",
            output
        );
    }
}

#[cfg(test)]
mod test_missing_coverage {
    use super::*;

    #[test]
    fn test_function_with_impl_trait_return() {
        // Function returning impl Trait
        let input: ItemFn = parse_quote! {
            fn returns_impl() -> impl Iterator<Item = i32> {
                vec![1, 2, 3].into_iter()
            }
        };

        let result = expand_spec(input);

        // Should handle impl Trait returns
        assert!(result.to_string().contains("impl"));
        assert!(result.to_string().contains("Iterator"));
    }

    #[test]
    fn test_function_with_dyn_trait_parameter() {
        // Function with dyn Trait parameter
        let input: ItemFn = parse_quote! {
            fn takes_dyn(x: &dyn std::fmt::Display) {
                // Use trait object
            }
        };

        let result = expand_proof(input);

        // Should handle dyn Trait
        assert!(result.to_string().contains("dyn"));
    }

    #[test]
    fn test_function_with_array_types() {
        // Function with array types
        let input: ItemFn = parse_quote! {
            fn array_fn(arr: [i32; 5]) -> [u8; 256] {
                [0; 256]
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should handle array types - normalize whitespace for consistent testing
        let normalized = output.replace(" ", "");
        assert!(
            normalized.contains("[i32;5]"),
            "Expected array type [i32; 5] in output: {}",
            output
        );
        assert!(
            output.contains("256"),
            "Expected constant 256 in output: {}",
            output
        );
    }

    #[test]
    fn test_function_with_tuple_patterns() {
        // Function with tuple destructuring
        let input: ItemFn = parse_quote! {
            fn tuple_fn((a, b): (i32, i32), (c, (d, e)): (u8, (u16, u32))) -> i32 {
                a + b
            }
        };

        let result = expand_spec(input);

        // Should handle complex patterns - verify tuple destructuring is preserved
        let output = result.to_string();
        assert!(output.contains("tuple_fn"));
        // Check that tuple pattern parameters are preserved
        assert!(output.contains("(") && output.contains(")"));
    }

    #[test]
    fn test_function_with_default_parameters() {
        // Function with default generic parameters
        let input: ItemFn = parse_quote! {
            fn default_generic<T = i32>() -> T {
                Default::default()
            }
        };

        let result = expand_spec(input);

        // Should handle default type parameters
        assert!(result.to_string().contains("T"));
    }

    #[test]
    fn test_extern_function() {
        // Extern function
        let input: ItemFn = parse_quote! {
            extern "C" fn ffi_function(x: i32) -> i32 {
                x * 2
            }
        };

        let result = expand_proof(input);

        // Should handle extern functions
        assert!(result.to_string().contains("extern"));
    }

    #[test]
    fn test_function_with_never_type() {
        // Function that never returns
        let input: ItemFn = parse_quote! {
            fn never_returns() -> ! {
                panic!("This function never returns")
            }
        };

        let result = expand_spec(input);

        // Should handle never type
        assert!(result.to_string().contains("!"));
    }
}
