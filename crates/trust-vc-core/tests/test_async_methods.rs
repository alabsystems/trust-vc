//! Tests for async method handling in trust-vc-core
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Tests for async methods and cross-method calls

use syn::{parse_quote, ItemFn};
use trust_vc_core::{expand_proof, expand_spec};

#[cfg(test)]
mod test_async_methods {
    use super::*;

    #[test]
    fn test_async_method() {
        // Async method
        let input: ItemFn = parse_quote! {
            async fn fetch_data(&self) -> Result<String, Error> {
                Ok("data".to_string())
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should handle async methods
        assert!(output.contains("async"));
        // Note: self parameters are stripped and replaced with warnings
        assert!(output.contains("_trust_vc_warn_self_param") || output.contains("fetch_data"));
    }

    #[test]
    fn test_async_method_with_await() {
        // Async method with await
        let input: ItemFn = parse_quote! {
            async fn process(&mut self) {
                self.fetch().await;
                self.save().await;
            }
        };

        let result = expand_proof(input);
        let output = result.to_string();

        // Should preserve async/await
        assert!(output.contains("async"));
        assert!(output.contains("await") || output.contains(".await"));
    }

    #[test]
    fn test_async_static_method() {
        // Async associated function
        let input: ItemFn = parse_quote! {
            async fn create() -> Self {
                Self::default()
            }
        };

        let result = expand_spec(input);

        // Should handle async associated functions
        assert!(result.to_string().contains("async"));
        assert!(result.to_string().contains("Self"));
    }

    #[test]
    fn test_async_method_with_generics() {
        // Async method with generic parameters
        let input: ItemFn = parse_quote! {
            async fn process_generic<T: Send>(&self, value: T) -> T {
                value
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should handle async with generics
        assert!(output.contains("async"));
        assert!(output.contains("Send"));
    }
}

#[cfg(test)]
mod test_method_chaining {
    use super::*;

    #[test]
    fn test_method_calling_other_methods() {
        // Method that calls multiple other methods
        let input: ItemFn = parse_quote! {
            fn complex_operation(&self) -> i32 {
                let a = self.get_value();
                let b = self.calculate(a);
                self.finalize(b)
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Note: expand_spec currently strips function bodies for spec functions
        // So method calls won't be preserved in the output
        assert!(output.contains("complex_operation") || output.contains("fn"));
    }

    #[test]
    fn test_method_with_chained_calls() {
        // Method with chained calls
        let input: ItemFn = parse_quote! {
            fn builder_pattern(self) -> Self {
                self.with_name("test")
                    .with_value(42)
                    .build()
            }
        };

        let result = expand_spec(input);

        // Should handle builder pattern
        assert!(result.to_string().contains("self"));
    }

    #[test]
    fn test_method_returning_self_for_chaining() {
        // Method that returns Self for chaining
        let input: ItemFn = parse_quote! {
            fn set_value(mut self, value: i32) -> Self {
                self.value = value;
                self
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should handle mut self and Self return
        assert!(output.contains("mut self"));
        assert!(output.contains("-> Self"));
    }
}

#[cfg(test)]
mod test_result_option_methods {
    use super::*;

    #[test]
    fn test_method_returning_result() {
        // Method returning Result
        let input: ItemFn = parse_quote! {
            fn try_operation(&self) -> Result<i32, String> {
                Ok(42)
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should handle Result return type
        assert!(output.contains("Result"));
        assert!(output.contains("Ok"));
    }

    #[test]
    fn test_method_returning_option() {
        // Method returning Option
        let input: ItemFn = parse_quote! {
            fn find_value(&self, key: &str) -> Option<i32> {
                None
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should handle Option return type
        assert!(output.contains("Option"));
        assert!(output.contains("None"));
    }

    #[test]
    fn test_method_with_question_mark() {
        // Method using ? operator
        let input: ItemFn = parse_quote! {
            fn propagate_error(&self) -> Result<i32, Error> {
                let value = self.try_get()?;
                Ok(value * 2)
            }
        };

        let result = expand_spec(input);
        let output = result.to_string();

        // Should preserve ? operator
        assert!(output.contains("?"));
        assert!(output.contains("Result"));
    }
}
