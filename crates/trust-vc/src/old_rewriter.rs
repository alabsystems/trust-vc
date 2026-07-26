//! Token stream rewriting for `old!()` patterns in postconditions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

/// Scans a token stream for `old!(var)` or `trust_vc::old!(var)` patterns and returns:
/// 1. A rewritten token stream with `old!(var)` replaced by `__trust_vc_old_var`
/// 2. A list of variable names found inside `old!()` calls
///
/// Only handles simple identifiers inside `old!()` (e.g., `old!(x)`, not `old!(a.b)`).
pub(crate) fn rewrite_old_in_tokens(
    tokens: proc_macro2::TokenStream,
) -> Result<(proc_macro2::TokenStream, Vec<String>), syn::Error> {
    let mut old_vars = Vec::new();
    let result = rewrite_old_recursive(tokens, &mut old_vars)?;
    Ok((result, old_vars))
}

/// Recursively walks a token stream, replacing `old!(var)` patterns.
///
/// Detects two forms:
/// - `old!(expr)` (unqualified)
/// - `trust_vc::old!(expr)` (fully qualified)
#[allow(clippy::indexing_slicing)] // invariant: all indices bounded by `i + N < token_vec.len()` guards
fn rewrite_old_recursive(
    tokens: proc_macro2::TokenStream,
    old_vars: &mut Vec<String>,
) -> Result<proc_macro2::TokenStream, syn::Error> {
    let token_vec: Vec<proc_macro2::TokenTree> = tokens.into_iter().collect();
    let mut result = Vec::new();
    let mut i = 0;

    while i < token_vec.len() {
        // Pattern 1: `old!(expr)` — ident "old" followed by `!` and group `(expr)`
        if i + 2 < token_vec.len() {
            if let proc_macro2::TokenTree::Ident(ref ident) = token_vec[i] {
                if ident == "old" {
                    if let proc_macro2::TokenTree::Punct(ref punct) = token_vec[i + 1] {
                        if punct.as_char() == '!' {
                            if let proc_macro2::TokenTree::Group(ref group) = token_vec[i + 2] {
                                if let Some(var_name) = extract_simple_ident_from_group(group) {
                                    let old_ident = proc_macro2::Ident::new(
                                        &format!("__trust_vc_old_{}", var_name),
                                        ident.span(),
                                    );
                                    result.push(proc_macro2::TokenTree::Ident(old_ident));
                                    if !old_vars.contains(&var_name) {
                                        old_vars.push(var_name);
                                    }
                                    i += 3;
                                    continue;
                                }

                                return Err(unsupported_old_expression(group));
                            }
                        }
                    }
                }
            }
        }

        // Pattern 2: `trust_vc :: old ! (expr)` — ident "trust_vc", `:`, `:`, ident "old", `!`, group
        if i + 5 < token_vec.len() {
            if let proc_macro2::TokenTree::Ident(ref ident) = token_vec[i] {
                if ident == "trust_vc" && is_double_colon(&token_vec[i + 1], &token_vec[i + 2]) {
                    if let proc_macro2::TokenTree::Ident(ref old_ident) = token_vec[i + 3] {
                        if old_ident == "old" {
                            if let proc_macro2::TokenTree::Punct(ref punct) = token_vec[i + 4] {
                                if punct.as_char() == '!' {
                                    if let proc_macro2::TokenTree::Group(ref group) =
                                        token_vec[i + 5]
                                    {
                                        if let Some(var_name) =
                                            extract_simple_ident_from_group(group)
                                        {
                                            let new_ident = proc_macro2::Ident::new(
                                                &format!("__trust_vc_old_{}", var_name),
                                                ident.span(),
                                            );
                                            result.push(proc_macro2::TokenTree::Ident(new_ident));
                                            if !old_vars.contains(&var_name) {
                                                old_vars.push(var_name);
                                            }
                                            i += 6;
                                            continue;
                                        }

                                        return Err(unsupported_old_expression(group));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // For groups (parentheses, brackets, braces), recurse into them
        if let proc_macro2::TokenTree::Group(ref group) = token_vec[i] {
            let inner = rewrite_old_recursive(group.stream(), old_vars)?;
            let mut new_group = proc_macro2::Group::new(group.delimiter(), inner);
            new_group.set_span(group.span());
            result.push(proc_macro2::TokenTree::Group(new_group));
        } else {
            result.push(token_vec[i].clone());
        }
        i += 1;
    }

    Ok(result.into_iter().collect())
}

/// Checks if two tokens form `::` (two consecutive colons).
fn is_double_colon(t1: &proc_macro2::TokenTree, t2: &proc_macro2::TokenTree) -> bool {
    if let (proc_macro2::TokenTree::Punct(p1), proc_macro2::TokenTree::Punct(p2)) = (t1, t2) {
        p1.as_char() == ':' && p2.as_char() == ':'
    } else {
        false
    }
}

/// Extracts a simple identifier from a group like `(x)`.
/// Returns None for complex expressions like `(a + b)` or `(a.b)`.
#[allow(clippy::indexing_slicing)] // invariant: indices bounded by `match tokens.len()` arms (1 or 2)
fn extract_simple_ident_from_group(group: &proc_macro2::Group) -> Option<String> {
    let tokens: Vec<proc_macro2::TokenTree> = group.stream().into_iter().collect();
    // Allow a single identifier optionally preceded by `*` (dereference)
    match tokens.len() {
        1 => {
            if let proc_macro2::TokenTree::Ident(ref ident) = tokens[0] {
                Some(ident.to_string())
            } else {
                None
            }
        }
        2 => {
            // Handle *x (dereference)
            if let proc_macro2::TokenTree::Punct(ref punct) = tokens[0] {
                if punct.as_char() == '*' {
                    if let proc_macro2::TokenTree::Ident(ref ident) = tokens[1] {
                        return Some(ident.to_string());
                    }
                }
            }
            None
        }
        _ => None,
    }
}

fn unsupported_old_expression(group: &proc_macro2::Group) -> syn::Error {
    syn::Error::new_spanned(
        group.clone(),
        "old!() in ensures! currently supports only `old!(ident)` and `old!(*ident)`; complex expressions are not yet supported",
    )
}

#[cfg(test)]
mod tests {
    use super::rewrite_old_in_tokens;
    use quote::quote;

    #[test]
    fn test_rewrite_old_deref_identifier() {
        let (rewritten, old_vars) =
            rewrite_old_in_tokens(quote!(value == old!(*ptr))).expect("deref old! should rewrite");

        assert!(
            rewritten.to_string().contains("__trust_vc_old_ptr"),
            "rewritten tokens should capture ptr, got {}",
            rewritten
        );
        assert!(
            !rewritten.to_string().contains("old!"),
            "rewritten tokens should not retain raw old!, got {}",
            rewritten
        );
        assert_eq!(old_vars, vec!["ptr".to_string()]);
    }

    #[test]
    fn test_rewrite_old_complex_expression_errors() {
        let err = rewrite_old_in_tokens(quote!(value == old!(state.field)))
            .expect_err("complex old! should fail closed");

        assert!(
            err.to_string().contains("complex expressions"),
            "unexpected error message: {err}"
        );
    }
}
