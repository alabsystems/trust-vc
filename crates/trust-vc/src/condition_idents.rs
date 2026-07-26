//! Variable identifier extraction from condition expressions.
//!
//! Used by `assert_by_*` macros to generate runtime `collect_variable_runtime`
//! calls for variables referenced in the condition expression (#1596).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use quote::quote;

/// Extracts variable identifiers from a condition expression token stream.
///
/// Walks the token tree and collects simple identifiers that look like variable
/// names, filtering out Rust keywords, type names, boolean literals, and
/// function calls (identifiers immediately followed by `!` or `(`).
pub(crate) fn extract_condition_idents(tokens: &proc_macro2::TokenStream) -> Vec<String> {
    let mut idents = Vec::new();
    extract_idents_recursive(tokens, &mut idents);
    idents.sort();
    idents.dedup();
    idents
}

/// Keywords and type names that should not be treated as variables.
const NON_VARIABLE_IDENTS: &[&str] = &[
    // Boolean literals
    "true", "false", // Rust keywords
    "as", "break", "const", "continue", "crate", "else", "enum", "extern", "fn", "for", "if",
    "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub", "ref", "return", "self",
    "Self", "static", "struct", "super", "trait", "type", "unsafe", "use", "where", "while",
    "async", "await", "dyn",
    // Primitive type names (these appear as path segments, not variables)
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize", "f32",
    "f64", "bool", "char", "str",
];

#[allow(clippy::indexing_slicing)] // invariant: all indices bounded by `i < token_vec.len()` and `i + N < token_vec.len()` / `i >= N` guards
fn extract_idents_recursive(tokens: &proc_macro2::TokenStream, idents: &mut Vec<String>) {
    let token_vec: Vec<proc_macro2::TokenTree> = tokens.clone().into_iter().collect();
    let mut i = 0;

    while i < token_vec.len() {
        match &token_vec[i] {
            proc_macro2::TokenTree::Ident(ident) => {
                let name = ident.to_string();
                // Skip if followed by `!` (macro call), `(` (function call), or `::` (path start)
                let is_call = i + 1 < token_vec.len()
                    && matches!(&token_vec[i + 1],
                        proc_macro2::TokenTree::Punct(p) if p.as_char() == '!'
                    );
                let is_fn_call = i + 1 < token_vec.len()
                    && matches!(&token_vec[i + 1],
                        proc_macro2::TokenTree::Group(g) if g.delimiter() == proc_macro2::Delimiter::Parenthesis
                    );
                let is_path_start = i + 2 < token_vec.len()
                    && matches!(&token_vec[i + 1],
                        proc_macro2::TokenTree::Punct(p) if p.as_char() == ':'
                    )
                    && matches!(&token_vec[i + 2],
                        proc_macro2::TokenTree::Punct(p) if p.as_char() == ':'
                    );
                // Skip if preceded by `::` (path segment like `std::i32::MAX`)
                let is_path_segment = i >= 2
                    && matches!(&token_vec[i - 1],
                        proc_macro2::TokenTree::Punct(p) if p.as_char() == ':'
                    )
                    && matches!(&token_vec[i - 2],
                        proc_macro2::TokenTree::Punct(p) if p.as_char() == ':'
                    );
                // Skip if preceded by `.` (method/field access like `x.len()`)
                let is_method_or_field = i >= 1
                    && matches!(&token_vec[i - 1],
                        proc_macro2::TokenTree::Punct(p) if p.as_char() == '.'
                    );

                if !is_call
                    && !is_fn_call
                    && !is_path_start
                    && !is_path_segment
                    && !is_method_or_field
                    && !NON_VARIABLE_IDENTS.contains(&name.as_str())
                {
                    idents.push(name);
                }
            }
            proc_macro2::TokenTree::Group(group) => {
                extract_idents_recursive(&group.stream(), idents);
            }
            _ => {}
        }
        i += 1;
    }
}

/// Generates `collect_variable_runtime` calls for each variable identifier
/// found in a condition expression token stream.
///
/// Returns a token stream of the form:
/// ```text
/// ::trust_vc_core::verify_macro::collect_variable_runtime("x", &x);
/// ::trust_vc_core::verify_macro::collect_variable_runtime("y", &y);
/// ```
pub(crate) fn generate_variable_registrations(
    tokens: &proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let idents = extract_condition_idents(tokens);
    if idents.is_empty() {
        return proc_macro2::TokenStream::new();
    }

    let registrations: Vec<proc_macro2::TokenStream> = idents
        .iter()
        .map(|name| {
            let var_ident = proc_macro2::Ident::new(name, proc_macro2::Span::call_site());
            let name_str = name.as_str();
            quote! {
                #support_root::verify_macro::collect_variable_runtime(#name_str, &#var_ident);
            }
        })
        .collect();

    quote! { #(#registrations)* }
}
