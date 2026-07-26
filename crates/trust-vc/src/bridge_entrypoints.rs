//! Bridge proc-macro entrypoint helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use proc_macro::TokenStream;
use syn::{parse_macro_input, ItemFn, ItemStruct};

use crate::attr_entrypoints;

pub(crate) fn extern_spec(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as trust_vc_core::ExternSpecInput);
    match trust_vc_core::expand_extern_spec(input) {
        Ok(tokens) => TokenStream::from(tokens),
        Err(err) => TokenStream::from(err.to_compile_error()),
    }
}

pub(crate) fn protocol(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(err) = attr_entrypoints::reject_unexpected_args("protocol", &attr) {
        return err;
    }
    let input = parse_macro_input!(item as ItemStruct);
    TokenStream::from(trust_vc_core::expand_protocol(input))
}

pub(crate) fn action(attr: TokenStream, item: TokenStream) -> TokenStream {
    let protocol_name = match parse_protocol_name_attr("action", &attr) {
        Ok(name) => name,
        Err(err) => return err,
    };
    let input = parse_macro_input!(item as ItemFn);
    TokenStream::from(trust_vc_core::expand_action(input, &protocol_name))
}

pub(crate) fn safety(attr: TokenStream, item: TokenStream) -> TokenStream {
    let protocol_name = match parse_protocol_name_attr("safety", &attr) {
        Ok(name) => name,
        Err(err) => return err,
    };
    let input = parse_macro_input!(item as ItemFn);
    TokenStream::from(trust_vc_core::expand_safety(input, &protocol_name))
}

pub(crate) fn liveness(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr_tokens: proc_macro2::TokenStream = attr.into();
    let (protocol_name, fairness) = match parse_liveness_attr(&attr_tokens) {
        Ok(result) => result,
        Err(err) => return err,
    };
    let input = parse_macro_input!(item as ItemFn);
    TokenStream::from(trust_vc_core::expand_liveness(
        input,
        &protocol_name,
        &fairness,
    ))
}

/// Parse protocol name from `#[action(ProtocolName)]` or `#[safety(ProtocolName)]`.
///
/// Returns the protocol name string or a compile error if the attribute is empty.
fn parse_protocol_name_attr(macro_name: &str, attr: &TokenStream) -> Result<String, TokenStream> {
    let attr_str = attr.to_string();
    let trimmed = attr_str.trim();
    if trimmed.is_empty() {
        let msg = format!(
            "#[trust_vc::{macro_name}] requires a protocol name argument, \
             e.g. #[trust_vc::{macro_name}(MyProtocol)]"
        );
        return Err(TokenStream::from(
            syn::Error::new(proc_macro2::Span::call_site(), msg).to_compile_error(),
        ));
    }
    Ok(trimmed.to_string())
}

/// Parse `#[liveness(ProtocolName, fairness = "weak")]` into (protocol_name, fairness).
///
/// If only the protocol name is given, fairness defaults to empty string.
/// Returns a compile error if the protocol name is missing.
fn parse_liveness_attr(attr: &proc_macro2::TokenStream) -> Result<(String, String), TokenStream> {
    let attr_str = attr.to_string();
    let trimmed = attr_str.trim();

    let err_msg = "#[trust_vc::liveness] requires a protocol name argument, \
                   e.g. #[trust_vc::liveness(MyProtocol, fairness = \"weak\")]";

    if trimmed.is_empty() {
        return Err(TokenStream::from(
            syn::Error::new(proc_macro2::Span::call_site(), err_msg).to_compile_error(),
        ));
    }

    // Split on first comma: "ProtocolName, fairness = \"weak\""
    if let Some(comma_pos) = trimmed.find(',') {
        let protocol_name = trimmed[..comma_pos].trim().to_string();
        if protocol_name.is_empty() || protocol_name.contains('=') {
            return Err(TokenStream::from(
                syn::Error::new(proc_macro2::Span::call_site(), err_msg).to_compile_error(),
            ));
        }
        let rest = trimmed[comma_pos + 1..].trim().to_string();
        Ok((protocol_name, rest))
    } else if trimmed.contains('=') {
        // Fairness-only form (e.g., `fairness = "weak"`) — no protocol name
        Err(TokenStream::from(
            syn::Error::new(proc_macro2::Span::call_site(), err_msg).to_compile_error(),
        ))
    } else {
        // Just protocol name, no fairness
        Ok((trimmed.to_string(), String::new()))
    }
}
