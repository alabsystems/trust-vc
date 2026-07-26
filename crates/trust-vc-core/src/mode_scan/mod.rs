//! Same-module mode scanning — order-independent function mode resolution.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Scans the source file containing the current proc-macro invocation to build
//! a complete mode table for all sibling functions. This makes mode legality
//! independent of declaration order within a module.
//!
//! The compile-time mode registry (`mode::COMPILE_TIME_MODE_REGISTRY`) only
//! knows about functions whose `#[trust_vc::*]` macros have already expanded.
//! This module supplements it by reading the full source file, finding the
//! module containing the current function, and classifying all siblings by
//! their attributes.
//!
//! Part of #2300.

use std::path::PathBuf;
use std::sync::Arc;

use crate::mode::FunctionMode;
use crate::mode_index::{self, CrateModeIndex};
use proc_macro2::TokenStream;
use syn::ItemFn;

mod exec_callers;
mod module_path;
mod scan;

pub(crate) use scan::{ModeScan, ScanOutcome};

/// Combined outbound + inbound mode validation for a function being expanded.
///
/// Builds a same-module scan and crate index, validates outbound calls from
/// `caller_mode`, and runs the inbound exec-caller audit.
pub(crate) fn validate_mode(
    input: &ItemFn,
    caller_mode: FunctionMode,
    block: &syn::Block,
) -> (Option<ModeScan>, Vec<TokenStream>) {
    let span = input.sig.ident.span();
    let fn_name = input.sig.ident.to_string();
    let fn_tokens = scan::normalize_fn_tokens(input);

    // Build crate index from source for qualified path resolution (#2066).
    let source_file: Option<PathBuf> = span.local_file();
    let crate_root = source_file
        .as_deref()
        .and_then(mode_index::discover_crate_root);
    let crate_index: Option<Arc<CrateModeIndex>> = crate_root
        .as_deref()
        .and_then(mode_index::get_or_build_index);

    let caller_module = match (source_file.as_deref(), crate_root.as_deref()) {
        (Some(src), Some(root)) => {
            module_path::determine_caller_module(src, root, &fn_name, &fn_tokens)
        }
        _ => Vec::new(),
    };

    let (scan, mut errors) = match scan::scan_module(input, span) {
        ScanOutcome::Found(scan) => {
            let errors = crate::validate_function_calls_for_mode(
                caller_mode,
                block,
                Some(&scan),
                crate_index.as_deref(),
                &caller_module,
            );
            (Some(scan), errors)
        }
        ScanOutcome::AmbiguousMatch => (
            None,
            vec![syn::Error::new(
                span,
                format!(
                    "trust_vc mode checker cannot uniquely locate `{}` in its source module; ambiguous same-name functions across inline modules prevent order-independent mode validation",
                    input.sig.ident
                ),
            )
            .to_compile_error()],
        ),
        ScanOutcome::Unavailable => (
            None,
            crate::validate_function_calls_for_mode(
                caller_mode,
                block,
                None,
                crate_index.as_deref(),
                &caller_module,
            ),
        ),
    };

    // Inbound exec-caller audit: same-file scan (existing + qualified #2066).
    if let Some(ref scan) = scan {
        errors.extend(exec_callers::find_exec_callers_from_source(
            scan,
            &fn_name,
            &fn_tokens,
            caller_mode,
            span,
            crate_index.as_deref(),
            &caller_module,
        ));
    }

    (scan, errors)
}

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_exec_callers;
#[cfg(test)]
mod tests_module_path;
#[cfg(test)]
mod tests_scan;
