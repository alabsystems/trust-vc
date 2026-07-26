//! Path-aware call collection and canonical resolution.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Replaces the tail-name-only call collection with full path capture and
//! lexical resolution against the crate mode index.
//!
//! Resolution rules (lexical, not semantic):
//! - `foo`           → `current_module::foo`
//! - `self::foo`     → `current_module::foo`
//! - `super::foo`    → strip one module segment per `super`
//! - `crate::a::foo` → `a::foo` (crate-relative)
//! - `a::b::foo`     → try `current_module::a::b::foo`, then `crate::a::b::foo`
//!
//! Unresolved or ambiguous paths are deferred to the existing fallback.
//!
//! Part of #2066.

use crate::mode::FunctionMode;
use crate::mode_index::{CanonicalFnPath, CrateModeIndex};
use proc_macro2::Span;
use syn::visit::Visit;

/// A captured function call path from source.
#[derive(Debug, Clone)]
pub(crate) struct CallPath {
    /// Path segments (e.g., `["self", "helper"]` or `["crate", "specs", "foo"]`).
    pub segments: Vec<String>,
    /// Span for error reporting.
    pub span: Span,
    /// Whether the path had a leading `::`.
    pub leading_colon: bool,
}

impl CallPath {
    /// Returns `true` if this is a single-segment unqualified call.
    pub(crate) fn is_simple(&self) -> bool {
        self.segments.len() == 1 && !self.leading_colon
    }

    /// Returns the tail function name.
    pub(crate) fn fn_name(&self) -> &str {
        self.segments.last().map(|s| s.as_str()).unwrap_or("")
    }
}

/// Collects all direct function call paths from a block.
#[derive(Default)]
pub(crate) struct PathCallCollector {
    pub calls: Vec<CallPath>,
}

impl<'ast> Visit<'ast> for PathCallCollector {
    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        if let syn::Expr::Path(path) = &*call.func {
            // Skip qualified-self paths (e.g., <T as Trait>::method) — out of scope.
            if path.qself.is_some() {
                syn::visit::visit_expr_call(self, call);
                return;
            }

            let segments: Vec<String> = path
                .path
                .segments
                .iter()
                .map(|s| s.ident.to_string())
                .collect();

            if let Some(last_seg) = path.path.segments.last() {
                self.calls.push(CallPath {
                    segments,
                    span: last_seg.ident.span(),
                    leading_colon: path.path.leading_colon.is_some(),
                });
            }
        }
        syn::visit::visit_expr_call(self, call);
    }

    /// Captures method calls (receiver.method(args)) as single-segment CallPaths.
    /// Resolution is approximate: without type info, we match by method name only.
    /// This is conservative — false positive SCC membership is safe (injecting
    /// unnecessary decrease checks), while false negative is unsound.
    /// Fix for #2550 finding F1.
    fn visit_expr_method_call(&mut self, method_call: &'ast syn::ExprMethodCall) {
        self.calls.push(CallPath {
            segments: vec![method_call.method.to_string()],
            span: method_call.method.span(),
            leading_colon: false,
        });
        syn::visit::visit_expr_method_call(self, method_call);
    }
}

/// Resolves a `CallPath` to a canonical crate-relative path.
///
/// Returns `None` if the path cannot be resolved or is ambiguous.
#[allow(clippy::indexing_slicing)] // segs[0] guarded by !is_empty(); slices only used in multi-segment branches
pub(crate) fn resolve_call_path(
    call: &CallPath,
    caller_module: &[String],
    index: &CrateModeIndex,
) -> Option<CanonicalFnPath> {
    // Skip paths with leading `::` — these are absolute/external paths
    // (e.g., `::trust_vc_core::verify_macro::*`).
    if call.leading_colon {
        return None;
    }

    let segs = &call.segments;
    if segs.is_empty() {
        return None;
    }

    // Single-segment: try current_module::name
    if segs.len() == 1 {
        let mut path = caller_module.to_vec();
        path.push(segs[0].clone());
        let candidate = CanonicalFnPath(path);
        if index.lookup(&candidate).is_some() {
            return Some(candidate);
        }
        // Also check crate-root level
        let root_candidate = CanonicalFnPath(vec![segs[0].clone()]);
        if index.lookup(&root_candidate).is_some() {
            return Some(root_candidate);
        }
        // Fallback: method name might be TypeName::method in current module's
        // impl blocks (e.g., `recurse` → `["mod", "Tree", "recurse"]`).
        // Fix for #2550 finding F1.
        if let Some(method_path) = index.lookup_method_in_module(&segs[0], caller_module) {
            return Some(method_path);
        }
        return None;
    }

    let first = &segs[0];

    // `self::...` → current_module + remaining segments
    if first == "self" {
        let mut path = caller_module.to_vec();
        path.extend(segs[1..].iter().cloned());
        let candidate = CanonicalFnPath(path);
        if index.lookup(&candidate).is_some() {
            return Some(candidate);
        }
        return None;
    }

    // `super::...` → strip one module segment per `super`
    if first == "super" {
        let mut module = caller_module.to_vec();
        let mut rest_start = 0;
        for (i, seg) in segs.iter().enumerate() {
            if seg == "super" {
                if module.is_empty() {
                    return None; // too many supers
                }
                module.pop();
                rest_start = i + 1;
            } else {
                break;
            }
        }
        module.extend(segs[rest_start..].iter().cloned());
        let candidate = CanonicalFnPath(module);
        if index.lookup(&candidate).is_some() {
            return Some(candidate);
        }
        return None;
    }

    // `crate::...` → crate-relative path (drop "crate" prefix)
    if first == "crate" {
        let path: Vec<String> = segs[1..].to_vec();
        let candidate = CanonicalFnPath(path);
        if index.lookup(&candidate).is_some() {
            return Some(candidate);
        }
        return None;
    }

    // Plain multi-segment: try current_module::a::b::foo, then crate::a::b::foo
    {
        let mut path = caller_module.to_vec();
        path.extend(segs.iter().cloned());
        let candidate = CanonicalFnPath(path);
        if index.lookup(&candidate).is_some() {
            return Some(candidate);
        }
    }
    {
        let candidate = CanonicalFnPath(segs.clone());
        if index.lookup(&candidate).is_some() {
            return Some(candidate);
        }
    }

    None
}

/// Resolves a call path and returns the callee mode if found.
pub(crate) fn resolve_callee_mode(
    call: &CallPath,
    caller_module: &[String],
    index: &CrateModeIndex,
) -> Option<FunctionMode> {
    let canonical = resolve_call_path(call, caller_module, index)?;
    index.lookup(&canonical).map(|f| f.mode)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_index(entries: &[(&[&str], FunctionMode)]) -> CrateModeIndex {
        CrateModeIndex::from_entries(entries)
    }

    #[test]
    fn test_resolve_self_path() {
        let index = make_index(&[(&["mymod", "helper"], FunctionMode::Proof)]);
        let call = CallPath {
            segments: vec!["self".into(), "helper".into()],
            span: Span::call_site(),
            leading_colon: false,
        };
        let result = resolve_call_path(&call, &["mymod".into()], &index);
        assert_eq!(
            result,
            Some(CanonicalFnPath(vec!["mymod".into(), "helper".into()]))
        );
    }

    #[test]
    fn test_resolve_super_path() {
        let index = make_index(&[(&["parent_fn"], FunctionMode::Exec)]);
        let call = CallPath {
            segments: vec!["super".into(), "parent_fn".into()],
            span: Span::call_site(),
            leading_colon: false,
        };
        let result = resolve_call_path(&call, &["child".into()], &index);
        assert_eq!(result, Some(CanonicalFnPath(vec!["parent_fn".into()])));
    }

    #[test]
    fn test_resolve_crate_path() {
        let index = make_index(&[(&["specs", "helper"], FunctionMode::Spec)]);
        let call = CallPath {
            segments: vec!["crate".into(), "specs".into(), "helper".into()],
            span: Span::call_site(),
            leading_colon: false,
        };
        let result = resolve_call_path(&call, &["other".into()], &index);
        assert_eq!(
            result,
            Some(CanonicalFnPath(vec!["specs".into(), "helper".into()]))
        );
    }

    #[test]
    fn test_resolve_plain_multi_segment() {
        let index = make_index(&[(&["proofs", "lemma"], FunctionMode::Proof)]);
        let call = CallPath {
            segments: vec!["proofs".into(), "lemma".into()],
            span: Span::call_site(),
            leading_colon: false,
        };
        // From crate root (empty module path), should resolve to crate::proofs::lemma
        let result = resolve_call_path(&call, &[], &index);
        assert_eq!(
            result,
            Some(CanonicalFnPath(vec!["proofs".into(), "lemma".into()]))
        );
    }

    #[test]
    fn test_resolve_leading_colon_skipped() {
        let index = make_index(&[(&["foo"], FunctionMode::Exec)]);
        let call = CallPath {
            segments: vec!["trust_vc_core".into(), "verify".into()],
            span: Span::call_site(),
            leading_colon: true,
        };
        let result = resolve_call_path(&call, &[], &index);
        assert!(result.is_none());
    }

    #[test]
    fn test_resolve_simple_unqualified() {
        let index = make_index(&[
            (&["mymod", "helper"], FunctionMode::Proof),
            (&["helper"], FunctionMode::Exec),
        ]);
        let call = CallPath {
            segments: vec!["helper".into()],
            span: Span::call_site(),
            leading_colon: false,
        };
        // From mymod, should prefer mymod::helper
        let result = resolve_call_path(&call, &["mymod".into()], &index);
        assert_eq!(
            result,
            Some(CanonicalFnPath(vec!["mymod".into(), "helper".into()]))
        );
    }
}
