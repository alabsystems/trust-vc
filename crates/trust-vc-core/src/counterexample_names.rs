// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared naming-policy module for counterexample variable display.
//!
//! Centralizes the classification of trust-vc-reserved helper names so that the
//! model renderer can hide internal transport variables and show user-facing
//! aliases. Mirrors the per-subsystem naming-policy pattern from trust_mc's
//! `mir_symbolic_names.rs` / `chc_state_names.rs`.
//!
//! Part of #2651.

/// Classification of a raw counterexample variable name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CounterexampleNameKind {
    /// Ordinary user-declared variable (parameter, local, etc.).
    UserVisible,
    /// `old!(x)` capture → raw name `__trust_vc_old_*`.
    OldCapture,
    /// Mut-ref SSA shadow → raw name `__trust_vc_mutref_*`.
    MutRefVersion,
    /// Closure parameter rename → raw name `__trust_vc_closure_arg*`.
    ClosureParam,
    /// Closure result binding → raw name `__trust_vc_closure_result`.
    ClosureResult,
    /// Extern-spec call temp → raw name `__trust_vc_extern_call_value_*`.
    ExternTemp,
    /// Any other `__trust_vc_*` helper not covered above.
    ReservedOther,
}

/// Classify a raw solver variable name into its helper category.
pub(crate) fn classify(raw_name: &str) -> CounterexampleNameKind {
    if !raw_name.starts_with("__trust_vc_") {
        return CounterexampleNameKind::UserVisible;
    }
    if raw_name.starts_with("__trust_vc_old_") {
        CounterexampleNameKind::OldCapture
    } else if raw_name.starts_with("__trust_vc_mutref_") {
        CounterexampleNameKind::MutRefVersion
    } else if raw_name.starts_with("__trust_vc_closure_result") {
        // Bare `__trust_vc_closure_result` or the per-closure-suffixed form
        // `__trust_vc_closure_result_c<hash>` introduced for #791.
        CounterexampleNameKind::ClosureResult
    } else if raw_name.starts_with("__trust_vc_closure_arg") {
        // Bare `__trust_vc_closure_arg{i}` or the suffixed `..._c<hash>` form.
        CounterexampleNameKind::ClosureParam
    } else if raw_name.starts_with("__trust_vc_extern_call_value_") {
        CounterexampleNameKind::ExternTemp
    } else {
        CounterexampleNameKind::ReservedOther
    }
}

/// Display metadata for a counterexample variable binding.
#[derive(Debug, Clone)]
pub(crate) struct CounterexampleVarMeta {
    /// User-facing display name (e.g., `old(x)` instead of `__trust_vc_old_x`).
    pub display_name: String,
    /// Whether this binding should appear in the rendered counterexample.
    pub visible: bool,
}

/// Produce default metadata for a raw variable name using the shared classifier.
///
/// - User-visible names: visible, display_name = raw_name.
/// - `old!()` captures: visible with `old(inner)` display.
/// - Mut-ref SSA: visible with stripped prefix.
/// - Closure params: hidden by default (need explicit alias from closure_expand).
/// - Extern temps, closure result, other reserved: hidden.
pub(crate) fn default_meta(raw_name: &str) -> CounterexampleVarMeta {
    match classify(raw_name) {
        CounterexampleNameKind::UserVisible => CounterexampleVarMeta {
            display_name: raw_name.to_string(),
            visible: true,
        },
        CounterexampleNameKind::OldCapture => {
            let inner = raw_name.strip_prefix("__trust_vc_old_").unwrap_or(raw_name);
            CounterexampleVarMeta {
                display_name: format!("old({inner})"),
                visible: true,
            }
        }
        CounterexampleNameKind::MutRefVersion => {
            // __trust_vc_mutref_<place>_<version> → place@version
            let suffix = raw_name
                .strip_prefix("__trust_vc_mutref_")
                .unwrap_or(raw_name);
            let display_name = match suffix.rsplit_once('_') {
                Some((place, version)) if version.chars().all(|c| c.is_ascii_digit()) => {
                    format!("{}@{}", place, version)
                }
                _ => suffix.to_string(),
            };
            CounterexampleVarMeta {
                display_name,
                visible: true,
            }
        }
        CounterexampleNameKind::ClosureParam
        | CounterexampleNameKind::ClosureResult
        | CounterexampleNameKind::ExternTemp
        | CounterexampleNameKind::ReservedOther => CounterexampleVarMeta {
            display_name: raw_name.to_string(),
            visible: false,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_classify_user_visible() {
        assert_eq!(classify("x"), CounterexampleNameKind::UserVisible);
        assert_eq!(classify("my_var"), CounterexampleNameKind::UserVisible);
        assert_eq!(classify("result"), CounterexampleNameKind::UserVisible);
    }

    #[test]
    fn test_classify_old_capture() {
        assert_eq!(
            classify("__trust_vc_old_x"),
            CounterexampleNameKind::OldCapture
        );
        assert_eq!(
            classify("__trust_vc_old_counter"),
            CounterexampleNameKind::OldCapture
        );
    }

    #[test]
    fn test_classify_mutref() {
        assert_eq!(
            classify("__trust_vc_mutref_x_0"),
            CounterexampleNameKind::MutRefVersion
        );
        assert_eq!(
            classify("__trust_vc_mutref_counter_count_1"),
            CounterexampleNameKind::MutRefVersion
        );
    }

    #[test]
    fn test_classify_closure() {
        assert_eq!(
            classify("__trust_vc_closure_arg0"),
            CounterexampleNameKind::ClosureParam
        );
        assert_eq!(
            classify("__trust_vc_closure_result"),
            CounterexampleNameKind::ClosureResult
        );
    }

    #[test]
    fn test_classify_closure_per_closure_suffixed() {
        // #791: per-closure-unique symbols carry a `_c<hash>` suffix.
        assert_eq!(
            classify("__trust_vc_closure_arg0_c1a2b3c4"),
            CounterexampleNameKind::ClosureParam
        );
        assert_eq!(
            classify("__trust_vc_closure_result_c1a2b3c4"),
            CounterexampleNameKind::ClosureResult
        );
        // Suffixed forms remain hidden by default, like the bare forms.
        assert!(!default_meta("__trust_vc_closure_arg0_c1a2b3c4").visible);
        assert!(!default_meta("__trust_vc_closure_result_c1a2b3c4").visible);
    }

    #[test]
    fn test_classify_extern_temp() {
        assert_eq!(
            classify("__trust_vc_extern_call_value_42_5"),
            CounterexampleNameKind::ExternTemp
        );
    }

    #[test]
    fn test_classify_reserved_other() {
        assert_eq!(
            classify("__trust_vc_something_else"),
            CounterexampleNameKind::ReservedOther
        );
    }

    #[test]
    fn test_default_meta_user_visible() {
        let meta = default_meta("x");
        assert_eq!(meta.display_name, "x");
        assert!(meta.visible);
    }

    #[test]
    fn test_default_meta_old_capture() {
        let meta = default_meta("__trust_vc_old_x");
        assert_eq!(meta.display_name, "old(x)");
        assert!(meta.visible);
    }

    #[test]
    fn test_default_meta_mutref_version() {
        let meta = default_meta("__trust_vc_mutref_counter_count_1");
        assert_eq!(meta.display_name, "counter_count@1");
        assert!(meta.visible);
    }

    #[test]
    fn test_default_meta_mutref_no_version() {
        let meta = default_meta("__trust_vc_mutref_x");
        assert_eq!(meta.display_name, "x");
        assert!(meta.visible);
    }

    #[test]
    fn test_default_meta_closure_param_hidden() {
        let meta = default_meta("__trust_vc_closure_arg0");
        assert!(!meta.visible);
    }

    #[test]
    fn test_default_meta_extern_temp_hidden() {
        let meta = default_meta("__trust_vc_extern_call_value_42_5");
        assert!(!meta.visible);
    }
}
