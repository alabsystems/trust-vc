// Guard tests for doc API syntax accuracy (#1937).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Prevents documentation from drifting back to unsupported proc-macro
// spellings. The forbidden patterns are the exact set from #1937.

mod common;

/// Forbidden syntax patterns that must not appear in target docs.
///
/// Each entry is a substring that indicates unsupported proc-macro usage.
/// Keep this list explicit so future drift shows up in diffs.
const FORBIDDEN_PATTERNS: &[&str] = &[
    "#[trust_vc::verified]",
    "#[trust_vc::ghost]",
    "#[trust_vc::lemma_cache]",
    "#[trust_vc::loop_invariant(",
    "#[trust_vc::invariant(",
    "#[trust_vc::requires(",
    "#[trust_vc::ensures(",
    "#[trust_vc::rational]",
    "#[trust_vc::trace_encoding]",
];

/// Patterns that indicate missing `!` on function-like macros.
///
/// These match `trust_vc::requires(` NOT followed by `!`, etc.
/// We check these separately because they can appear inside code fences
/// as bare function calls (without `!`).
const MISSING_BANG_PATTERNS: &[(&str, &str)] = &[
    ("trust_vc::requires(", "trust_vc::requires!("),
    ("trust_vc::ensures(", "trust_vc::ensures!("),
    ("trust_vc::assume(", "trust_vc::assume!("),
];

/// Target documentation files.
///
/// Some source-repo docs are intentionally excluded from the staged/public
/// publish tree. Load them at runtime so source checkouts still get coverage
/// without making staged cargo tests depend on stripped paths.
const DOC_FILE_PATHS: &[(&str, &str)] = &[
    ("README.md", "../../README.md"),
    (
        "verification-patterns.md",
        "../../docs/verification-patterns.md",
    ),
    (
        "verification-test-patterns.md",
        "../../docs/verification-test-patterns.md",
    ),
    ("type-semantics.md", "../../docs/type-semantics.md"),
    ("unsigned-overflow.md", "../../docs/unsigned-overflow.md"),
    ("ay-backend.md", "../../docs/ay-backend.md"),
    ("termination-proofs.md", "../../docs/termination-proofs.md"),
    ("TEST_VERIFICATION.md", "../../docs/TEST_VERIFICATION.md"),
    (
        "marker_extraction.rs",
        "../trust-vc-core/src/marker_extraction.rs",
    ),
];

fn doc_files() -> Vec<(&'static str, String)> {
    let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    DOC_FILE_PATHS
        .iter()
        .filter_map(|(name, rel_path)| {
            std::fs::read_to_string(manifest_dir.join(rel_path))
                .ok()
                .map(|content| (*name, content))
        })
        .collect()
}

fn extract_proof_signature(lines: &[&str], attr_line_num: usize) -> Option<String> {
    let mut signature = String::new();
    let mut saw_fn = false;

    for line in lines.iter().skip(attr_line_num + 1) {
        let trimmed = line.trim();

        if trimmed.starts_with("```") {
            break;
        }

        if !saw_fn {
            if trimmed.is_empty()
                || trimmed.starts_with("#[")
                || trimmed.starts_with("//")
                || trimmed.starts_with("///")
            {
                continue;
            }

            let is_fn_sig = trimmed.starts_with("fn ")
                || trimmed.starts_with("pub fn ")
                || trimmed.starts_with("pub(crate) fn ");
            if !is_fn_sig {
                break;
            }
            saw_fn = true;
        }

        if !signature.is_empty() {
            signature.push(' ');
        }
        signature.push_str(trimmed);

        if trimmed.contains('{') || trimmed.ends_with(';') {
            break;
        }
    }

    saw_fn.then_some(signature)
}

fn find_parameter_list_start(signature: &str) -> Option<usize> {
    let mut angle_depth = 0usize;
    let mut bracket_depth = 0usize;
    let mut brace_depth = 0usize;

    for (offset, ch) in signature.char_indices() {
        match ch {
            '<' => angle_depth += 1,
            '>' if angle_depth > 0 => angle_depth -= 1,
            '[' => bracket_depth += 1,
            ']' if bracket_depth > 0 => bracket_depth -= 1,
            '{' => brace_depth += 1,
            '}' if brace_depth > 0 => brace_depth -= 1,
            '(' if angle_depth == 0 && bracket_depth == 0 && brace_depth == 0 => {
                return Some(offset + ch.len_utf8());
            }
            _ => {}
        }
    }

    None
}

fn extract_first_parameter(signature: &str) -> Option<&str> {
    let start = find_parameter_list_start(signature)?;
    let params = &signature[start..];
    let mut paren_depth = 0usize;
    let mut bracket_depth = 0usize;
    let mut brace_depth = 0usize;
    let mut angle_depth = 0usize;

    for (offset, ch) in params.char_indices() {
        match ch {
            '(' => paren_depth += 1,
            ')' if paren_depth == 0
                && bracket_depth == 0
                && brace_depth == 0
                && angle_depth == 0 =>
            {
                return Some(params[..offset].trim());
            }
            ')' => paren_depth -= 1,
            '[' => bracket_depth += 1,
            ']' if bracket_depth > 0 => bracket_depth -= 1,
            '{' => brace_depth += 1,
            '}' if brace_depth > 0 => brace_depth -= 1,
            '<' => angle_depth += 1,
            '>' if angle_depth > 0 => angle_depth -= 1,
            ',' if paren_depth == 0
                && bracket_depth == 0
                && brace_depth == 0
                && angle_depth == 0 =>
            {
                return Some(params[..offset].trim());
            }
            _ => {}
        }
    }

    None
}

fn strip_receiver_lifetime(param: &str) -> Option<&str> {
    let mut chars = param.char_indices();
    let Some((_, '\'')) = chars.next() else {
        return None;
    };

    let mut end = 1;
    for (idx, ch) in chars {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            end = idx + ch.len_utf8();
            continue;
        }
        break;
    }

    Some(&param[end..])
}

fn first_parameter_is_receiver(param: &str) -> bool {
    let normalized = param
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .replace("& ", "&")
        .replace(" :", ":");

    if matches!(
        normalized.as_str(),
        "self" | "mut self" | "&self" | "&mut self"
    ) || normalized.starts_with("self:")
        || normalized.starts_with("mut self:")
        || normalized.starts_with("&self:")
        || normalized.starts_with("&mut self:")
    {
        return true;
    }

    let Some(rest) = normalized.strip_prefix('&') else {
        return false;
    };
    let Some(rest) = strip_receiver_lifetime(rest) else {
        return false;
    };
    let rest = rest.trim_start();

    matches!(rest, "self" | "mut self")
        || rest.starts_with("self:")
        || rest.starts_with("mut self:")
}

fn proof_signature_contains_receiver(signature: &str) -> bool {
    extract_first_parameter(signature).is_some_and(first_parameter_is_receiver)
}

fn collect_proof_receiver_violations(name: &str, content: &str) -> Vec<String> {
    let lines: Vec<_> = content.lines().collect();
    let mut violations = Vec::new();

    for (line_num, line) in lines.iter().enumerate() {
        if !line.contains("#[trust_vc::proof]") {
            continue;
        }

        let Some(signature) = extract_proof_signature(&lines, line_num) else {
            continue;
        };

        if proof_signature_contains_receiver(&signature) {
            violations.push(format!(
                "  {}:{}: found unsupported #[trust_vc::proof] receiver\n    > {}",
                name,
                line_num + 1,
                signature
            ));
        }
    }

    violations
}

#[test]
fn test_docs_contain_no_forbidden_attribute_syntax() {
    let mut violations = Vec::new();
    let doc_files = doc_files();

    for (name, content) in &doc_files {
        for (line_num, line) in content.lines().enumerate() {
            for pattern in FORBIDDEN_PATTERNS {
                if line.contains(pattern) {
                    violations.push(format!(
                        "  {}:{}: found `{}`\n    > {}",
                        name,
                        line_num + 1,
                        pattern,
                        line.trim()
                    ));
                }
            }
        }
    }

    assert!(
        violations.is_empty(),
        "Unsupported proc-macro syntax found in docs (#1937):\n{}",
        violations.join("\n")
    );
}

#[test]
fn test_docs_contain_no_missing_bang_on_function_macros() {
    let mut violations = Vec::new();
    let doc_files = doc_files();

    for (name, content) in &doc_files {
        for (line_num, line) in content.lines().enumerate() {
            for (bad, good) in MISSING_BANG_PATTERNS {
                // Match the bad pattern but skip if the good pattern is present
                if line.contains(bad) && !line.contains(good) {
                    violations.push(format!(
                        "  {}:{}: found `{}` (should be `{}`)\n    > {}",
                        name,
                        line_num + 1,
                        bad,
                        good,
                        line.trim()
                    ));
                }
            }
        }
    }

    assert!(
        violations.is_empty(),
        "Function-like macros missing `!` found in docs (#1937):\n{}",
        violations.join("\n")
    );
}

#[test]
fn test_docs_contain_no_proof_methods_with_self_params() {
    let mut violations = Vec::new();
    let doc_files = doc_files();

    for (name, content) in &doc_files {
        violations.extend(collect_proof_receiver_violations(name, content));
    }

    assert!(
        violations.is_empty(),
        "Docs must not advertise unsupported #[trust_vc::proof] methods with self params (#1753):\n{}",
        violations.join("\n")
    );
}

#[test]
fn test_proof_receiver_guard_catches_multiline_self_signature() {
    let content = r#"
```rust
#[trust_vc::proof]
fn increment(
    &mut self,
    amount: u32,
) {
    trust_vc::assert!(amount >= 0);
}
```
"#;

    let violations = collect_proof_receiver_violations("fixture.md", content);
    assert_eq!(violations.len(), 1, "expected one multiline self receiver");
}

#[test]
fn test_proof_receiver_guard_catches_multiline_owned_self_signature() {
    let content = r#"
```rust
#[trust_vc::proof]
fn consume(
    self
) {
    trust_vc::assert!(true);
}
```
"#;

    let violations = collect_proof_receiver_violations("fixture.md", content);
    assert_eq!(
        violations.len(),
        1,
        "expected one multiline owned self receiver"
    );
}

#[test]
fn test_proof_receiver_guard_allows_multiline_non_method_signature() {
    let content = r#"
```rust
#[trust_vc::proof]
fn lemma_sum_nonneg(
    value: u32,
    amount: u32,
) {
    trust_vc::assert!(value + amount >= value);
}
```
"#;

    let violations = collect_proof_receiver_violations("fixture.md", content);
    assert!(
        violations.is_empty(),
        "non-method proof should not be flagged"
    );
}

#[test]
fn test_proof_receiver_guard_allows_self_module_path_parameter_type() {
    let content = r#"
```rust
#[trust_vc::proof]
fn lemma_with_self_path(
    value: self::ghost::Token,
) {
    trust_vc::assert!(true);
}
```
"#;

    let violations = collect_proof_receiver_violations("fixture.md", content);
    assert!(
        violations.is_empty(),
        "self:: path parameter should not be treated as a receiver"
    );
}

#[test]
fn test_proof_receiver_guard_catches_receiver_after_fn_trait_bound() {
    let content = r#"
```rust
#[trust_vc::proof]
fn invoke<F: Fn(u32) -> u32>(
    self,
    callback: F,
) {
    trust_vc::assert!(true);
}
```
"#;

    let violations = collect_proof_receiver_violations("fixture.md", content);
    assert_eq!(
        violations.len(),
        1,
        "expected receiver after generic Fn-trait bound"
    );
}

/// Canonical example exercising the supported contract + invariant surface.
///
/// This test verifies that the core TrustVc API surface compiles and
/// produces verification conditions through the standard pipeline.
/// Follows the same VC registration pattern as contracts_basic.rs.
#[test]
fn test_canonical_contract_invariant_example_compiles_and_verifies() {
    use trust_vc_core::verification_bridge::VerificationPipeline;
    use trust_vc_core::verify_macro;

    common::with_clean_verification(|| {
        // Register a variable and contract using the canonical macro surface
        verify_macro::collect_variable("n".to_string(), "u64".to_string());
        trust_vc::requires!(n <= 100);
        trust_vc::ensures!(n <= 100);

        // Collect and verify
        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, trust_vc_core::VerifyResult::Verified),
            "Canonical contract example should verify, got: {:?}",
            result
        );
    });
}

#[test]
fn test_unsigned_overflow_doc_guarded_sum_example_verifies() {
    use trust_vc_core::vc::VerificationContext;
    use trust_vc_core::VerifyResult;

    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("a", "u32");
        ctx.declare_var_parsed("b", "u32");
        ctx.push_assume("a_is_doc_example", "a == 100");
        ctx.push_assume("b_is_doc_example", "b == 200");
        ctx.push_assume("sum_has_headroom", "a <= u32::MAX - b");
        ctx.push_assert("sum_non_decreasing", "a + b >= a");

        let result = common::verify_context_with_pipeline(ctx);
        assert!(
            matches!(result, VerifyResult::Verified),
            "Guarded unsigned sum doc example should verify, got: {:?}",
            result
        );
    });
}

#[test]
fn test_unsigned_overflow_doc_unguarded_sum_example_fails() {
    use trust_vc_core::vc::VerificationContext;
    use trust_vc_core::VerifyResult;

    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("a", "u32");
        ctx.declare_var_parsed("b", "u32");
        ctx.push_assert("sum_non_decreasing", "a + b >= a");

        let result = common::verify_context_with_pipeline(ctx);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Unguarded unsigned sum doc example should produce Counterexample, got: {:?}",
            result
        );
    });
}

#[test]
fn test_unsigned_overflow_doc_wrapping_example_verifies() {
    use trust_vc_core::vc::VerificationContext;
    use trust_vc_core::VerifyResult;

    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "u32");
        ctx.push_assume("x_is_max", "x == u32::MAX");
        ctx.push_assert("wraps_to_zero", "x.wrapping_add(1) == 0");

        let result = common::verify_context_with_pipeline(ctx);
        assert!(
            matches!(result, VerifyResult::Verified),
            "Wrapping overflow doc example should verify, got: {:?}",
            result
        );
    });
}

#[test]
fn test_unsigned_overflow_doc_checked_example_verifies_with_overflow_checks() {
    use trust_vc_core::vc::VerificationContext;
    use trust_vc_core::VerifyResult;

    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_parsed("x", "u32");
        ctx.push_assume("x_has_headroom", "x < u32::MAX");
        ctx.push_assert("checked_add_headroom", "x.checked_add(1) > x");

        let result = common::verify_context_with_pipeline(ctx);
        assert!(
            matches!(result, VerifyResult::Verified),
            "Checked-add doc example should verify under overflow checking, got: {:?}",
            result
        );
    });
}

#[test]
fn test_unsigned_overflow_doc_saturating_example_verifies() {
    use trust_vc_core::vc::VerificationContext;
    use trust_vc_core::VerifyResult;

    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "u32");
        ctx.push_assume("x_is_max", "x == u32::MAX");
        ctx.push_assert("saturates_to_max", "x.saturating_add(1) == u32::MAX");

        let result = common::verify_context_with_pipeline(ctx);
        assert!(
            matches!(result, VerifyResult::Verified),
            "Saturating overflow doc example should verify, got: {:?}",
            result
        );
    });
}
