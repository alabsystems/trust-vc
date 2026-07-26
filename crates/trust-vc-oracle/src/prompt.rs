// trust-vc-oracle — Prompt engineering for LLM proof synthesis
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::backend::ProposedAnnotations;
use crate::feedback::ProofFeedback;

/// System instructions that teach the LLM trust_vc annotation syntax.
pub const SYSTEM_PROMPT: &str = r#"You are a formal verification expert for Rust programs using the trust_vc verification tool.

Your job: given a Rust function, propose formal specifications (preconditions and postconditions) that the function satisfies.

## trust_vc annotation syntax

Preconditions (what must be true before the function runs):
  requires!(condition)

Postconditions (what must be true after the function returns):
  ensures!(condition)

## Rules for writing specs

1. Use the EXACT variable names from the function signature
2. Specs are mathematical expressions over the function parameters
3. For postconditions, refer to the return value as `result`
   (but only if the function has a return type — trust_vc adds a `result` variable automatically)
4. Common operators: ==, !=, <, <=, >, >=, &&, ||, !, +, -, *, /, %
5. Integer arithmetic is mathematical (no overflow) in specs
6. For collections: .len(), indexing with @[i], .contains()
7. Quantifiers: forall(|x: Type| condition), exists(|x: Type| condition)

## Response format

Respond with ONLY the annotations in this exact format. No explanations, no code fences, no other text.

REQUIRES: <condition>
REQUIRES: <condition>
ENSURES: <condition>
ENSURES: <condition>
INVARIANT: <label>: <condition>
DECREASES: <expression>

If no precondition is needed, omit REQUIRES lines.
If there are no loops, omit INVARIANT lines.
If there is no recursion, omit DECREASES lines.
If you cannot determine a meaningful postcondition, write:
ENSURES: true

## Examples

For `fn abs(x: i32) -> i32`:
REQUIRES: x != i32::MIN
ENSURES: result >= 0
ENSURES: result == x || result == -x

For `fn max(a: i32, b: i32) -> i32`:
ENSURES: result >= a && result >= b
ENSURES: result == a || result == b

For `fn clamp(x: i32, lo: i32, hi: i32) -> i32`:
REQUIRES: lo <= hi
ENSURES: result >= lo && result <= hi
"#;

/// Build the user prompt for a given function and feedback history.
pub fn build_user_prompt(
    source: &str,
    feedback_history: &[(ProposedAnnotations, ProofFeedback)],
) -> String {
    let mut prompt = String::new();

    prompt.push_str("Propose formal specifications for this Rust function:\n\n```rust\n");
    prompt.push_str(source);
    prompt.push_str("\n```\n");

    if !feedback_history.is_empty() {
        prompt.push_str("\n## Previous attempts and feedback\n\n");
        for (i, (proposal, feedback)) in feedback_history.iter().enumerate() {
            prompt.push_str(&format!("### Attempt {} ", i + 1));

            // Show what was proposed
            prompt.push_str("(proposed: ");
            for r in &proposal.requires {
                prompt.push_str(&format!("requires!({}), ", r));
            }
            for e in &proposal.ensures {
                prompt.push_str(&format!("ensures!({}), ", e));
            }
            prompt.push_str(")\n");

            // Show feedback
            prompt.push_str(&feedback.to_llm_summary());
            prompt.push('\n');
        }

        prompt.push_str(
            "\nUse the feedback above to fix your specification. \
             Counterexample values show concrete inputs that violate the proposed spec. \
             Either weaken the postcondition or strengthen the precondition.\n",
        );
    }

    prompt
}

/// Parse an LLM response into `ProposedAnnotations`.
///
/// Accepts two formats:
///   1. Structured: `REQUIRES:`, `ENSURES:`, `INVARIANT:`, `DECREASES:` prefixed lines.
///   2. Macro-style: `requires!(...)`, `ensures!(...)`, `invariant!(...)`, `decreases!(...)`.
///
/// The parser ignores markdown fences, explanatory prose, and blank lines.
/// If structured format is found, it takes priority; macro-style is a fallback.
pub fn parse_annotations(response: &str) -> ProposedAnnotations {
    let mut requires = Vec::new();
    let mut ensures = Vec::new();
    let mut invariants: Vec<(String, String)> = Vec::new();
    let mut decreases = Vec::new();

    for line in response.lines() {
        let trimmed = line.trim();

        if let Some(cond) = trimmed.strip_prefix("REQUIRES:") {
            let cond = cond.trim();
            if !cond.is_empty() {
                requires.push(cond.to_string());
            }
        } else if let Some(cond) = trimmed.strip_prefix("ENSURES:") {
            let cond = cond.trim();
            if !cond.is_empty() {
                ensures.push(cond.to_string());
            }
        } else if let Some(cond) = trimmed.strip_prefix("INVARIANT:") {
            let cond = cond.trim();
            if !cond.is_empty() {
                // Format: "label: condition" or just "condition"
                if let Some((label, expr)) = cond.split_once(':') {
                    invariants.push((label.trim().to_string(), expr.trim().to_string()));
                } else {
                    invariants.push(("loop".to_string(), cond.to_string()));
                }
            }
        } else if let Some(cond) = trimmed.strip_prefix("DECREASES:") {
            let cond = cond.trim();
            if !cond.is_empty() {
                decreases.push(cond.to_string());
            }
        }
    }

    // If no annotations found, try to extract from fenced code or inline format
    if requires.is_empty() && ensures.is_empty() && invariants.is_empty() && decreases.is_empty() {
        for line in response.lines() {
            let trimmed = line.trim();
            // Strip trailing semicolons that LLMs sometimes add
            let trimmed = trimmed.strip_suffix(';').unwrap_or(trimmed);
            if let Some(rest) = trimmed.strip_prefix("requires!(") {
                if let Some(cond) = rest.strip_suffix(')') {
                    requires.push(cond.to_string());
                }
            } else if let Some(rest) = trimmed.strip_prefix("ensures!(") {
                if let Some(cond) = rest.strip_suffix(')') {
                    ensures.push(cond.to_string());
                }
            } else if let Some(rest) = trimmed.strip_prefix("invariant!(") {
                if let Some(cond) = rest.strip_suffix(')') {
                    invariants.push(("loop".to_string(), cond.to_string()));
                }
            } else if let Some(rest) = trimmed.strip_prefix("decreases!(") {
                if let Some(cond) = rest.strip_suffix(')') {
                    decreases.push(cond.to_string());
                }
            }
        }
    }

    ProposedAnnotations {
        requires,
        ensures,
        invariants,
        decreases,
        raw_response: response.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_clean_format() {
        let response = "REQUIRES: x > 0\nENSURES: result >= 1\nENSURES: result <= x";
        let ann = parse_annotations(response);
        assert_eq!(ann.requires, vec!["x > 0"]);
        assert_eq!(ann.ensures, vec!["result >= 1", "result <= x"]);
    }

    #[test]
    fn test_parse_macro_format() {
        let response = "requires!(x > 0)\nensures!(result >= 0)";
        let ann = parse_annotations(response);
        assert_eq!(ann.requires, vec!["x > 0"]);
        assert_eq!(ann.ensures, vec!["result >= 0"]);
    }

    #[test]
    fn test_parse_with_noise() {
        let response = "Here are the specs:\n\nREQUIRES: x != 0\nENSURES: result > 0\n\nGood luck!";
        let ann = parse_annotations(response);
        assert_eq!(ann.requires, vec!["x != 0"]);
        assert_eq!(ann.ensures, vec!["result > 0"]);
    }

    #[test]
    fn test_parse_empty() {
        let response = "I don't know what to propose.";
        let ann = parse_annotations(response);
        assert!(ann.requires.is_empty());
        assert!(ann.ensures.is_empty());
    }

    #[test]
    fn test_build_prompt_no_history() {
        let prompt = build_user_prompt("fn foo(x: i32) -> i32 { x + 1 }", &[]);
        assert!(prompt.contains("fn foo"));
        assert!(!prompt.contains("Previous attempts"));
    }

    #[test]
    fn test_parse_invariant_with_label() {
        let response = "REQUIRES: n > 0\nINVARIANT: main_loop: i <= n\nENSURES: result >= 0";
        let ann = parse_annotations(response);
        assert_eq!(ann.requires, vec!["n > 0"]);
        assert_eq!(ann.ensures, vec!["result >= 0"]);
        assert_eq!(ann.invariants.len(), 1);
        assert_eq!(ann.invariants[0].0, "main_loop");
        assert_eq!(ann.invariants[0].1, "i <= n");
    }

    #[test]
    fn test_parse_invariant_without_label() {
        let response = "INVARIANT: i >= 0";
        let ann = parse_annotations(response);
        assert_eq!(ann.invariants.len(), 1);
        assert_eq!(ann.invariants[0].0, "loop");
        assert_eq!(ann.invariants[0].1, "i >= 0");
    }

    #[test]
    fn test_parse_decreases() {
        let response = "DECREASES: n - i\nENSURES: result == n";
        let ann = parse_annotations(response);
        assert_eq!(ann.decreases, vec!["n - i"]);
        assert_eq!(ann.ensures, vec!["result == n"]);
    }

    #[test]
    fn test_parse_macro_format_with_invariant() {
        let response =
            "requires!(x > 0)\ninvariant!(i < x)\nensures!(result >= 0)\ndecreases!(x - i)";
        let ann = parse_annotations(response);
        assert_eq!(ann.requires, vec!["x > 0"]);
        assert_eq!(ann.ensures, vec!["result >= 0"]);
        assert_eq!(ann.invariants.len(), 1);
        assert_eq!(ann.invariants[0].1, "i < x");
        assert_eq!(ann.decreases, vec!["x - i"]);
    }

    #[test]
    fn test_parse_macro_format_with_semicolons() {
        let response = "requires!(x > 0);\nensures!(result >= 0);";
        let ann = parse_annotations(response);
        assert_eq!(ann.requires, vec!["x > 0"]);
        assert_eq!(ann.ensures, vec!["result >= 0"]);
    }

    #[test]
    fn test_build_prompt_with_history() {
        let history = vec![(
            ProposedAnnotations {
                requires: vec![],
                ensures: vec!["x > 0".to_string()],
                invariants: vec![],
                decreases: vec![],
                raw_response: String::new(),
            },
            ProofFeedback::Failed {
                counterexamples: vec![],
                localization: crate::feedback::FailureLocalization {
                    full_assertion: None,
                    sub_results: vec![],
                },
                obligation_name: "test".to_string(),
                solver_mode: "default".to_string(),
                elapsed: std::time::Duration::from_millis(10),
            },
        )];
        let prompt = build_user_prompt("fn foo(x: i32) -> i32 { x + 1 }", &history);
        assert!(prompt.contains("Previous attempts"));
        assert!(prompt.contains("Attempt 1"));
    }
}
