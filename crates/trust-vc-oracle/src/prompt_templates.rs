// trust-vc-oracle — Prompt template engine for LLM proof synthesis
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Manages prompt templates with variable substitution, context windowing,
// and token budget management for generating structured LLM prompts.

use std::collections::HashMap;
use std::fmt;

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A named variable that can be substituted into a template.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TemplateVariable {
    /// Variable name used in `{{name}}` placeholders.
    pub name: String,
    /// Human-readable description of what this variable represents.
    pub description: String,
    /// Whether this variable must be provided before rendering.
    pub required: bool,
    /// Default value used when the variable is not explicitly set.
    pub default_value: Option<String>,
}

impl TemplateVariable {
    #[must_use]
    pub fn new(name: &str, description: &str, required: bool) -> Self {
        Self {
            name: name.to_string(),
            description: description.to_string(),
            required,
            default_value: None,
        }
    }

    #[must_use]
    pub fn with_default(mut self, value: &str) -> Self {
        self.default_value = Some(value.to_string());
        self
    }
}

/// A prompt template with placeholders and metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PromptTemplate {
    /// Unique template identifier.
    pub name: String,
    /// Raw template text with `{{variable}}` placeholders.
    pub text: String,
    /// Variables that this template expects.
    pub variables: Vec<TemplateVariable>,
    /// Task categories this template is applicable to.
    pub applicable_tasks: Vec<String>,
}

impl PromptTemplate {
    #[must_use]
    pub fn new(name: &str, text: &str) -> Self {
        Self {
            name: name.to_string(),
            text: text.to_string(),
            variables: Vec::new(),
            applicable_tasks: Vec::new(),
        }
    }

    #[must_use]
    pub fn with_variable(mut self, var: TemplateVariable) -> Self {
        self.variables.push(var);
        self
    }

    #[must_use]
    pub fn with_task(mut self, task: &str) -> Self {
        self.applicable_tasks.push(task.to_string());
        self
    }

    /// Render this template by substituting variables from the given bindings.
    ///
    /// Returns an error if a required variable is missing and has no default.
    pub fn render(&self, bindings: &HashMap<String, String>) -> Result<String, TemplateError> {
        let mut output = self.text.clone();

        for var in &self.variables {
            let placeholder = format!("{{{{{}}}}}", var.name);
            if let Some(value) = bindings.get(&var.name) {
                output = output.replace(&placeholder, value);
            } else if let Some(ref default) = var.default_value {
                output = output.replace(&placeholder, default);
            } else if var.required {
                return Err(TemplateError::MissingVariable {
                    template: self.name.clone(),
                    variable: var.name.clone(),
                });
            }
            // Optional without default: leave placeholder removed (empty)
            else {
                output = output.replace(&placeholder, "");
            }
        }

        Ok(output)
    }
}

/// Holds variable bindings for template rendering.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct TemplateContext {
    bindings: HashMap<String, String>,
}

impl TemplateContext {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Set a variable binding. Overwrites any previous value.
    pub fn set(&mut self, key: &str, value: &str) {
        self.bindings.insert(key.to_string(), value.to_string());
    }

    #[must_use]
    pub fn get(&self, key: &str) -> Option<&str> {
        self.bindings.get(key).map(String::as_str)
    }

    #[must_use]
    pub fn bindings(&self) -> &HashMap<String, String> {
        &self.bindings
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Prompt sections and strategies
// ---------------------------------------------------------------------------

/// The role of a prompt section in the conversation structure.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum PromptSection {
    /// System instructions defining the LLM's role and constraints.
    System,
    /// User message containing the task or query.
    User,
    /// Assistant message (for few-shot priming or chain-of-thought).
    Assistant,
    /// An example pair used in few-shot prompting.
    Example,
}

impl fmt::Display for PromptSection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::System => write!(f, "system"),
            Self::User => write!(f, "user"),
            Self::Assistant => write!(f, "assistant"),
            Self::Example => write!(f, "example"),
        }
    }
}

/// A single input/output example for few-shot prompting.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FewShotExample {
    /// The example input (e.g., a Rust function).
    pub input: String,
    /// The expected output (e.g., annotations).
    pub output: String,
    /// Optional explanation of the reasoning.
    pub explanation: Option<String>,
}

impl FewShotExample {
    #[must_use]
    pub fn new(input: &str, output: &str) -> Self {
        Self {
            input: input.to_string(),
            output: output.to_string(),
            explanation: None,
        }
    }

    #[must_use]
    pub fn with_explanation(mut self, explanation: &str) -> Self {
        self.explanation = Some(explanation.to_string());
        self
    }

    /// Estimated token count (approximation: 1 token per 4 chars).
    #[must_use]
    pub fn estimated_tokens(&self) -> usize {
        let chars =
            self.input.len() + self.output.len() + self.explanation.as_ref().map_or(0, String::len);
        estimate_tokens_from_chars(chars)
    }
}

/// The prompting strategy to use for a given task.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PromptStrategy {
    /// No examples; rely on system instructions alone.
    ZeroShot,
    /// Include concrete input/output examples.
    FewShot { examples: Vec<FewShotExample> },
    /// Instruct the LLM to reason step-by-step.
    ChainOfThought,
    /// Reasoning + action loop (think, act, observe).
    ReAct,
}

impl PromptStrategy {
    #[must_use]
    pub fn few_shot(examples: Vec<FewShotExample>) -> Self {
        Self::FewShot { examples }
    }
}

// ---------------------------------------------------------------------------
// Token budget
// ---------------------------------------------------------------------------

/// Tracks token allocation across prompt sections to stay within model limits.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TokenBudget {
    max_tokens: usize,
    allocations: HashMap<String, usize>,
}

impl TokenBudget {
    #[must_use]
    pub fn new(max_tokens: usize) -> Self {
        Self {
            max_tokens,
            allocations: HashMap::new(),
        }
    }

    /// Allocate tokens to a named section. Overwrites any previous allocation.
    ///
    /// Returns an error if the total would exceed the maximum budget.
    pub fn allocate_section(&mut self, name: &str, tokens: usize) -> Result<(), TemplateError> {
        let current_for_name = self.allocations.get(name).copied().unwrap_or(0);
        let used_by_others = self.used() - current_for_name;
        if used_by_others + tokens > self.max_tokens {
            return Err(TemplateError::BudgetExceeded {
                section: name.to_string(),
                requested: tokens,
                available: self.max_tokens.saturating_sub(used_by_others),
            });
        }
        self.allocations.insert(name.to_string(), tokens);
        Ok(())
    }

    /// Total tokens already allocated.
    #[must_use]
    pub fn used(&self) -> usize {
        self.allocations.values().sum()
    }

    /// Tokens remaining in the budget.
    #[must_use]
    pub fn remaining(&self) -> usize {
        self.max_tokens.saturating_sub(self.used())
    }

    /// Maximum token budget.
    #[must_use]
    pub fn max_tokens(&self) -> usize {
        self.max_tokens
    }

    /// Get the allocation for a named section.
    #[must_use]
    pub fn allocation(&self, name: &str) -> Option<usize> {
        self.allocations.get(name).copied()
    }
}

// ---------------------------------------------------------------------------
// Context window
// ---------------------------------------------------------------------------

/// An item with content and priority for context window packing.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ContextItem {
    content: String,
    priority: u32,
    estimated_tokens: usize,
}

/// Manages a fixed-size context window, packing items by priority.
///
/// When total tokens exceed the budget, lower-priority items are dropped first.
#[derive(Debug, Clone)]
pub struct ContextWindow {
    max_tokens: usize,
    items: Vec<ContextItem>,
}

impl ContextWindow {
    #[must_use]
    pub fn new(max_tokens: usize) -> Self {
        Self {
            max_tokens,
            items: Vec::new(),
        }
    }

    /// Add a content item with the given priority (higher = more important).
    pub fn add_item(&mut self, content: &str, priority: u32) {
        let estimated_tokens = estimate_tokens_from_chars(content.len());
        self.items.push(ContextItem {
            content: content.to_string(),
            priority,
            estimated_tokens,
        });
    }

    /// Render the context window, trimming lowest-priority items to fit.
    #[must_use]
    pub fn render(&self) -> String {
        // Sort by priority descending (highest first).
        let mut sorted: Vec<&ContextItem> = self.items.iter().collect();
        sorted.sort_by_key(|item| std::cmp::Reverse(item.priority));

        let mut result = Vec::new();
        let mut budget_remaining = self.max_tokens;

        for item in &sorted {
            if item.estimated_tokens <= budget_remaining {
                result.push(item);
                budget_remaining -= item.estimated_tokens;
            }
            // Item doesn't fit; skip it.
        }

        // Restore original insertion order among selected items.
        // Build a map from content to original index for stable ordering.
        let original_positions: HashMap<&str, usize> = self
            .items
            .iter()
            .enumerate()
            .map(|(i, item)| (item.content.as_str(), i))
            .collect();

        result.sort_by_key(|item| {
            original_positions
                .get(item.content.as_str())
                .copied()
                .unwrap_or(0)
        });

        result
            .iter()
            .map(|item| item.content.as_str())
            .collect::<Vec<_>>()
            .join("\n\n")
    }

    /// Total estimated tokens of all items (before trimming).
    #[must_use]
    pub fn total_tokens(&self) -> usize {
        self.items.iter().map(|i| i.estimated_tokens).sum()
    }

    /// Number of items added.
    #[must_use]
    pub fn item_count(&self) -> usize {
        self.items.len()
    }

    #[must_use]
    pub fn max_tokens(&self) -> usize {
        self.max_tokens
    }
}

// ---------------------------------------------------------------------------
// Render result
// ---------------------------------------------------------------------------

/// The fully rendered prompt ready for LLM submission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RenderResult {
    /// Rendered sections keyed by role.
    pub sections: Vec<(PromptSection, String)>,
    /// Estimated total token count.
    pub estimated_tokens: usize,
    /// Whether the prompt was truncated to fit the budget.
    pub truncated: bool,
}

impl RenderResult {
    /// Concatenate all sections into a single string (for single-turn APIs).
    #[must_use]
    pub fn to_flat_string(&self) -> String {
        self.sections
            .iter()
            .map(|(section, text)| format!("[{}]\n{}", section, text))
            .collect::<Vec<_>>()
            .join("\n\n")
    }

    /// Get the first section matching the given role.
    #[must_use]
    pub fn get_section(&self, section: &PromptSection) -> Option<&str> {
        self.sections
            .iter()
            .find(|(s, _)| s == section)
            .map(|(_, text)| text.as_str())
    }
}

// ---------------------------------------------------------------------------
// Prompt builder
// ---------------------------------------------------------------------------

/// Fluent builder for constructing structured prompts with budget awareness.
#[derive(Debug, Clone)]
#[must_use]
pub struct PromptBuilder {
    strategy: PromptStrategy,
    system_template: Option<PromptTemplate>,
    user_template: Option<PromptTemplate>,
    context: TemplateContext,
    examples: Vec<FewShotExample>,
    budget: Option<TokenBudget>,
    context_window: Option<ContextWindow>,
}

impl PromptBuilder {
    pub fn new(strategy: PromptStrategy) -> Self {
        Self {
            strategy,
            system_template: None,
            user_template: None,
            context: TemplateContext::new(),
            examples: Vec::new(),
            budget: None,
            context_window: None,
        }
    }

    pub fn with_system(mut self, template: PromptTemplate) -> Self {
        self.system_template = Some(template);
        self
    }

    pub fn with_user(mut self, template: PromptTemplate) -> Self {
        self.user_template = Some(template);
        self
    }

    pub fn with_context(mut self, ctx: TemplateContext) -> Self {
        self.context = ctx;
        self
    }

    pub fn add_example(mut self, example: FewShotExample) -> Self {
        self.examples.push(example);
        self
    }

    pub fn with_budget(mut self, budget: TokenBudget) -> Self {
        self.budget = Some(budget);
        self
    }

    pub fn with_context_window(mut self, window: ContextWindow) -> Self {
        self.context_window = Some(window);
        self
    }

    /// Build the final prompt, rendering templates and applying budget constraints.
    pub fn build(self) -> Result<RenderResult, TemplateError> {
        let bindings = self.context.bindings();
        let mut sections: Vec<(PromptSection, String)> = Vec::new();
        let mut total_tokens: usize = 0;
        let mut truncated = false;

        let max_budget = self
            .budget
            .as_ref()
            .map_or(usize::MAX, TokenBudget::max_tokens);

        // 1. System section
        if let Some(ref tmpl) = self.system_template {
            let rendered = tmpl.render(bindings)?;
            let tokens = estimate_tokens_from_chars(rendered.len());
            total_tokens += tokens;
            sections.push((PromptSection::System, rendered));
        }

        // 2. Strategy preamble (chain-of-thought / react instructions)
        match &self.strategy {
            PromptStrategy::ChainOfThought => {
                let cot = "Think step by step. Show your reasoning before giving the final answer.";
                let tokens = estimate_tokens_from_chars(cot.len());
                total_tokens += tokens;
                sections.push((PromptSection::System, cot.to_string()));
            }
            PromptStrategy::ReAct => {
                let react = "Use the following loop:\n\
                    Thought: reason about what to do next\n\
                    Action: take an action\n\
                    Observation: observe the result\n\
                    Repeat until you have the final answer.";
                let tokens = estimate_tokens_from_chars(react.len());
                total_tokens += tokens;
                sections.push((PromptSection::System, react.to_string()));
            }
            _ => {}
        }

        // 3. Examples (few-shot from strategy + builder-added)
        let all_examples = match &self.strategy {
            PromptStrategy::FewShot { examples } => {
                let mut merged = examples.clone();
                merged.extend(self.examples.clone());
                merged
            }
            _ => self.examples.clone(),
        };

        for ex in &all_examples {
            let ex_tokens = ex.estimated_tokens();
            if total_tokens + ex_tokens > max_budget {
                truncated = true;
                break;
            }
            let mut example_text = format!("Input:\n{}\n\nOutput:\n{}", ex.input, ex.output);
            if let Some(ref explanation) = ex.explanation {
                example_text.push_str(&format!("\n\nExplanation:\n{}", explanation));
            }
            total_tokens += ex_tokens;
            sections.push((PromptSection::Example, example_text));
        }

        // 4. Context window content
        if let Some(ref window) = self.context_window {
            let rendered_context = window.render();
            if !rendered_context.is_empty() {
                let tokens = estimate_tokens_from_chars(rendered_context.len());
                if total_tokens + tokens > max_budget {
                    truncated = true;
                } else {
                    total_tokens += tokens;
                    sections.push((PromptSection::User, rendered_context));
                }
            }
        }

        // 5. User section
        if let Some(ref tmpl) = self.user_template {
            let rendered = tmpl.render(bindings)?;
            let tokens = estimate_tokens_from_chars(rendered.len());
            if total_tokens + tokens > max_budget {
                truncated = true;
                // Truncate to fit remaining budget
                let available_chars = max_budget.saturating_sub(total_tokens) * 4;
                let truncated_text: String = rendered.chars().take(available_chars).collect();
                total_tokens += estimate_tokens_from_chars(truncated_text.len());
                sections.push((PromptSection::User, truncated_text));
            } else {
                total_tokens += tokens;
                sections.push((PromptSection::User, rendered));
            }
        }

        Ok(RenderResult {
            sections,
            estimated_tokens: total_tokens,
            truncated,
        })
    }
}

// ---------------------------------------------------------------------------
// Template library
// ---------------------------------------------------------------------------

/// A collection of named prompt templates for various verification tasks.
#[derive(Debug, Clone, Default)]
pub struct TemplateLibrary {
    templates: HashMap<String, PromptTemplate>,
}

impl TemplateLibrary {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Load the built-in trust_vc proof synthesis templates.
    #[must_use]
    pub fn load_builtin() -> Self {
        let mut lib = Self::new();

        // Precondition synthesis
        lib.add(
            PromptTemplate::new(
                "precondition_synthesis",
                "Given the following Rust function:\n\n```rust\n{{source}}\n```\n\n\
                 Propose preconditions (requires! clauses) that prevent undefined behavior \
                 and ensure the function's correctness.",
            )
            .with_variable(TemplateVariable::new(
                "source",
                "Rust function source code",
                true,
            ))
            .with_task("precondition")
            .with_task("synthesis"),
        );

        // Postcondition synthesis
        lib.add(
            PromptTemplate::new(
                "postcondition_synthesis",
                "Given the following Rust function:\n\n```rust\n{{source}}\n```\n\n\
                 Propose postconditions (ensures! clauses) that describe \
                 what the function guarantees about its return value.",
            )
            .with_variable(TemplateVariable::new(
                "source",
                "Rust function source code",
                true,
            ))
            .with_task("postcondition")
            .with_task("synthesis"),
        );

        // Loop invariant synthesis
        lib.add(
            PromptTemplate::new(
                "loop_invariant_synthesis",
                "Given the following Rust function with loops:\n\n```rust\n{{source}}\n```\n\n\
                 Propose loop invariants (invariant! clauses) that hold at every iteration \
                 and help establish the postcondition.{{hint}}",
            )
            .with_variable(TemplateVariable::new(
                "source",
                "Rust function source code",
                true,
            ))
            .with_variable(
                TemplateVariable::new("hint", "Optional hint about the loop pattern", false)
                    .with_default(""),
            )
            .with_task("invariant")
            .with_task("synthesis"),
        );

        // Counterexample-guided refinement
        lib.add(
            PromptTemplate::new(
                "refinement",
                "The verifier rejected the following specification:\n\n\
                 {{previous_spec}}\n\n\
                 Counterexample: {{counterexample}}\n\n\
                 Refine the specification to exclude this counterexample \
                 while preserving as much precision as possible.",
            )
            .with_variable(TemplateVariable::new(
                "previous_spec",
                "The rejected specification",
                true,
            ))
            .with_variable(TemplateVariable::new(
                "counterexample",
                "Concrete counterexample values",
                true,
            ))
            .with_task("refinement"),
        );

        // Full annotation synthesis
        lib.add(
            PromptTemplate::new(
                "full_annotation",
                "Analyze the following Rust function and propose a complete formal specification \
                 including preconditions, postconditions, and loop invariants as needed.\n\n\
                 ```rust\n{{source}}\n```\n\n\
                 Context: {{context}}",
            )
            .with_variable(TemplateVariable::new(
                "source",
                "Rust function source code",
                true,
            ))
            .with_variable(
                TemplateVariable::new("context", "Additional context about the function", false)
                    .with_default("No additional context provided."),
            )
            .with_task("precondition")
            .with_task("postcondition")
            .with_task("invariant")
            .with_task("synthesis"),
        );

        lib
    }

    /// Add a template to the library. Overwrites any existing template with the same name.
    pub fn add(&mut self, template: PromptTemplate) {
        self.templates.insert(template.name.clone(), template);
    }

    /// Retrieve a template by name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&PromptTemplate> {
        self.templates.get(name)
    }

    /// List all template names applicable to the given task.
    #[must_use]
    pub fn list_for_task(&self, task: &str) -> Vec<&str> {
        self.templates
            .values()
            .filter(|t| t.applicable_tasks.iter().any(|at| at == task))
            .map(|t| t.name.as_str())
            .collect()
    }

    /// List all template names in the library.
    #[must_use]
    pub fn list_all(&self) -> Vec<&str> {
        self.templates.keys().map(String::as_str).collect()
    }

    /// Number of templates in the library.
    #[must_use]
    pub fn len(&self) -> usize {
        self.templates.len()
    }

    /// Whether the library is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.templates.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors that can occur during template rendering and budget management.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum TemplateError {
    /// A required variable was not provided and has no default.
    #[error("template '{template}': required variable '{variable}' not provided")]
    MissingVariable { template: String, variable: String },
    /// Token budget would be exceeded by the requested allocation.
    #[error("section '{section}': requested {requested} tokens but only {available} available")]
    BudgetExceeded {
        section: String,
        requested: usize,
        available: usize,
    },
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Rough token estimate: ~4 characters per token (GPT-family heuristic).
#[must_use]
fn estimate_tokens_from_chars(chars: usize) -> usize {
    chars.div_ceil(4)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- TemplateVariable ---------------------------------------------------

    #[test]
    fn test_template_variable_new_required() {
        let v = TemplateVariable::new("source", "Source code", true);
        assert_eq!(v.name, "source");
        assert_eq!(v.description, "Source code");
        assert!(v.required);
        assert!(v.default_value.is_none());
    }

    #[test]
    fn test_template_variable_with_default() {
        let v = TemplateVariable::new("hint", "Hint", false).with_default("none");
        assert!(!v.required);
        assert_eq!(v.default_value.as_deref(), Some("none"));
    }

    // -- PromptTemplate -----------------------------------------------------

    #[test]
    fn test_template_render_basic_substitution() {
        let tmpl = PromptTemplate::new("test", "Hello, {{name}}!")
            .with_variable(TemplateVariable::new("name", "name", true));
        let mut bindings = HashMap::new();
        bindings.insert("name".to_string(), "world".to_string());
        let result = tmpl.render(&bindings).expect("render should succeed");
        assert_eq!(result, "Hello, world!");
    }

    #[test]
    fn test_template_render_multiple_variables() {
        let tmpl = PromptTemplate::new("test", "{{greeting}}, {{name}}!")
            .with_variable(TemplateVariable::new("greeting", "greeting", true))
            .with_variable(TemplateVariable::new("name", "name", true));
        let mut bindings = HashMap::new();
        bindings.insert("greeting".to_string(), "Hi".to_string());
        bindings.insert("name".to_string(), "Alice".to_string());
        let result = tmpl.render(&bindings).expect("render should succeed");
        assert_eq!(result, "Hi, Alice!");
    }

    #[test]
    fn test_template_render_missing_required_variable_returns_error() {
        let tmpl = PromptTemplate::new("test", "{{name}}")
            .with_variable(TemplateVariable::new("name", "name", true));
        let bindings = HashMap::new();
        let err = tmpl.render(&bindings).unwrap_err();
        assert_eq!(
            err,
            TemplateError::MissingVariable {
                template: "test".to_string(),
                variable: "name".to_string(),
            }
        );
    }

    #[test]
    fn test_template_render_optional_missing_becomes_empty() {
        let tmpl = PromptTemplate::new("test", "A{{opt}}B")
            .with_variable(TemplateVariable::new("opt", "optional", false));
        let bindings = HashMap::new();
        let result = tmpl.render(&bindings).expect("render should succeed");
        assert_eq!(result, "AB");
    }

    #[test]
    fn test_template_render_default_value_used() {
        let tmpl = PromptTemplate::new("test", "Mode: {{mode}}")
            .with_variable(TemplateVariable::new("mode", "mode", false).with_default("strict"));
        let bindings = HashMap::new();
        let result = tmpl.render(&bindings).expect("render should succeed");
        assert_eq!(result, "Mode: strict");
    }

    #[test]
    fn test_template_render_explicit_overrides_default() {
        let tmpl = PromptTemplate::new("test", "Mode: {{mode}}")
            .with_variable(TemplateVariable::new("mode", "mode", false).with_default("strict"));
        let mut bindings = HashMap::new();
        bindings.insert("mode".to_string(), "lenient".to_string());
        let result = tmpl.render(&bindings).expect("render should succeed");
        assert_eq!(result, "Mode: lenient");
    }

    #[test]
    fn test_template_with_task() {
        let tmpl = PromptTemplate::new("t", "text")
            .with_task("synthesis")
            .with_task("refinement");
        assert_eq!(tmpl.applicable_tasks, vec!["synthesis", "refinement"]);
    }

    // -- TemplateContext -----------------------------------------------------

    #[test]
    fn test_context_set_and_get() {
        let mut ctx = TemplateContext::new();
        ctx.set("key", "value");
        assert_eq!(ctx.get("key"), Some("value"));
    }

    #[test]
    fn test_context_overwrite() {
        let mut ctx = TemplateContext::new();
        ctx.set("key", "v1");
        ctx.set("key", "v2");
        assert_eq!(ctx.get("key"), Some("v2"));
    }

    #[test]
    fn test_context_missing_returns_none() {
        let ctx = TemplateContext::new();
        assert_eq!(ctx.get("nonexistent"), None);
    }

    #[test]
    fn test_context_len_and_is_empty() {
        let mut ctx = TemplateContext::new();
        assert!(ctx.is_empty());
        assert_eq!(ctx.len(), 0);
        ctx.set("a", "1");
        assert!(!ctx.is_empty());
        assert_eq!(ctx.len(), 1);
    }

    // -- FewShotExample -----------------------------------------------------

    #[test]
    fn test_few_shot_example_basic() {
        let ex = FewShotExample::new("fn f() {}", "ENSURES: true");
        assert_eq!(ex.input, "fn f() {}");
        assert_eq!(ex.output, "ENSURES: true");
        assert!(ex.explanation.is_none());
    }

    #[test]
    fn test_few_shot_example_with_explanation() {
        let ex =
            FewShotExample::new("fn f() {}", "ENSURES: true").with_explanation("Trivial case.");
        assert_eq!(ex.explanation.as_deref(), Some("Trivial case."));
    }

    #[test]
    fn test_few_shot_example_estimated_tokens() {
        let ex = FewShotExample::new("abcd", "efgh"); // 8 chars total
        assert_eq!(ex.estimated_tokens(), 2); // ceil(8/4) = 2
    }

    // -- PromptStrategy -----------------------------------------------------

    #[test]
    fn test_strategy_zero_shot() {
        let s = PromptStrategy::ZeroShot;
        assert_eq!(s, PromptStrategy::ZeroShot);
    }

    #[test]
    fn test_strategy_few_shot_factory() {
        let examples = vec![FewShotExample::new("in", "out")];
        let s = PromptStrategy::few_shot(examples.clone());
        match s {
            PromptStrategy::FewShot { examples: ex } => assert_eq!(ex.len(), 1),
            _ => panic!("expected FewShot variant"),
        }
    }

    // -- TokenBudget --------------------------------------------------------

    #[test]
    fn test_budget_new_full_remaining() {
        let b = TokenBudget::new(1000);
        assert_eq!(b.max_tokens(), 1000);
        assert_eq!(b.remaining(), 1000);
        assert_eq!(b.used(), 0);
    }

    #[test]
    fn test_budget_allocate_and_remaining() {
        let mut b = TokenBudget::new(1000);
        b.allocate_section("system", 300)
            .expect("allocation should succeed");
        assert_eq!(b.used(), 300);
        assert_eq!(b.remaining(), 700);
        assert_eq!(b.allocation("system"), Some(300));
    }

    #[test]
    fn test_budget_multiple_allocations() {
        let mut b = TokenBudget::new(1000);
        b.allocate_section("system", 300).unwrap();
        b.allocate_section("user", 500).unwrap();
        assert_eq!(b.used(), 800);
        assert_eq!(b.remaining(), 200);
    }

    #[test]
    fn test_budget_overwrite_allocation() {
        let mut b = TokenBudget::new(1000);
        b.allocate_section("system", 300).unwrap();
        b.allocate_section("system", 200).unwrap(); // shrink
        assert_eq!(b.used(), 200);
        assert_eq!(b.remaining(), 800);
    }

    #[test]
    fn test_budget_exceeded_returns_error() {
        let mut b = TokenBudget::new(100);
        b.allocate_section("system", 80).unwrap();
        let err = b.allocate_section("user", 30).unwrap_err();
        assert_eq!(
            err,
            TemplateError::BudgetExceeded {
                section: "user".to_string(),
                requested: 30,
                available: 20,
            }
        );
    }

    #[test]
    fn test_budget_allocation_missing_returns_none() {
        let b = TokenBudget::new(1000);
        assert_eq!(b.allocation("nonexistent"), None);
    }

    // -- ContextWindow ------------------------------------------------------

    #[test]
    fn test_context_window_single_item() {
        let mut w = ContextWindow::new(1000);
        w.add_item("Hello", 1);
        assert_eq!(w.item_count(), 1);
        assert_eq!(w.render(), "Hello");
    }

    #[test]
    fn test_context_window_priority_trimming() {
        // Each char is ~0.25 tokens. Budget of 3 tokens = ~12 chars.
        let mut w = ContextWindow::new(3);
        w.add_item("low priority", 1); // ~3 tokens
        w.add_item("hi", 10); // ~1 token
        let rendered = w.render();
        // "hi" fits (1 token), "low priority" does not fit in remaining 2 tokens (3 tokens)
        // Actually: "low priority" = 12 chars = ceil(12/4)=3 tokens, "hi" = 2 chars = ceil(2/4)=1 token.
        // Budget is 3. "hi" (priority 10) gets in first: 1 token used, 2 remaining.
        // "low priority" needs 3 tokens, only 2 remaining => dropped.
        assert!(rendered.contains("hi"));
        assert!(!rendered.contains("low priority"));
    }

    #[test]
    fn test_context_window_preserves_insertion_order() {
        let mut w = ContextWindow::new(10000);
        w.add_item("first", 1);
        w.add_item("second", 2);
        w.add_item("third", 3);
        let rendered = w.render();
        let first_pos = rendered.find("first").expect("should contain 'first'");
        let second_pos = rendered.find("second").expect("should contain 'second'");
        let third_pos = rendered.find("third").expect("should contain 'third'");
        assert!(first_pos < second_pos);
        assert!(second_pos < third_pos);
    }

    #[test]
    fn test_context_window_empty() {
        let w = ContextWindow::new(1000);
        assert_eq!(w.render(), "");
        assert_eq!(w.item_count(), 0);
        assert_eq!(w.total_tokens(), 0);
    }

    #[test]
    fn test_context_window_total_tokens() {
        let mut w = ContextWindow::new(1000);
        w.add_item("abcdefgh", 1); // 8 chars = 2 tokens
        w.add_item("ijkl", 2); // 4 chars = 1 token
        assert_eq!(w.total_tokens(), 3);
    }

    // -- RenderResult -------------------------------------------------------

    #[test]
    fn test_render_result_to_flat_string() {
        let rr = RenderResult {
            sections: vec![
                (PromptSection::System, "You are a verifier.".to_string()),
                (PromptSection::User, "Verify this.".to_string()),
            ],
            estimated_tokens: 10,
            truncated: false,
        };
        let flat = rr.to_flat_string();
        assert!(flat.contains("[system]"));
        assert!(flat.contains("You are a verifier."));
        assert!(flat.contains("[user]"));
        assert!(flat.contains("Verify this."));
    }

    #[test]
    fn test_render_result_get_section() {
        let rr = RenderResult {
            sections: vec![
                (PromptSection::System, "sys".to_string()),
                (PromptSection::User, "usr".to_string()),
            ],
            estimated_tokens: 2,
            truncated: false,
        };
        assert_eq!(rr.get_section(&PromptSection::System), Some("sys"));
        assert_eq!(rr.get_section(&PromptSection::User), Some("usr"));
        assert_eq!(rr.get_section(&PromptSection::Assistant), None);
    }

    // -- PromptBuilder ------------------------------------------------------

    #[test]
    fn test_builder_zero_shot_minimal() {
        let result = PromptBuilder::new(PromptStrategy::ZeroShot)
            .build()
            .expect("build should succeed");
        assert!(result.sections.is_empty());
        assert_eq!(result.estimated_tokens, 0);
        assert!(!result.truncated);
    }

    #[test]
    fn test_builder_with_system_template() {
        let tmpl = PromptTemplate::new("sys", "You are an expert.");
        let result = PromptBuilder::new(PromptStrategy::ZeroShot)
            .with_system(tmpl)
            .build()
            .expect("build should succeed");
        assert_eq!(result.sections.len(), 1);
        assert_eq!(
            result.get_section(&PromptSection::System),
            Some("You are an expert.")
        );
    }

    #[test]
    fn test_builder_with_variables() {
        let tmpl = PromptTemplate::new("sys", "Analyze: {{source}}")
            .with_variable(TemplateVariable::new("source", "code", true));
        let mut ctx = TemplateContext::new();
        ctx.set("source", "fn main() {}");
        let result = PromptBuilder::new(PromptStrategy::ZeroShot)
            .with_system(tmpl)
            .with_context(ctx)
            .build()
            .expect("build should succeed");
        assert_eq!(
            result.get_section(&PromptSection::System),
            Some("Analyze: fn main() {}")
        );
    }

    #[test]
    fn test_builder_missing_variable_propagates_error() {
        let tmpl = PromptTemplate::new("sys", "{{required_var}}")
            .with_variable(TemplateVariable::new("required_var", "needed", true));
        let err = PromptBuilder::new(PromptStrategy::ZeroShot)
            .with_system(tmpl)
            .build()
            .unwrap_err();
        match err {
            TemplateError::MissingVariable { variable, .. } => {
                assert_eq!(variable, "required_var");
            }
            other => panic!("expected MissingVariable, got {:?}", other),
        }
    }

    #[test]
    fn test_builder_chain_of_thought_adds_instruction() {
        let result = PromptBuilder::new(PromptStrategy::ChainOfThought)
            .build()
            .expect("build should succeed");
        let system_sections: Vec<_> = result
            .sections
            .iter()
            .filter(|(s, _)| *s == PromptSection::System)
            .collect();
        assert_eq!(system_sections.len(), 1);
        assert!(system_sections[0].1.contains("step by step"));
    }

    #[test]
    fn test_builder_react_adds_instruction() {
        let result = PromptBuilder::new(PromptStrategy::ReAct)
            .build()
            .expect("build should succeed");
        let has_react = result
            .sections
            .iter()
            .any(|(_, text)| text.contains("Thought:") && text.contains("Action:"));
        assert!(has_react);
    }

    #[test]
    fn test_builder_few_shot_includes_examples() {
        let examples = vec![FewShotExample::new(
            "fn abs(x: i32) -> i32",
            "ENSURES: result >= 0",
        )];
        let result = PromptBuilder::new(PromptStrategy::few_shot(examples))
            .build()
            .expect("build should succeed");
        let example_sections: Vec<_> = result
            .sections
            .iter()
            .filter(|(s, _)| *s == PromptSection::Example)
            .collect();
        assert_eq!(example_sections.len(), 1);
        assert!(example_sections[0].1.contains("fn abs"));
        assert!(example_sections[0].1.contains("ENSURES: result >= 0"));
    }

    #[test]
    fn test_builder_add_example_appended() {
        let result = PromptBuilder::new(PromptStrategy::ZeroShot)
            .add_example(FewShotExample::new("input1", "output1"))
            .add_example(FewShotExample::new("input2", "output2"))
            .build()
            .expect("build should succeed");
        let example_sections: Vec<_> = result
            .sections
            .iter()
            .filter(|(s, _)| *s == PromptSection::Example)
            .collect();
        assert_eq!(example_sections.len(), 2);
    }

    #[test]
    fn test_builder_with_budget_truncates_examples() {
        // Create a tight budget that can fit the system but not all examples.
        let budget = TokenBudget::new(5); // very small
        let result = PromptBuilder::new(PromptStrategy::ZeroShot)
            .add_example(FewShotExample::new(
                "a]very long input that exceeds the budget by a lot of tokens",
                "a very long output that also takes many tokens to represent",
            ))
            .with_budget(budget)
            .build()
            .expect("build should succeed");
        assert!(result.truncated);
    }

    #[test]
    fn test_builder_with_context_window() {
        let mut window = ContextWindow::new(10000);
        window.add_item("Important context", 10);
        let result = PromptBuilder::new(PromptStrategy::ZeroShot)
            .with_context_window(window)
            .build()
            .expect("build should succeed");
        let user_text = result.get_section(&PromptSection::User);
        assert!(user_text.is_some());
        assert!(user_text.unwrap().contains("Important context"));
    }

    #[test]
    fn test_builder_user_template_rendered() {
        let tmpl = PromptTemplate::new("user", "Please verify: {{task}}")
            .with_variable(TemplateVariable::new("task", "task description", true));
        let mut ctx = TemplateContext::new();
        ctx.set("task", "check overflow");
        let result = PromptBuilder::new(PromptStrategy::ZeroShot)
            .with_user(tmpl)
            .with_context(ctx)
            .build()
            .expect("build should succeed");
        let found = result
            .sections
            .iter()
            .any(|(s, t)| *s == PromptSection::User && t == "Please verify: check overflow");
        assert!(found);
    }

    // -- TemplateLibrary ----------------------------------------------------

    #[test]
    fn test_library_load_builtin_nonempty() {
        let lib = TemplateLibrary::load_builtin();
        assert!(!lib.is_empty());
        assert!(lib.len() >= 5);
    }

    #[test]
    fn test_library_get_existing() {
        let lib = TemplateLibrary::load_builtin();
        let tmpl = lib.get("precondition_synthesis");
        assert!(tmpl.is_some());
        assert_eq!(tmpl.unwrap().name, "precondition_synthesis");
    }

    #[test]
    fn test_library_get_missing_returns_none() {
        let lib = TemplateLibrary::load_builtin();
        assert!(lib.get("nonexistent_template").is_none());
    }

    #[test]
    fn test_library_list_for_task_synthesis() {
        let lib = TemplateLibrary::load_builtin();
        let names = lib.list_for_task("synthesis");
        assert!(!names.is_empty());
        assert!(names.contains(&"precondition_synthesis"));
        assert!(names.contains(&"postcondition_synthesis"));
    }

    #[test]
    fn test_library_list_for_task_refinement() {
        let lib = TemplateLibrary::load_builtin();
        let names = lib.list_for_task("refinement");
        assert!(names.contains(&"refinement"));
    }

    #[test]
    fn test_library_list_for_task_unknown_returns_empty() {
        let lib = TemplateLibrary::load_builtin();
        let names = lib.list_for_task("nonexistent_task");
        assert!(names.is_empty());
    }

    #[test]
    fn test_library_add_custom_template() {
        let mut lib = TemplateLibrary::new();
        lib.add(PromptTemplate::new("custom", "Hello!").with_task("custom_task"));
        assert_eq!(lib.len(), 1);
        assert!(lib.get("custom").is_some());
        assert!(lib.list_for_task("custom_task").contains(&"custom"));
    }

    #[test]
    fn test_library_overwrite_template() {
        let mut lib = TemplateLibrary::new();
        lib.add(PromptTemplate::new("t", "v1"));
        lib.add(PromptTemplate::new("t", "v2"));
        assert_eq!(lib.len(), 1);
        assert_eq!(lib.get("t").unwrap().text, "v2");
    }

    #[test]
    fn test_library_list_all() {
        let lib = TemplateLibrary::load_builtin();
        let all = lib.list_all();
        assert!(all.len() >= 5);
    }

    // -- TemplateError display ----------------------------------------------

    #[test]
    fn test_error_display_missing_variable() {
        let e = TemplateError::MissingVariable {
            template: "my_tmpl".to_string(),
            variable: "x".to_string(),
        };
        let msg = format!("{}", e);
        assert!(msg.contains("my_tmpl"));
        assert!(msg.contains("x"));
        assert!(msg.contains("not provided"));
    }

    #[test]
    fn test_error_display_budget_exceeded() {
        let e = TemplateError::BudgetExceeded {
            section: "user".to_string(),
            requested: 500,
            available: 100,
        };
        let msg = format!("{}", e);
        assert!(msg.contains("500"));
        assert!(msg.contains("100"));
    }

    // -- estimate_tokens_from_chars -----------------------------------------

    #[test]
    fn test_estimate_tokens_empty() {
        assert_eq!(estimate_tokens_from_chars(0), 0);
    }

    #[test]
    fn test_estimate_tokens_exact_multiple() {
        assert_eq!(estimate_tokens_from_chars(8), 2);
    }

    #[test]
    fn test_estimate_tokens_rounds_up() {
        assert_eq!(estimate_tokens_from_chars(5), 2); // ceil(5/4) = 2
        assert_eq!(estimate_tokens_from_chars(1), 1); // ceil(1/4) = 1
    }

    // -- PromptSection display ----------------------------------------------

    #[test]
    fn test_prompt_section_display() {
        assert_eq!(format!("{}", PromptSection::System), "system");
        assert_eq!(format!("{}", PromptSection::User), "user");
        assert_eq!(format!("{}", PromptSection::Assistant), "assistant");
        assert_eq!(format!("{}", PromptSection::Example), "example");
    }

    // -- Integration: builtin template rendering ----------------------------

    #[test]
    fn test_builtin_precondition_synthesis_renders() {
        let lib = TemplateLibrary::load_builtin();
        let tmpl = lib.get("precondition_synthesis").unwrap();
        let mut bindings = HashMap::new();
        bindings.insert(
            "source".to_string(),
            "fn add(a: u32, b: u32) -> u32 { a + b }".to_string(),
        );
        let rendered = tmpl.render(&bindings).expect("render should succeed");
        assert!(rendered.contains("fn add(a: u32, b: u32)"));
        assert!(rendered.contains("preconditions"));
    }

    #[test]
    fn test_builtin_loop_invariant_default_hint() {
        let lib = TemplateLibrary::load_builtin();
        let tmpl = lib.get("loop_invariant_synthesis").unwrap();
        let mut bindings = HashMap::new();
        bindings.insert(
            "source".to_string(),
            "fn sum(n: u32) -> u32 { let mut s = 0; for i in 0..n { s += i; } s }".to_string(),
        );
        let rendered = tmpl.render(&bindings).expect("render should succeed");
        assert!(rendered.contains("fn sum"));
        // hint defaults to empty, so no leftover placeholder
        assert!(!rendered.contains("{{hint}}"));
    }

    #[test]
    fn test_end_to_end_few_shot_build() {
        let lib = TemplateLibrary::load_builtin();
        let system = lib.get("precondition_synthesis").unwrap().clone();
        let mut ctx = TemplateContext::new();
        ctx.set("source", "fn div(a: i32, b: i32) -> i32 { a / b }");

        let examples = vec![FewShotExample::new(
            "fn abs(x: i32) -> i32 { if x < 0 { -x } else { x } }",
            "REQUIRES: x != i32::MIN\nENSURES: result >= 0",
        )];

        let result = PromptBuilder::new(PromptStrategy::few_shot(examples))
            .with_system(system)
            .with_context(ctx)
            .build()
            .expect("build should succeed");

        assert!(!result.truncated);
        assert!(result.estimated_tokens > 0);
        // Should have system section + example section
        let has_system = result
            .sections
            .iter()
            .any(|(s, _)| *s == PromptSection::System);
        let has_example = result
            .sections
            .iter()
            .any(|(s, _)| *s == PromptSection::Example);
        assert!(has_system);
        assert!(has_example);
    }
}
