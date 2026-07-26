//! Rust protocol components → TLA+ spec text translation.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Converts `#[protocol]`/`#[action]`/`#[safety]`/`#[liveness]` registrations
//! into TLA+ module text and TLC configuration text for model checking.

use std::fmt::Write as _;

use crate::error::{TrustVcError, TrustVcResult};
use crate::verification_bridge::{
    ProtocolActionDef, ProtocolInvariantDef, ProtocolLivenessDef, ProtocolStateVarDef,
};

/// Translation output: TLA+ module text + TLC config text.
pub(crate) struct TranslatedProtocol {
    pub spec: String,
    pub config: String,
}

/// Translate collected protocol components into a TLA+ module and config.
///
/// Generates a complete TLA+ module with:
/// - `VARIABLE` declarations from `#[protocol]` struct fields
/// - `TypeOK` invariant bounding state variables by Rust type widths
/// - `Init` predicate setting initial values per type
/// - `Next` as disjunction of `#[action]` translations
/// - Operator definitions for `#[safety]` invariants
/// - Temporal properties from `#[liveness]` annotations
pub(crate) fn translate_protocol(
    protocol_name: &str,
    state_vars: &[&ProtocolStateVarDef],
    actions: &[ProtocolActionDef],
    invariants: &[ProtocolInvariantDef],
    liveness: &[ProtocolLivenessDef],
) -> TrustVcResult<TranslatedProtocol> {
    let mut spec = String::new();
    let mut config = String::new();

    for var in state_vars {
        if !rust_type_supported(&var.rust_type) {
            return Err(TrustVcError::Internal {
                context: "protocol translation",
                detail: format!(
                    "unsupported protocol state type '{}::{}: {}'",
                    var.protocol_name, var.field_name, var.rust_type
                ),
            });
        }
    }

    // Module header
    let _ = write!(spec, "---- MODULE {} ----\n", protocol_name);

    // VARIABLE declarations
    if !state_vars.is_empty() {
        let var_names: Vec<&str> = state_vars.iter().map(|v| v.field_name.as_str()).collect();
        let _ = write!(spec, "VARIABLE {}\n\n", var_names.join(", "));
    }

    // TypeOK: type bounds derived from Rust types
    if !state_vars.is_empty() {
        spec.push_str("TypeOK ==\n");
        let type_constraints: Vec<String> = state_vars
            .iter()
            .map(|v| {
                format!(
                    "  /\\ {} \\in {}",
                    v.field_name,
                    rust_type_to_tla_domain(&v.rust_type)
                )
            })
            .collect();
        spec.push_str(&type_constraints.join("\n"));
        spec.push_str("\n\n");
    }

    // Init predicate: default values per type
    spec.push_str("Init ==\n");
    if state_vars.is_empty() {
        spec.push_str("  TRUE\n\n");
    } else {
        let init_clauses: Vec<String> = state_vars
            .iter()
            .map(|v| {
                format!(
                    "  /\\ {} = {}",
                    v.field_name,
                    rust_type_default(&v.rust_type)
                )
            })
            .collect();
        spec.push_str(&init_clauses.join("\n"));
        spec.push_str("\n\n");
    }

    // Action operators
    for action in actions {
        let _ = write!(spec, "{} ==\n", action.name);
        let translated = translate_action_body(&action.body, state_vars).map_err(|detail| {
            TrustVcError::Internal {
                context: "protocol translation",
                detail: format!(
                    "cannot translate action '{}::{}': {}",
                    action.protocol_name, action.name, detail
                ),
            }
        })?;
        spec.push_str(&translated);
        spec.push_str("\n\n");
    }

    // Next: disjunction of all actions + stutter step
    // The stutter step (UNCHANGED all vars) prevents false deadlock reports
    // for protocols that can terminate (all actions disabled in some state).
    if actions.is_empty() {
        spec.push_str("Next == FALSE\n\n");
    } else {
        spec.push_str("Next ==\n");
        let disjuncts: Vec<String> = actions
            .iter()
            .map(|a| format!("  \\/ {}", a.name))
            .collect();
        spec.push_str(&disjuncts.join("\n"));
        // Stutter step: allow the system to remain in the current state
        if !state_vars.is_empty() {
            let var_names: Vec<&str> = state_vars.iter().map(|v| v.field_name.as_str()).collect();
            if var_names.len() == 1 {
                let _ = write!(spec, "\n  \\/ UNCHANGED {}", var_names[0]);
            } else {
                let _ = write!(spec, "\n  \\/ UNCHANGED <<{}>>", var_names.join(", "));
            }
        }
        spec.push_str("\n\n");
    }

    // Safety invariant operators
    for inv in invariants {
        let _ = write!(spec, "{} ==\n", inv.name);
        spec.push_str(&translate_invariant_body(&inv.expr, state_vars));
        spec.push_str("\n\n");
    }

    // Liveness property operators
    for prop in liveness {
        let _ = write!(spec, "{} ==\n", prop.name);
        spec.push_str(&translate_liveness_body(&prop.expr, &prop.fairness));
        spec.push_str("\n\n");
    }

    spec.push_str("====\n");

    // TLC config
    config.push_str("INIT Init\n");
    config.push_str("NEXT Next\n");
    config.push_str("INVARIANT TypeOK\n");
    for inv in invariants {
        let _ = write!(config, "INVARIANT {}\n", inv.name);
    }
    for prop in liveness {
        let _ = write!(config, "PROPERTY {}\n", prop.name);
    }

    Ok(TranslatedProtocol { spec, config })
}

/// Convert a Rust type string to a TLA+ domain expression.
///
/// Only supports the types meaningful for protocol state machines.
/// Unknown types produce an `UNSUPPORTED` comment with the raw type.
pub(super) fn rust_type_to_tla_domain(rust_type: &str) -> String {
    let trimmed = rust_type.trim();
    match trimmed {
        "bool" => "BOOLEAN".to_string(),
        "u8" => "0..255".to_string(),
        "u16" => "0..65535".to_string(),
        "u32" => "0..4294967295".to_string(),
        "u64" => "0..18446744073709551615".to_string(),
        "usize" => "0..4294967295".to_string(),
        "i8" => "-128..127".to_string(),
        "i16" => "-32768..32767".to_string(),
        "i32" => "-2147483648..2147483647".to_string(),
        "i64" => "-9223372036854775808..9223372036854775807".to_string(),
        _ if trimmed.starts_with("Option") => {
            let inner = extract_generic_arg(trimmed);
            format!("{{\"None\"}} \\union {}", rust_type_to_tla_domain(&inner))
        }
        _ => format!("{{}} \\* UNSUPPORTED: type {}", trimmed),
    }
}

fn rust_type_supported(rust_type: &str) -> bool {
    let trimmed = rust_type.trim();
    match trimmed {
        "bool" | "u8" | "u16" | "u32" | "u64" | "usize" | "i8" | "i16" | "i32" | "i64" => true,
        _ if trimmed.starts_with("Option") => rust_type_supported(&extract_generic_arg(trimmed)),
        _ => false,
    }
}

/// Extract the inner type from `Option<T>`, `Vec<T>`, etc.
fn extract_generic_arg(ty: &str) -> String {
    if let Some(start) = ty.find('<') {
        if let Some(end) = ty.rfind('>') {
            return ty[start + 1..end].trim().to_string();
        }
    }
    ty.to_string()
}

/// Default value for a Rust type in TLA+ Init predicate.
pub(super) fn rust_type_default(rust_type: &str) -> String {
    let trimmed = rust_type.trim();
    match trimmed {
        "bool" => "FALSE".to_string(),
        "u8" | "u16" | "u32" | "u64" | "usize" | "i8" | "i16" | "i32" | "i64" => "0".to_string(),
        _ if trimmed.starts_with("Option") => "\"None\"".to_string(),
        _ => format!("0 \\* UNSUPPORTED: default for type {}", trimmed),
    }
}

/// Translate a Rust action body (stringified token stream) to TLA+ action text.
///
/// Handles the core Rust→TLA+ patterns for protocol state machine transitions:
/// - `self.field = value` → `field' = value`
/// - `self.field` → `field`
/// - `==` → `=`, `!=` → #`
/// - `&&` → `/\`, `||` → `\/`
/// - `!expr` → `~expr`
/// - `true`/`false` → `TRUE`/`FALSE`
///
/// The body comes from `quote!(#block).to_string()` in the proc macro, so it's
/// a stringified Rust block with `{ ... }` delimiters.
fn translate_action_body(
    body: &str,
    state_vars: &[&ProtocolStateVarDef],
) -> Result<String, String> {
    let stripped = strip_braces(body);
    let lines = split_statements(&stripped);
    if lines.is_empty() {
        return Ok("  TRUE".to_string());
    }

    let var_names: Vec<&str> = state_vars.iter().map(|v| v.field_name.as_str()).collect();
    validate_action_lines(&lines, &var_names)?;
    let mut tla_clauses = Vec::new();

    for line in &lines {
        let translated = translate_rust_expr(line.trim(), &var_names);
        if !translated.is_empty() {
            tla_clauses.push(format!("  /\\ {}", translated));
        }
    }

    // Add UNCHANGED for vars not assigned in this action
    let assigned = find_assigned_vars(&lines, &var_names);
    let unchanged: Vec<&str> = var_names
        .iter()
        .filter(|v| !assigned.contains(v))
        .copied()
        .collect();
    if !unchanged.is_empty() {
        if unchanged.len() == 1 {
            tla_clauses.push(format!("  /\\ UNCHANGED {}", unchanged[0]));
        } else {
            tla_clauses.push(format!("  /\\ UNCHANGED <<{}>>", unchanged.join(", ")));
        }
    }

    if tla_clauses.is_empty() {
        Ok("  TRUE".to_string())
    } else {
        Ok(tla_clauses.join("\n"))
    }
}

/// Translate a safety invariant body to TLA+ invariant expression.
fn translate_invariant_body(body: &str, state_vars: &[&ProtocolStateVarDef]) -> String {
    let stripped = strip_braces(body);
    let var_names: Vec<&str> = state_vars.iter().map(|v| v.field_name.as_str()).collect();
    let translated = translate_rust_expr(stripped.trim(), &var_names);
    format!("  {}", translated)
}

/// Translate a liveness body to TLA+ temporal property.
fn translate_liveness_body(body: &str, _fairness: &str) -> String {
    let stripped = strip_braces(body);
    let trimmed = stripped.trim();
    // If the body contains a trust_vc::temporal!("...") call, extract the TLA+ text
    if let Some(tla_text) = extract_temporal_macro(trimmed) {
        return format!("  {}", tla_text);
    }
    format!("  {}", trimmed)
}

/// Extract TLA+ text from `trust_vc :: temporal ! ("...")` pattern.
pub(super) fn extract_temporal_macro(s: &str) -> Option<String> {
    let needle = "temporal";
    let pos = s.find(needle)?;
    let after = &s[pos + needle.len()..];
    // Find the string literal inside
    let quote_start = after.find('"')?;
    let rest = &after[quote_start + 1..];
    let quote_end = rest.find('"')?;
    Some(rest[..quote_end].to_string())
}

/// Strip outer braces from a stringified Rust block.
pub(super) fn strip_braces(s: &str) -> String {
    let trimmed = s.trim();
    if trimmed.starts_with('{') && trimmed.ends_with('}') {
        trimmed[1..trimmed.len() - 1].to_string()
    } else {
        trimmed.to_string()
    }
}

/// Split a Rust block into semicolon-delimited statements.
fn split_statements(s: &str) -> Vec<String> {
    s.split(';')
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect()
}

/// Translate a single Rust expression/statement to TLA+.
pub(super) fn translate_rust_expr(expr: &str, var_names: &[&str]) -> String {
    let mut result = expr.to_string();

    // Assignment: `self.field = value` → `field' = value`
    // Must be done before the general `self.field` → `field` replacement
    for var in var_names {
        let assign_pattern = format!("self . {} =", var);
        let assign_pattern_tight = format!("self.{} =", var);
        // Avoid matching `==` by checking the character after `=`
        result = replace_assignment(&result, &assign_pattern, &format!("{}' =", var));
        result = replace_assignment(&result, &assign_pattern_tight, &format!("{}' =", var));
    }

    // Field access: `self.field` → `field`
    for var in var_names {
        result = result.replace(&format!("self . {}", var), var);
        result = result.replace(&format!("self.{}", var), var);
    }

    // Operators
    result = result.replace("&&", "/\\");
    result = result.replace("||", "\\/");
    result = result.replace("!=", "#");
    result = replace_logical_not(&result);
    // Replace `==` with `=` (TLA+ equality)
    result = result.replace("==", "=");
    result = replace_word(&result, "true", "TRUE");
    result = replace_word(&result, "false", "FALSE");

    result.trim().to_string()
}

fn validate_action_lines(lines: &[String], var_names: &[&str]) -> Result<(), String> {
    let mut assigned = Vec::new();
    for line in lines {
        let lhs = assigned_var(line, var_names);
        if let Some(var) = lhs {
            if assigned.contains(&var) {
                return Err(format!(
                    "multiple assignments to state variable '{var}' in one action are unsupported"
                ));
            }
            for earlier in &assigned {
                if line_references_var(line, earlier) {
                    return Err(format!(
                        "read-after-write of state variable '{earlier}' in one action is unsupported"
                    ));
                }
            }
            assigned.push(var);
        } else {
            for earlier in &assigned {
                if line_references_var(line, earlier) {
                    return Err(format!(
                        "guard reads state variable '{earlier}' after it was assigned in the same action"
                    ));
                }
            }
        }
    }
    Ok(())
}

fn assigned_var<'a>(line: &str, var_names: &[&'a str]) -> Option<&'a str> {
    var_names.iter().copied().find(|var| {
        let tight = format!("self.{} =", var);
        let spaced = format!("self . {} =", var);
        contains_assignment(line, &tight) || contains_assignment(line, &spaced)
    })
}

fn line_references_var(line: &str, var: &str) -> bool {
    line.contains(&format!("self.{var}")) || line.contains(&format!("self . {var}"))
}

fn replace_word(s: &str, needle: &str, replacement: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut cursor = 0;
    while let Some(rel_pos) = s[cursor..].find(needle) {
        let pos = cursor + rel_pos;
        result.push_str(&s[cursor..pos]);
        let end = pos + needle.len();
        if is_word_boundary(s, pos, end) {
            result.push_str(replacement);
        } else {
            result.push_str(&s[pos..end]);
        }
        cursor = end;
    }
    result.push_str(&s[cursor..]);
    result
}

fn replace_logical_not(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'!' {
            if bytes.get(i + 1) == Some(&b'=') {
                result.push('!');
            } else {
                result.push('~');
            }
        } else {
            result.push(bytes[i] as char);
        }
        i += 1;
    }
    result
}

fn is_word_boundary(s: &str, start: usize, end: usize) -> bool {
    let before = s[..start].chars().next_back();
    let after = s[end..].chars().next();
    !before.is_some_and(is_ident_char) && !after.is_some_and(is_ident_char)
}

fn is_ident_char(c: char) -> bool {
    c == '_' || c.is_ascii_alphanumeric()
}

/// Replace assignment patterns, avoiding `==` false matches.
///
/// Matches `self.field =` but not `self.field ==`.
fn replace_assignment(s: &str, pattern: &str, replacement: &str) -> String {
    let mut result = String::new();
    let mut remaining = s;

    while let Some(pos) = remaining.find(pattern) {
        let after_pat = pos + pattern.len();
        // Check if the next char after the `=` in pattern is also `=` (i.e., `==`)
        if remaining[after_pat..].starts_with('=') {
            // This is `==`, skip it
            result.push_str(&remaining[..after_pat]);
            remaining = &remaining[after_pat..];
        } else {
            result.push_str(&remaining[..pos]);
            result.push_str(replacement);
            remaining = &remaining[after_pat..];
        }
    }
    result.push_str(remaining);
    result
}

/// Find which state variables are assigned in the action body.
fn find_assigned_vars<'a>(lines: &[String], var_names: &[&'a str]) -> Vec<&'a str> {
    var_names
        .iter()
        .filter(|&&var| {
            lines.iter().any(|line| {
                let tight = format!("self.{} =", var);
                let spaced = format!("self . {} =", var);
                contains_assignment(line, &tight) || contains_assignment(line, &spaced)
            })
        })
        .copied()
        .collect()
}

/// Check if a line contains an assignment (not `==` comparison).
fn contains_assignment(line: &str, pattern: &str) -> bool {
    if let Some(pos) = line.find(pattern) {
        let after = pos + pattern.len();
        !line[after..].starts_with('=')
    } else {
        false
    }
}

#[cfg(test)]
#[path = "translate_tests.rs"]
mod tests;
