//! Measure parsing, validation, and type inference helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracted from decreases_runtime.rs as part of #2010.

use std::fmt::Write as _;

use crate::vc::VerificationContext;

/// Returns true if the string is a valid decreases measure component.
/// Rejects empty strings and pure numeric literals.
/// Allows identifiers, field access (x.len), and expressions (n - 1).
pub(crate) fn is_valid_measure_component(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    // Reject pure numeric literals (e.g., "5", "123")
    if s.chars().all(|c| c.is_ascii_digit()) {
        return false;
    }
    // Must contain at least one alphabetic or underscore character
    // (ensures it references a variable, not just operators/punctuation)
    if !s.chars().any(|c| c.is_ascii_alphabetic() || c == '_') {
        return false;
    }
    true
}

/// Sanitizes a measure expression to produce a valid, unique variable name.
///
/// Maps operators to descriptive suffixes and strips spaces to avoid collisions.
/// E.g., "x + y" -> "x_plus_y", "n" -> "n", "a - b" -> "a_minus_b".
/// A digit-leading result is prefixed so it remains a valid identifier.
pub(crate) fn sanitize_measure_name(measure: &str) -> String {
    let mut result = String::with_capacity(measure.len() * 2);
    for c in measure.chars() {
        match c {
            c if c.is_ascii_alphanumeric() || c == '_' => result.push(c),
            '+' => result.push_str("_plus_"),
            '-' => result.push_str("_minus_"),
            '*' => result.push_str("_star_"),
            '/' => result.push_str("_div_"),
            '%' => result.push_str("_mod_"),
            '(' => result.push_str("_lp_"),
            ')' => result.push_str("_rp_"),
            ' ' => {} // skip spaces to keep names compact
            _ => {
                // Encode as _uXXXX_ to guarantee uniqueness for any character
                let _ = write!(result, "_u{:04x}_", c as u32);
            }
        }
    }
    if result.starts_with(|c: char| c.is_ascii_digit()) {
        result.insert_str(0, "m_");
    }
    result
}

/// Returns the bit width for a Rust integer type, or 0 for non-BV types.
/// Delegates to `TrustVcType::bit_width()` — the canonical type→width mapping.
/// Part of #1903: eliminates duplicated string→width match table.
#[cfg(test)]
pub(crate) fn measure_type_bit_width(ty: &str) -> u32 {
    crate::ir::TrustVcType::parse_or_opaque(ty)
        .bit_width()
        .unwrap_or(0)
}

/// Infers the type of a measure expression by looking up component variable types.
///
/// For simple variables like `n`, returns `get_variable_type("n")`.
/// For expressions like `n - i`, extracts all identifiers, looks up their types,
/// and returns the **widest** match to avoid truncation in the entry variable.
/// This fixes #1726: first-match heuristic could return a narrower type when the
/// first identifier was narrower (e.g., `i: u32` before `n: u64` in `i - n`).
///
/// Returns `None` if no variable in the measure expression has a declared type.
/// Callers should skip obligation generation on `None` — the measure references
/// undeclared variables, so type inference cannot proceed (#1669, #1955).
pub(crate) fn infer_measure_type<'a>(
    context: &'a VerificationContext,
    measure: &str,
) -> Option<&'a crate::ir::TrustVcType> {
    // Direct variable lookup — single-variable measures don't need width comparison
    if let Some(ty) = context.get_variable_type(measure) {
        return Some(ty);
    }
    // Extract all identifiers from expression and select the widest matching type.
    // For `i - n` where i: u32, n: u64, this correctly returns u64.
    let mut best_type: Option<(&crate::ir::TrustVcType, u32)> = None;
    let mut ident = String::new();
    for c in measure.chars() {
        if c.is_ascii_alphanumeric() || c == '_' {
            ident.push(c);
        } else if !ident.is_empty() {
            if let Some(ty) = context.get_variable_type(&ident) {
                let width = ty.bit_width().unwrap_or(0);
                if best_type.is_none_or(|(_, best_w)| width > best_w) {
                    best_type = Some((ty, width));
                }
            }
            ident.clear();
        }
    }
    // Check trailing identifier (e.g., last token in "n - 1" is "1", but in "a - b" is "b")
    if !ident.is_empty() {
        if let Some(ty) = context.get_variable_type(&ident) {
            let width = ty.bit_width().unwrap_or(0);
            if best_type.is_none_or(|(_, best_w)| width > best_w) {
                best_type = Some((ty, width));
            }
        }
    }
    best_type.map(|(ty, _)| ty)
}
