// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A STRUCTURED source location for a proof obligation.
//!
//! Why this type exists at all: the obligation record carried its location as a
//! bare `Option<String>` shaped `file:line:column`, and every consumer that
//! needed a line back did string surgery on it (`rfind(':')`, `rsplitn(3, ':')`).
//! That is fine for a lane that only ever RENDERS the string, and wrong for the
//! lane this type was added for — the evidence gate cross-checks the reported
//! line against upstream Verus's own `FAILS` marker, so the line is DATA, not
//! prose, and a parse that silently returns `None` on a Windows path or a
//! colon-bearing directory would read as "no location" rather than as a bug.
//!
//! The rendered `file:line:column` spelling is preserved EXACTLY (see
//! [`SourceLocation::render`]) so the existing string consumers keep working
//! unchanged; this type is the authority and the string is derived from it,
//! never the other way round.
//!
//! FAIL-CLOSED: [`SourceLocation::from_span`] returns `None` for a span with no
//! recorded position. A synthesized token (`Span::call_site()`, which is what
//! every token a normalization pass rebuilds carries, and what `syn`'s
//! `Spanned` falls back to when a join fails) does NOT report line 0 — measured
//! against proc-macro2 1.0.107, it reports line 1 COLUMN 0, i.e. the top of the
//! file, which is exactly the kind of plausible-but-wrong line the evidence
//! gate cannot detect. The discriminator is the span's BYTE RANGE, which
//! proc-macro2 defines as `0..0` for a call-site span and for every span on a
//! backend that cannot supply one; a parsed token's range is never empty.
//! A missing location fails the gate's marker cross-check; a WRONG one could
//! pass it against the wrong statement, so guessing is never the safer default.

use proc_macro2::Span;
use std::fmt;

/// A resolved position in a source file: 1-based line, 1-based column.
///
/// `file` is optional because the extractor learns the span before it learns
/// the path in some lanes; [`SourceLocation::render`] degrades to `line:column`
/// rather than inventing a filename.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SourceLocation {
    file: Option<String>,
    line: usize,
    column: usize,
}

impl SourceLocation {
    /// A location at `line`:`column` with no file attached.
    ///
    /// Both are 1-based, matching rustc's own diagnostic convention and the
    /// `file:line:column` strings the proc-macro lane already emits.
    #[must_use]
    pub const fn new(line: usize, column: usize) -> Self {
        Self {
            file: None,
            line,
            column,
        }
    }

    /// The position `span` starts at, or `None` when the span carries none.
    ///
    /// Requires proc-macro2's `span-locations` feature (enabled workspace-wide)
    /// AND the fallback (non-proc-macro) backend, which is what every
    /// file-context lane runs under. An EMPTY byte range means "synthesized, or
    /// this backend has no positions", and a `line` of `0` is the compiler
    /// backend's no-position answer; both are rejected — see the module note on
    /// failing closed.
    #[must_use]
    pub fn from_span(span: Span) -> Option<Self> {
        if span.byte_range().is_empty() {
            return None;
        }
        let start = span.start();
        if start.line == 0 {
            return None;
        }
        Some(Self {
            file: None,
            line: start.line,
            // proc-macro2 columns are 0-based; rustc diagnostics and the
            // `file:line:column` strings already in the tree are 1-based.
            column: start.column.saturating_add(1),
        })
    }

    /// The same location with `file` attached.
    #[must_use]
    pub fn with_file(mut self, file: impl Into<String>) -> Self {
        self.file = Some(file.into());
        self
    }

    /// The same location with `file` attached only if it does not already name
    /// one. Used where a per-file default is applied to locations recorded
    /// before the path was known.
    #[must_use]
    pub fn or_file(mut self, file: &str) -> Self {
        if self.file.is_none() {
            self.file = Some(file.to_string());
        }
        self
    }

    /// The file this location names, when known.
    #[must_use]
    pub fn file(&self) -> Option<&str> {
        self.file.as_deref()
    }

    /// The 1-based line.
    #[must_use]
    pub const fn line(&self) -> usize {
        self.line
    }

    /// The 1-based column.
    #[must_use]
    pub const fn column(&self) -> usize {
        self.column
    }

    /// The `file:line:column` rendering consumed by the diagnostic string
    /// channel (`ProofObligation::location`), or `line:column` with no file.
    #[must_use]
    pub fn render(&self) -> String {
        match &self.file {
            Some(file) => format!("{file}:{}:{}", self.line, self.column),
            None => format!("{}:{}", self.line, self.column),
        }
    }
}

impl fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.render())
    }
}

#[cfg(test)]
#[path = "source_location_tests.rs"]
mod tests;
