// trust-vc-oracle — Source text indexing helpers
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::ops::Range;

use proc_macro2::LineColumn;
use syn::spanned::Spanned;

pub(super) struct SourceMap<'src> {
    source: &'src str,
    line_starts: Vec<usize>,
}

impl<'src> SourceMap<'src> {
    pub(super) fn new(source: &'src str) -> Self {
        let mut line_starts = vec![0];
        for (index, byte) in source.bytes().enumerate() {
            if byte == b'\n' {
                line_starts.push(index + 1);
            }
        }

        Self {
            source,
            line_starts,
        }
    }

    pub(super) fn byte_offset(&self, location: LineColumn) -> Option<usize> {
        let line_index = location.line.checked_sub(1)?;
        let line_start = *self.line_starts.get(line_index)?;
        let line_end = self
            .line_starts
            .get(line_index + 1)
            .copied()
            .unwrap_or(self.source.len());
        let offset = line_start.checked_add(location.column)?;
        (offset <= line_end).then_some(offset)
    }

    pub(super) fn range_for<T>(&self, node: &T) -> Option<Range<usize>>
    where
        T: Spanned + ?Sized,
    {
        let span = node.span();
        let start = self.byte_offset(span.start())?;
        let end = self.byte_offset(span.end())?;
        (start <= end).then_some(start..end)
    }

    pub(super) fn slice(&self, range: &Range<usize>) -> &'src str {
        &self.source[range.clone()]
    }
}
