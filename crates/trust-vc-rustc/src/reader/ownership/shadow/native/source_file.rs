//! One actual parsed source allocation per fresh native transaction.
//!
//! This is byte/allocation correspondence data, never ownership permission.
//! Consumers still need their current AST/HIR/owner/type/role joins.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};

use rustc_span::source_map::SourceMap;
use rustc_span::{FileName, SourceFile, Span};

pub(super) struct ParsedSource<'a> {
    file: &'a SourceFile,
}

impl<'a> ParsedSource<'a> {
    pub(super) fn new(
        file: &'a SourceFile,
        path: &Path,
        emitted: &str,
        comparisons: &AtomicUsize,
    ) -> Result<Self, String> {
        if !matches!(&file.name, FileName::Real(name) if name.local_path() == Some(path)) {
            return Err(
                "the fresh AST was not parsed from the exact generated native program".into(),
            );
        }
        let source = file
            .src
            .as_ref()
            .ok_or("the actual parser source bytes are unavailable")?;
        // Transaction-local observation data, never a work credit or admission
        // predicate. Native driver pool callbacks may run on another thread.
        comparisons.fetch_add(1, Ordering::Relaxed);
        if source.as_bytes() != emitted.as_bytes() {
            return Err(
                "the fresh AST was not parsed from the exact generated native program".into(),
            );
        }
        Ok(Self { file })
    }

    pub(super) fn range(
        &self,
        source_map: &SourceMap,
        span: Span,
    ) -> Result<(usize, usize), String> {
        if !self.file.contains(span.lo()) || !self.file.contains(span.hi()) {
            return Err("a native source span crosses the validated parser allocation".into());
        }
        let current = source_map.lookup_source_file(span.lo());
        if !std::ptr::eq(current.as_ref(), self.file) {
            return Err("a native source span belongs to another actual parser allocation".into());
        }
        Ok((
            (span.lo().0 - self.file.start_pos.0) as usize,
            (span.hi().0 - self.file.start_pos.0) as usize,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_span::source_map::FilePathMapping;
    use rustc_span::BytePos;

    #[test]
    fn equal_path_and_bytes_in_another_native_allocation_do_not_join() {
        let path = Path::new("/native-source-allocation-control.rs");
        let text = "fn original() {}\n";
        let original_map = SourceMap::new(FilePathMapping::empty());
        let filename = FilePathMapping::empty().to_real_filename(original_map.working_dir(), path);
        let original = original_map.new_source_file(FileName::Real(filename.clone()), text.into());
        let comparisons = AtomicUsize::new(0);
        let parsed = ParsedSource::new(&original, path, text, &comparisons).unwrap();
        let span = Span::with_root_ctxt(
            original.start_pos,
            original.start_pos + BytePos(text.len() as u32),
        );
        assert_eq!(parsed.range(&original_map, span).unwrap(), (0, text.len()));
        let other_map = SourceMap::new(FilePathMapping::empty());
        let other = other_map.new_source_file(FileName::Real(filename), text.into());
        assert_eq!(original.start_pos, other.start_pos);
        assert!(!std::ptr::eq(original.as_ref(), other.as_ref()));
        assert!(parsed
            .range(&other_map, span)
            .unwrap_err()
            .starts_with("a native source span belongs to another actual parser allocation"));
        assert_eq!(comparisons.load(Ordering::Relaxed), 1);
    }
}
