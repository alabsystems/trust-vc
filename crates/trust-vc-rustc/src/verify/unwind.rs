// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An unwind failure requires its complete original source presentation.

use super::*;
use trust_vc_vcir::UnwindSpec;

pub(super) const SOURCE_TAG: &str = "unwind-diagnostic-source";

#[derive(Debug)]
pub(super) struct SourceError(pub(super) &'static str);

fn source_span(read: &CrateRead, id: SpanId, detail: &'static str) -> Result<Span, SourceError> {
    read.span(id)
        .filter(|span| !span.is_dummy())
        .ok_or(SourceError(detail))
}

/// A refusal can lack a location; it must not become a partial user failure.
pub(super) fn source_anchor(read: &CrateRead, decl: &FnDecl, check: &Check) -> Span {
    read.span(check_span(check))
        .filter(|span| !span.is_dummy())
        .or_else(|| read.span(decl.span).filter(|span| !span.is_dummy()))
        .unwrap_or(rustc_span::DUMMY_SP)
}

pub(super) fn failure(
    read: &CrateRead,
    caller: &FnDecl,
    call: SpanId,
    callee: FnId,
) -> Result<Failure, SourceError> {
    let target = read
        .krate
        .fn_decl(callee)
        .ok_or(SourceError("the unwind failure has no callee declaration"))?;
    let at = source_span(read, call, "the unwind failure has no original call span")?;
    let first = match caller.unwind_spec() {
        UnwindSpec::NoUnwind => format!("call to {} might unwind", target.name),
        UnwindSpec::NoUnwindWhen(_) => "this call might unwind".into(),
        UnwindSpec::MayUnwind => {
            return Err(SourceError(
                "an unwind failure has no caller no-unwind promise",
            ));
        }
    };
    let second = match target.unwind_spec() {
        UnwindSpec::NoUnwindWhen(condition) => (
            source_span(
                read,
                condition.span,
                "the conditional unwind callee has no original condition span",
            )?,
            "this conditition needs to hold to show that the callee will not unwind".into(),
        ),
        UnwindSpec::MayUnwind => (
            source_span(
                read,
                target.span,
                "the possibly unwinding callee has no original declaration span",
            )?,
            "perhaps you need to mark this function as 'no_unwind'?".into(),
        ),
        UnwindSpec::NoUnwind => {
            return Err(SourceError(
                "an unwind failure targets an unconditional no-unwind callee",
            ));
        }
    };
    Ok(Failure {
        message: "cannot show this call will not unwind, in function marked 'no_unwind'".into(),
        primary: vec![at],
        labels: vec![(at, first), second],
    })
}
