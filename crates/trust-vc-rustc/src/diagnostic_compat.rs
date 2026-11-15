//! Render compiler diagnostics using the terminology of the pinned Verus
//! compiler. Adapt structured diagnostics before the compiler's normal
//! tracker, error accounting and JSON or human emitter see them.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::sync::{Mutex, PoisonError};

use rustc_errors::formatting::format_diag_messages;
use rustc_errors::{DiagInner, ErrorGuaranteed, Level, Style, Sublevel, TRACK_DIAGNOSTIC};
use rustc_interface::interface::Config;

type Tracker =
    fn(DiagInner, &mut dyn FnMut(DiagInner) -> Option<ErrorGuaranteed>) -> Option<ErrorGuaranteed>;

fn forward(
    diagnostic: DiagInner,
    emit: &mut dyn FnMut(DiagInner) -> Option<ErrorGuaranteed>,
) -> Option<ErrorGuaranteed> {
    emit(diagnostic)
}

// rustc installs its own tracker during session initialization. Capture it
// after that initialization, preserving query/incremental tracking. The
// driver runs one compiler per process; the mutex also permits diagnostics
// emitted by compiler worker threads to use the same tracker.
static PREVIOUS_TRACKER: Mutex<Tracker> = Mutex::new(forward);

/// Chain the diagnostic adapter after any existing parse-session callback.
pub(crate) fn configure(config: &mut Config) {
    let previous_callback = config.psess_created.take();
    config.psess_created = Some(Box::new(move |psess| {
        if let Some(previous) = previous_callback {
            previous(psess);
        }
        install();
    }));
}

fn install() {
    let mut previous = PREVIOUS_TRACKER
        .lock()
        .unwrap_or_else(PoisonError::into_inner);
    let current = *TRACK_DIAGNOSTIC;
    if std::ptr::fn_addr_eq(current, track as Tracker) {
        return;
    }
    *previous = current;
    TRACK_DIAGNOSTIC.swap(&(track as Tracker));
}

fn track(
    mut diagnostic: DiagInner,
    emit: &mut dyn FnMut(DiagInner) -> Option<ErrorGuaranteed>,
) -> Option<ErrorGuaranteed> {
    adapt(&mut diagnostic);
    let previous = *PREVIOUS_TRACKER
        .lock()
        .unwrap_or_else(PoisonError::into_inner);
    previous(diagnostic, emit)
}

fn adapt(diagnostic: &mut DiagInner) {
    if diagnostic.level() != Level::Error {
        return;
    }
    let Some(code) = diagnostic.code else {
        return;
    };
    // Format only diagnostics whose codes have a compatibility rule. All
    // other messages, including unknown formatting forms, remain untouched.
    let replacement = match code.as_u32() {
        391 => {
            let message = format_diag_messages(&diagnostic.messages, &diagnostic.args);
            message
                .strip_prefix("cycle detected when computing the super clauses of ")
                .filter(|target| {
                    target.starts_with('`') && target.ends_with('`') && target.len() > 2
                })
                .map(|target| {
                    format!("cycle detected when computing the super predicates of {target}")
                })
        }
        423 => {
            let message = format_diag_messages(&diagnostic.messages, &diagnostic.args);
            let name = message
                .strip_prefix("cannot find value `")
                .and_then(|text| text.strip_suffix("` in this scope"))
                .filter(|name| !name.is_empty() && !name.contains('`'));
            name.and_then(|name| {
                let note = format!("a module named `{name}` exists in another namespace");
                diagnostic
                    .children
                    .iter()
                    .any(|child| {
                        child.level == Sublevel::Note
                            && format_diag_messages(&child.messages, &diagnostic.args) == note
                    })
                    .then(|| format!("expected value, found module `{name}`"))
            })
        }
        _ => None,
    };
    if let Some(message) = replacement {
        // Change only the primary message. Codes, severity, spans, notes,
        // suggestions, arguments and the compiler's result stay intact.
        diagnostic.messages = vec![(message.into(), Style::NoStyle)];
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_errors::{DiagMessage, ErrCode, MultiSpan, Subdiag};

    fn diagnostic(code: u32, message: &str) -> DiagInner {
        let mut diagnostic = DiagInner::new(Level::Error, message.to_string());
        diagnostic.code = Some(ErrCode::from_u32(code));
        diagnostic
    }

    fn add_note(diagnostic: &mut DiagInner, message: &str) {
        diagnostic.children.push(Subdiag {
            level: Sublevel::Note,
            messages: vec![(DiagMessage::from(message.to_string()), Style::NoStyle)],
            span: MultiSpan::new(),
        });
    }

    fn message(diagnostic: &DiagInner) -> String {
        format_diag_messages(&diagnostic.messages, &diagnostic.args)
    }

    #[test]
    fn cycle_query_terminology_is_compatible() {
        for target in ["A", "nested::DifferentTrait"] {
            let mut diagnostic = diagnostic(
                391,
                &format!("cycle detected when computing the super clauses of `{target}`"),
            );
            let original = diagnostic.clone();
            adapt(&mut diagnostic);
            assert_eq!(
                message(&diagnostic),
                format!("cycle detected when computing the super predicates of `{target}`")
            );
            diagnostic.messages = original.messages.clone();
            assert_eq!(format!("{diagnostic:?}"), format!("{original:?}"));
        }
    }

    #[test]
    fn missing_value_requires_matching_module_note() {
        for name in ["m1", "other_module"] {
            let mut diagnostic =
                diagnostic(423, &format!("cannot find value `{name}` in this scope"));
            add_note(
                &mut diagnostic,
                &format!("a module named `{name}` exists in another namespace"),
            );
            let original = diagnostic.clone();
            adapt(&mut diagnostic);
            assert_eq!(
                message(&diagnostic),
                format!("expected value, found module `{name}`")
            );
            diagnostic.messages = original.messages.clone();
            assert_eq!(format!("{diagnostic:?}"), format!("{original:?}"));
        }
    }

    #[test]
    fn unrelated_diagnostics_are_unchanged() {
        let mut missing_note = diagnostic(423, "cannot find value `m1` in this scope");
        let no_note = missing_note.clone();
        adapt(&mut missing_note);
        assert_eq!(format!("{missing_note:?}"), format!("{no_note:?}"));

        for (code, primary, note) in [
            (
                423,
                "cannot find value `m1` in this scope",
                "a module named `m2` exists in another namespace",
            ),
            (
                423,
                "cannot find value `m1` in this scope",
                "a struct named `m1` exists in another namespace",
            ),
            (
                425,
                "cannot find value `m1` in this scope",
                "a module named `m1` exists in another namespace",
            ),
            (391, "cycle detected when computing the clauses of `A`", ""),
            (
                399,
                "cycle detected when computing the super clauses of `A`",
                "",
            ),
        ] {
            let mut diagnostic = diagnostic(code, primary);
            add_note(&mut diagnostic, note);
            let original = diagnostic.clone();
            adapt(&mut diagnostic);
            assert_eq!(format!("{diagnostic:?}"), format!("{original:?}"));
        }

        for (level, coded) in [
            (Level::Error, false),
            (Level::Note, false),
            (Level::Note, true),
        ] {
            let mut diagnostic = DiagInner::new(
                level,
                "cycle detected when computing the super clauses of `A`",
            );
            diagnostic.code = coded.then(|| ErrCode::from_u32(391));
            let original = diagnostic.clone();
            adapt(&mut diagnostic);
            assert_eq!(format!("{diagnostic:?}"), format!("{original:?}"));
        }

        let mut diagnostic = diagnostic(423, "cannot find value `m1` in this scope");
        add_note(
            &mut diagnostic,
            "a module named `m1` exists in another namespace",
        );
        diagnostic.children[0].level = Sublevel::Help;
        let original = diagnostic.clone();
        adapt(&mut diagnostic);
        assert_eq!(format!("{diagnostic:?}"), format!("{original:?}"));
    }
}
