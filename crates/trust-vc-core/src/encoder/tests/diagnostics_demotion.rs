//! Tests for encoding diagnostics and result demotion pipeline (#2224).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Verifies that:
//! 1. EncodingDiagnostics correctly tracks all approximation counters
//! 2. Verified results are demoted to Unknown when demoting categories fire
//! 3. Non-demoting categories are tracked but do NOT trigger demotion
//!
//! Split by dominant regression cluster to reduce churn in a hot test file and
//! keep focused regression entry points discoverable.
// Helper items in this parent module are intentionally consumed from child
// regression modules via `super::*`, but Rust's dead_code/unused_imports lints
// still fire on the split test shell itself.
#![allow(dead_code, unused_imports)]

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, Once, OnceLock};

use super::*;
use crate::encoder::diagnostics::{EncodingApproximation, EncodingDiagnostics};
use crate::encoder::verification::test_hooks::FORCE_OVERFLOW_PRECHECK_DEMOTION;
use crate::vc::{FunctionContext, ProofObligation};
use tracing::field::{Field, Visit};
use tracing::metadata::LevelFilter;
use tracing::span::{Attributes, Id, Record};
use tracing::subscriber::Interest;
use tracing::{Event, Level, Metadata, Subscriber};

mod demotion_behaviors;
mod diagnostics_core;
mod fixpoint_warnings;
mod opaque_type_guard;

static WARN_EVENTS: OnceLock<Mutex<Vec<WarnEvent>>> = OnceLock::new();
static WARN_CAPTURE_LOCK: OnceLock<Mutex<()>> = OnceLock::new();
static WARN_SUBSCRIBER_INIT: Once = Once::new();
static WARN_SPAN_IDS: AtomicU64 = AtomicU64::new(1);

#[derive(Debug, Clone, PartialEq, Eq)]
struct WarnEvent {
    assertion: Option<String>,
    message: Option<String>,
}

#[derive(Default)]
struct WarnVisitor {
    assertion: Option<String>,
    message: Option<String>,
}

impl WarnVisitor {
    fn record_value(&mut self, field: &Field, value: String) {
        match field.name() {
            "assertion" => self.assertion = Some(value),
            "message" => self.message = Some(value),
            _ => {}
        }
    }
}

impl Visit for WarnVisitor {
    fn record_debug(&mut self, field: &Field, value: &dyn std::fmt::Debug) {
        self.record_value(field, format!("{value:?}"));
    }

    fn record_str(&mut self, field: &Field, value: &str) {
        self.record_value(field, value.to_string());
    }

    fn record_i64(&mut self, field: &Field, value: i64) {
        self.record_value(field, value.to_string());
    }

    fn record_u64(&mut self, field: &Field, value: u64) {
        self.record_value(field, value.to_string());
    }
}

struct WarnCaptureSubscriber;

impl Subscriber for WarnCaptureSubscriber {
    fn enabled(&self, metadata: &Metadata<'_>) -> bool {
        *metadata.level() <= Level::WARN
    }

    fn new_span(&self, _attrs: &Attributes<'_>) -> Id {
        Id::from_u64(WARN_SPAN_IDS.fetch_add(1, Ordering::Relaxed))
    }

    fn record(&self, _span: &Id, _values: &Record<'_>) {}

    fn record_follows_from(&self, _span: &Id, _follows: &Id) {}

    fn event(&self, event: &Event<'_>) {
        if *event.metadata().level() != Level::WARN {
            return;
        }
        let mut visitor = WarnVisitor::default();
        event.record(&mut visitor);
        warn_events()
            .lock()
            .expect("warn capture mutex should not poison")
            .push(WarnEvent {
                assertion: visitor.assertion,
                message: visitor.message,
            });
    }

    fn enter(&self, _span: &Id) {}

    fn exit(&self, _span: &Id) {}

    fn register_callsite(&self, metadata: &'static Metadata<'static>) -> Interest {
        if *metadata.level() <= Level::WARN {
            Interest::always()
        } else {
            Interest::never()
        }
    }

    fn max_level_hint(&self) -> Option<LevelFilter> {
        Some(LevelFilter::WARN)
    }
}

fn warn_events() -> &'static Mutex<Vec<WarnEvent>> {
    WARN_EVENTS.get_or_init(|| Mutex::new(Vec::new()))
}

fn warn_capture_lock() -> &'static Mutex<()> {
    WARN_CAPTURE_LOCK.get_or_init(|| Mutex::new(()))
}

fn install_warn_capture_subscriber() {
    WARN_SUBSCRIBER_INIT.call_once(|| {
        tracing::subscriber::set_global_default(WarnCaptureSubscriber)
            .expect("warn capture subscriber should install once");
    });
}

fn capture_warns<T>(f: impl FnOnce() -> T) -> (T, Vec<WarnEvent>) {
    install_warn_capture_subscriber();
    let _capture_guard = warn_capture_lock()
        .lock()
        .expect("warn capture lock should not poison");
    warn_events()
        .lock()
        .expect("warn capture mutex should not poison")
        .clear();
    let result = f();
    let events = std::mem::take(
        &mut *warn_events()
            .lock()
            .expect("warn capture mutex should not poison"),
    );
    (result, events)
}

fn i32_spec_fn(name: &str) -> FunctionContext {
    FunctionContext {
        name: name.to_string(),
        params: vec![("x".to_string(), crate::ir::TrustVcType::Int { width: 32 })],
        return_type: crate::ir::TrustVcType::Int { width: 32 },
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    }
}

fn add_body_axiom_to_context(ctx: &mut VerificationContext, condition: &str) {
    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_f", condition)
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["f(x)".to_string()]]),
    );
}

fn build_non_convergent_pipeline_context(assertion_name: &str) -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(i32_spec_fn("f"));
    add_body_axiom_to_context(&mut ctx, "f(x) == f(x + 1) + 1");
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        assertion_name,
        "f(0) == 0",
    ));
    ctx
}

fn build_convergent_pipeline_context(assertion_name: &str) -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(i32_spec_fn("f"));
    add_body_axiom_to_context(&mut ctx, "f(x) == x");
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        assertion_name,
        "f(3) == 3",
    ));
    ctx
}

fn diagnostics_with(entries: &[(EncodingApproximation, u32)]) -> EncodingDiagnostics {
    let mut diagnostics = EncodingDiagnostics::default();
    for (category, count) in entries {
        for _ in 0..*count {
            diagnostics.record(*category);
        }
    }
    diagnostics
}
