// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test-only observation of existing C31 work. No solver or resource authority.
//!
//! Durations are inclusive, nested wall times. Collection and output add overhead;
//! these records diagnose work and do not establish a new performance baseline.
//! Solver-call spans additionally observe their current thread CPU time; unavailable
//! clocks remain absent. No observation supplies solver or resource authority.

use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;
use std::time::{Duration, Instant};

struct Event {
    kind: &'static str,
    label: &'static str,
    parent: Option<usize>,
    elapsed: Duration,
    thread_cpu: Option<Duration>,
}

struct Collector {
    identity: Rc<()>,
    events: Vec<Event>,
    stack: Vec<usize>,
}

thread_local! {
    static ACTIVE: RefCell<Option<Collector>> = const { RefCell::new(None) };
}

/// A capture remains on its creating thread and restores any prior observation.
pub(in crate::encoder) struct Capture {
    previous: Option<Collector>,
    enabled: bool,
    _thread: PhantomData<Rc<()>>,
}

pub(in crate::encoder) struct Report {
    events: Vec<Event>,
}

pub(in crate::encoder) fn begin(enabled: bool) -> Capture {
    let previous = if enabled {
        ACTIVE.with(|active| {
            active.replace(Some(Collector {
                identity: Rc::new(()),
                events: Vec::with_capacity(256),
                stack: Vec::with_capacity(16),
            }))
        })
    } else {
        None
    };
    Capture {
        previous,
        enabled,
        _thread: PhantomData,
    }
}

impl Capture {
    /// Called only after the existing sample timer stops.
    pub(in crate::encoder) fn finish(mut self) -> Option<Report> {
        if !self.enabled {
            return None;
        }
        let collector = ACTIVE.with(|active| active.replace(self.previous.take()));
        self.enabled = false;
        collector.map(|collector| Report {
            events: collector.events,
        })
    }
}

impl Drop for Capture {
    fn drop(&mut self) {
        if self.enabled {
            ACTIVE.with(|active| active.replace(self.previous.take()));
        }
    }
}

/// Spans cannot cross threads or affect a different nested capture.
pub(in crate::encoder) struct Span {
    entry: Option<Entry>,
}

struct Entry {
    identity: Rc<()>,
    id: usize,
    start: Instant,
    thread_cpu_start: Option<Duration>,
}

pub(in crate::encoder) fn span(kind: &'static str, label: &'static str) -> Span {
    let entry = ACTIVE.with(|active| {
        let mut active = active.borrow_mut();
        let collector = active.as_mut()?;
        let id = collector.events.len();
        collector.events.push(Event {
            kind,
            label,
            parent: collector.stack.last().copied(),
            elapsed: Duration::ZERO,
            thread_cpu: None,
        });
        collector.stack.push(id);
        Some(Entry {
            identity: Rc::clone(&collector.identity),
            id,
            start: Instant::now(),
            // Two reads per observed solver call, never in its hot loop.
            // The existing AY revision provides this clock; no dependency
            // checkout, budget, solver invocation or retry is added here.
            thread_cpu_start: (kind == "solver_call")
                .then(ay_sys::thread_cpu_time)
                .flatten(),
        })
    });
    Span { entry }
}

impl Drop for Span {
    fn drop(&mut self) {
        let Some(Entry {
            identity,
            id,
            start,
            thread_cpu_start,
        }) = self.entry.take()
        else {
            return;
        };
        let elapsed = start.elapsed();
        let thread_cpu = thread_cpu_start.and_then(|before| {
            ay_sys::thread_cpu_time().and_then(|after| after.checked_sub(before))
        });
        ACTIVE.with(|active| {
            let mut active = active.borrow_mut();
            let Some(collector) = active.as_mut() else {
                return;
            };
            if Rc::ptr_eq(&identity, &collector.identity) {
                collector.events[id].elapsed = elapsed;
                collector.events[id].thread_cpu = thread_cpu;
                collector.stack.pop();
            }
        });
    }
}

pub(in crate::encoder) fn retry(label: &'static str) {
    let _event = span("retry", label);
}

impl Report {
    /// Output occurs after ALL original sample timers, before budget judgment.
    pub(in crate::encoder) fn emit(&self, sample: usize) {
        let count = |kind| {
            self.events
                .iter()
                .filter(|event| event.kind == kind)
                .count()
        };
        eprintln!(
            "[C31_phase] sample={} inclusive_wall_time=true setups={} solver_calls={} retries={}",
            sample,
            count("setup"),
            count("solver_call"),
            count("retry"),
        );
        for (id, event) in self.events.iter().enumerate() {
            eprintln!(
                "[C31_phase] sample={} event={} parent={:?} kind={} label={} elapsed_us={}",
                sample,
                id,
                event.parent,
                event.kind,
                event.label,
                event.elapsed.as_micros(),
            );
            if event.kind == "solver_call" {
                eprintln!(
                    "[C31_solver_thread_cpu] sample={} event={} current_thread=true inclusive_wall_ns={} thread_cpu_ns={:?}",
                    sample,
                    id,
                    event.elapsed.as_nanos(),
                    event.thread_cpu.map(|cpu| cpu.as_nanos()),
                );
            }
        }
    }
}
