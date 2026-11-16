//! Complete native binding modes for one original inherited trait header.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use std::cell::RefCell;
use std::rc::Rc;

use rustc_hir::{self as hir, def::DefKind, def_id::LocalDefId};
use trust_vc_vcir::Mode;

use super::{FnProblem, FnReader, R, Refusal};
use crate::reader::{Cx, modes::CheckedModes};

#[derive(Clone)]
pub(super) struct Source<'a, 'tcx> {
    cx: &'a Cx<'tcx>,
    destination: LocalDefId,
    destination_body: LocalDefId,
    declaration: LocalDefId,
    source: LocalDefId,
    body: &'tcx hir::Body<'tcx>,
    destination_modes: Rc<CheckedModes<'tcx>>,
    source_modes: Rc<CheckedModes<'tcx>>,
}

impl<'a, 'tcx> Source<'a, 'tcx> {
    pub(super) fn for_inherited(
        reader: &FnReader<'a, 'tcx>,
        declaration: LocalDefId,
        source: LocalDefId,
        body: &'tcx hir::Body<'tcx>,
    ) -> R<Self> {
        let facts = reader.cx.checked_modes.borrow();
        let destination_modes = facts.get(&reader.def_id).cloned();
        let source_modes = facts.get(&declaration).cloned();
        drop(facts);
        let (Some(destination_modes), Some(source_modes)) = (destination_modes, source_modes)
        else {
            return Self::refuse(
                reader,
                "an inherited header lacks complete native source or destination mode facts",
            );
        };
        let packet = Self {
            cx: reader.cx,
            destination: reader.def_id,
            destination_body: reader.body_def,
            declaration,
            source,
            body,
            destination_modes,
            source_modes,
        };
        packet.current(reader)?;
        Ok(packet)
    }

    fn refuse<T>(reader: &FnReader<'_, 'tcx>, reason: impl Into<String>) -> R<T> {
        Err(FnProblem::Refused(Refusal::new(
            "binding-modes",
            reason,
            reader.sig_span,
        )))
    }

    fn current(&self, reader: &FnReader<'_, 'tcx>) -> R<()> {
        let tcx = reader.tcx;
        if !std::ptr::eq(self.cx, reader.cx)
            || !std::ptr::eq(*self.cx.tcx, *tcx)
            || reader.def_id != self.destination
            || reader.body_def != self.destination_body
            || tcx
                .trait_impl_of_assoc(self.destination.to_def_id())
                .is_none()
            || tcx.associated_item(self.destination).trait_item_def_id()
                != Some(self.declaration.to_def_id())
            || tcx.def_kind(tcx.local_parent(self.declaration)) != DefKind::Trait
            || self
                .cx
                .spec_methods
                .get(&self.declaration)
                .copied()
                .unwrap_or(self.declaration)
                != self.source
            || !tcx
                .hir_maybe_body_owned_by(self.source)
                .is_some_and(|body| std::ptr::eq(body, self.body))
        {
            return Self::refuse(
                reader,
                "an inherited header replaced its native source, destination or body",
            );
        }
        let facts = self.cx.checked_modes.borrow();
        if !facts
            .get(&self.destination)
            .is_some_and(|actual| Rc::ptr_eq(actual, &self.destination_modes))
            || !facts
                .get(&self.declaration)
                .is_some_and(|actual| Rc::ptr_eq(actual, &self.source_modes))
        {
            return Self::refuse(
                reader,
                "an inherited header lost its complete native mode facts",
            );
        }
        self.destination_modes
            .bindings
            .checked(tcx, self.destination, self.destination_body)
            .and_then(|_| {
                self.destination_modes.availability.checked(
                    tcx,
                    self.destination,
                    self.destination_body,
                )
            })
            .and_then(|_| {
                self.source_modes
                    .bindings
                    .checked(tcx, self.declaration, self.source)
            })
            .and_then(|_| {
                self.source_modes
                    .availability
                    .checked(tcx, self.declaration, self.source)
            })
            .map(|_| ())
            .map_err(|reason| {
                FnProblem::Refused(Refusal::new("binding-modes", reason, reader.sig_span))
            })
    }

    fn mode_for(&self, reader: &FnReader<'_, 'tcx>, pattern: &hir::Pat<'tcx>) -> R<Mode> {
        self.current(reader)?;
        if !reader.inheriting || !std::ptr::eq(reader.typeck, reader.tcx.typeck(self.source)) {
            return Self::refuse(
                reader,
                "native source binding modes are outside their inherited header read",
            );
        }
        self.source_modes
            .bindings
            .mode_for(
                reader.tcx,
                self.declaration,
                self.source,
                self.body,
                pattern,
            )
            .map_err(|reason| {
                FnProblem::Refused(Refusal::new("binding-modes", reason, pattern.span))
            })
    }
}

/// This private cell never returns a borrowed packet. Every query completes
/// before another scope enters or its Drop guard restores the previous packet.
pub(super) struct Scopes<'a, 'tcx>(Stack<Source<'a, 'tcx>>);

impl Default for Scopes<'_, '_> {
    fn default() -> Self {
        Self(Stack::default())
    }
}

impl<'a, 'tcx> Scopes<'a, 'tcx> {
    pub(super) fn enter(&self, source: Source<'a, 'tcx>) -> R<Entered<Source<'a, 'tcx>>> {
        let span = source.cx.tcx.def_span(source.destination);
        self.0.enter(source).map_err(|()| {
            FnProblem::Refused(Refusal::new(
                "binding-modes",
                "inherited header binding scopes were revoked",
                span,
            ))
        })
    }

    pub(super) fn mode_for(
        &self,
        reader: &FnReader<'_, 'tcx>,
        pattern: &hir::Pat<'tcx>,
    ) -> Option<R<Mode>> {
        let state = self.0.cell.borrow();
        if state.revoked {
            return Some(Source::refuse(
                reader,
                "inherited header binding scopes were revoked",
            ));
        }
        state
            .active
            .as_ref()
            .map(|source| source.mode_for(reader, pattern))
    }
}

struct State<T> {
    active: Option<Rc<T>>,
    revoked: bool,
}

struct Stack<T> {
    cell: Rc<RefCell<State<T>>>,
}

impl<T> Default for Stack<T> {
    fn default() -> Self {
        Self {
            cell: Rc::new(RefCell::new(State {
                active: None,
                revoked: false,
            })),
        }
    }
}

pub(super) struct Entered<T> {
    cell: Rc<RefCell<State<T>>>,
    active: Rc<T>,
    previous: Option<Rc<T>>,
}

impl<T> Stack<T> {
    fn enter(&self, value: T) -> Result<Entered<T>, ()> {
        let mut state = self.cell.borrow_mut();
        if state.revoked {
            return Err(());
        }
        let active = Rc::new(value);
        let previous = state.active.replace(Rc::clone(&active));
        Ok(Entered {
            cell: Rc::clone(&self.cell),
            active,
            previous,
        })
    }
}

impl<T> Drop for Entered<T> {
    fn drop(&mut self) {
        let mut state = self.cell.borrow_mut();
        if !state.revoked
            && state
                .active
                .as_ref()
                .is_some_and(|active| Rc::ptr_eq(active, &self.active))
        {
            state.active = self.previous.take();
        } else {
            // A stale/out-of-order guard cannot reinstall an already-ended
            // scope. Revocation is permanent for this reader, never fallback.
            state.active = None;
            state.revoked = true;
        }
    }
}

#[cfg(test)]
type Inspect = for<'a, 'tcx> fn(&FnReader<'a, 'tcx>, &Source<'a, 'tcx>);

#[cfg(test)]
static INSPECT: std::sync::Mutex<Option<Inspect>> = std::sync::Mutex::new(None);

#[cfg(test)]
pub(super) fn inspect(reader: &FnReader<'_, '_>) {
    let inspect = *INSPECT.lock().unwrap();
    let source = reader.header_binding_scopes.0.cell.borrow().active.clone();
    if let (Some(inspect), Some(source)) = (inspect, source) {
        inspect(reader, &source);
    }
}

#[cfg(test)]
mod tests {
    use super::Stack;
    use std::panic::{AssertUnwindSafe, catch_unwind};

    // Small marker values exercise lifetime mechanics only. They create no
    // CheckedModes, compiler context or source-header permission.
    #[test]
    fn nested_scopes_restore_after_success_error_and_panic() {
        let stack = Stack::default();
        let outer = stack.enter(1).unwrap();
        {
            let _inner = stack.enter(2).unwrap();
            assert_eq!(stack.cell.borrow().active.as_deref(), Some(&2));
        }
        assert_eq!(stack.cell.borrow().active.as_deref(), Some(&1));
        let fail = || -> Result<(), ()> {
            let _inner = stack.enter(3).unwrap();
            Err(())
        };
        assert_eq!(fail(), Err(()));
        assert_eq!(stack.cell.borrow().active.as_deref(), Some(&1));
        assert!(
            catch_unwind(AssertUnwindSafe(|| {
                let _inner = stack.enter(4).unwrap();
                panic!("scope-unwind control");
            }))
            .is_err()
        );
        assert_eq!(stack.cell.borrow().active.as_deref(), Some(&1));
        drop(outer);
        assert!(stack.cell.borrow().active.is_none());
        assert!(!stack.cell.borrow().revoked);
    }

    #[test]
    fn out_of_order_drop_revokes_and_cannot_restore_an_ended_scope() {
        let stack = Stack::default();
        let outer = stack.enter(1).unwrap();
        let inner = stack.enter(2).unwrap();
        drop(outer);
        assert!(stack.cell.borrow().revoked);
        assert!(stack.cell.borrow().active.is_none());
        drop(inner);
        assert!(stack.cell.borrow().active.is_none());
        assert!(stack.enter(3).is_err());
    }
}

#[cfg(test)]
mod native_tests;
