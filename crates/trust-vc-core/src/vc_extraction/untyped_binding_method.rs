//! The trait methods an unsuffixed-literal binding can be the receiver of,
//! and how each relates the binding's type to its arguments and result
//! ([`super::infer_untyped_binding_type`]).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::{Constraint, Uses};
use syn::visit::Visit;
use syn::Expr;

/// How a method called on an integer relates its receiver's type to its
/// arguments and its result, for the trait methods an unsuffixed-literal
/// binding can be the receiver of (E0689 refuses an inherent one).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum MethodTyping {
    /// `Ord::{max, min, clamp}`: every argument and the result are `Self`.
    SelfArgsSelfResult,
    /// `PartialEq::{eq, ne}`, `PartialOrd::{lt, le, gt, ge, partial_cmp}`,
    /// `Ord::cmp`: every argument is a `&Self`; the result is not an integer.
    RefSelfArgs,
    /// `Clone::clone`, `ToOwned::to_owned`: no argument, a `Self` result.
    SelfResult,
    /// Any other method.
    Unknown,
}

impl MethodTyping {
    pub(super) fn returns_self(self) -> bool {
        matches!(self, Self::SelfArgsSelfResult | Self::SelfResult)
    }
}

pub(super) fn method_typing(call: &syn::ExprMethodCall) -> MethodTyping {
    if call.turbofish.is_some() {
        return MethodTyping::Unknown;
    }
    match (call.method.to_string().as_str(), call.args.len()) {
        ("max" | "min", 1) | ("clamp", 2) => MethodTyping::SelfArgsSelfResult,
        ("eq" | "ne" | "lt" | "le" | "gt" | "ge" | "cmp" | "partial_cmp", 1) => {
            MethodTyping::RefSelfArgs
        }
        ("clone" | "to_owned", 0) => MethodTyping::SelfResult,
        _ => MethodTyping::Unknown,
    }
}

/// `expr` with one shared borrow `&e` peeled (`y.eq(&w)`).
pub(super) fn peel_shared_ref(expr: &Expr) -> &Expr {
    match super::peel(expr) {
        Expr::Reference(reference) if reference.mutability.is_none() => {
            super::peel(&reference.expr)
        }
        other => other,
    }
}

impl Uses<'_> {
    /// A method called on the binding (or on an operation of its type). Rust
    /// refuses an INHERENT method on a still-unconstrained integer (E0689),
    /// but a TRAIT method resolves on one and unifies the binding with what
    /// the method's signature ties to `Self`: `w.min(y)` and `w.eq(&y)` make
    /// a `let mut w = 0` the `u8` that `y` is, and `w.max(1)` / `w.clone()`
    /// have the binding's type, which their position types (`carries_name`).
    /// Read as fixing nothing, a loop-written `w` was declared `i32` and its
    /// `u8` overflow was never checked. A method this reading does not know
    /// is unknown.
    pub(super) fn visit_receiver_method_call(&mut self, call: &syn::ExprMethodCall) {
        let typing = method_typing(call);
        if typing == MethodTyping::Unknown {
            self.record(Constraint::Unknown);
        }
        if !self.is_name(&call.receiver) {
            self.visit_typed(&call.receiver);
        }
        let unifies = matches!(
            typing,
            MethodTyping::SelfArgsSelfResult | MethodTyping::RefSelfArgs
        );
        for arg in &call.args {
            let arg = match typing {
                MethodTyping::RefSelfArgs => peel_shared_ref(arg),
                _ => arg,
            };
            if unifies {
                let constraint = self.operand(arg);
                self.record(constraint);
                if !self.is_name(arg) {
                    self.visit_typed(arg);
                }
            } else {
                self.visit_expr(arg);
            }
        }
    }

    /// Whether a known trait method takes the binding (or an operation of
    /// its type) as an argument: `y.min(w)`, `y.eq(&w)`.
    pub(super) fn method_argument_carries_name(&self, call: &syn::ExprMethodCall) -> bool {
        method_typing(call) != MethodTyping::Unknown
            && call
                .args
                .iter()
                .any(|arg| self.carries_name(peel_shared_ref(arg)))
    }

    /// `y.min(w)`, `y.eq(&w)`: the argument has the receiver's type.
    pub(super) fn visit_argument_method_call(&mut self, call: &syn::ExprMethodCall) {
        let constraint = self.operand(&call.receiver);
        self.record(constraint);
        self.visit_typed(&call.receiver);
        for arg in &call.args {
            let inner = peel_shared_ref(arg);
            if self.carries_name(inner) {
                if !self.is_name(inner) {
                    self.visit_typed(inner);
                }
            } else {
                self.visit_expr(arg);
            }
        }
    }
}
