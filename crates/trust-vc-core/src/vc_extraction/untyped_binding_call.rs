//! A call argument as a use of an unsuffixed-literal binding
//! ([`super::infer_untyped_binding_type`]): a parameter whose fixed-width
//! integer type this lane reads (a file function's declared `x: u8`) unifies
//! the argument with it, so `let a = 200 + 100; g8(a);` makes `a` a `u8`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::{path_ident, peel, Constraint, Uses};
use syn::visit::Visit;

impl Uses<'_> {
    /// Visit `call` when one of its arguments carries the binding (the name,
    /// or an operation of its type) and the callee's parameter there has a
    /// type this lane reads, recording that type; `false` (nothing visited)
    /// otherwise, which leaves the call to the generic reading — where a
    /// bare name in an argument is unknown. A callee spelled by a name the
    /// statements after the `let` re-bind (a closure `let g8 = |x| ..;`) is
    /// not the file function and reads nothing.
    pub(super) fn visit_typed_call(&mut self, call: &syn::ExprCall) -> bool {
        if let Some(callee) = path_ident(peel(&call.func)) {
            if self.rebound.contains(&callee) {
                return false;
            }
        }
        let typed: Vec<Option<crate::ir::TrustVcType>> = call
            .args
            .iter()
            .enumerate()
            .map(|(index, arg)| {
                if self.carries_name(arg) {
                    (self.types.call_param)(call, index)
                } else {
                    None
                }
            })
            .collect();
        if typed.iter().all(Option::is_none) {
            return false;
        }
        self.visit_expr(&call.func);
        for (arg, ty) in call.args.iter().zip(typed) {
            match ty {
                Some(ty) => {
                    self.record(Constraint::Fixed(ty));
                    if !self.is_name(arg) {
                        self.visit_typed(arg);
                    }
                }
                None => self.visit_expr(arg),
            }
        }
        true
    }
}
