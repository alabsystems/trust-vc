//! Control-flow restrictions for proof ghost-statement bridging.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::helpers::{
    is_proph_wrapper_type, is_prophecy_new_expr, local_binding_name, prophecy_view_receiver,
    typed_local_binding,
};
use proc_macro2::Span;
use std::collections::{HashMap, HashSet};
use syn::spanned::Spanned;
use syn::{Expr, ExprMethodCall, ExprPath, Local};

pub(super) fn reject_control_flow_dependence(
    expr: &Expr,
    prophecy_locals: &HashMap<String, String>,
    bridged_locals: &HashSet<String>,
    position: &str,
) -> syn::Result<()> {
    let mut visitor = BridgedLocalUseFinder::new(prophecy_locals, bridged_locals);
    syn::visit::Visit::visit_expr(&mut visitor, expr);
    if let Some((what, span)) = visitor.found {
        return Err(syn::Error::new(
            span,
            format!(
                "proof ghost-statement bridge currently supports only straight-line proof use; \
                 {what} cannot appear in {position}"
            ),
        ));
    }
    Ok(())
}

pub(super) fn expr_depends_on_symbolic_value(
    expr: &Expr,
    prophecy_locals: &HashMap<String, String>,
    bridged_locals: &HashSet<String>,
) -> bool {
    let mut visitor = BridgedLocalUseFinder::new(prophecy_locals, bridged_locals);
    syn::visit::Visit::visit_expr(&mut visitor, expr);
    visitor.found.is_some()
}

struct BridgedLocalUseFinder {
    prophecy_locals: HashSet<String>,
    bridged_locals: HashSet<String>,
    found: Option<(String, Span)>,
}

fn single_segment_ident(path: &syn::Path) -> Option<&syn::Ident> {
    let mut segments = path.segments.iter();
    let segment = segments.next()?;
    if segments.next().is_some() {
        return None;
    }
    Some(&segment.ident)
}

impl BridgedLocalUseFinder {
    fn new(prophecy_locals: &HashMap<String, String>, bridged_locals: &HashSet<String>) -> Self {
        Self {
            prophecy_locals: prophecy_locals.keys().cloned().collect(),
            bridged_locals: bridged_locals.clone(),
            found: None,
        }
    }

    fn shadow_name(&mut self, name: &str) {
        self.prophecy_locals.remove(name);
        self.bridged_locals.remove(name);
    }

    fn record_binding(&mut self, local: &Local) {
        let Some(name) = local_binding_name(local) else {
            return;
        };
        let Some(init) = &local.init else {
            self.shadow_name(&name);
            return;
        };

        self.shadow_name(&name);

        if let Some((binding_ident, binding_ty)) = typed_local_binding(local) {
            if is_proph_wrapper_type(binding_ty) && is_prophecy_new_expr(init.expr.as_ref()) {
                self.prophecy_locals.insert(binding_ident.to_string());
                return;
            }
        }

        if let Some((receiver_name, _)) = prophecy_view_receiver(init.expr.as_ref()) {
            if self.prophecy_locals.contains(&receiver_name) {
                self.bridged_locals.insert(name);
            }
        }
    }
}

impl<'ast> syn::visit::Visit<'ast> for BridgedLocalUseFinder {
    fn visit_block(&mut self, block: &'ast syn::Block) {
        if self.found.is_some() {
            return;
        }

        let saved_prophecy = self.prophecy_locals.clone();
        let saved_bridged = self.bridged_locals.clone();

        for stmt in &block.stmts {
            if self.found.is_some() {
                break;
            }
            syn::visit::Visit::visit_stmt(self, stmt);
        }

        self.prophecy_locals = saved_prophecy;
        self.bridged_locals = saved_bridged;
    }

    fn visit_local(&mut self, local: &'ast Local) {
        if self.found.is_some() {
            return;
        }

        if let Some(init) = &local.init {
            syn::visit::Visit::visit_expr(self, init.expr.as_ref());
            if let Some((_, diverge_expr)) = &init.diverge {
                syn::visit::Visit::visit_expr(self, diverge_expr.as_ref());
            }
        }

        if self.found.is_none() {
            self.record_binding(local);
        }
    }

    fn visit_expr_method_call(&mut self, method_call: &'ast ExprMethodCall) {
        if self.found.is_some() {
            return;
        }

        if method_call.method == "view" || method_call.method == "resolve" {
            if let Expr::Path(receiver_path) = method_call.receiver.as_ref() {
                if receiver_path.qself.is_none() {
                    if let Some(receiver_ident) = single_segment_ident(&receiver_path.path) {
                        let receiver_name = receiver_ident.to_string();
                        if self.prophecy_locals.contains(&receiver_name) {
                            self.found = Some((
                                format!(
                                    "prophecy method `{receiver_name}.{}(...)`",
                                    method_call.method
                                ),
                                method_call.span(),
                            ));
                            return;
                        }
                    }
                }
            }
        }

        syn::visit::visit_expr_method_call(self, method_call);
    }

    fn visit_expr_path(&mut self, path: &'ast ExprPath) {
        if self.found.is_some() {
            return;
        }

        if path.qself.is_none() {
            if let Some(ident) = single_segment_ident(&path.path) {
                let ident_name = ident.to_string();
                if self.bridged_locals.contains(&ident_name) {
                    self.found = Some((format!("bridged local `{ident}`"), path.span()));
                    return;
                }
            }
        }

        syn::visit::visit_expr_path(self, path);
    }
}
