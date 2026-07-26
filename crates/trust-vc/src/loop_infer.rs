//! Loop invariant inference for `for i in lo..hi` range loops.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Provides an AST fold pass that detects `for IDENT in lo..hi` patterns and
//! auto-generates:
//! 1. Range bound invariant: `lo <= i` (LoopInvariant obligation)
//! 2. Loop scope metadata: modified_vars + guard (via push/pop context)
//! 3. Post-loop exit fact: `i == hi` (Assume obligation)
//!
//! The fold pass wraps each detected for-range loop in a block with cfg-gated
//! metadata registration calls. User-written `invariant!()` calls within the
//! loop body inherit the auto-inferred metadata via the loop context stack.
//!
//! Part of #2502.

use proc_macro2::Span;
use quote::quote;
use syn::fold::{self, Fold};
use syn::visit::Visit;
use syn::{Expr, ExprForLoop, Pat, RangeLimits};

/// Information extracted from a `for IDENT in lo..hi` loop.
struct ForRangeInfo {
    iter_var: String,
    lo_str: String,
    hi_str: String,
    inclusive: bool,
    body_modified: Vec<String>,
    /// If `hi` is a simple identifier (e.g., `n`), store its name for type
    /// inference via `collect_variable_from_ref`. If `hi` is a complex
    /// expression or literal, this is `None` and we default to `"i32"`.
    hi_ident: Option<String>,
    /// Explicit type suffix detected from a literal bound (e.g., `10usize`
    /// → `"usize"`, `10u64` → `"u64"`). Takes precedence over `hi_ident`
    /// fallback. Part of #2523 (Phase 2 P1).
    literal_suffix_type: Option<String>,
}

/// Attempt to extract range loop info from a for-loop expression.
fn try_extract_for_range(expr: &ExprForLoop) -> Option<ForRangeInfo> {
    // Pattern must be a simple identifier binding (e.g., `i`)
    let iter_var = match &*expr.pat {
        Pat::Ident(pi) if pi.by_ref.is_none() && pi.subpat.is_none() => pi.ident.to_string(),
        _ => return None,
    };

    // Iterator expression must be a range (lo..hi or lo..=hi)
    let range = match &*expr.expr {
        Expr::Range(r) => r,
        _ => return None,
    };

    let lo = range.start.as_ref()?;
    let hi = range.end.as_ref()?;
    let lo_str = quote!(#lo).to_string();
    let hi_str = quote!(#hi).to_string();
    let inclusive = matches!(range.limits, RangeLimits::Closed(_));

    // Check if hi is a simple identifier for type inference
    let hi_ident = match hi.as_ref() {
        Expr::Path(p) => p.path.get_ident().map(|i| i.to_string()),
        _ => None,
    };

    // Check for literal suffixes on either bound (e.g., 10usize, 0u64).
    // hi takes precedence, then lo. Part of #2523 (Phase 2 P1).
    let literal_suffix_type =
        extract_int_literal_suffix(hi).or_else(|| extract_int_literal_suffix(lo));

    let body_modified = collect_assigned_vars(&expr.body);

    Some(ForRangeInfo {
        iter_var,
        lo_str,
        hi_str,
        inclusive,
        body_modified,
        hi_ident,
        literal_suffix_type,
    })
}

/// Extract an integer type suffix from a literal expression.
///
/// Returns `Some("usize")` for `10usize`, `Some("u64")` for `0u64`, etc.
/// Returns `None` for unsuffixed literals or non-literal expressions.
/// Part of #2523 (Phase 2 P1).
fn extract_int_literal_suffix(expr: &Expr) -> Option<String> {
    if let Expr::Lit(lit) = expr {
        if let syn::Lit::Int(int_lit) = &lit.lit {
            let suffix = int_lit.suffix();
            if !suffix.is_empty() {
                return Some(suffix.to_string());
            }
        }
    }
    None
}

fn is_assignment_binop(op: &syn::BinOp) -> bool {
    matches!(
        op,
        syn::BinOp::AddAssign(_)
            | syn::BinOp::SubAssign(_)
            | syn::BinOp::MulAssign(_)
            | syn::BinOp::DivAssign(_)
            | syn::BinOp::RemAssign(_)
            | syn::BinOp::BitXorAssign(_)
            | syn::BinOp::BitAndAssign(_)
            | syn::BinOp::BitOrAssign(_)
            | syn::BinOp::ShlAssign(_)
            | syn::BinOp::ShrAssign(_)
    )
}

/// Collect variable names that are assigned in a block.
///
/// Conservative: any `x = ...` or `x op= ...` counts as a modification.
/// Catches both simple assignment (`ExprAssign`) and compound assignment
/// operators (`+=`, `-=`, etc. via `ExprBinary` with assign-op `BinOp`).
fn collect_assigned_vars(block: &syn::Block) -> Vec<String> {
    struct AssignCollector(Vec<String>);

    impl AssignCollector {
        fn try_push_ident(&mut self, expr: &Expr) {
            if let Expr::Path(p) = expr {
                if let Some(ident) = p.path.get_ident() {
                    self.0.push(ident.to_string());
                }
            }
        }
    }

    impl<'ast> Visit<'ast> for AssignCollector {
        fn visit_expr_assign(&mut self, expr: &'ast syn::ExprAssign) {
            self.try_push_ident(&expr.left);
            syn::visit::visit_expr_assign(self, expr);
        }

        fn visit_expr_binary(&mut self, expr: &'ast syn::ExprBinary) {
            // Compound assignment operators (+=, -=, *=, etc.)
            if is_assignment_binop(&expr.op) {
                self.try_push_ident(&expr.left);
            }
            syn::visit::visit_expr_binary(self, expr);
        }
    }

    let mut collector = AssignCollector(Vec::new());
    syn::visit::visit_block(&mut collector, block);
    collector.0.sort();
    collector.0.dedup();
    collector.0
}

/// Information extracted from a `while COND { BODY }` loop.
/// Part of #2523 (Phase 2 P3).
struct WhileLoopInfo {
    guard_str: String,
    body_modified: Vec<String>,
    can_assume_normal_exit: bool,
}

/// Information extracted from a bare `loop { BODY }` expression.
struct BareLoopInfo {
    body_modified: Vec<String>,
}

/// Attempt to extract while-loop info from a while expression.
///
/// Returns the guard condition and body-modified variables. Does NOT
/// auto-generate invariants (unlike range loops) — while loops have no
/// predictable range structure. The metadata enables frame-condition mode
/// for user-written `invariant!()` calls within the loop body.
///
/// Part of #2523 (Phase 2 P3).
fn try_extract_while_loop(expr: &syn::ExprWhile) -> Option<WhileLoopInfo> {
    // Reject `while let` patterns — those are not simple condition guards.
    // In syn 2.x, `while let` has `Expr::Let` as the condition.
    if matches!(*expr.cond, Expr::Let(_)) {
        return None;
    }

    let cond = &expr.cond;
    let cond_str = quote!(#cond).to_string();

    let body_modified = collect_assigned_vars(&expr.body);
    let can_assume_normal_exit =
        is_side_effect_free_guard(cond) && !contains_break_exiting_current_loop(&expr.body);

    Some(WhileLoopInfo {
        guard_str: cond_str,
        body_modified,
        can_assume_normal_exit,
    })
}

fn extract_bare_loop(expr: &syn::ExprLoop) -> BareLoopInfo {
    BareLoopInfo {
        body_modified: collect_assigned_vars(&expr.body),
    }
}

fn contains_break_exiting_current_loop(block: &syn::Block) -> bool {
    struct BreakVisitor {
        nested_loop_depth: usize,
        nested_loop_labels: Vec<String>,
        found: bool,
    }

    impl BreakVisitor {
        fn push_nested_label(&mut self, label: Option<&syn::Label>) -> usize {
            if let Some(label) = label {
                self.nested_loop_labels.push(label.name.ident.to_string());
                1
            } else {
                0
            }
        }

        fn pop_nested_labels(&mut self, pushed: usize) {
            for _ in 0..pushed {
                self.nested_loop_labels.pop();
            }
        }

        fn labeled_break_exits_current_loop(&self, label: &syn::Lifetime) -> bool {
            let label = label.ident.to_string();
            !self
                .nested_loop_labels
                .iter()
                .rev()
                .any(|nested_label| nested_label == &label)
        }
    }

    impl<'ast> Visit<'ast> for BreakVisitor {
        fn visit_expr_break(&mut self, expr: &'ast syn::ExprBreak) {
            let exits_current = match &expr.label {
                Some(label) => self.labeled_break_exits_current_loop(label),
                None => self.nested_loop_depth == 0,
            };
            self.found |= exits_current;
        }

        fn visit_expr_for_loop(&mut self, expr: &'ast syn::ExprForLoop) {
            self.visit_pat(&expr.pat);
            self.visit_expr(&expr.expr);

            self.nested_loop_depth += 1;
            let pushed = self.push_nested_label(expr.label.as_ref());
            self.visit_block(&expr.body);
            self.pop_nested_labels(pushed);
            self.nested_loop_depth -= 1;
        }

        fn visit_expr_loop(&mut self, expr: &'ast syn::ExprLoop) {
            self.nested_loop_depth += 1;
            let pushed = self.push_nested_label(expr.label.as_ref());
            self.visit_block(&expr.body);
            self.pop_nested_labels(pushed);
            self.nested_loop_depth -= 1;
        }

        fn visit_expr_while(&mut self, expr: &'ast syn::ExprWhile) {
            self.visit_expr(&expr.cond);

            self.nested_loop_depth += 1;
            let pushed = self.push_nested_label(expr.label.as_ref());
            self.visit_block(&expr.body);
            self.pop_nested_labels(pushed);
            self.nested_loop_depth -= 1;
        }

        fn visit_expr_closure(&mut self, _expr: &'ast syn::ExprClosure) {}
    }

    let mut visitor = BreakVisitor {
        nested_loop_depth: 0,
        nested_loop_labels: Vec::new(),
        found: false,
    };
    visitor.visit_block(block);
    visitor.found
}

fn is_side_effect_free_guard(expr: &Expr) -> bool {
    struct GuardVisitor {
        has_side_effect: bool,
    }

    impl<'ast> Visit<'ast> for GuardVisitor {
        fn visit_expr_assign(&mut self, _expr: &'ast syn::ExprAssign) {
            self.has_side_effect = true;
        }

        fn visit_expr_binary(&mut self, expr: &'ast syn::ExprBinary) {
            if is_assignment_binop(&expr.op) {
                self.has_side_effect = true;
            } else {
                syn::visit::visit_expr_binary(self, expr);
            }
        }

        fn visit_expr_block(&mut self, _expr: &'ast syn::ExprBlock) {
            self.has_side_effect = true;
        }

        fn visit_expr_call(&mut self, _expr: &'ast syn::ExprCall) {
            self.has_side_effect = true;
        }

        fn visit_expr_method_call(&mut self, _expr: &'ast syn::ExprMethodCall) {
            self.has_side_effect = true;
        }

        fn visit_expr_macro(&mut self, _expr: &'ast syn::ExprMacro) {
            self.has_side_effect = true;
        }

        fn visit_expr_break(&mut self, _expr: &'ast syn::ExprBreak) {
            self.has_side_effect = true;
        }

        fn visit_expr_continue(&mut self, _expr: &'ast syn::ExprContinue) {
            self.has_side_effect = true;
        }

        fn visit_expr_return(&mut self, _expr: &'ast syn::ExprReturn) {
            self.has_side_effect = true;
        }

        fn visit_expr_closure(&mut self, _expr: &'ast syn::ExprClosure) {
            self.has_side_effect = true;
        }
    }

    let mut visitor = GuardVisitor {
        has_side_effect: false,
    };
    visitor.visit_expr(expr);
    !visitor.has_side_effect
}

/// Fold pass that wraps loops with auto-inferred metadata.
///
/// Handles:
/// - `for i in lo..hi` / `for i in lo..=hi`: full inference (metadata + auto invariant + exit fact)
/// - `while cond { body }`: metadata and, for pure no-break boolean guards, a normal-exit fact
/// - `loop { body }`: metadata only; no normal-exit fact is assumed
struct LoopInferenceFolder;

impl Fold for LoopInferenceFolder {
    fn fold_expr(&mut self, expr: Expr) -> Expr {
        match expr {
            Expr::ForLoop(for_loop) => {
                // Recursively fold the for loop's sub-expressions and body first
                let folded = fold::fold_expr_for_loop(self, for_loop);

                if let Some(info) = try_extract_for_range(&folded) {
                    generate_range_loop_wrapper(folded, info)
                } else {
                    Expr::ForLoop(folded)
                }
            }
            Expr::While(while_loop) => {
                // Recursively fold the while loop's sub-expressions and body first
                let folded = fold::fold_expr_while(self, while_loop);

                if let Some(info) = try_extract_while_loop(&folded) {
                    generate_while_loop_wrapper(folded, info)
                } else {
                    Expr::While(folded)
                }
            }
            Expr::Loop(loop_expr) => {
                let folded = fold::fold_expr_loop(self, loop_expr);
                let info = extract_bare_loop(&folded);
                generate_bare_loop_wrapper(folded, info)
            }
            other => fold::fold_expr(self, other),
        }
    }
}

/// Generate a wrapper block around a for-range loop with auto-inferred metadata.
///
/// The generated code is cfg-gated to only run in test mode.
fn generate_range_loop_wrapper(for_loop: ExprForLoop, info: ForRangeInfo) -> Expr {
    let iter_var = &info.iter_var;
    let lo_str = &info.lo_str;
    let hi_str = &info.hi_str;

    // Build condition strings
    let range_bound_condition = format!("{lo_str} <= {iter_var}");
    let guard_condition = if info.inclusive {
        format!("{iter_var} <= {hi_str}")
    } else {
        format!("{iter_var} < {hi_str}")
    };
    let exit_condition = if info.inclusive {
        // For lo..=hi, after the loop i == hi + 1 (it iterates through hi)
        // Actually, in Rust `for i in lo..=hi`, i takes values lo, lo+1, ..., hi.
        // After the loop, the iterator is exhausted. The "exit" fact is that
        // the loop completed all iterations. We express this as i > hi
        // (since i went up to and including hi, the next step would exceed).
        // But for verification, the useful fact is that all values in [lo, hi]
        // were visited. We'll use the convention that i == hi at the last
        // iteration's end (matching Verus).
        format!("{iter_var} == {hi_str}")
    } else {
        format!("{iter_var} == {hi_str}")
    };

    // Build modified vars list: iterator + body-assigned
    let mut modified_vars: Vec<String> = vec![info.iter_var.clone()];
    modified_vars.extend(info.body_modified);
    modified_vars.sort();
    modified_vars.dedup();

    let modified_var_literals: Vec<syn::LitStr> = modified_vars
        .iter()
        .map(|s| syn::LitStr::new(s, Span::call_site()))
        .collect();

    let iter_var_lit = syn::LitStr::new(iter_var, Span::call_site());
    let guard_lit = syn::LitStr::new(&guard_condition, Span::call_site());
    let range_bound_lit = syn::LitStr::new(&range_bound_condition, Span::call_site());
    let exit_lit = syn::LitStr::new(&exit_condition, Span::call_site());
    let support_root = trust_vc_core::macro_support_root();
    let iter_registration = if let Some(suffix_ty) = &info.literal_suffix_type {
        // Phase 2 P1: literal suffix detected (e.g., 0usize..10usize → "usize")
        let ty_lit = syn::LitStr::new(suffix_ty, Span::call_site());
        quote! {
            #support_root::verify_macro::collect_variable(
                #iter_var_lit.to_string(),
                #ty_lit.to_string(),
            );
        }
    } else if let Some(hi_ident) = &info.hi_ident {
        let hi_ident_lit = syn::LitStr::new(hi_ident, Span::call_site());
        quote! {
            #support_root::verify_macro::collect_variable_from_ref(
                #iter_var_lit.to_string(),
                #hi_ident_lit.to_string(),
            );
        }
    } else {
        // Fallback for complex range bound expressions without type hints.
        quote! {
            #support_root::verify_macro::collect_variable(
                #iter_var_lit.to_string(),
                "i32".to_string(),
            );
        }
    };

    let tokens = quote! {
        {
            #[cfg(all(test, not(trust_mc)))]
            {
                #iter_registration
            }
            {
                #[cfg(all(test, not(trust_mc)))]
                let _trust_vc_loop_guard = #support_root::loop_metadata::LoopContextGuard::new(
                    vec![#(#modified_var_literals.to_string()),*],
                    #guard_lit.to_string(),
                );
                #[cfg(all(test, not(trust_mc)))]
                {
                    #support_root::verify_macro::collect_obligation(
                        #support_root::vc::ObligationKind::LoopInvariant,
                        format!("auto_range_bound_{}_{}", line!(), column!()),
                        #range_bound_lit.to_string(),
                        Some(format!("{}:{}:{}", file!(), line!(), column!())),
                    );
                }
                #for_loop
            }
            #[cfg(all(test, not(trust_mc)))]
            {
                #support_root::verify_macro::collect_obligation(
                    #support_root::vc::ObligationKind::PostLoopAssume,
                    format!("auto_loop_exit_{}_{}", line!(), column!()),
                    #exit_lit.to_string(),
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            }
        }
    };

    syn::parse2(tokens).unwrap_or(Expr::ForLoop(for_loop))
}

/// Generate a wrapper block around a while loop with auto-inferred metadata.
///
/// Unlike range loops, while loops do NOT get auto-generated invariants. The
/// loop context (modified_vars + guard) is registered so that user-written
/// `invariant!()` calls within the body inherit frame-condition metadata. For
/// the narrow no-break/pure-guard shape, a post-loop normal-exit fact is also
/// recorded so assertions after the loop can use the negated guard.
///
/// Part of #2523 (Phase 2 P3).
fn generate_while_loop_wrapper(while_loop: syn::ExprWhile, info: WhileLoopInfo) -> Expr {
    let guard_lit = syn::LitStr::new(&info.guard_str, Span::call_site());
    let support_root = trust_vc_core::macro_support_root();

    let mut modified_vars = info.body_modified;
    modified_vars.sort();
    modified_vars.dedup();

    let modified_var_literals: Vec<syn::LitStr> = modified_vars
        .iter()
        .map(|s| syn::LitStr::new(s, Span::call_site()))
        .collect();

    let normal_exit_collection = if info.can_assume_normal_exit {
        let exit_condition = format!("!({})", info.guard_str);
        let exit_lit = syn::LitStr::new(&exit_condition, Span::call_site());
        quote! {
            #[cfg(all(test, not(trust_mc)))]
            {
                #support_root::verify_macro::collect_obligation(
                    #support_root::vc::ObligationKind::PostLoopAssume,
                    format!("auto_while_exit_{}_{}", line!(), column!()),
                    #exit_lit.to_string(),
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            }
        }
    } else {
        quote! {}
    };

    let tokens = quote! {
        {
            {
                #[cfg(all(test, not(trust_mc)))]
                let _trust_vc_loop_guard = #support_root::loop_metadata::LoopContextGuard::new(
                    vec![#(#modified_var_literals.to_string()),*],
                    #guard_lit.to_string(),
                );
                #while_loop
            }
            #normal_exit_collection
        }
    };

    syn::parse2(tokens).unwrap_or(Expr::While(while_loop))
}

/// Generate a wrapper block around a bare `loop`.
///
/// Bare loops have no guard and may exit through `break`, so this wrapper only
/// registers modified-variable metadata for invariants collected inside the
/// loop body. It intentionally does not emit a post-loop normal-exit fact.
fn generate_bare_loop_wrapper(loop_expr: syn::ExprLoop, info: BareLoopInfo) -> Expr {
    let support_root = trust_vc_core::macro_support_root();

    let mut modified_vars = info.body_modified;
    modified_vars.sort();
    modified_vars.dedup();

    let modified_var_literals: Vec<syn::LitStr> = modified_vars
        .iter()
        .map(|s| syn::LitStr::new(s, Span::call_site()))
        .collect();
    let guard_lit = syn::LitStr::new("true", Span::call_site());

    let tokens = quote! {
        {
            {
                #[cfg(all(test, not(trust_mc)))]
                let _trust_vc_loop_guard = #support_root::loop_metadata::LoopContextGuard::new(
                    vec![#(#modified_var_literals.to_string()),*],
                    #guard_lit.to_string(),
                );
                #loop_expr
            }
        }
    };

    syn::parse2(tokens).unwrap_or(Expr::Loop(loop_expr))
}

/// Apply the loop inference fold pass to a block.
///
/// Returns a new block with detected loops wrapped in metadata registration
/// and (for range loops) auto-generated obligations.
pub(crate) fn fold_with_range_inference(block: &syn::Block) -> syn::Block {
    let mut folder = LoopInferenceFolder;
    folder.fold_block(block.clone())
}

#[cfg(test)]
#[path = "loop_infer_tests.rs"]
mod tests;
