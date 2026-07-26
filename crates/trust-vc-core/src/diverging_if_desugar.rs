//! Source-level desugaring of `if COND { A } else { panic!() }` (a diverging
//! FAILURE arm) into a guarded block that evaluates `COND` exactly once.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! A `panic!()` / `unreachable!()` / `todo!()` / `unimplemented!()` arm ABORTS —
//! Verus verifies such code only by proving the arm is UNREACHABLE (panic-freedom
//! is the goal for verified exec code). trust-vc's extractor otherwise reports
//! "Unsupported panic!()" and fail-closes the whole function.
//!
//! When exactly one branch of an `if` is such a diverging-failure block, the
//! other branch's guard must hold whenever control reaches the `if` (else the
//! abort is reachable). So:
//!   · `if C { A } else { panic!() }` →
//!     `{ let fresh = C; trust_vc::assert!(fresh); A }`
//!   · `if C { panic!() } else { B }` →
//!     `{ let fresh = C; trust_vc::assert!(!fresh); B }`
//! The `assert!` is the unreachability proof obligation (discharged when the
//! guard is provable from the context — a `requires`, an earlier assert, a match
//! refinement — and FAILING otherwise, exactly mirroring "reachable panic =
//! verification failure"), and the surviving branch supplies the value under the
//! now-asserted guard.
//!
//! SOUNDNESS (never a false `Verified`): the fresh ordinary local preserves the
//! source condition's single evaluation, modeled side effects, and exec
//! arithmetic/index panic obligations; the assertion only adds the diverging
//! arm's unreachability obligation; and the surviving branch stays verbatim.
//! Conditions containing `let` expressions (including `if let` and let chains)
//! remain untouched because moving their bindings out of the condition would not
//! preserve branch scope. The rewrite fires ONLY when EXACTLY ONE branch is a
//! diverging-failure block (both-diverging or neither-diverging is left
//! untouched), so a non-diverging `if` is never perturbed.

use proc_macro2::{Span, TokenStream, TokenTree};
use quote::ToTokens;
use std::collections::BTreeSet;
use syn::visit::Visit;
use syn::visit_mut::VisitMut;
use syn::{Block, Expr, Ident, ItemFn, Stmt};

/// A macro path whose invocation aborts (a diverging FAILURE).
fn is_diverging_failure_macro(mac: &syn::Macro) -> bool {
    mac.path.segments.last().is_some_and(|seg| {
        matches!(
            seg.ident.to_string().as_str(),
            "panic" | "unreachable" | "todo" | "unimplemented"
        )
    })
}

/// True iff `block` is exactly a single diverging-failure macro invocation
/// (`{ panic!() }`, `{ unreachable!("x") }`, …) and nothing else.
fn is_diverging_block(block: &Block) -> bool {
    if block.stmts.len() != 1 {
        return false;
    }
    match &block.stmts[0] {
        Stmt::Macro(stmt_macro) => is_diverging_failure_macro(&stmt_macro.mac),
        Stmt::Expr(Expr::Macro(expr_macro), _) => is_diverging_failure_macro(&expr_macro.mac),
        _ => false,
    }
}

fn collect_token_idents(tokens: TokenStream, used: &mut BTreeSet<String>) {
    for token in tokens {
        match token {
            TokenTree::Group(group) => collect_token_idents(group.stream(), used),
            TokenTree::Ident(ident) => {
                let rendered = ident.to_string();
                used.insert(rendered.strip_prefix("r#").unwrap_or(&rendered).to_owned());
            }
            TokenTree::Punct(_) | TokenTree::Literal(_) => {}
        }
    }
}

struct FreshDivergingIfNames {
    used: BTreeSet<String>,
    next: usize,
}

impl FreshDivergingIfNames {
    fn for_function(func: &ItemFn) -> Self {
        let mut used = BTreeSet::new();
        // Inspect the complete token stream, including macro and attribute
        // payloads that syn's ordinary AST visitor deliberately treats as opaque.
        collect_token_idents(func.to_token_stream(), &mut used);
        Self { used, next: 0 }
    }

    fn take(&mut self) -> Ident {
        loop {
            let name = format!("__trust_vc_diverging_if_guard_{}", self.next);
            self.next += 1;
            if self.used.insert(name.clone()) {
                return Ident::new(&name, Span::call_site());
            }
        }
    }
}

#[derive(Clone, Copy)]
enum RequiredGuard {
    True,
    False,
}

/// Build a guarded block whose fresh ordinary local evaluates `condition`
/// exactly once. Keeping the condition in a local initializer is load-bearing:
/// the body extractor visits that initializer before binding the local and emits
/// its exec arithmetic/index safety obligations there.
fn guarded_block(
    condition: Expr,
    required: RequiredGuard,
    value: &Block,
    guard_name: Ident,
) -> Expr {
    match required {
        RequiredGuard::True => syn::parse_quote!({
            let #guard_name = #condition;
            trust_vc::assert!(#guard_name);
            #value
        }),
        RequiredGuard::False => syn::parse_quote!({
            let #guard_name = #condition;
            trust_vc::assert!(!(#guard_name));
            #value
        }),
    }
}

fn condition_contains_let(condition: &Expr) -> bool {
    #[derive(Default)]
    struct LetFinder {
        found: bool,
    }

    impl<'ast> Visit<'ast> for LetFinder {
        fn visit_expr_let(&mut self, _expr_let: &'ast syn::ExprLet) {
            self.found = true;
        }
    }

    let mut finder = LetFinder::default();
    finder.visit_expr(condition);
    finder.found
}

struct DivergingIfRewriter {
    rewrote: bool,
    fresh_names: FreshDivergingIfNames,
}
impl VisitMut for DivergingIfRewriter {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        // Bottom-up so a nested `if … panic` inside the surviving branch is
        // handled before this level.
        syn::visit_mut::visit_expr_mut(self, expr);

        let Expr::If(expr_if) = expr else {
            return;
        };
        // Only the `if COND { .. } else { .. }` shape (an else-if chain's else is
        // an `Expr::If`, not a diverging block, so it is left alone).
        let Some((_, else_branch)) = &expr_if.else_branch else {
            return;
        };
        let Expr::Block(else_block) = &**else_branch else {
            return;
        };

        let then_diverges = is_diverging_block(&expr_if.then_branch);
        let else_diverges = is_diverging_block(&else_block.block);
        // Exactly one branch diverges.
        if then_diverges == else_diverges {
            return;
        }
        // `if let` and let-chain bindings scope over the then branch. Capturing
        // such a condition in a local would move or discard those bindings.
        if condition_contains_let(&expr_if.cond) {
            return;
        }

        let cond = (*expr_if.cond).clone();
        let guard_name = self.fresh_names.take();
        let replacement = if else_diverges {
            // Reaching the else aborts ⇒ COND must hold; value is the then branch.
            guarded_block(cond, RequiredGuard::True, &expr_if.then_branch, guard_name)
        } else {
            // Reaching the then aborts ⇒ !COND must hold; value is the else branch.
            guarded_block(cond, RequiredGuard::False, &else_block.block, guard_name)
        };
        *expr = replacement;
        self.rewrote = true;
    }
}

/// Rewrite every `if` whose sole diverging branch is a `panic!`/`unreachable!`/
/// `todo!`/`unimplemented!` block into an equivalent guarded block. Returns
/// `Some(rewritten)` iff any `if` was rewritten.
pub(crate) fn desugar_diverging_if(func: &ItemFn) -> Option<ItemFn> {
    // Cheap pre-check: only clone+visit when a diverging-failure macro appears in
    // the rendered body at all.
    let rendered = func.block.to_token_stream().to_string();
    if !["panic", "unreachable", "todo", "unimplemented"]
        .iter()
        .any(|name| rendered.contains(name))
    {
        return None;
    }
    let mut rewritten = func.clone();
    let mut rewriter = DivergingIfRewriter {
        rewrote: false,
        fresh_names: FreshDivergingIfNames::for_function(func),
    };
    rewriter.visit_item_fn_mut(&mut rewritten);
    rewriter.rewrote.then_some(rewritten)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn if_let_condition_stays_fail_closed() {
        let function: ItemFn = syn::parse_quote! {
            fn f(value: Option<u64>) -> u64 {
                if let Some(inner) = value {
                    inner
                } else {
                    panic!()
                }
            }
        };

        assert!(desugar_diverging_if(&function).is_none());

        let let_chain: ItemFn = syn::parse_quote! {
            fn f(value: Option<u64>) -> u64 {
                if let Some(inner) = value && inner > 0u64 {
                    inner
                } else {
                    panic!()
                }
            }
        };

        assert!(desugar_diverging_if(&let_chain).is_none());
    }

    #[test]
    fn generated_guard_name_avoids_source_identifiers() {
        let function: ItemFn = syn::parse_quote! {
            fn f(condition: bool) -> u64 {
                let __trust_vc_diverging_if_guard_0 = 7u64;
                if condition {
                    __trust_vc_diverging_if_guard_0
                } else {
                    panic!()
                }
            }
        };

        let rewritten = desugar_diverging_if(&function).expect("eligible if should be rewritten");
        let rendered = rewritten.to_token_stream().to_string();
        assert!(rendered.contains("__trust_vc_diverging_if_guard_1"));
    }

    #[test]
    fn side_effecting_condition_is_emitted_exactly_once() {
        let function: ItemFn = syn::parse_quote! {
            fn f() -> u64 {
                let mut evaluations = 0u64;
                if {
                    evaluations += 1u64;
                    evaluations == 1u64
                } {
                    1u64
                } else {
                    panic!()
                }
            }
        };

        let rewritten = desugar_diverging_if(&function).expect("eligible if should be rewritten");

        #[derive(Default)]
        struct AddAssignCounter(usize);

        impl<'ast> Visit<'ast> for AddAssignCounter {
            fn visit_expr_binary(&mut self, binary: &'ast syn::ExprBinary) {
                if matches!(&binary.op, syn::BinOp::AddAssign(_)) {
                    self.0 += 1;
                }
                syn::visit::visit_expr_binary(self, binary);
            }
        }

        let Some(Stmt::Expr(Expr::Block(wrapper), None)) = rewritten.block.stmts.last() else {
            panic!("rewrite should produce a tail block");
        };
        let [Stmt::Local(guard_local), Stmt::Macro(assertion), Stmt::Expr(_, None)] =
            wrapper.block.stmts.as_slice()
        else {
            panic!("guarded block should contain a local, assertion, and surviving value");
        };
        let guard_init = guard_local
            .init
            .as_ref()
            .expect("generated guard local should have an initializer");

        let mut counter = AddAssignCounter::default();
        counter.visit_expr(&guard_init.expr);
        assert_eq!(
            counter.0, 1,
            "the side effect must occur exactly once in the fresh initializer"
        );
        assert!(
            !assertion.mac.tokens.to_string().contains("evaluations"),
            "assert! must reference only the captured guard, never re-evaluate the condition"
        );
    }

    #[test]
    fn guard_initializer_retains_exec_arithmetic_obligation() {
        let function: ItemFn = syn::parse_quote! {
            #[trust_vc::requires(a == -2147483648i32)]
            #[trust_vc::requires(b == -1i32)]
            #[trust_vc::ensures(result == 1u64)]
            fn f(a: i32, b: i32) -> u64 {
                if a / b == a {
                    1u64
                } else {
                    panic!()
                }
            }
        };

        let vc = crate::vc_extraction::extract_verification_conditions(&function)
            .expect("diverging-if fixture should extract");
        assert!(
            vc.obligations
                .iter()
                .any(|obligation| obligation.name.starts_with("overflow_check")),
            "the fresh guard initializer must pass through exec MIN/-1 instrumentation"
        );
    }
}
