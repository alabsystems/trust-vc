// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use quote::quote;
use syn::fold::{self, Fold};

use trust_vc_core::{expr_to_try_builder_tokens, AssertForallByParsed};

use super::{
    canonical_expr_ast_string, generate_obligation_collection, obligations::expand_assume,
};

/// Expands `assert_by!(condition, { proof })`.
///
/// Phase 5 Step 3b (#1866): Tries TrustVcExpr builder path for the condition.
/// Falls back to string-based `end_assert_by_scope` if the condition expression
/// is unsupported by the builder API.
pub(crate) fn expand_assert_by(
    tokens: proc_macro2::TokenStream,
    condition_tokens: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let condition_ast_string = canonical_expr_ast_string(&condition_tokens);

    let parsed = syn::parse2::<syn::Expr>(condition_tokens.clone()).ok();
    let try_builder = parsed.as_ref().and_then(expr_to_try_builder_tokens);

    let scope_end = if let Some(builder) = try_builder {
        // Runtime fallback: if variable type lookup fails, use string path. #2233.
        quote! {
            if let Some(__trust_vc_expr) = { #builder } {
                #support_root::verify_macro::end_assert_by_scope_expr(
                    condition_str,
                    __trust_vc_expr,
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            } else {
                #support_root::verify_macro::end_assert_by_scope(
                    condition_str,
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            }
        }
    } else {
        quote! {
            #support_root::verify_macro::end_assert_by_scope(
                condition_str,
                Some(format!("{}:{}:{}", file!(), line!(), column!())),
            );
        }
    };

    // Use line+column for unique scope keys. Part of #2652.
    quote! {
        {
            #[cfg(test)]
            {
                #support_root::verify_macro::begin_assert_by_scope(
                    format!("assert_by_line_{}_col_{}", line!(), column!())
                );
                let result = { #tokens };
                let condition_str = #condition_ast_string.to_string();
                #scope_end
            }
            #[cfg(not(test))]
            {
                if false {
                    let _ = || { #tokens };
                }
            }
        }
    }
}

/// Expands Verus-style `assert_by!(condition, { proof_block })`.
///
/// The proof block runs between `begin_assert_by_scope` and `end_assert_by_scope`,
/// so any inner `trust_vc::assert!()` calls create scoped obligations that are only
/// visible within the assert_by sub-query. The condition is proved with those
/// scoped obligations as additional context.
///
/// Part of #2386 Phase 2: assert_by proc-macro usability.
pub(crate) fn expand_assert_by_with_proof_block(
    condition_tokens: proc_macro2::TokenStream,
    proof_block_tokens: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let condition_ast_string = canonical_expr_ast_string(&condition_tokens);

    let parsed = syn::parse2::<syn::Expr>(condition_tokens.clone()).ok();
    let try_builder = parsed.as_ref().and_then(expr_to_try_builder_tokens);

    let scope_end = if let Some(builder) = try_builder {
        quote! {
            if let Some(__trust_vc_expr) = { #builder } {
                #support_root::verify_macro::end_assert_by_scope_expr(
                    condition_str,
                    __trust_vc_expr,
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            } else {
                #support_root::verify_macro::end_assert_by_scope(
                    condition_str,
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            }
        }
    } else {
        quote! {
            #support_root::verify_macro::end_assert_by_scope(
                condition_str,
                Some(format!("{}:{}:{}", file!(), line!(), column!())),
            );
        }
    };

    // Use line+column for unique scope keys. Part of #2652.
    quote! {
        {
            #[cfg(test)]
            {
                #support_root::verify_macro::begin_assert_by_scope(
                    format!("assert_by_line_{}_col_{}", line!(), column!())
                );
                // Run the proof block — inner trust_vc::assert!() calls create
                // scoped obligations captured by the assert_by scope.
                #proof_block_tokens
                let condition_str = #condition_ast_string.to_string();
                #scope_end
            }
            #[cfg(not(test))]
            {
                if false {
                    let _ = || { #condition_tokens };
                    let _ = || #proof_block_tokens;
                }
            }
        }
    }
}

/// Expands `assert_forall_by!(|x: T| condition, { proof_block })`.
pub(crate) fn expand_assert_forall_by(parsed: AssertForallByParsed) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let body = parsed.closure.body.as_ref();
    let sanitized_body = strip_expr_trigger_attrs_for_typecheck(body.clone());
    let sanitized_body_tokens = quote! { #sanitized_body };
    let body_ast_string = canonical_expr_ast_string(&sanitized_body_tokens);
    let trigger_patterns = trigger_pattern_tokens(&parsed.trigger_patterns);
    let proof_block = &parsed.proof_block;
    let closure_inputs = &parsed.closure.inputs;
    let proof_obligation_collections = expand_assert_forall_by_proof_obligations(proof_block);

    let try_builder = expr_to_try_builder_tokens(body);
    let scope_end = if let Some(builder) = try_builder {
        quote! {
            if let Some(__trust_vc_expr) = { #builder } {
                #support_root::verify_macro::end_assert_forall_by_scope_expr_with_triggers(
                    __trust_vc_condition_str,
                    __trust_vc_expr,
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                    __trust_vc_trigger_patterns,
                );
            } else {
                #support_root::verify_macro::end_assert_forall_by_scope_with_triggers(
                    __trust_vc_condition_str,
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                    __trust_vc_trigger_patterns,
                );
            }
        }
    } else {
        quote! {
            #support_root::verify_macro::end_assert_forall_by_scope_with_triggers(
                __trust_vc_condition_str,
                Some(format!("{}:{}:{}", file!(), line!(), column!())),
                __trust_vc_trigger_patterns,
            );
        }
    };

    let bound_var_entries = parsed.bound_vars.iter().map(|var| {
        let name = &var.name;
        let ty = &var.ty;
        quote! {
            (
                #name.to_string(),
                #support_root::ir::TrustVcType::parse_or_opaque(stringify!(#ty)),
            )
        }
    });
    let bound_var_registrations = parsed.bound_vars.iter().map(|var| {
        let name = &var.name;
        let ty = &var.ty;
        quote! {
            __trust_vc_forall_bound_vars.register(
                #name.to_string(),
                #support_root::ir::TrustVcType::parse_or_opaque(stringify!(#ty)),
            );
        }
    });
    quote! {
        {
            #[cfg(test)]
            {
                let mut __trust_vc_forall_bound_vars =
                    #support_root::QuantifierBoundVarGuard::new();
                #(#bound_var_registrations)*

                #support_root::verify_macro::begin_assert_forall_by_scope(
                    format!("assert_forall_by_line_{}_col_{}", line!(), column!()),
                    vec![#(#bound_var_entries),*],
                );

                #(#proof_obligation_collections)*
                if false {
                    let _ = |#closure_inputs| #proof_block;
                }

                let __trust_vc_condition_str = #body_ast_string.to_string();
                let __trust_vc_trigger_patterns: Vec<Vec<String>> = #trigger_patterns;
                #scope_end
            }
            #[cfg(not(test))]
            {
                if false {
                    let _ = |#closure_inputs| { #sanitized_body_tokens };
                    let _ = |#closure_inputs| #proof_block;
                }
            }
        }
    }
}

fn trigger_pattern_tokens(patterns: &[Vec<syn::Expr>]) -> proc_macro2::TokenStream {
    if patterns.is_empty() {
        return quote! { Vec::<Vec<String>>::new() };
    }

    let groups = patterns.iter().map(|group| {
        let patterns = group.iter().map(|expr| {
            let expr_tokens = quote! { #expr };
            let pattern = canonical_expr_ast_string(&expr_tokens);
            quote! { #pattern.to_string() }
        });
        quote! { vec![#(#patterns),*] }
    });

    quote! { vec![#(#groups),*] }
}

struct TriggerAttrStripper;

impl Fold for TriggerAttrStripper {
    fn fold_expr(&mut self, expr: syn::Expr) -> syn::Expr {
        let mut expr = fold::fold_expr(self, expr);
        strip_expr_trigger_attrs(&mut expr);
        expr
    }
}

fn strip_expr_trigger_attrs_for_typecheck(expr: syn::Expr) -> syn::Expr {
    TriggerAttrStripper.fold_expr(expr)
}

fn strip_expr_trigger_attrs(expr: &mut syn::Expr) {
    let Some(attrs) = expr_attrs_mut(expr) else {
        return;
    };
    attrs.retain(|attr| !attr_path_ends_with(attr, "trigger"));
}

fn expr_attrs_mut(expr: &mut syn::Expr) -> Option<&mut Vec<syn::Attribute>> {
    match expr {
        syn::Expr::Array(expr) => Some(&mut expr.attrs),
        syn::Expr::Assign(expr) => Some(&mut expr.attrs),
        syn::Expr::Async(expr) => Some(&mut expr.attrs),
        syn::Expr::Await(expr) => Some(&mut expr.attrs),
        syn::Expr::Binary(expr) => Some(&mut expr.attrs),
        syn::Expr::Block(expr) => Some(&mut expr.attrs),
        syn::Expr::Break(expr) => Some(&mut expr.attrs),
        syn::Expr::Call(expr) => Some(&mut expr.attrs),
        syn::Expr::Cast(expr) => Some(&mut expr.attrs),
        syn::Expr::Closure(expr) => Some(&mut expr.attrs),
        syn::Expr::Const(expr) => Some(&mut expr.attrs),
        syn::Expr::Continue(expr) => Some(&mut expr.attrs),
        syn::Expr::Field(expr) => Some(&mut expr.attrs),
        syn::Expr::ForLoop(expr) => Some(&mut expr.attrs),
        syn::Expr::Group(expr) => Some(&mut expr.attrs),
        syn::Expr::If(expr) => Some(&mut expr.attrs),
        syn::Expr::Index(expr) => Some(&mut expr.attrs),
        syn::Expr::Infer(expr) => Some(&mut expr.attrs),
        syn::Expr::Let(expr) => Some(&mut expr.attrs),
        syn::Expr::Lit(expr) => Some(&mut expr.attrs),
        syn::Expr::Loop(expr) => Some(&mut expr.attrs),
        syn::Expr::Macro(expr) => Some(&mut expr.attrs),
        syn::Expr::Match(expr) => Some(&mut expr.attrs),
        syn::Expr::MethodCall(expr) => Some(&mut expr.attrs),
        syn::Expr::Paren(expr) => Some(&mut expr.attrs),
        syn::Expr::Path(expr) => Some(&mut expr.attrs),
        syn::Expr::Range(expr) => Some(&mut expr.attrs),
        syn::Expr::Reference(expr) => Some(&mut expr.attrs),
        syn::Expr::Repeat(expr) => Some(&mut expr.attrs),
        syn::Expr::Return(expr) => Some(&mut expr.attrs),
        syn::Expr::Struct(expr) => Some(&mut expr.attrs),
        syn::Expr::Try(expr) => Some(&mut expr.attrs),
        syn::Expr::TryBlock(expr) => Some(&mut expr.attrs),
        syn::Expr::Tuple(expr) => Some(&mut expr.attrs),
        syn::Expr::Unary(expr) => Some(&mut expr.attrs),
        syn::Expr::Unsafe(expr) => Some(&mut expr.attrs),
        _ => None,
    }
}

fn attr_path_ends_with(attr: &syn::Attribute, name: &str) -> bool {
    attr.path()
        .segments
        .last()
        .is_some_and(|segment| segment.ident == name)
}

fn expand_assert_forall_by_proof_obligations(
    proof_block: &syn::Block,
) -> Vec<proc_macro2::TokenStream> {
    proof_block
        .stmts
        .iter()
        .enumerate()
        .filter_map(|(index, stmt)| {
            let (path, tokens) = assert_forall_stmt_macro(stmt)?;
            let macro_name = path.segments.last()?.ident.to_string();
            let support_root = trust_vc_core::macro_support_root();
            let (kind, prefix_kind) = match macro_name.as_str() {
                "assume" | "ghost_requires" => (
                    quote! { #support_root::vc::ObligationKind::Assume },
                    "assume",
                ),
                "assert" => (
                    quote! { #support_root::vc::ObligationKind::Assert },
                    "assert",
                ),
                "requires" => (
                    quote! { #support_root::vc::ObligationKind::Requires },
                    "requires",
                ),
                "ensures" | "ghost_ensures" => (
                    quote! { #support_root::vc::ObligationKind::Ensures },
                    "ensures",
                ),
                _ => return None,
            };
            let ast_string = canonical_expr_ast_string(&tokens);
            let name_prefix = format!("assert_forall_by_{}_{}_line_", prefix_kind, index);
            Some(generate_obligation_collection(
                &tokens,
                &ast_string,
                kind,
                &name_prefix,
            ))
        })
        .collect()
}

fn assert_forall_stmt_macro(stmt: &syn::Stmt) -> Option<(&syn::Path, proc_macro2::TokenStream)> {
    match stmt {
        syn::Stmt::Macro(stmt_macro) => Some((&stmt_macro.mac.path, stmt_macro.mac.tokens.clone())),
        syn::Stmt::Expr(syn::Expr::Macro(expr_macro), _) => {
            Some((&expr_macro.mac.path, expr_macro.mac.tokens.clone()))
        }
        _ => None,
    }
}

/// Expands `assume_by!(condition, { block })` — scoped assumption.
///
/// Opens an assert_by scope, injects `condition` as an `Assume` obligation,
/// runs the proof block, then closes the scope with condition `"true"` (nothing
/// to prove). The assumption is visible only within the block and does not
/// propagate outside. Part of #945.
pub(crate) fn expand_assume_by_with_block(
    condition_tokens: proc_macro2::TokenStream,
    proof_block_tokens: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let condition_ast_string = canonical_expr_ast_string(&condition_tokens);

    // Inject the condition as a scoped assumption
    let assumption_collection = generate_obligation_collection(
        &condition_tokens,
        &condition_ast_string,
        quote! { #support_root::vc::ObligationKind::Assume },
        "assume_by_cond_line_",
    );

    // Use line+column for unique scope keys. Part of #2652.
    quote! {
        {
            #[cfg(test)]
            {
                #support_root::verify_macro::begin_assert_by_scope(
                    format!("assume_by_line_{}_col_{}", line!(), column!())
                );
                // Inject the condition as a scoped assumption
                #assumption_collection
                // Run the block with the assumption in scope
                #proof_block_tokens
                // Close scope with trivial condition — nothing to prove
                #support_root::verify_macro::end_assert_by_scope(
                    "true".to_string(),
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            }
            #[cfg(not(test))]
            {
                if false {
                    let _ = || { #condition_tokens };
                    let _ = || #proof_block_tokens;
                }
            }
        }
    }
}

/// Expands `assert_by_contradiction!(condition, { proof_block })`.
///
/// This is a thin wrapper over the existing scoped `assert_by!` path: it
/// injects an `assume!(!condition)` into the proof scope, then runs the user
/// proof block inside that same scope.
pub(crate) fn expand_assert_by_contradiction(
    condition_tokens: proc_macro2::TokenStream,
    proof_block_tokens: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let contradiction_assumption = expand_assume(quote! { !(#condition_tokens) });
    let contradiction_block = quote! {{
        #contradiction_assumption
        #proof_block_tokens
    }};

    expand_assert_by_with_proof_block(condition_tokens, contradiction_block)
}

/// Expands `calc! { ... }` into a chain of scoped assert_by calls.
///
/// Each step `lhs op { proof } rhs;` gets a unique scope key
/// `calc_line_<line>_step_<k>` and display label `calc step <k> of <n>`.
/// For multi-step chains, a transitive conclusion `first overall_op last` is
/// emitted with label `calc conclusion`. Part of #2413, #2652.
#[allow(clippy::indexing_slicing)] // invariant: `expressions[i]`/`[i+1]` bounded by `for i in 0..operators.len()` where expressions.len() == operators.len() + 1
pub(crate) fn expand_calc(tokens: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let block = match trust_vc_core::parse_calc(tokens) {
        Ok(b) => b,
        Err(err) => return err.to_compile_error(),
    };

    let support_root = trust_vc_core::macro_support_root();
    let n_steps = block.operators.len();
    let mut stmts = Vec::new();
    let mut step_condition_ast_strings = Vec::new();

    // Emit one scoped assert_by per step with explicit step labels. Part of #2652.
    // Uses begin_assert_by_scope_with_label to avoid scope key collisions
    // that occur when multiple calc! steps share the same call-site line!().
    for i in 0..n_steps {
        let lhs = &block.expressions[i];
        let rhs = &block.expressions[i + 1];
        let op = block.operators[i].to_tokens();
        let proof = &block.proof_blocks[i];
        let step_num = i + 1;
        let step_label = format!("calc step {step_num} of {n_steps}");

        let condition_tokens = quote! { #lhs #op #rhs };
        let condition_ast_string = canonical_expr_ast_string(&condition_tokens);
        step_condition_ast_strings.push((step_num, condition_ast_string.clone()));

        let parsed = syn::parse2::<syn::Expr>(condition_tokens.clone()).ok();
        let try_builder = parsed
            .as_ref()
            .and_then(trust_vc_core::expr_to_try_builder_tokens);

        let scope_end = if let Some(builder) = try_builder {
            quote! {
                if let Some(__trust_vc_expr) = { #builder } {
                    #support_root::verify_macro::end_assert_by_scope_expr(
                        __calc_condition_str,
                        __trust_vc_expr,
                        Some(format!("{}:{}:{}", file!(), line!(), column!())),
                    );
                } else {
                    #support_root::verify_macro::end_assert_by_scope(
                        __calc_condition_str,
                        Some(format!("{}:{}:{}", file!(), line!(), column!())),
                    );
                }
            }
        } else {
            quote! {
                #support_root::verify_macro::end_assert_by_scope(
                    __calc_condition_str,
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            }
        };

        // `==>` / `<==>` are Verus spec connectives, NOT exec operators, so the
        // raw `#condition_tokens` would not compile in the exec-side type-check
        // closure. For those steps, type-check the two operands independently.
        let non_test_operands_check = if matches!(
            block.operators[i],
            trust_vc_core::CalcOp::Implies | trust_vc_core::CalcOp::Iff
        ) {
            quote! {
                let _ = || { let _ = &#lhs; };
                let _ = || { let _ = &#rhs; };
            }
        } else {
            quote! { let _ = || { #condition_tokens }; }
        };

        stmts.push(quote! {
            #[cfg(test)]
            {
                #support_root::verify_macro::begin_assert_by_scope_with_label(
                    format!("calc_line_{}_step_{}", line!(), #step_num),
                    Some(#step_label.to_string()),
                );
                #proof
                let __calc_condition_str = #condition_ast_string.to_string();
                #scope_end
            }
            #[cfg(not(test))]
            {
                if false {
                    #non_test_operands_check
                    let _ = || { #proof };
                }
            }
        });
    }

    // Emit transitive conclusion (first overall_op last) for multi-step chains
    if n_steps > 1 {
        if let Some(overall_op) = block
            .overall_op_hint
            .or_else(|| trust_vc_core::transitive_op(&block.operators))
        {
            let Some(first) = block.expressions.first() else {
                return syn::Error::new(
                    proc_macro2::Span::call_site(),
                    "internal error: calc! multi-step chain missing initial expression",
                )
                .to_compile_error();
            };
            let Some(last) = block.expressions.last() else {
                return syn::Error::new(
                    proc_macro2::Span::call_site(),
                    "internal error: calc! multi-step chain missing final expression",
                )
                .to_compile_error();
            };
            let op = overall_op.to_tokens();
            let condition_tokens = quote! { #first #op #last };
            let condition_ast_string = canonical_expr_ast_string(&condition_tokens);
            let conclusion_step_assumes = step_condition_ast_strings
                .iter()
                .map(|(step_num, step_condition)| {
                    quote! {
                        #support_root::verify_macro::collect_typed_obligation(
                            #support_root::vc::ObligationKind::Assume,
                            format!("calc_line_{}_conclusion_step_{}", line!(), #step_num),
                            #step_condition.to_string(),
                            Some(format!("{}:{}:{}", file!(), line!(), column!())),
                        );
                    }
                })
                .collect::<Vec<_>>();

            let parsed = syn::parse2::<syn::Expr>(condition_tokens.clone()).ok();
            let try_builder = parsed
                .as_ref()
                .and_then(trust_vc_core::expr_to_try_builder_tokens);

            let scope_end = if let Some(builder) = try_builder {
                quote! {
                    if let Some(__trust_vc_expr) = { #builder } {
                        #support_root::verify_macro::end_assert_by_scope_expr(
                            __calc_condition_str,
                            __trust_vc_expr,
                            Some(format!("{}:{}:{}", file!(), line!(), column!())),
                        );
                    } else {
                        #support_root::verify_macro::end_assert_by_scope(
                            __calc_condition_str,
                            Some(format!("{}:{}:{}", file!(), line!(), column!())),
                        );
                    }
                }
            } else {
                quote! {
                    #support_root::verify_macro::end_assert_by_scope(
                        __calc_condition_str,
                        Some(format!("{}:{}:{}", file!(), line!(), column!())),
                    );
                }
            };

            // See the per-step note: the transitive conclusion may itself carry
            // a logical connective (`==>` / `<==>`), which is not an exec
            // operator, so type-check its operands independently there.
            let conclusion_non_test_check = if matches!(
                overall_op,
                trust_vc_core::CalcOp::Implies | trust_vc_core::CalcOp::Iff
            ) {
                quote! {
                    let _ = || { let _ = &#first; };
                    let _ = || { let _ = &#last; };
                }
            } else {
                quote! { let _ = || { #condition_tokens }; }
            };

            stmts.push(quote! {
                #[cfg(test)]
                {
                    #support_root::verify_macro::begin_assert_by_scope_with_label(
                        format!("calc_line_{}_conclusion", line!()),
                        Some("calc conclusion".to_string()),
                    );
                    #(#conclusion_step_assumes)*
                    let __calc_condition_str = #condition_ast_string.to_string();
                    #scope_end
                }
                #[cfg(not(test))]
                {
                    if false {
                        #conclusion_non_test_check
                    }
                }
            });
        }
    }

    quote! { #(#stmts)* }
}
