//! Compile-time function contract registry for postcondition propagation.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Stores requires/ensures contracts discovered during proc-macro expansion.
//! At call sites within proof functions, the caller looks up the callee's
//! contract and emits:
//! - Assert(requires) — caller must prove preconditions
//! - Assume(ensures) — postconditions become available to caller
//!
//! Mirrors the `mode.rs` compile-time registry pattern.
//!
//! Part of #2513, #1573.

use crate::extern_spec_call_bindings::{substitute_contract_placeholders, ExternSpecCallBindings};
use quote::quote;
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};
use syn::visit_mut::VisitMut;

/// A function's proof contract: requires and ensures clauses.
#[derive(Debug, Clone)]
pub(crate) struct FunctionContract {
    pub param_names: Vec<String>,
    pub requires: Vec<String>,
    pub ensures: Vec<String>,
}

/// Process-global registry for function contracts discovered during macro
/// expansion. Uses the same `OnceLock<Mutex<...>>` pattern as the compile-time
/// mode registry in `mode.rs`.
static COMPILE_TIME_CONTRACT_REGISTRY: OnceLock<Mutex<HashMap<String, FunctionContract>>> =
    OnceLock::new();

fn contract_registry() -> &'static Mutex<HashMap<String, FunctionContract>> {
    COMPILE_TIME_CONTRACT_REGISTRY.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Registers a function's contract in the compile-time registry.
///
/// Called during `expand_proof_with_tracked` after extracting requires/ensures
/// from the function body.
pub(crate) fn register_compile_time_function_contract(name: &str, contract: FunctionContract) {
    let mut registry = contract_registry()
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    registry.insert(name.to_string(), contract);
}

/// Looks up a function's contract from the compile-time registry.
///
/// Returns `None` if the function has no registered contract (e.g., it was
/// expanded after the caller, or has no requires/ensures clauses).
pub(crate) fn lookup_compile_time_function_contract(name: &str) -> Option<FunctionContract> {
    let registry = contract_registry()
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    registry.get(name).cloned()
}

/// Extracts requires/ensures contract clauses from a proof function body.
///
/// Walks the block's top-level statements looking for macro invocations
/// whose last path segment is `requires` or `ensures` (matching both
/// `trust_vc::requires!(...)` and `requires!(...)`). Returns the condition
/// token streams as strings.
pub(crate) fn extract_contracts_from_block(block: &syn::Block) -> (Vec<String>, Vec<String>) {
    let mut requires = Vec::new();
    let mut ensures = Vec::new();

    for stmt in &block.stmts {
        let syn::Stmt::Macro(stmt_macro) = stmt else {
            continue;
        };
        let Some(name) = stmt_macro
            .mac
            .path
            .segments
            .last()
            .map(|s| s.ident.to_string())
        else {
            continue;
        };
        let condition = stmt_macro.mac.tokens.to_string();
        match name.as_str() {
            "requires" => requires.push(condition),
            "ensures" => ensures.push(condition),
            _ => {}
        }
    }

    (requires, ensures)
}

/// Extracts parameter names from a function signature.
///
/// Returns names of simple `Pat::Ident` parameters, skipping `self` and
/// complex patterns.
pub(crate) fn extract_param_names(sig: &syn::Signature) -> Vec<String> {
    sig.inputs
        .iter()
        .filter_map(|arg| match arg {
            syn::FnArg::Typed(pat_type) => match &*pat_type.pat {
                syn::Pat::Ident(pat_ident) => Some(pat_ident.ident.to_string()),
                _ => None,
            },
            syn::FnArg::Receiver(_) => None,
        })
        .collect()
}

/// Transforms a proof block to inject call-site contract checking.
///
/// For each standalone function call statement `callee(args);` where the
/// callee has a registered contract, replaces the statement with:
/// 1. Assert requires (substituted with actual args)
/// 2. The original call
/// 3. Assume ensures (substituted with actual args)
///
/// Calls without registered contracts are left unchanged.
pub(crate) fn inject_call_site_contracts(block: &syn::Block) -> syn::Result<syn::Block> {
    let mut rewritten = block.clone();
    let mut injector = CallSiteContractInjector::default();
    injector.visit_block_mut(&mut rewritten);

    match injector.into_error() {
        Some(err) => Err(err),
        None => Ok(rewritten),
    }
}

#[derive(Default)]
struct CallSiteContractInjector {
    errors: Vec<syn::Error>,
}

impl CallSiteContractInjector {
    fn into_error(self) -> Option<syn::Error> {
        let mut errors = self.errors.into_iter();
        let mut combined = errors.next()?;
        for err in errors {
            combined.combine(err);
        }
        Some(combined)
    }
}

impl VisitMut for CallSiteContractInjector {
    fn visit_block_mut(&mut self, block: &mut syn::Block) {
        let mut new_stmts = Vec::with_capacity(block.stmts.len());

        for mut stmt in std::mem::take(&mut block.stmts) {
            syn::visit_mut::visit_stmt_mut(self, &mut stmt);

            match try_expand_call_stmt(&stmt) {
                Ok(Some(expanded)) => new_stmts.extend(expanded),
                Ok(None) => new_stmts.push(stmt),
                Err(err) => {
                    self.errors.push(err);
                    new_stmts.push(stmt);
                }
            }
        }

        block.stmts = new_stmts;
    }
}

/// Tries to expand a statement that is a standalone function call with a
/// registered contract. Returns `Ok(None)` if the statement is not a call or
/// the callee has no registered contract.
fn try_expand_call_stmt(stmt: &syn::Stmt) -> syn::Result<Option<Vec<syn::Stmt>>> {
    // Match standalone call statements: `callee(args);`
    let (call_expr, semi) = match stmt {
        syn::Stmt::Expr(syn::Expr::Call(call), semi) => (call, *semi),
        _ => return Ok(None),
    };

    // Extract callee function name (last segment of path)
    let (callee_name, call_span) = match &*call_expr.func {
        syn::Expr::Path(path) => {
            let Some(last_segment) = path.path.segments.last() else {
                return Ok(None);
            };
            (last_segment.ident.to_string(), last_segment.ident.span())
        }
        _ => return Ok(None),
    };

    // Look up the callee's contract
    let Some(contract) = lookup_compile_time_function_contract(&callee_name) else {
        return Ok(None);
    };

    // Extract actual argument expressions as strings
    let actual_args: Vec<String> = call_expr
        .args
        .iter()
        .map(|arg| quote!(#arg).to_string())
        .collect();

    // Build the substitution bindings
    let bindings = ExternSpecCallBindings {
        receiver_expr: None,
        arg_exprs: actual_args,
        result_expr: None,
    };
    let support_root = crate::macro_support_root();

    let mut stmts: Vec<syn::Stmt> = Vec::new();

    // 1. Assert requires (caller must prove preconditions)
    for (i, req) in contract.requires.iter().enumerate() {
        let substituted = rewrite_call_site_contract_clause(
            req,
            &contract.param_names,
            &bindings,
            call_span,
            &callee_name,
            "requires",
            i,
        )?;
        let name = format!("{}_requires_{}", callee_name, i);
        let assert_stmt: syn::Stmt = syn::parse_quote! {
            #support_root::verify_macro::collect_obligation(
                #support_root::vc::ObligationKind::Assert,
                #name.to_string(),
                #substituted.to_string(),
                None,
            );
        };
        stmts.push(assert_stmt);
    }

    // 2. The original call
    let orig = syn::Expr::Call(call_expr.clone());
    stmts.push(syn::Stmt::Expr(orig, semi));

    // 3. Assume ensures (postconditions become available to caller)
    for (i, ens) in contract.ensures.iter().enumerate() {
        let substituted = rewrite_call_site_contract_clause(
            ens,
            &contract.param_names,
            &bindings,
            call_span,
            &callee_name,
            "ensures",
            i,
        )?;
        let name = format!("{}_ensures_{}", callee_name, i);
        let assume_stmt: syn::Stmt = syn::parse_quote! {
            #support_root::verify_macro::collect_obligation(
                #support_root::vc::ObligationKind::Assume,
                #name.to_string(),
                #substituted.to_string(),
                None,
            );
        };
        stmts.push(assume_stmt);
    }

    Ok(Some(stmts))
}

fn rewrite_call_site_contract_clause(
    clause: &str,
    param_names: &[String],
    bindings: &ExternSpecCallBindings,
    call_span: proc_macro2::Span,
    callee_name: &str,
    clause_kind: &str,
    clause_index: usize,
) -> syn::Result<String> {
    substitute_contract_placeholders(clause, param_names, bindings).map_err(|err| {
        syn::Error::new(
            call_span,
            format!(
                "failed to rewrite proof-call {} clause {} for `{}`: {}",
                clause_kind, clause_index, callee_name, err
            ),
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_register_and_lookup_contract() {
        let contract = FunctionContract {
            param_names: vec!["n".to_string()],
            requires: vec!["n > 0".to_string()],
            ensures: vec!["sum(n) >= 0".to_string()],
        };
        register_compile_time_function_contract("lemma_sum_positive", contract);

        let found = lookup_compile_time_function_contract("lemma_sum_positive");
        assert!(found.is_some());
        let c = found.unwrap();
        assert_eq!(c.param_names, vec!["n"]);
        assert_eq!(c.requires, vec!["n > 0"]);
        assert_eq!(c.ensures, vec!["sum(n) >= 0"]);
    }

    #[test]
    fn test_lookup_unknown_returns_none() {
        assert!(lookup_compile_time_function_contract("unknown_fn").is_none());
    }

    #[test]
    fn test_register_overwrites_previous() {
        let c1 = FunctionContract {
            param_names: vec!["x".to_string()],
            requires: vec!["x > 0".to_string()],
            ensures: vec![],
        };
        register_compile_time_function_contract("my_fn", c1);

        let c2 = FunctionContract {
            param_names: vec!["x".to_string()],
            requires: vec![],
            ensures: vec!["x == x".to_string()],
        };
        register_compile_time_function_contract("my_fn", c2);

        let found = lookup_compile_time_function_contract("my_fn").unwrap();
        assert!(found.requires.is_empty());
        assert_eq!(found.ensures, vec!["x == x"]);
    }

    #[test]
    fn test_extract_contracts_from_block_collects_requires_and_ensures() {
        let block: syn::Block = syn::parse_quote!({
            trust_vc::requires!(n > 0);
            trust_vc::ensures!(mystery(n) == 7);
            helper(n);
        });

        let (requires, ensures) = extract_contracts_from_block(&block);
        assert_eq!(requires, vec!["n > 0"]);
        assert_eq!(ensures, vec!["mystery (n) == 7"]);
    }

    #[test]
    fn test_inject_call_site_contracts_inserts_asserts_and_assumes() {
        register_compile_time_function_contract(
            "lemma_contract_2513",
            FunctionContract {
                param_names: vec!["n".to_string()],
                requires: vec!["n > 0".to_string()],
                ensures: vec!["mystery(n) == 7".to_string()],
            },
        );

        let block: syn::Block = syn::parse_quote!({
            lemma_contract_2513(x + 1);
        });
        let rewritten = inject_call_site_contracts(&block).expect("call-site rewrite should work");
        let rewritten_str = quote!(#rewritten).to_string();

        assert!(rewritten_str.contains("lemma_contract_2513_requires_0"));
        assert!(rewritten_str.contains("lemma_contract_2513_ensures_0"));
        assert!(rewritten_str.contains("ObligationKind :: Assert"));
        assert!(rewritten_str.contains("ObligationKind :: Assume"));
        assert!(rewritten_str.contains("x + 1"));
    }

    #[test]
    fn test_inject_call_site_contracts_rewrites_nested_blocks() {
        register_compile_time_function_contract(
            "lemma_nested_2513",
            FunctionContract {
                param_names: vec!["x".to_string()],
                requires: vec![],
                ensures: vec!["mystery(x) == 7".to_string()],
            },
        );

        let block: syn::Block = syn::parse_quote!({
            if guard {
                lemma_nested_2513(value);
            }
        });
        let rewritten = inject_call_site_contracts(&block).expect("nested rewrite should work");
        let rewritten_str = quote!(#rewritten).to_string();

        assert!(rewritten_str.contains("if guard"));
        assert!(rewritten_str.contains("lemma_nested_2513_ensures_0"));
    }

    #[test]
    fn test_inject_call_site_contracts_errors_on_substitution_failure() {
        register_compile_time_function_contract(
            "lemma_broken_2513",
            FunctionContract {
                param_names: vec!["x".to_string()],
                requires: vec!["x > 0".to_string()],
                ensures: vec![],
            },
        );

        let block: syn::Block = syn::parse_quote!({
            lemma_broken_2513();
        });
        let err = match inject_call_site_contracts(&block) {
            Ok(_) => panic!("arity mismatch should surface as a compile-time error"),
            Err(err) => err,
        };
        let err_text = err.to_string();

        assert!(err_text.contains("failed to rewrite proof-call requires clause 0"));
        assert!(err_text.contains("arity mismatch"));
    }
}
