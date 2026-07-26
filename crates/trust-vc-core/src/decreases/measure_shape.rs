//! Measure-shape analysis for `#[decreases(...)]`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Detects when a decreases component is a direct recursive-datatype
//! parameter so the macro can rewrite it to `__trust_vc_dt_size(...)`.

use std::collections::HashSet;

use proc_macro2::TokenStream;
use quote::quote;
use syn::visit::{self, Visit};
use syn::{punctuated::Punctuated, Expr, Signature, Token};

use crate::ir::TrustVcType;
use crate::local_vars::extract_type_string;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MeasurePlan {
    Legacy,
    RecursiveAware(Vec<DirectMeasureComponent>),
    UnsupportedRecursiveDatatype,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DirectMeasureComponent {
    pub(crate) param_name: String,
    pub(crate) param_index: usize,
    pub(crate) recursive_datatype: bool,
}

#[derive(Debug, Clone)]
struct ParamInfo {
    name: String,
    index: usize,
    recursive_datatype: bool,
}

pub(crate) fn analyze_measure_plan(
    sig: &Signature,
    parsed: &Punctuated<Expr, Token![,]>,
) -> MeasurePlan {
    let params = collect_param_infos(sig);
    let recursive_params: HashSet<String> = params
        .iter()
        .filter(|param| param.recursive_datatype)
        .map(|param| param.name.clone())
        .collect();

    let mut direct_components = Vec::with_capacity(parsed.len());
    let mut saw_recursive_component = false;
    let mut saw_non_param_component = false;

    for expr in parsed {
        if let Some(name) = direct_param_ident(expr) {
            if let Some(param) = params.iter().find(|param| param.name == name) {
                saw_recursive_component |= param.recursive_datatype;
                direct_components.push(DirectMeasureComponent {
                    param_name: param.name.clone(),
                    param_index: param.index,
                    recursive_datatype: param.recursive_datatype,
                });
                continue;
            }
        }

        if expr_references_recursive_param(expr, &recursive_params) {
            return MeasurePlan::UnsupportedRecursiveDatatype;
        }
        saw_non_param_component = true;
    }

    if saw_recursive_component {
        if saw_non_param_component {
            MeasurePlan::UnsupportedRecursiveDatatype
        } else {
            MeasurePlan::RecursiveAware(direct_components)
        }
    } else {
        MeasurePlan::Legacy
    }
}

pub(crate) fn render_entry_measure(components: &[DirectMeasureComponent]) -> String {
    let rendered: Vec<String> = components
        .iter()
        .map(|component| render_component_expr(&component.param_name, component.recursive_datatype))
        .collect();
    render_measure_tuple(&rendered)
}

/// Renders the recursive measure for a call site's arguments.
///
/// `is_self_call` indicates whether this is a self-recursive call (same function).
/// For mutual recursion (`!is_self_call`), the caller's `param_index` mapping may
/// not correspond to the callee's parameter ordering, so we conservatively return
/// `None` and let the caller emit a rejecting decrease condition. This prevents
/// unsound measure extraction when mutual peers have different parameter
/// orderings (e.g., `f(n, m)` calls `g(m, n)`). Fix for #2550 finding F3.
pub(crate) fn render_recursive_measure(
    components: &[DirectMeasureComponent],
    args: &Punctuated<Expr, Token![,]>,
    is_self_call: bool,
) -> Option<String> {
    // For mutual recursion, the caller's param_index mapping is unreliable
    // because the callee may have different parameter ordering.
    // Conservative: return None so the caller can emit a rejecting obligation.
    if !is_self_call {
        return None;
    }
    let rendered_args: Vec<String> = args.iter().map(expr_to_string).collect();
    let rendered: Option<Vec<String>> = components
        .iter()
        .map(|component| {
            rendered_args
                .get(component.param_index)
                .map(|expr| render_component_expr(expr, component.recursive_datatype))
        })
        .collect();
    rendered.map(|parts| render_measure_tuple(&parts))
}

pub(crate) fn render_unsupported_recursive_measure_condition(
    when_condition: Option<&str>,
) -> String {
    let condition = "false".to_string();
    if let Some(when_condition) = when_condition {
        format!("(!({})) || ({})", when_condition, condition)
    } else {
        condition
    }
}

fn collect_param_infos(sig: &Signature) -> Vec<ParamInfo> {
    sig.inputs
        .iter()
        .enumerate()
        .filter_map(|(index, arg)| {
            let syn::FnArg::Typed(pat_type) = arg else {
                return None;
            };
            let syn::Pat::Ident(pat_ident) = &*pat_type.pat else {
                return None;
            };

            let ty = TrustVcType::parse_or_opaque(&extract_type_string(&pat_type.ty));
            Some(ParamInfo {
                name: pat_ident.ident.to_string(),
                index,
                recursive_datatype: is_recursive_datatype(&ty),
            })
        })
        .collect()
}

fn is_recursive_datatype(ty: &TrustVcType) -> bool {
    let TrustVcType::Datatype { name, variants } = ty else {
        return false;
    };

    variants.iter().any(|variant| {
        variant.fields.iter().any(|(_, field_ty)| {
            matches!(field_ty, TrustVcType::RecursiveRef(ref recursive_name) if recursive_name == name)
        })
    })
}

fn direct_param_ident(expr: &Expr) -> Option<String> {
    match strip_parens(expr) {
        Expr::Path(path) if path.qself.is_none() && path.path.segments.len() == 1 => path
            .path
            .segments
            .first()
            .map(|segment| segment.ident.to_string()),
        _ => None,
    }
}

fn strip_parens(expr: &Expr) -> &Expr {
    match expr {
        Expr::Paren(paren) => strip_parens(&paren.expr),
        Expr::Group(group) => strip_parens(&group.expr),
        other => other,
    }
}

fn expr_references_recursive_param(expr: &Expr, recursive_params: &HashSet<String>) -> bool {
    if recursive_params.is_empty() {
        return false;
    }

    struct RecursiveParamFinder<'a> {
        recursive_params: &'a HashSet<String>,
        found: bool,
    }

    impl Visit<'_> for RecursiveParamFinder<'_> {
        fn visit_expr_path(&mut self, path: &syn::ExprPath) {
            if self.found {
                return;
            }
            if path.qself.is_none() && path.path.segments.len() == 1 {
                if let Some(segment) = path.path.segments.first() {
                    let ident = segment.ident.to_string();
                    if self.recursive_params.contains(&ident) {
                        self.found = true;
                        return;
                    }
                }
            }
            visit::visit_expr_path(self, path);
        }
    }

    let mut finder = RecursiveParamFinder {
        recursive_params,
        found: false,
    };
    finder.visit_expr(expr);
    finder.found
}

fn render_component_expr(expr: &str, recursive_datatype: bool) -> String {
    if recursive_datatype {
        format!("__trust_vc_dt_size({expr})")
    } else {
        expr.to_string()
    }
}

fn render_measure_tuple(parts: &[String]) -> String {
    match parts {
        [single] => single.clone(),
        many => format!("({})", many.join(", ")),
    }
}

fn expr_to_string(expr: &Expr) -> String {
    let tokens: TokenStream = quote!(#expr);
    tokens.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use syn::parse::Parser;

    fn parse_sig(src: &str) -> Signature {
        syn::parse_str::<syn::ItemFn>(src)
            .expect("function should parse")
            .sig
    }

    fn parse_measures(src: &str) -> Punctuated<Expr, Token![,]> {
        syn::punctuated::Punctuated::<Expr, Token![,]>::parse_terminated
            .parse_str(src)
            .expect("measures should parse")
    }

    #[test]
    fn measure_plan_uses_legacy_for_non_recursive_expressions() {
        let sig = parse_sig("fn count(n: u64) {}");
        let parsed = parse_measures("n - 1");

        assert_eq!(analyze_measure_plan(&sig, &parsed), MeasurePlan::Legacy);
    }

    #[test]
    fn measure_plan_detects_recursive_direct_param() {
        let sig = parse_sig("fn walk(list: List<i32>) {}");
        let parsed = parse_measures("list");

        assert_eq!(
            analyze_measure_plan(&sig, &parsed),
            MeasurePlan::RecursiveAware(vec![DirectMeasureComponent {
                param_name: "list".to_string(),
                param_index: 0,
                recursive_datatype: true,
            }])
        );
    }

    #[test]
    fn measure_plan_detects_mixed_recursive_and_scalar_direct_params() {
        let sig = parse_sig("fn walk(tree: Tree<i32>, fuel: u64) {}");
        let parsed = parse_measures("tree, fuel");
        let plan = analyze_measure_plan(&sig, &parsed);

        let MeasurePlan::RecursiveAware(components) = plan else {
            panic!("expected recursive-aware plan");
        };
        assert_eq!(
            render_entry_measure(&components),
            "(__trust_vc_dt_size(tree), fuel)"
        );

        let call_args = parse_measures("left, fuel - 1");
        // Self-call: param_index mapping is correct.
        assert_eq!(
            render_recursive_measure(&components, &call_args, true).as_deref(),
            Some("(__trust_vc_dt_size(left), fuel - 1)")
        );
        // Mutual call: conservative fallback returns None (#2550 F3).
        assert_eq!(
            render_recursive_measure(&components, &call_args, false),
            None,
        );
    }

    #[test]
    fn measure_plan_rejects_recursive_helper_expression() {
        let sig = parse_sig("fn walk(list: List<i32>) {}");
        let parsed = parse_measures("list.tail()");

        assert_eq!(
            analyze_measure_plan(&sig, &parsed),
            MeasurePlan::UnsupportedRecursiveDatatype
        );
    }

    #[test]
    fn unsupported_recursive_measure_condition_honors_when_guard() {
        assert_eq!(
            render_unsupported_recursive_measure_condition(Some("n > 0")),
            "(!(n > 0)) || (false)"
        );
        assert_eq!(
            render_unsupported_recursive_measure_condition(None),
            "false".to_string()
        );
    }
}
