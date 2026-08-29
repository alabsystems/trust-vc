//! Fail-closed modeling of `self.<field>` reads on an abstract trait receiver.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Trait-default and generic-struct conformance is checked on a `Poly` receiver.
//! `Poly` has no datatype selectors, so a direct field read used to make the
//! auxiliary obligation unbuildable.  Model each such read as a stable,
//! trait-scoped projection UF.  Its value is intentionally unconstrained: this
//! preserves a valid relation such as `result == self.flag`, while preventing
//! `self.flag` from establishing an unrelated fact such as `result == true`.
//!
//! The projection sort is proof authority.  We therefore infer it only from a
//! small set of source-typed contexts and reject missing or conflicting evidence.
//! In particular, there is no return-type fallback for an arbitrary nested read.

use std::collections::{BTreeMap, BTreeSet};

use syn::visit::Visit;

use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::{TraitMethodDecl, TrustVcType};

/// A modeled `self.<field>` projection on an abstract `Poly` receiver.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PolySelfFieldProjection {
    pub(crate) field_name: String,
    pub(crate) uf_name: String,
    pub(crate) field_type: TrustVcType,
}

/// One deterministic solver identity, shared by trait registration, contract
/// lowering, default-body axioms, and conformance checking.
pub(crate) fn poly_self_field_uf_name(trait_name: &str, field_name: &str) -> String {
    format!(
        "__trust_vc_poly_self_field_{}__{}",
        crate::encoder::sanitize_symbol(trait_name),
        crate::encoder::sanitize_symbol(field_name),
    )
}

/// Discovers and types every direct `self.<field>` in this method's contracts
/// and the supplied effective bodies.
///
/// Contract roots have the expected type `bool`; an effective-body root has the
/// method return type.  Comparison/arithmetic peers, declared parameters,
/// `result`, suffixed integer literals, boolean literals, and explicit casts
/// supply additional evidence.  Parse failures, type conflicts, and fields with
/// no supported evidence are errors so no caller can accidentally mint a UF at
/// a guessed sort.
pub(crate) fn poly_self_field_projections(
    trait_name: &str,
    method: &TraitMethodDecl,
    extra_body_texts: &[&str],
) -> TrustVcResult<Vec<PolySelfFieldProjection>> {
    let mut collector = SelfFieldCollector::new(method);

    for contract in method.requires.iter().chain(&method.ensures) {
        let expr = parse_projection_expr(contract)?;
        collector.record_root_type(&expr, &TrustVcType::Bool);
        collector.visit_expr(&expr);
    }
    for body in extra_body_texts {
        let expr = parse_projection_expr(body)?;
        collector.record_root_type(&expr, &method.return_type);
        collector.visit_expr(&expr);
    }

    collector.finish(trait_name, &method.name)
}

fn parse_projection_expr(text: &str) -> TrustVcResult<syn::Expr> {
    syn::parse_str(text).map_err(|source| TrustVcError::Parse {
        context: "parse trait self-field expression",
        source,
    })
}

struct SelfFieldCollector<'a> {
    method: &'a TraitMethodDecl,
    fields: BTreeSet<String>,
    evidence: BTreeMap<String, Vec<TrustVcType>>,
}

impl<'a> SelfFieldCollector<'a> {
    fn new(method: &'a TraitMethodDecl) -> Self {
        Self {
            method,
            fields: BTreeSet::new(),
            evidence: BTreeMap::new(),
        }
    }

    fn record(&mut self, field: String, ty: TrustVcType) {
        self.fields.insert(field.clone());
        let candidates = self.evidence.entry(field).or_default();
        if !candidates.contains(&ty) {
            candidates.push(ty);
        }
    }

    fn record_root_type(&mut self, expr: &syn::Expr, expected: &TrustVcType) {
        if let Some(field) = returned_self_field_name(expr) {
            self.record(field, expected.clone());
        }
    }

    fn finish(
        self,
        trait_name: &str,
        method_name: &str,
    ) -> TrustVcResult<Vec<PolySelfFieldProjection>> {
        self.fields
            .into_iter()
            .map(|field_name| {
                let candidates = self
                    .evidence
                    .get(&field_name)
                    .map(Vec::as_slice)
                    .unwrap_or(&[]);
                let [field_type] = candidates else {
                    let detail = if candidates.is_empty() {
                        format!(
                            "cannot infer a sound type for abstract receiver field \
                             '{trait_name}::{method_name}: self.{field_name}'"
                        )
                    } else {
                        let rendered = candidates
                            .iter()
                            .map(TrustVcType::to_type_string)
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!(
                            "conflicting types for abstract receiver field \
                             '{trait_name}::{method_name}: self.{field_name}': {rendered}"
                        )
                    };
                    return Err(TrustVcError::Encoding {
                        context: "trait self-field projection",
                        detail,
                    });
                };
                Ok(PolySelfFieldProjection {
                    uf_name: poly_self_field_uf_name(trait_name, &field_name),
                    field_name,
                    field_type: field_type.clone(),
                })
            })
            .collect()
    }
}

impl<'ast> Visit<'ast> for SelfFieldCollector<'_> {
    fn visit_expr_field(&mut self, field: &'ast syn::ExprField) {
        if let Some(name) = self_field_name_from_field(field) {
            self.fields.insert(name);
        }
        syn::visit::visit_expr_field(self, field);
    }

    fn visit_expr_binary(&mut self, binary: &'ast syn::ExprBinary) {
        use syn::BinOp;

        let same_typed_operands = matches!(
            binary.op,
            BinOp::Add(_)
                | BinOp::Sub(_)
                | BinOp::Mul(_)
                | BinOp::Div(_)
                | BinOp::Rem(_)
                | BinOp::BitXor(_)
                | BinOp::BitAnd(_)
                | BinOp::BitOr(_)
                | BinOp::Eq(_)
                | BinOp::Lt(_)
                | BinOp::Le(_)
                | BinOp::Ne(_)
                | BinOp::Ge(_)
                | BinOp::Gt(_)
        );
        if same_typed_operands {
            if let (Some(field), Some(ty)) = (
                self_field_name(&binary.left),
                infer_known_expr_type(&binary.right, self.method),
            ) {
                self.record(field, ty);
            }
            if let (Some(field), Some(ty)) = (
                self_field_name(&binary.right),
                infer_known_expr_type(&binary.left, self.method),
            ) {
                self.record(field, ty);
            }
        }
        if matches!(binary.op, BinOp::And(_) | BinOp::Or(_)) {
            if let Some(field) = self_field_name(&binary.left) {
                self.record(field, TrustVcType::Bool);
            }
            if let Some(field) = self_field_name(&binary.right) {
                self.record(field, TrustVcType::Bool);
            }
        }
        syn::visit::visit_expr_binary(self, binary);
    }

    fn visit_expr_unary(&mut self, unary: &'ast syn::ExprUnary) {
        if matches!(unary.op, syn::UnOp::Not(_)) {
            if let Some(field) = self_field_name(&unary.expr) {
                self.record(field, TrustVcType::Bool);
            }
        }
        syn::visit::visit_expr_unary(self, unary);
    }

    fn visit_expr_if(&mut self, expr_if: &'ast syn::ExprIf) {
        if let Some(field) = self_field_name(&expr_if.cond) {
            self.record(field, TrustVcType::Bool);
        }
        syn::visit::visit_expr_if(self, expr_if);
    }
}

fn returned_self_field_name(expr: &syn::Expr) -> Option<String> {
    match expr {
        syn::Expr::Paren(paren) => returned_self_field_name(&paren.expr),
        syn::Expr::Group(group) => returned_self_field_name(&group.expr),
        syn::Expr::Block(block) if block.label.is_none() => {
            let [statement] = block.block.stmts.as_slice() else {
                return None;
            };
            match statement {
                syn::Stmt::Expr(syn::Expr::Return(ret), _) => {
                    ret.expr.as_deref().and_then(returned_self_field_name)
                }
                syn::Stmt::Expr(tail, None) => returned_self_field_name(tail),
                _ => None,
            }
        }
        syn::Expr::Return(ret) => ret.expr.as_deref().and_then(returned_self_field_name),
        _ => self_field_name(expr),
    }
}

fn self_field_name(expr: &syn::Expr) -> Option<String> {
    match expr {
        syn::Expr::Field(field) => self_field_name_from_field(field),
        syn::Expr::Paren(paren) => self_field_name(&paren.expr),
        syn::Expr::Group(group) => self_field_name(&group.expr),
        _ => None,
    }
}

fn self_field_name_from_field(field: &syn::ExprField) -> Option<String> {
    if !expr_is_self_receiver(&field.base) {
        return None;
    }
    Some(match &field.member {
        syn::Member::Named(ident) => ident.to_string(),
        syn::Member::Unnamed(index) => index.index.to_string(),
    })
}

fn expr_is_self_receiver(expr: &syn::Expr) -> bool {
    match expr {
        syn::Expr::Path(path) => path.qself.is_none() && path.path.is_ident("self"),
        syn::Expr::Paren(paren) => expr_is_self_receiver(&paren.expr),
        syn::Expr::Group(group) => expr_is_self_receiver(&group.expr),
        _ => false,
    }
}

fn infer_known_expr_type(expr: &syn::Expr, method: &TraitMethodDecl) -> Option<TrustVcType> {
    match expr {
        syn::Expr::Path(path) if path.qself.is_none() && path.path.segments.len() == 1 => {
            let name = path.path.segments[0].ident.to_string();
            if name == "result" {
                return Some(method.return_type.clone());
            }
            method
                .params
                .iter()
                .find(|(param_name, _)| param_name == &name)
                .map(|(_, ty)| ty.clone())
        }
        syn::Expr::Lit(lit) => match &lit.lit {
            syn::Lit::Int(int) if !int.suffix().is_empty() => {
                TrustVcType::try_from_str(int.suffix()).ok()
            }
            syn::Lit::Bool(_) => Some(TrustVcType::Bool),
            _ => None,
        },
        syn::Expr::Cast(cast) => {
            let rendered = quote::ToTokens::to_token_stream(&cast.ty).to_string();
            Some(TrustVcType::parse_or_opaque(&rendered))
        }
        syn::Expr::Paren(paren) => infer_known_expr_type(&paren.expr, method),
        syn::Expr::Group(group) => infer_known_expr_type(&group.expr, method),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn method(return_type: TrustVcType) -> TraitMethodDecl {
        TraitMethodDecl::new(
            "m",
            Vec::new(),
            return_type,
            Vec::new(),
            Vec::new(),
            false,
            None,
        )
    }

    #[test]
    fn root_body_field_uses_return_type() {
        let method = method(TrustVcType::Bool);
        let projections = poly_self_field_projections("T", &method, &["{ self.flag }"])
            .expect("root field has exact return-type evidence");
        assert_eq!(projections[0].field_type, TrustVcType::Bool);
    }

    #[test]
    fn unknown_nested_field_type_fails_closed() {
        let method = method(TrustVcType::Bool);
        let error = poly_self_field_projections("T", &method, &["helper(self.value)"])
            .expect_err("nested field without source-typed context must be rejected");
        assert!(error.to_string().contains("cannot infer a sound type"));
    }

    #[test]
    fn conflicting_field_types_fail_closed() {
        let mut method = method(TrustVcType::Bool);
        method.ensures = vec![
            "self.value == true".to_string(),
            "self.value == 1u32".to_string(),
        ];
        let error = poly_self_field_projections("T", &method, &[])
            .expect_err("one field cannot acquire two solver sorts");
        assert!(error.to_string().contains("conflicting types"));
    }
}
