//! Trait-impl conformance type-specialization and syntax helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;

use syn::visit_mut::{self, VisitMut};

use super::super::encoding_error;
use super::{CONFORMANCE_CONTEXT, CONFORMANCE_RESULT, CONFORMANCE_SELF};
use crate::error::TrustVcError;
use crate::ir::{DatatypeVariant, TraitDecl, TraitImplDecl, TraitMethodDecl, TrustVcType};
use crate::vc::{FunctionContext, VariableDecl};

pub(super) fn validate_concrete_function_signature(
    concrete_fn_ctx: &FunctionContext,
    bindings: &ContractBindings,
    impl_decl: &TraitImplDecl,
    trait_decl: &TraitDecl,
    method: &TraitMethodDecl,
) -> Result<(), TrustVcError> {
    let expected_param_count = bindings.params.len() + 1;
    if concrete_fn_ctx.params.len() != expected_param_count {
        return Err(encoding_error(
            CONFORMANCE_CONTEXT,
            format!(
                "concrete impl function '{}' for '{}::{}' expected {} params, found {}",
                concrete_fn_ctx.name,
                trait_decl.name,
                method.name,
                expected_param_count,
                concrete_fn_ctx.params.len()
            ),
        ));
    }

    let Some((_, self_ty)) = concrete_fn_ctx.params.first() else {
        return Err(encoding_error(
            CONFORMANCE_CONTEXT,
            format!(
                "concrete impl function '{}' missing receiver parameter",
                concrete_fn_ctx.name
            ),
        ));
    };
    if self_ty != &impl_decl.concrete_type {
        return Err(encoding_error(
            CONFORMANCE_CONTEXT,
            format!(
                "concrete impl function '{}' has receiver type '{}', expected '{}'",
                concrete_fn_ctx.name,
                self_ty.to_type_string(),
                impl_decl.concrete_type.to_type_string()
            ),
        ));
    }

    for ((param_name, param_ty), binding) in
        concrete_fn_ctx.params.iter().skip(1).zip(&bindings.params)
    {
        if param_ty != &binding.ty {
            return Err(encoding_error(
                CONFORMANCE_CONTEXT,
                format!(
                    "concrete impl function '{}' param '{}' has type '{}', expected '{}'",
                    concrete_fn_ctx.name,
                    param_name,
                    param_ty.to_type_string(),
                    binding.ty.to_type_string()
                ),
            ));
        }
    }

    if concrete_fn_ctx.return_type != bindings.result_ty {
        return Err(encoding_error(
            CONFORMANCE_CONTEXT,
            format!(
                "concrete impl function '{}' returns '{}', expected '{}'",
                concrete_fn_ctx.name,
                concrete_fn_ctx.return_type.to_type_string(),
                bindings.result_ty.to_type_string()
            ),
        ));
    }

    Ok(())
}

pub(super) fn specialize_self_type(ty: &TrustVcType, concrete_type: &TrustVcType) -> TrustVcType {
    match ty {
        TrustVcType::Poly => concrete_type.clone(),
        TrustVcType::Seq(inner) => {
            TrustVcType::Seq(Box::new(specialize_self_type(inner, concrete_type)))
        }
        TrustVcType::Array(inner, len) => {
            TrustVcType::Array(Box::new(specialize_self_type(inner, concrete_type)), *len)
        }
        TrustVcType::Set(inner) => {
            TrustVcType::Set(Box::new(specialize_self_type(inner, concrete_type)))
        }
        TrustVcType::Multiset(inner) => {
            TrustVcType::Multiset(Box::new(specialize_self_type(inner, concrete_type)))
        }
        TrustVcType::Map(key, value) => TrustVcType::Map(
            Box::new(specialize_self_type(key, concrete_type)),
            Box::new(specialize_self_type(value, concrete_type)),
        ),
        TrustVcType::Datatype { name, variants } => TrustVcType::Datatype {
            name: name.clone(),
            variants: variants
                .iter()
                .map(|variant| DatatypeVariant {
                    name: variant.name.clone(),
                    fields: variant
                        .fields
                        .iter()
                        .map(|(field_name, field_ty)| {
                            (
                                field_name.clone(),
                                specialize_self_type(field_ty, concrete_type),
                            )
                        })
                        .collect(),
                })
                .collect(),
        },
        TrustVcType::RecursiveRef(name) => TrustVcType::RecursiveRef(name.clone()),
        other => other.clone(),
    }
}

#[derive(Debug, Clone)]
pub(super) struct ContractBindings {
    pub(super) receiver_name: String,
    pub(super) receiver_ty: TrustVcType,
    pub(super) result_name: String,
    pub(super) result_ty: TrustVcType,
    pub(super) params: Vec<ContractParamBinding>,
}

impl ContractBindings {
    pub(super) fn new(
        method: &TraitMethodDecl,
        impl_decl: &TraitImplDecl,
        trait_generics: &[String],
    ) -> Self {
        // Instantiate a parameterized trait's type params at the impl's trait
        // type args (`impl T<u64> for S` → `A := u64`) so the conformance
        // obligation checks the impl AT ITS INSTANTIATION — with declared
        // (Poly-erased) types, the body-definition equality cannot even encode
        // (Poly vs concrete sort) and the obligation degrades to an Error.
        // Substitution happens only for a full arity match with fully-concrete
        // args; anything else keeps the declared types and the existing
        // fail-closed behavior downstream.
        let generic_bindings: Vec<(String, TrustVcType)> = if !trait_generics.is_empty()
            && trait_generics.len() == impl_decl.trait_type_args.len()
            && impl_decl
                .trait_type_args
                .iter()
                .all(crate::trait_instantiation::is_fully_concrete)
        {
            trait_generics
                .iter()
                .cloned()
                .zip(impl_decl.trait_type_args.iter().cloned())
                .collect()
        } else {
            Vec::new()
        };
        let bind_ty = |ty: &TrustVcType| {
            specialize_self_type(
                &crate::ir_lowering::substitute_type_params(
                    &impl_decl.resolve_assoc_projections(ty),
                    &generic_bindings,
                ),
                &impl_decl.concrete_type,
            )
        };

        let params = method
            .params
            .iter()
            .enumerate()
            .map(|(index, (source_name, ty))| ContractParamBinding {
                source_name: source_name.clone(),
                lowered_name: format!(
                    "__trust_vc_impl_param_{}_{}",
                    sanitize_identifier(source_name),
                    index
                ),
                // Normalize `Self::X` projections to the impl's associated-type
                // binding before Self-specialization; unresolved projections
                // stay Opaque and fail closed downstream.
                ty: bind_ty(ty),
            })
            .collect();

        Self {
            receiver_name: CONFORMANCE_SELF.to_string(),
            receiver_ty: impl_decl.concrete_type.clone(),
            result_name: CONFORMANCE_RESULT.to_string(),
            result_ty: bind_ty(&method.return_type),
            params,
        }
    }

    pub(super) fn rename_map(&self) -> HashMap<String, String> {
        let mut renames = HashMap::with_capacity(self.params.len() + 2);
        renames.insert("self".to_string(), self.receiver_name.clone());
        renames.insert("result".to_string(), self.result_name.clone());
        for param in &self.params {
            renames.insert(param.source_name.clone(), param.lowered_name.clone());
        }
        renames
    }

    pub(super) fn variables(&self) -> Vec<VariableDecl> {
        let mut variables = Vec::with_capacity(self.params.len() + 2);
        variables.push(VariableDecl {
            bounded_len: false,
            name: self.receiver_name.clone(),
            ty: self.receiver_ty.clone(),
        });
        for param in &self.params {
            variables.push(VariableDecl {
                bounded_len: false,
                name: param.lowered_name.clone(),
                ty: param.ty.clone(),
            });
        }
        variables.push(VariableDecl {
            bounded_len: false,
            name: self.result_name.clone(),
            ty: self.result_ty.clone(),
        });
        variables
    }
}

#[derive(Debug, Clone)]
pub(super) struct ContractParamBinding {
    pub(super) source_name: String,
    pub(super) lowered_name: String,
    pub(super) ty: TrustVcType,
}

pub(super) struct IdentifierRenamer<'a> {
    renames: &'a HashMap<String, String>,
}

impl<'a> IdentifierRenamer<'a> {
    pub(super) fn new(renames: &'a HashMap<String, String>) -> Self {
        Self { renames }
    }
}

impl VisitMut for IdentifierRenamer<'_> {
    fn visit_expr_path_mut(&mut self, expr_path: &mut syn::ExprPath) {
        if expr_path.qself.is_none() && expr_path.path.segments.len() == 1 {
            if let Some(segment) = expr_path.path.segments.iter_mut().next() {
                let ident = &mut segment.ident;
                if let Some(replacement) = self.renames.get(&ident.to_string()) {
                    *ident = syn::Ident::new(replacement, ident.span());
                }
            }
        }

        visit_mut::visit_expr_path_mut(self, expr_path);
    }
}

/// Sanitize a name into a valid Rust-style identifier fragment.
///
/// Unlike `crate::encoder::sanitize_symbol` (which produces SMT symbol
/// fragments with collapsed underscores and trimmed edges), this function
/// preserves consecutive underscores and prepends `_` when the result would
/// start with a digit or be empty — guaranteeing a valid Rust identifier.
fn sanitize_identifier(name: &str) -> String {
    let mut sanitized = String::with_capacity(name.len());
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            sanitized.push(ch);
        } else {
            sanitized.push('_');
        }
    }

    if sanitized.is_empty() || sanitized.starts_with(|ch: char| ch.is_ascii_digit()) {
        sanitized.insert(0, '_');
    }

    sanitized
}
