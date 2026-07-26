// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Static extraction and direct verification for proof doc attrs.
//!
//! Part of #2593: recover proof contracts and typed parameters from durable
//! item-level doc metadata and verify them without thread-local collection.

use num_bigint::BigInt;
use trust_vc_merge_contract::{MergeBundle, SortMeta, TypedExpr, VarDecl};

use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::TrustVcType;
use crate::proof_doc_metadata::{
    doc_value, extract_proof_doc_metadata, ENSURES_DOC_PREFIX, PARAM_DOC_PREFIX,
    REQUIRES_DOC_PREFIX,
};
use crate::smtlib2_emit::condition_to_smtlib2;
use crate::vc::{ProofObligation, VerificationContext};

/// Proof metadata recovered entirely from durable item doc attrs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StaticProofContext {
    pub(crate) fn_name: String,
    pub(crate) params: Vec<(String, String)>,
    pub(crate) requires: Vec<String>,
    pub(crate) ensures: Vec<String>,
    pub(crate) tracked_params: Vec<String>,
}

/// Extract a static proof context from durable proof doc attrs.
pub(crate) fn extract_static_proof_context(
    attrs: &[syn::Attribute],
    fn_name: &str,
) -> TrustVcResult<Option<StaticProofContext>> {
    let proof_metadata = extract_proof_doc_metadata(attrs)?;
    let mut params = Vec::new();
    let mut requires = Vec::new();
    let mut ensures = Vec::new();

    for attr in attrs {
        let Some(value) = doc_value(attr) else {
            continue;
        };

        if let Some(condition) = value.strip_prefix(REQUIRES_DOC_PREFIX) {
            requires.push(condition.to_string());
            continue;
        }
        if let Some(condition) = value.strip_prefix(ENSURES_DOC_PREFIX) {
            ensures.push(condition.to_string());
            continue;
        }
        if let Some(param) = value.strip_prefix(PARAM_DOC_PREFIX) {
            params.push(parse_param_doc_value(param, &value)?);
        }
    }

    match proof_metadata {
        Some(metadata) => Ok(Some(StaticProofContext {
            fn_name: fn_name.to_string(),
            params,
            requires,
            ensures,
            tracked_params: metadata.tracked_params,
        })),
        None if requires.is_empty() && ensures.is_empty() && params.is_empty() => Ok(None),
        None => Err(TrustVcError::from(
            "malformed static proof metadata: contract/param markers without trust_vc:proof marker"
                .to_string(),
        )),
    }
}

/// Verify a proof directly from extracted static metadata.
pub(crate) fn verify_from_static_context(
    ctx: &StaticProofContext,
) -> TrustVcResult<crate::VerifyResult> {
    let mut verification = VerificationContext::new();

    for (name, ty) in &ctx.params {
        verification.declare_var_typed(name, crate::ir::TrustVcType::parse_or_opaque(ty));
    }

    for (index, condition) in ctx.requires.iter().enumerate() {
        verification.push_obligation(ProofObligation::assume(
            format!("{}_requires_{index}", ctx.fn_name),
            condition,
        ));
    }

    for (index, condition) in ctx.ensures.iter().enumerate() {
        verification.push_obligation(ProofObligation::assert(
            format!("{}_ensures_{index}", ctx.fn_name),
            condition,
        ));
    }

    Ok(verification.verify())
}

/// Emits a phase-1 MergeBundle bridge from a static proof context.
///
/// This bridge intentionally lowers scalar integer parameters to `MathInt`
/// sorts so the emitted SMT-LIB2 conditions can stay in Int mode. To keep this
/// fail-closed, the bridge adds domain assumptions for bounded integer kinds
/// and rejects overflow-sensitive arithmetic over finite-width parameters in
/// `condition_to_smtlib2()`. The goal is executable round-trip validation for
/// the #2593 static proof spike, not full parity with every encoder-backed
/// expression form.
pub(crate) fn emit_merge_bundle(ctx: &StaticProofContext) -> TrustVcResult<MergeBundle> {
    let variables = ctx
        .params
        .iter()
        .map(|(name, ty)| {
            Ok(VarDecl::new(
                name.clone(),
                trust_vc_type_to_sort_meta(&TrustVcType::parse_or_opaque(ty))?,
            ))
        })
        .collect::<TrustVcResult<Vec<_>>>()?;
    let assumptions = int_mode_domain_assumptions(&ctx.params)?
        .into_iter()
        .map(Ok)
        .chain(ctx.requires.iter().map(|condition| {
            Ok(TypedExpr::new(
                condition_to_smtlib2(condition, &ctx.params)?,
                SortMeta::Bool,
            ))
        }))
        .collect::<TrustVcResult<Vec<_>>>()?;
    let assertions = ctx
        .ensures
        .iter()
        .map(|condition| {
            Ok(TypedExpr::new(
                condition_to_smtlib2(condition, &ctx.params)?,
                SortMeta::Bool,
            ))
        })
        .collect::<TrustVcResult<Vec<_>>>()?;

    let bundle = MergeBundle::new(format!("trust_vc::static::{}", ctx.fn_name))
        .with_variables(variables)
        .with_assumptions(assumptions)
        .with_assertions(assertions)
        .insert_metadata("source_backend", "ay")
        .insert_metadata("source_repo", "trust_vc")
        .insert_metadata("source_path", "static_extraction");
    Ok(bundle)
}

fn int_mode_domain_assumptions(params: &[(String, String)]) -> TrustVcResult<Vec<TypedExpr>> {
    let mut assumptions = Vec::new();

    for (name, ty) in params {
        let ty = TrustVcType::parse_or_opaque(ty);
        match ty {
            TrustVcType::Nat => assumptions.push(bool_typed_expr(format!("(>= {name} 0)"))),
            TrustVcType::Int { .. } | TrustVcType::Uint { .. } => {
                let (lower, upper) = finite_int_range_bounds(&ty)?;
                assumptions.push(bool_typed_expr(format!(
                    "(<= {} {name})",
                    smt_int_literal(&lower)
                )));
                assumptions.push(bool_typed_expr(format!(
                    "(< {name} {})",
                    smt_int_literal(&upper)
                )));
            }
            _ => {}
        }
    }

    Ok(assumptions)
}

fn finite_int_range_bounds(ty: &TrustVcType) -> TrustVcResult<(BigInt, BigInt)> {
    match ty {
        TrustVcType::Uint { width } => Ok((BigInt::from(0u8), BigInt::from(1u8) << *width)),
        TrustVcType::Int { width } => {
            if *width == 0 {
                return Err(TrustVcError::Encoding {
                    context: "emit merge bundle variable bounds",
                    detail: "unsupported zero-width signed integer in static proof bridge"
                        .to_string(),
                });
            }
            let upper = BigInt::from(1u8) << (*width - 1);
            Ok((-upper.clone(), upper))
        }
        other => Err(TrustVcError::Encoding {
            context: "emit merge bundle variable bounds",
            detail: format!(
                "expected finite-width integer type, got `{}`",
                other.to_type_string()
            ),
        }),
    }
}

fn smt_int_literal(value: &BigInt) -> String {
    let digits = value.to_string();
    if let Some(magnitude) = digits.strip_prefix('-') {
        format!("(- {magnitude})")
    } else {
        digits
    }
}

fn bool_typed_expr(expr: String) -> TypedExpr {
    TypedExpr::new(expr, SortMeta::Bool)
}

fn trust_vc_type_to_sort_meta(ty: &TrustVcType) -> TrustVcResult<SortMeta> {
    match ty {
        TrustVcType::Bool => Ok(SortMeta::Bool),
        TrustVcType::Int { .. }
        | TrustVcType::Uint { .. }
        | TrustVcType::MathInt
        | TrustVcType::Nat => Ok(SortMeta::MathInt),
        _ => Err(TrustVcError::Encoding {
            context: "emit merge bundle variable sort",
            detail: format!(
                "unsupported static proof parameter type `{}` for phase-1 MergeBundle emission",
                ty.to_type_string()
            ),
        }),
    }
}

fn parse_param_doc_value(raw: &str, full_value: &str) -> TrustVcResult<(String, String)> {
    let Some((name, ty)) = raw.split_once(':') else {
        return Err(TrustVcError::from(format!(
            "malformed static proof metadata: parameter marker missing type in `{full_value}`"
        )));
    };

    let name = name.trim();
    let ty = ty.trim();
    if name.is_empty() || ty.is_empty() {
        return Err(TrustVcError::from(format!(
            "malformed static proof metadata: parameter marker requires non-empty name and type in `{full_value}`"
        )));
    }

    Ok((name.to_string(), ty.to_string()))
}

#[cfg(test)]
#[path = "static_extraction_tests.rs"]
mod tests;
