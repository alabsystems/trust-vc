//! Datatype coverage helpers for match-expression encoding.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::BTreeSet;

use crate::error::TrustVcResult;
use crate::ir::{DatatypeVariant, MatchPattern, TrustVcType};
use crate::ir_expr::MatchArm;

pub(super) fn datatype_variant<'a>(
    scrutinee_ty: &'a TrustVcType,
    variant_name: &str,
) -> TrustVcResult<(&'a str, &'a DatatypeVariant)> {
    let TrustVcType::Datatype { name, variants } = scrutinee_ty else {
        return Err(format!(
            "Constructor pattern '{}' requires datatype scrutinee, got '{}'",
            variant_name,
            scrutinee_ty.to_type_string()
        )
        .into());
    };
    let variant = variants
        .iter()
        .find(|variant| variant.name == variant_name)
        .ok_or_else(|| format!("Unknown datatype variant '{}' for '{}'", variant_name, name))?;
    Ok((name.as_str(), variant))
}

pub(super) fn datatype_field<'a>(
    variant_name: &str,
    variant: &'a DatatypeVariant,
    field_name: &str,
) -> TrustVcResult<(usize, &'a TrustVcType)> {
    variant
        .fields
        .iter()
        .enumerate()
        .find(|(_, (name, _))| name == field_name)
        .map(|(index, (_, field_ty))| (index, field_ty))
        .ok_or_else(|| {
            format!(
                "Struct pattern '{}' references unknown field '{}'",
                variant_name, field_name
            )
            .into()
        })
}

pub(super) fn constructor_patterns_cover_datatype(
    scrutinee_ty: &TrustVcType,
    arms: &[MatchArm],
) -> bool {
    let TrustVcType::Datatype { variants, .. } = scrutinee_ty else {
        return false;
    };

    let expected: BTreeSet<_> = variants
        .iter()
        .map(|variant| variant.name.as_str())
        .collect();
    if expected.is_empty() {
        return false;
    }

    let mut covered = BTreeSet::new();
    for arm in arms {
        // A GUARDED arm covers NOTHING: its guard may be false, so its variant can
        // still fall through to a later arm. SKIP it (do not count its variant) — the
        // match is exhaustive only if the UNGUARDED arms already cover every variant.
        // (If a variant is reachable only through a guarded arm, `covered != expected`
        // ⇒ not exhaustive ⇒ the encoder fails closed rather than drop the arm
        // condition, which would be an unconditional-default false-verify — TRAP #2.)
        if arm.guard.is_some() {
            continue;
        }
        let Some(pattern_variants) = covered_constructor_variants(&arm.pattern, variants) else {
            return false;
        };
        covered.extend(pattern_variants);
    }

    covered == expected
}

pub(super) fn covered_constructor_variants<'a>(
    pattern: &'a MatchPattern,
    variants: &'a [DatatypeVariant],
) -> Option<BTreeSet<&'a str>> {
    match pattern {
        MatchPattern::Constructor { variant_name, .. } => variants
            .iter()
            .find(|variant| variant.name == *variant_name)
            .map(|variant| BTreeSet::from([variant.name.as_str()])),
        MatchPattern::Struct { variant_name, .. } => variants
            .iter()
            .find(|variant| variant.name == *variant_name)
            .map(|variant| BTreeSet::from([variant.name.as_str()])),
        MatchPattern::Or(patterns) => {
            let mut covered = BTreeSet::new();
            for pattern in patterns {
                covered.extend(covered_constructor_variants(pattern, variants)?);
            }
            Some(covered)
        }
        MatchPattern::Ident(_) | MatchPattern::Lit(_) | MatchPattern::Wildcard => None,
    }
}
