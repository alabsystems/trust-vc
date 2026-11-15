//! Type-shape predicates of the IR typing validator.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::ir::TrustVcType;

use super::super::types::is_integer_type;

/// Whether a value of type `value` is a value of the composite type `target`
/// at every INTEGER position: equal integer types there, containers of one
/// kind (a sequence and an array are one carrier), datatypes of one shape.
/// A value type that holds no integer (a type parameter, an opaque type)
/// agrees — nothing in it is re-read; any other disagreement does not.
pub(crate) fn integer_positions_agree(value: &TrustVcType, target: &TrustVcType) -> bool {
    use TrustVcType as T;
    if value == target || !type_holds_an_integer(value) {
        return true;
    }
    match (value, target) {
        (T::Seq(v) | T::Array(v, _), T::Seq(t) | T::Array(t, _))
        | (T::Set(v), T::Set(t))
        | (T::Multiset(v), T::Multiset(t)) => integer_positions_agree(v, t),
        (T::Map(vk, vv), T::Map(tk, tv)) => {
            integer_positions_agree(vk, tk) && integer_positions_agree(vv, tv)
        }
        (T::Datatype { variants: vv, .. }, T::Datatype { variants: tv, .. }) => {
            vv.len() == tv.len()
                && vv.iter().zip(tv).all(|(v, t)| {
                    v.name == t.name
                        && v.fields.len() == t.fields.len()
                        && v.fields
                            .iter()
                            .zip(&t.fields)
                            .all(|((_, vf), (_, tf))| integer_positions_agree(vf, tf))
                })
        }
        _ => false,
    }
}

/// Whether `ty` mentions a type parameter (a generic signature).
pub(crate) fn mentions_type_parameter(ty: &TrustVcType) -> bool {
    match ty {
        TrustVcType::TypeParam(_) | TrustVcType::Poly => true,
        TrustVcType::Seq(inner)
        | TrustVcType::Array(inner, _)
        | TrustVcType::Set(inner)
        | TrustVcType::Multiset(inner) => mentions_type_parameter(inner),
        TrustVcType::Map(key, value) => {
            mentions_type_parameter(key) || mentions_type_parameter(value)
        }
        TrustVcType::SpecFn(args, ret) => {
            args.iter().any(mentions_type_parameter) || mentions_type_parameter(ret)
        }
        TrustVcType::Datatype { variants, .. } => variants.iter().any(|variant| {
            variant
                .fields
                .iter()
                .any(|(_, field)| mentions_type_parameter(field))
        }),
        _ => false,
    }
}

/// Whether the type `ty` is, or holds anywhere in it, an integer type.
pub(crate) fn type_holds_an_integer(ty: &TrustVcType) -> bool {
    match ty {
        TrustVcType::Seq(inner)
        | TrustVcType::Array(inner, _)
        | TrustVcType::Set(inner)
        | TrustVcType::Multiset(inner) => type_holds_an_integer(inner),
        TrustVcType::Map(key, value) => type_holds_an_integer(key) || type_holds_an_integer(value),
        TrustVcType::Datatype { variants, .. } => variants.iter().any(|variant| {
            variant
                .fields
                .iter()
                .any(|(_, field)| type_holds_an_integer(field))
        }),
        other => is_integer_type(other),
    }
}
