//! Literal, path, and leaf type helpers for expression lowering.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::encoder::datatype::variant_symbol_name;
use crate::ir::TrustVcType;
use crate::ir_expr::{IntConstKind, TrustVcExpr};
use sha2::{Digest, Sha256};

use super::{LoweringError, TypeEnv};

pub(super) fn lower_lit(lit: &syn::ExprLit) -> Result<TrustVcExpr, LoweringError> {
    match &lit.lit {
        syn::Lit::Bool(b) => Ok(TrustVcExpr::BoolLit(b.value)),
        syn::Lit::Char(char_lit) => Ok(TrustVcExpr::IntLit {
            value: i128::from(u32::from(char_lit.value())),
            ty: TrustVcType::Char,
        }),
        syn::Lit::Int(int_lit) => {
            let value: i128 = int_lit
                .base10_parse()
                .map_err(|e| LoweringError::InvalidLiteral(format!("integer parse: {}", e)))?;
            let suffix = int_lit.suffix();
            let ty = type_from_int_suffix(suffix)?;
            // Diagnostic parity (#2778): a *positive* literal with an EXPLICIT
            // finite-width suffix (`300u8`, `256u8`, `128i8`, …) that escapes
            // its declared type's range is an upstream `integer literal out of
            // range` error.
            //
            // We must NOT range-check *unsuffixed* literals: in trust-vc an
            // unsuffixed integer literal carries the placeholder type
            // `Int { width: 32 }` and is coerced to its real type later (by
            // `coerce_unsuffixed_literal` / context-width inference in the
            // encoder). Values like `4294967295` (u32::MAX) are written without
            // a suffix and would be falsely rejected against the i32 placeholder.
            // Verus runs `check_lit_int` only after type inference resolves the
            // literal's concrete type; the suffixed case is the one trust-vc can
            // resolve soundly at lowering time.
            //
            // Negative literals like `-128i8` are handled in `lower_unary`'s
            // `Neg` arm, where the negation is folded in before the range check,
            // so a bare positive literal arriving here is never the inner
            // operand of a leading negation.
            if !suffix.is_empty() {
                super::diagnostic_parity::check_int_literal_in_range(value, &ty)?;
            }
            Ok(typed_int_literal(TrustVcExpr::IntLit { value, ty }, suffix))
        }
        syn::Lit::Float(float_lit) => lower_real_lit(float_lit),
        // A string literal lowers to `StringLit`, which the encoder already
        // unconditionally lowers to `solver.string_const` (ir_encoder/mod.rs) —
        // ay's native `Sort::String` decides constant (dis)equality soundly. The
        // former `native-strings`-feature gate errored here by default even though
        // the encoder path was unconditional; removing it activates string-literal
        // content/disequality reasoning (probe-confirmed: literal equalities verify,
        // liars CTREX, and string METHODS on a literal still fail closed).
        syn::Lit::Str(str_lit) => Ok(TrustVcExpr::StringLit(str_lit.value())),
        _ => Err(LoweringError::InvalidLiteral(
            "not bool, char, or int".into(),
        )),
    }
}

fn lower_real_lit(lit: &syn::LitFloat) -> Result<TrustVcExpr, LoweringError> {
    let (mut numerator, denominator) = decimal_real_parts(lit.base10_digits())?;
    let mut denominator = denominator;
    let gcd = gcd_i128(numerator.abs(), denominator);
    if gcd > 1 {
        numerator /= gcd;
        denominator /= gcd;
    }

    match lit.suffix() {
        "" | "real" => {}
        "f32" | "f64" => return lower_integral_float_lit(lit.suffix(), numerator, denominator),
        suffix => {
            return Err(LoweringError::InvalidLiteral(format!(
                "unsupported float literal suffix: {suffix}"
            )))
        }
    }

    let numerator = TrustVcExpr::IntLit {
        value: numerator,
        ty: TrustVcType::Real,
    };
    if denominator == 1 {
        return Ok(numerator);
    }
    Ok(TrustVcExpr::Arith {
        op: crate::ir_expr::ArithOp::Div,
        left: Box::new(numerator),
        right: Box::new(TrustVcExpr::IntLit {
            value: denominator,
            ty: TrustVcType::Real,
        }),
        ty: TrustVcType::Real,
    })
}

fn lower_integral_float_lit(
    suffix: &str,
    numerator: i128,
    denominator: i128,
) -> Result<TrustVcExpr, LoweringError> {
    if denominator != 1 {
        return Err(LoweringError::InvalidLiteral(format!(
            "unsupported non-integral {suffix} literal; use an integer cast until rounded float literals are supported"
        )));
    }

    let from_ty = if i128::from(i32::MIN) <= numerator && numerator <= i128::from(i32::MAX) {
        TrustVcType::Int { width: 32 }
    } else if i128::from(i64::MIN) <= numerator && numerator <= i128::from(i64::MAX) {
        TrustVcType::Int { width: 64 }
    } else {
        return Err(LoweringError::InvalidLiteral(format!(
            "{suffix} literal integer part is outside supported i64 cast range"
        )));
    };
    let to_ty = match suffix {
        "f32" => TrustVcType::Float { width: 32 },
        "f64" => TrustVcType::Float { width: 64 },
        _ => unreachable!("caller filters supported float suffixes"),
    };
    Ok(TrustVcExpr::Cast {
        expr: Box::new(TrustVcExpr::IntLit {
            value: numerator,
            ty: from_ty.clone(),
        }),
        from_ty,
        to_ty,
    })
}

fn decimal_real_parts(raw: &str) -> Result<(i128, i128), LoweringError> {
    let cleaned = raw.replace('_', "");
    let (mantissa, exponent) = split_decimal_exponent(&cleaned)?;
    let (whole, frac) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let digits = format!("{whole}{frac}");
    let mut numerator = digits
        .parse::<i128>()
        .map_err(|err| LoweringError::InvalidLiteral(format!("real literal parse: {err}")))?;
    let scale = i32::try_from(frac.len())
        .map_err(|_| LoweringError::InvalidLiteral("real literal is too precise".into()))?
        .checked_sub(exponent)
        .ok_or_else(|| LoweringError::InvalidLiteral("real literal exponent overflow".into()))?;
    if scale <= 0 {
        let shift = scale.checked_neg().ok_or_else(|| {
            LoweringError::InvalidLiteral("real literal exponent overflow".into())
        })?;
        let shift = u32::try_from(shift)
            .map_err(|_| LoweringError::InvalidLiteral("real literal exponent overflow".into()))?;
        numerator = checked_mul_pow10(numerator, shift)?;
        Ok((numerator, 1))
    } else {
        let scale = u32::try_from(scale)
            .map_err(|_| LoweringError::InvalidLiteral("real literal exponent overflow".into()))?;
        Ok((numerator, checked_pow10(scale)?))
    }
}

fn split_decimal_exponent(cleaned: &str) -> Result<(&str, i32), LoweringError> {
    let Some((mantissa, exponent)) = cleaned.split_once(['e', 'E']) else {
        return Ok((cleaned, 0));
    };
    let exponent = exponent
        .parse::<i32>()
        .map_err(|err| LoweringError::InvalidLiteral(format!("real exponent parse: {err}")))?;
    Ok((mantissa, exponent))
}

fn checked_mul_pow10(mut value: i128, exp: u32) -> Result<i128, LoweringError> {
    for _ in 0..exp {
        value = value.checked_mul(10).ok_or_else(|| {
            LoweringError::InvalidLiteral("real literal numerator overflow".into())
        })?;
    }
    Ok(value)
}

fn checked_pow10(exp: u32) -> Result<i128, LoweringError> {
    checked_mul_pow10(1, exp)
}

fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

/// A literal whose suffix TYPES it `i32` (`200i32`, `-128i32`), pinned by an
/// identity cast. An unsuffixed literal lowers to the same `Int { width: 32 }`
/// type — the placeholder that takes the type of the peer it meets — so a bare
/// `200i32` next to `x: u8` was retyped to the `u8` 200: `x + 200i32 == 44`
/// (`x == 100`) came back `Verified`, where the operands of two types make the
/// sum the integer 300 (design-trust-proof-backend.md §5b). Every other suffix
/// already names a type no placeholder has.
pub(crate) fn typed_int_literal(literal: TrustVcExpr, suffix: &str) -> TrustVcExpr {
    if suffix != "i32" {
        return literal;
    }
    TrustVcExpr::Cast {
        expr: Box::new(literal),
        from_ty: TrustVcType::Int { width: 32 },
        to_ty: TrustVcType::Int { width: 32 },
    }
}

pub(crate) fn type_from_int_suffix(suffix: &str) -> Result<TrustVcType, LoweringError> {
    match suffix {
        "" => Ok(TrustVcType::Int { width: 32 }),
        "int" => Ok(TrustVcType::MathInt),
        "nat" => Ok(TrustVcType::Nat),
        "real" => Ok(TrustVcType::Real),
        "i8" => Ok(TrustVcType::Int { width: 8 }),
        "i16" => Ok(TrustVcType::Int { width: 16 }),
        "i32" => Ok(TrustVcType::Int { width: 32 }),
        "i64" => Ok(TrustVcType::Int { width: 64 }),
        "i128" => Ok(TrustVcType::Int { width: 128 }),
        "isize" => Ok(TrustVcType::Int {
            width: crate::ir::pointer_width(),
        }),
        "u8" => Ok(TrustVcType::Uint { width: 8 }),
        "u16" => Ok(TrustVcType::Uint { width: 16 }),
        "u32" => Ok(TrustVcType::Uint { width: 32 }),
        "u64" => Ok(TrustVcType::Uint { width: 64 }),
        "u128" => Ok(TrustVcType::Uint { width: 128 }),
        "usize" => Ok(TrustVcType::Uint {
            width: crate::ir::pointer_width(),
        }),
        _ => Err(LoweringError::InvalidType(format!(
            "unknown suffix: {}",
            suffix
        ))),
    }
}

#[allow(clippy::indexing_slicing)] // path.path.segments[0]/[1] are only used inside the len() == 1 and len() == 2 branches below
pub(super) fn lower_path(
    path: &syn::ExprPath,
    env: &TypeEnv,
) -> Result<TrustVcExpr, LoweringError> {
    if let Some(constructor) = lower_explicit_nullary_option_constructor(path, env)? {
        return Ok(constructor);
    }
    // `PhantomData` / `PhantomData::<T>` (optionally `core::marker::` or
    // `std::marker::` qualified) is the unique inhabitant of the zero-sized
    // `PhantomData<T>` marker type, so it lowers to the unit literal. This is
    // sound because the type itself erases to `Unit` (see `ir_type_parse.rs`),
    // and the encoder's unit singleton constraint forces every unit-typed term
    // to the shared `__trust_vc_unit` term — making `a == PhantomData::<T>`
    // provable exactly as Verus's `phantom_data_is_unit` expects. We only take
    // this path when the leading identifier is not shadowed by a same-named
    // local variable in scope. Cluster #2779.
    if is_phantom_data_constructor_path(path, env) {
        return Ok(TrustVcExpr::UnitLit);
    }
    if path.path.segments.len() == 1 {
        let name = path.path.segments[0].ident.to_string();
        match name.as_str() {
            "true" => return Ok(TrustVcExpr::BoolLit(true)),
            "false" => return Ok(TrustVcExpr::BoolLit(false)),
            _ => {}
        }
        if let Some(ty) = env.lookup(&name) {
            return Ok(TrustVcExpr::Var {
                name,
                ty: ty.clone(),
            });
        }
        if let Some(meta) = env.resolve_variant_constructor(&path.path)? {
            if meta.fields.is_empty() {
                return Ok(TrustVcExpr::FnCall {
                    name: meta.uf_name.clone(),
                    args: vec![],
                    return_ty: meta.return_ty.clone(),
                });
            }
            return Err(LoweringError::TypeInference(format!(
                "constructor '{}' expects {} argument(s); use {}(...)",
                meta.variant_name,
                meta.fields.len(),
                meta.variant_name,
            )));
        }
        Err(LoweringError::UnresolvedVar(name))
    } else if path.path.segments.len() == 2 {
        let type_name = path.path.segments[0].ident.to_string();
        let const_name = path.path.segments[1].ident.to_string();
        if let Ok(ty) = TrustVcType::try_from_str(&type_name) {
            match const_name.as_str() {
                "MAX" => {
                    return Ok(TrustVcExpr::IntConst {
                        ty,
                        kind: IntConstKind::Max,
                    })
                }
                "MIN" => {
                    return Ok(TrustVcExpr::IntConst {
                        ty,
                        kind: IntConstKind::Min,
                    })
                }
                "BITS" => {
                    return Ok(crate::ir_builder::int_bits(ty));
                }
                _ => {}
            }
        }
        if let Some(meta) = env.resolve_variant_constructor(&path.path)? {
            if meta.fields.is_empty() {
                return Ok(TrustVcExpr::FnCall {
                    name: meta.uf_name.clone(),
                    args: vec![],
                    return_ty: meta.return_ty.clone(),
                });
            }
            return Err(LoweringError::TypeInference(format!(
                "constructor '{}::{}' expects {} argument(s); use {}::{}(...)",
                type_name,
                meta.variant_name,
                meta.fields.len(),
                type_name,
                meta.variant_name,
            )));
        }
        Err(LoweringError::UnsupportedExpr(format!(
            "{}::{}",
            type_name, const_name
        )))
    } else {
        if let Some(meta) = env.resolve_variant_constructor(&path.path)? {
            if meta.fields.is_empty() {
                return Ok(TrustVcExpr::FnCall {
                    name: meta.uf_name.clone(),
                    args: vec![],
                    return_ty: meta.return_ty.clone(),
                });
            }
            return Err(LoweringError::TypeInference(format!(
                "constructor '{}' expects {} argument(s); use call syntax",
                meta.variant_name,
                meta.fields.len(),
            )));
        }
        Err(LoweringError::UnsupportedExpr(format!(
            "multi-segment path: {}",
            path_to_string(&path.path)
        )))
    }
}

/// Returns true when `path` is the `PhantomData` value constructor.
///
/// Accepted forms (matching the upstream Verus `phantom_data_is_unit` test):
///   - `PhantomData`
///   - `PhantomData::<T>`
///   - `core::marker::PhantomData` / `core::marker::PhantomData::<T>`
///   - `std::marker::PhantomData` / `std::marker::PhantomData::<T>`
///
/// A same-named local variable in scope shadows the constructor, so we decline
/// to treat a bare `PhantomData` identifier as the constructor when the env
/// binds it. Any unrecognized prefix fails this check (returns false) and falls
/// through to the existing resolution paths, which fail closed.
fn is_phantom_data_constructor_path(path: &syn::ExprPath, env: &TypeEnv) -> bool {
    if path.qself.is_some() {
        return false;
    }
    let segments = &path.path.segments;
    let Some(last) = segments.last() else {
        return false;
    };
    if last.ident != "PhantomData" {
        return false;
    }
    // The trailing segment may carry a turbofish (`::<T>`) but no other
    // argument shape (e.g. parenthesized `Fn`-style args) is the constructor.
    if matches!(last.arguments, syn::PathArguments::Parenthesized(_)) {
        return false;
    }
    // Leading segments (if any) must spell exactly `core::marker` or
    // `std::marker`, and must not themselves carry generic arguments.
    let prefix_count = segments.len() - 1;
    let prefix: Option<Vec<String>> = segments
        .iter()
        .take(prefix_count)
        .map(|seg| {
            if matches!(seg.arguments, syn::PathArguments::None) {
                Some(seg.ident.to_string())
            } else {
                None
            }
        })
        .collect();
    let Some(prefix) = prefix else {
        // A leading segment carried generic arguments — not a recognized
        // qualified `PhantomData` path.
        return false;
    };
    let prefix: Vec<&str> = prefix.iter().map(String::as_str).collect();
    match prefix.as_slice() {
        [] => {
            // Bare `PhantomData`: a local variable of the same name shadows
            // the constructor.
            env.lookup("PhantomData").is_none()
        }
        ["core", "marker"] | ["std", "marker"] => true,
        _ => false,
    }
}

fn lower_explicit_nullary_option_constructor(
    path: &syn::ExprPath,
    env: &TypeEnv,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let Some(last) = path.path.segments.last() else {
        return Ok(None);
    };
    if last.ident != "None" {
        return Ok(None);
    }
    let inner_ty = if let syn::PathArguments::AngleBracketed(args) = &last.arguments {
        Some(generic_type_arg(args, 0, env)?)
    } else if let Some(option_segment) = path.path.segments.iter().rev().nth(1) {
        if option_segment.ident == "Option" {
            let syn::PathArguments::AngleBracketed(args) = &option_segment.arguments else {
                return Ok(None);
            };
            Some(generic_type_arg(args, 0, env)?)
        } else {
            None
        }
    } else {
        None
    };
    let Some(inner_ty) = inner_ty else {
        return Ok(None);
    };
    let option_ty = TrustVcType::from_str(&format!("Option<{}>", inner_ty.to_type_string()))
        .map_err(LoweringError::InvalidType)?;
    let TrustVcType::Datatype { name, .. } = &option_ty else {
        return Err(LoweringError::InvalidType(
            "Option constructor did not produce a datatype".into(),
        ));
    };
    Ok(Some(TrustVcExpr::FnCall {
        name: variant_symbol_name(name, "None"),
        args: vec![],
        return_ty: option_ty,
    }))
}

fn generic_type_arg(
    args: &syn::AngleBracketedGenericArguments,
    index: usize,
    env: &TypeEnv,
) -> Result<TrustVcType, LoweringError> {
    let ty = args
        .args
        .iter()
        .filter_map(|arg| match arg {
            syn::GenericArgument::Type(ty) => Some(ty),
            _ => None,
        })
        .nth(index)
        .ok_or_else(|| {
            LoweringError::TypeInference(format!(
                "Option::None is missing type argument {}",
                index + 1
            ))
        })?;
    trust_vc_type_from_syn_type_with_env(ty, env)
}

pub(crate) fn path_to_string(path: &syn::Path) -> String {
    path.segments
        .iter()
        .map(|s| s.ident.to_string())
        .collect::<Vec<_>>()
        .join("::")
}

pub(crate) fn expr_path_to_string(path: &syn::ExprPath) -> String {
    if path.qself.is_none() {
        return path_to_string(&path.path);
    }
    let canonical = compact_tokens(path);
    let digest = Sha256::digest(canonical.as_bytes());
    format!(
        "__qualified_{}_sha256_{digest:x}",
        sanitize_path_symbol(&canonical)
    )
}

fn compact_tokens<T: quote::ToTokens>(tokens: T) -> String {
    quote::quote!(#tokens).to_string().replace(' ', "")
}

fn sanitize_path_symbol(name: &str) -> String {
    let mut sanitized = String::with_capacity(name.len());
    let mut last_was_underscore = false;
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() {
            sanitized.push(ch);
            last_was_underscore = false;
        } else if !last_was_underscore {
            sanitized.push('_');
            last_was_underscore = true;
        }
    }
    while sanitized.ends_with('_') {
        sanitized.pop();
    }
    while sanitized.starts_with('_') {
        sanitized.remove(0);
    }
    sanitized
}

#[cfg(test)]
pub(crate) fn trust_vc_type_from_syn_type(ty: &syn::Type) -> Result<TrustVcType, LoweringError> {
    if let syn::Type::Reference(reference) = ty {
        return trust_vc_type_from_syn_type(&reference.elem);
    }
    let ty_str = quote::quote!(#ty).to_string().replace(' ', "");
    Ok(TrustVcType::parse_or_opaque(&ty_str))
}

pub(crate) fn trust_vc_type_from_syn_type_with_env(
    ty: &syn::Type,
    env: &TypeEnv,
) -> Result<TrustVcType, LoweringError> {
    env.resolve_syn_type(ty)
}
