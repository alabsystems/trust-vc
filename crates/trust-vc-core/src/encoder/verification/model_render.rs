//! Human-readable counterexample model formatter for typed values.
//!
//! Replaces raw `format!("{:?}", model)` with type-aware rendering that
//! converts ay array and floating-point models back to Rust-like syntax.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;

use ay_dpll::api::{FpSpecialKind, Model, ModelValue, VerifiedModel};
use num_bigint::BigInt;

use crate::counterexample_names::{self, CounterexampleVarMeta};
use crate::ir::TrustVcType;
use crate::verify_result::CounterexampleBinding;

mod functions;
pub(super) use functions::published_function_bindings;

/// Format a counterexample model with type-aware rendering and source-level names.
///
/// Uses `counterexample_var_meta` to filter hidden variables and display
/// user-facing aliases instead of raw solver names. Falls back to raw names
/// when no metadata is available (backward compatibility). Part of #2651.
pub(in crate::encoder) fn format_counterexample_model(
    verified_model: &VerifiedModel,
    var_types: &HashMap<String, TrustVcType>,
    counterexample_var_meta: &HashMap<String, CounterexampleVarMeta>,
) -> String {
    let model = verified_model.model();

    let mut bindings: Vec<String> = Vec::new();
    let mut sorted_vars: Vec<(&String, &TrustVcType)> = var_types.iter().collect();
    sorted_vars.sort_by_key(|(name, _)| name.as_str());

    for (raw_name, ty) in &sorted_vars {
        let meta = counterexample_var_meta
            .get(raw_name.as_str())
            .cloned()
            .unwrap_or_else(|| counterexample_names::default_meta(raw_name));

        if !meta.visible {
            continue;
        }

        if let Some(rendered) = render_variable(raw_name, ty, model) {
            bindings.push(format!("{} = {rendered}", meta.display_name));
        }
    }

    if bindings.is_empty() {
        format!("{verified_model:?}")
    } else {
        // Sort by display_name for stable, user-friendly ordering
        bindings.sort();
        bindings.join(", ")
    }
}

/// Collect structured counterexample bindings with type-aware rendering.
///
/// Returns a `Vec<CounterexampleBinding>` containing each visible variable's
/// display name, raw solver name, type, and rendered value. Uses the same
/// rendering logic as `format_counterexample_model` but preserves structure.
pub(in crate::encoder) fn collect_counterexample_bindings(
    verified_model: &VerifiedModel,
    var_types: &HashMap<String, TrustVcType>,
    counterexample_var_meta: &HashMap<String, CounterexampleVarMeta>,
) -> Vec<CounterexampleBinding> {
    let model = verified_model.model();

    let mut sorted_vars: Vec<(&String, &TrustVcType)> = var_types.iter().collect();
    sorted_vars.sort_by_key(|(name, _)| name.as_str());

    let mut bindings = Vec::new();
    for (raw_name, ty) in &sorted_vars {
        let meta = counterexample_var_meta
            .get(raw_name.as_str())
            .cloned()
            .unwrap_or_else(|| counterexample_names::default_meta(raw_name));

        if !meta.visible {
            continue;
        }

        if let Some(rendered) = render_variable(raw_name, ty, model) {
            bindings.push(CounterexampleBinding {
                display_name: meta.display_name,
                raw_name: raw_name.to_string(),
                ty: trust_vc_type_display_name(ty),
                value: rendered,
            });
        }
    }

    bindings.sort_by_key(|binding| binding.display_name.clone());
    bindings
}

/// Render a single variable's model value using its declared type.
///
/// For collection types (Seq/Set/Map/Multiset), tries the typed renderer first and
/// falls back to the raw solver display if the typed renderer cannot
/// interpret the model value (e.g., ArraySmtlib, missing companion variables).
fn render_variable(name: &str, ty: &TrustVcType, model: &Model) -> Option<String> {
    match ty {
        TrustVcType::Seq(elem_ty) | TrustVcType::Array(elem_ty, _) => {
            render_seq(name, elem_ty, model)
                .or_else(|| model.value_by_name(name).map(|v| format!("{v}")))
        }
        TrustVcType::Set(elem_ty) => render_set(name, elem_ty, model)
            .or_else(|| model.value_by_name(name).map(|v| format!("{v}"))),
        TrustVcType::Multiset(elem_ty) => render_multiset(name, elem_ty, model)
            .or_else(|| model.value_by_name(name).map(|v| format!("{v}"))),
        TrustVcType::Map(key_ty, val_ty) => render_map(name, key_ty, val_ty, model)
            .or_else(|| model.value_by_name(name).map(|v| format!("{v}"))),
        _ => render_scalar(name, ty, model),
    }
}

/// Render a scalar variable from the model.
fn render_scalar(name: &str, ty: &TrustVcType, model: &Model) -> Option<String> {
    match ty {
        TrustVcType::Unit => Some("()".to_string()),
        TrustVcType::Bool => model.bool_val(name).map(|b| b.to_string()),
        TrustVcType::MathInt | TrustVcType::Nat => model.int_val(name).map(|i| i.to_string()),
        TrustVcType::Int { width } => render_signed_bv(name, *width, model),
        TrustVcType::Uint { width } => render_unsigned_bv(name, *width, model),
        TrustVcType::Float { width } => render_float(name, *width, model),
        TrustVcType::Char => render_char(name, model),
        _ => {
            // Fall back to generic model value display for unsupported types
            model.value_by_name(name).map(|v| format!("{v}"))
        }
    }
}

/// Render a signed bitvector as a decimal integer with two's complement.
fn render_signed_bv(name: &str, width: u32, model: &Model) -> Option<String> {
    let (value, _bv_width) = model.bv_val(name)?;
    Some(bv_to_signed(&value, width).to_string())
}

/// Render an unsigned bitvector as a decimal integer.
fn render_unsigned_bv(name: &str, width: u32, model: &Model) -> Option<String> {
    let (value, _bv_width) = model.bv_val(name)?;
    Some(bv_to_unsigned(&value, width).to_string())
}

/// Interpret a BigInt bitvector as a signed value using two's complement.
fn bv_to_signed(value: &BigInt, width: u32) -> BigInt {
    if width == 0 {
        return BigInt::from(0);
    }
    let modulus = BigInt::from(1) << width;
    let half = BigInt::from(1) << (width - 1);
    let unsigned = ((value % &modulus) + &modulus) % &modulus;
    if unsigned >= half {
        unsigned - modulus
    } else {
        unsigned
    }
}

/// Interpret a BigInt bitvector as an unsigned value.
fn bv_to_unsigned(value: &BigInt, width: u32) -> BigInt {
    if width == 0 {
        return BigInt::from(0);
    }
    let modulus = BigInt::from(1) << width;
    ((value % &modulus) + &modulus) % &modulus
}

/// Render a char value from a 32-bit bitvector model.
fn render_char(name: &str, model: &Model) -> Option<String> {
    let (value, _) = model.bv_val(name)?;
    let scalar: u32 = (&value).try_into().ok()?;
    match char::from_u32(scalar) {
        Some(c) if !c.is_control() => Some(format!("'{c}'")),
        Some(_) | None => Some(format!("'\\u{{{scalar:x}}}'")),
    }
}

/// Render a floating-point value using Rust-style decimal formatting.
fn render_float(name: &str, width: u32, model: &Model) -> Option<String> {
    let value = model.fp_val(name)?;
    render_float_value(value, width)
}

fn render_float_value(value: &ModelValue, width: u32) -> Option<String> {
    match (width, value) {
        (_, ModelValue::FloatingPointSpecial { kind, .. }) => Some(render_fp_special(kind)),
        (
            32,
            ModelValue::FloatingPoint {
                sign,
                exponent,
                significand,
                eb: 8,
                sb: 24,
            },
        ) => {
            let exponent = u32::try_from(*exponent).ok()?;
            let significand = u32::try_from(*significand).ok()?;
            let bits = (u32::from(*sign) << 31) | (exponent << 23) | significand;
            Some(format_f32_value(f32::from_bits(bits)))
        }
        (
            64,
            ModelValue::FloatingPoint {
                sign,
                exponent,
                significand,
                eb: 11,
                sb: 53,
            },
        ) => {
            let bits = (u64::from(*sign) << 63) | (*exponent << 52) | *significand;
            Some(format_f64_value(f64::from_bits(bits)))
        }
        _ => None,
    }
}

fn render_fp_special(kind: &FpSpecialKind) -> String {
    match kind {
        FpSpecialKind::PosZero => "0.0".to_string(),
        FpSpecialKind::NegZero => "-0.0".to_string(),
        FpSpecialKind::PosInf => "+Inf".to_string(),
        FpSpecialKind::NegInf => "-Inf".to_string(),
        FpSpecialKind::NaN => "NaN".to_string(),
        _ => format!("{kind:?}"),
    }
}

fn format_f32_value(value: f32) -> String {
    if value.is_nan() {
        return "NaN".to_string();
    }
    if value.is_infinite() {
        return if value.is_sign_positive() {
            "+Inf".to_string()
        } else {
            "-Inf".to_string()
        };
    }
    if value == 0.0 {
        return if value.is_sign_negative() {
            "-0.0".to_string()
        } else {
            "0.0".to_string()
        };
    }
    let mut rendered = value.to_string();
    if !rendered.contains('.') && !rendered.contains('e') && !rendered.contains('E') {
        rendered.push_str(".0");
    }
    rendered
}

fn format_f64_value(value: f64) -> String {
    if value.is_nan() {
        return "NaN".to_string();
    }
    if value.is_infinite() {
        return if value.is_sign_positive() {
            "+Inf".to_string()
        } else {
            "-Inf".to_string()
        };
    }
    if value == 0.0 {
        return if value.is_sign_negative() {
            "-0.0".to_string()
        } else {
            "0.0".to_string()
        };
    }
    let mut rendered = value.to_string();
    if !rendered.contains('.') && !rendered.contains('e') && !rendered.contains('E') {
        rendered.push_str(".0");
    }
    rendered
}

/// Render a Seq<T> using the `__trust_vc_len_<name>` companion variable.
fn render_seq(name: &str, elem_ty: &TrustVcType, model: &Model) -> Option<String> {
    let array = model.array_val(name)?;
    let (default, stores) = match array {
        ModelValue::Array { default, stores } => (default, stores),
        _ => return None,
    };

    let len_name = format!("__trust_vc_len_{name}");
    let len = read_length(&len_name, model)?;

    // Cap at 1000 elements to avoid pathological model expansion
    if len > 1000 {
        return None;
    }

    // Build index→value map from stores (later stores override earlier)
    let mut index_map: HashMap<u64, &ModelValue> = HashMap::new();
    for (idx, val) in stores {
        if let Some(i) = model_value_to_u64(idx) {
            index_map.insert(i, val);
        }
    }

    let mut elements = Vec::with_capacity(len);
    for i in 0..len as u64 {
        let elem = index_map.get(&i).copied().unwrap_or(default.as_ref());
        elements.push(render_model_value(elem, elem_ty));
    }

    Some(format!("[{}]", elements.join(", ")))
}

/// Render a Set<T> — only when the model is finite (default=false).
fn render_set(name: &str, elem_ty: &TrustVcType, model: &Model) -> Option<String> {
    let array = model.array_val(name)?;
    let (default, stores) = match array {
        ModelValue::Array { default, stores } => (default, stores),
        _ => return None,
    };

    // Only render finite sets (default = false)
    match default.as_ref() {
        ModelValue::Bool(false) => {}
        _ => return None, // co-finite or unknown default — fall back
    }

    // Collect keys whose final stored value is true
    let mut member_map: HashMap<String, bool> = HashMap::new();
    for (key, val) in stores {
        let key_str = render_model_value(key, elem_ty);
        let is_member = matches!(val, ModelValue::Bool(true));
        member_map.insert(key_str, is_member);
    }

    let mut members: Vec<String> = member_map
        .into_iter()
        .filter(|(_, is_member)| *is_member)
        .map(|(key, _)| key)
        .collect();
    members.sort();

    Some(format!("{{{}}}", members.join(", ")))
}

/// Render a Multiset<T> when the model is finite (default count = 0).
fn render_multiset(name: &str, elem_ty: &TrustVcType, model: &Model) -> Option<String> {
    let array = model.array_val(name)?;
    render_multiset_value(array, elem_ty)
}

fn render_multiset_value(array: &ModelValue, elem_ty: &TrustVcType) -> Option<String> {
    let (default, stores) = match array {
        ModelValue::Array { default, stores } => (default, stores),
        _ => return None,
    };

    if !matches!(
        multiset_count_value(default.as_ref()),
        Some(count) if count == BigInt::from(0)
    ) {
        return None;
    }

    let mut count_map: HashMap<String, BigInt> = HashMap::new();
    for (key, val) in stores {
        let key_str = render_model_value(key, elem_ty);
        let count = multiset_count_value(val)?;
        count_map.insert(key_str, count);
    }

    let mut members: Vec<(String, BigInt)> = count_map
        .into_iter()
        .filter(|(_, count)| *count > BigInt::from(0))
        .collect();
    members.sort_by_key(|(key, _)| key.clone());

    let rendered: Vec<String> = members
        .iter()
        .map(|(key, count)| format!("{key}: {count}"))
        .collect();
    Some(format!("{{{}}}", rendered.join(", ")))
}

fn multiset_count_value(value: &ModelValue) -> Option<BigInt> {
    match value {
        ModelValue::BitVec { value, width } => Some(bv_to_unsigned(value, *width)),
        ModelValue::Int(value) => Some(value.clone()),
        _ => None,
    }
}

/// Render a Map<K,V> using the `<name>_dom` companion domain array.
fn render_map(
    name: &str,
    key_ty: &TrustVcType,
    val_ty: &TrustVcType,
    model: &Model,
) -> Option<String> {
    let main_array = model.array_val(name)?;
    let (main_default, main_stores) = match main_array {
        ModelValue::Array {
            default: main_default,
            stores: main_stores,
        } => (main_default, main_stores),
        _ => return None,
    };

    // Read domain membership array
    let dom_name = format!("{name}_dom");
    let dom_array = model.array_val(&dom_name)?;
    let (dom_default, dom_stores) = match dom_array {
        ModelValue::Array { default, stores } => (default, stores),
        _ => return None,
    };

    // Only render finite maps (domain default = false)
    match dom_default.as_ref() {
        ModelValue::Bool(false) => {}
        _ => return None,
    }

    // Collect keys present in the domain
    let mut domain_keys: Vec<&ModelValue> = Vec::new();
    for (key, val) in dom_stores {
        if matches!(val, ModelValue::Bool(true)) {
            domain_keys.push(key);
        }
    }

    // Build store map from main array for value lookups
    // Later stores override earlier — walk in order, last write wins
    let mut store_map: Vec<(&ModelValue, &ModelValue)> = Vec::new();
    for (k, v) in main_stores {
        store_map.push((k, v));
    }

    let mut entries: Vec<(String, String)> = Vec::new();
    for key in &domain_keys {
        let key_str = render_model_value(key, key_ty);
        // Find the value: last store that matches this key, or default
        let value = store_map
            .iter()
            .rev()
            .find(|(k, _)| model_values_equal(k, key))
            .map(|(_, v)| *v)
            .unwrap_or(main_default.as_ref());
        let val_str = render_model_value(value, val_ty);
        entries.push((key_str, val_str));
    }

    entries.sort_by_key(|(key, _)| key.clone());
    let formatted: Vec<String> = entries.iter().map(|(k, v)| format!("{k}: {v}")).collect();
    Some(format!("{{{}}}", formatted.join(", ")))
}

/// Render a ModelValue using the declared TrustVcType for proper formatting.
fn render_model_value(value: &ModelValue, ty: &TrustVcType) -> String {
    match (value, ty) {
        (_, TrustVcType::Unit) => "()".to_string(),
        (ModelValue::Bool(b), _) => b.to_string(),
        (ModelValue::Int(i), _) => i.to_string(),
        (value, TrustVcType::Float { width }) => {
            render_float_value(value, *width).unwrap_or_else(|| format!("{value}"))
        }
        (ModelValue::BitVec { value, width }, TrustVcType::Int { width: ty_width }) => {
            bv_to_signed(value, *ty_width.min(width)).to_string()
        }
        (ModelValue::BitVec { value, width }, TrustVcType::Uint { width: ty_width }) => {
            bv_to_unsigned(value, *ty_width.min(width)).to_string()
        }
        (ModelValue::BitVec { value, width }, TrustVcType::Char) => u32::try_from(value)
            .ok()
            .and_then(char::from_u32)
            .map_or_else(
                || format!("'\\u{{{:x}}}'", bv_to_unsigned(value, *width)),
                |c| {
                    if c.is_control() {
                        format!("'\\u{{{:x}}}'", c as u32)
                    } else {
                        format!("'{c}'")
                    }
                },
            ),
        (ModelValue::BitVec { value, width }, _) => {
            // Default: treat as unsigned decimal
            bv_to_unsigned(value, *width).to_string()
        }
        (value, TrustVcType::Multiset(elem_ty)) => {
            render_multiset_value(value, elem_ty).unwrap_or_else(|| format!("{value}"))
        }
        _ => format!("{value}"),
    }
}

/// Read a length companion variable as usize.
fn read_length(len_name: &str, model: &Model) -> Option<usize> {
    // Length is stored as BitVec(pointer_width())
    if let Some((value, _width)) = model.bv_val(len_name) {
        return usize::try_from(&value).ok();
    }
    // Fallback: might be stored as Int in some modes
    if let Some(value) = model.int_val(len_name) {
        return usize::try_from(value).ok();
    }
    None
}

/// Convert a ModelValue to a u64 index (for Seq array indexing).
fn model_value_to_u64(value: &ModelValue) -> Option<u64> {
    match value {
        ModelValue::BitVec { value, .. } => u64::try_from(value).ok(),
        ModelValue::Int(i) => u64::try_from(i).ok(),
        _ => None,
    }
}

/// Structural equality check for ModelValues (for map key lookup).
fn model_values_equal(a: &ModelValue, b: &ModelValue) -> bool {
    match (a, b) {
        (ModelValue::Bool(x), ModelValue::Bool(y)) => x == y,
        (ModelValue::Int(x), ModelValue::Int(y)) => x == y,
        (
            ModelValue::BitVec {
                value: v1,
                width: w1,
            },
            ModelValue::BitVec {
                value: v2,
                width: w2,
            },
        ) => v1 == v2 && w1 == w2,
        (ModelValue::String(x), ModelValue::String(y)) => x == y,
        (
            ModelValue::FloatingPoint {
                sign: sign_x,
                exponent: exponent_x,
                significand: significand_x,
                eb: eb_x,
                sb: sb_x,
            },
            ModelValue::FloatingPoint {
                sign: sign_y,
                exponent: exponent_y,
                significand: significand_y,
                eb: eb_y,
                sb: sb_y,
            },
        ) => {
            sign_x == sign_y
                && exponent_x == exponent_y
                && significand_x == significand_y
                && eb_x == eb_y
                && sb_x == sb_y
        }
        (
            ModelValue::FloatingPointSpecial {
                kind: kind_x,
                eb: eb_x,
                sb: sb_x,
            },
            ModelValue::FloatingPointSpecial {
                kind: kind_y,
                eb: eb_y,
                sb: sb_y,
            },
        ) => kind_x == kind_y && eb_x == eb_y && sb_x == sb_y,
        _ => false,
    }
}

/// Human-readable type name for a TrustVcType, matching Rust surface syntax.
fn trust_vc_type_display_name(ty: &TrustVcType) -> String {
    match ty {
        TrustVcType::Unit => "()".into(),
        TrustVcType::Bool => "bool".into(),
        TrustVcType::Int { width: 8 } => "i8".into(),
        TrustVcType::Int { width: 16 } => "i16".into(),
        TrustVcType::Int { width: 32 } => "i32".into(),
        TrustVcType::Int { width: 64 } => "i64".into(),
        TrustVcType::Int { width: 128 } => "i128".into(),
        TrustVcType::Int { width } => format!("i{width}"),
        TrustVcType::Uint { width: 8 } => "u8".into(),
        TrustVcType::Uint { width: 16 } => "u16".into(),
        TrustVcType::Uint { width: 32 } => "u32".into(),
        TrustVcType::Uint { width: 64 } => "u64".into(),
        TrustVcType::Uint { width: 128 } => "u128".into(),
        TrustVcType::Uint { width } => format!("u{width}"),
        TrustVcType::MathInt => "int".into(),
        TrustVcType::Nat => "nat".into(),
        TrustVcType::Real => "real".into(),
        TrustVcType::Float { width: 32 } => "f32".into(),
        TrustVcType::Float { width: 64 } => "f64".into(),
        TrustVcType::Float { width } => format!("f{width}"),
        TrustVcType::Char => "char".into(),
        TrustVcType::StrSlice => "str".into(),
        TrustVcType::String => "String".into(),
        TrustVcType::Seq(elem) => format!("Seq<{}>", trust_vc_type_display_name(elem)),
        TrustVcType::Array(elem, len) => {
            format!("[{}; {}]", trust_vc_type_display_name(elem), len)
        }
        TrustVcType::Set(elem) => format!("Set<{}>", trust_vc_type_display_name(elem)),
        TrustVcType::Multiset(elem) => format!("Multiset<{}>", trust_vc_type_display_name(elem)),
        TrustVcType::Map(k, v) => format!(
            "Map<{}, {}>",
            trust_vc_type_display_name(k),
            trust_vc_type_display_name(v)
        ),
        _ => format!("{ty:?}"),
    }
}

#[cfg(test)]
#[path = "model_render_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "model_render_proof_tests.rs"]
mod proof_tests;
