//! TrustVcType parsing, serialization, and builtin type constructors.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracted from `ir.rs` to keep that file under 500 lines.
//! Part of #2608.

use super::{pointer_width, DatatypeVariant, TrustVcType, TrustVcTypeParseError};
use crate::type_syntax::{split_generic_args, split_top_level_args};

impl TrustVcType {
    /// Strict parsing: returns `Err` for unrecognized type strings.
    ///
    /// Use this when unknown types should be rejected (e.g., encoder paths,
    /// return type resolution). For call sites that intentionally tolerate
    /// unknown runtime types, use `parse_or_opaque` instead (#2126).
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(ty: &str) -> Result<TrustVcType, String> {
        Self::try_from_str(ty).map_err(|err| err.to_string())
    }

    /// Typed strict parsing path for programmatic callers.
    pub fn try_from_str(ty: &str) -> Result<TrustVcType, TrustVcTypeParseError> {
        Self::parse_inner(ty, true)
    }

    /// Lossy parsing: unrecognized type strings become `TrustVcType::Opaque`.
    ///
    /// Use when the caller intentionally permits runtime types outside
    /// trust_vc's type vocabulary (e.g., macro-generated variable declarations,
    /// syn type conversion). The verification layer rejects Opaque-typed
    /// variables before encoding (#1926, #2224).
    pub fn parse_or_opaque(ty: &str) -> TrustVcType {
        Self::parse_inner(ty, false).unwrap_or_else(|_| TrustVcType::Opaque(ty.to_string()))
    }

    fn parse_inner(ty: &str, strict: bool) -> Result<TrustVcType, TrustVcTypeParseError> {
        let ty = ty.trim();
        if let Some(inner) = strip_reference_type(ty) {
            return Self::parse_inner(inner, strict);
        }
        // A `TrustVcUnmodeledConstPat_` marker can only have been stamped onto
        // this name by `const_pattern_desugar`'s R5 token salvage, which
        // substitutes registry names in EVERY token position of a stream it
        // cannot parse — including TYPE ASCRIPTIONS such as the `int` in
        // `assert_forall_by!(assert forall|x: int| ...)` when the file holds
        // `use trust_vc_types::int;` (an EXTERNAL import, which the file-local
        // resolver must classify Unmodeled). A const cannot syntactically
        // occupy type position, so the marker's fail-closed pattern reading
        // has no work to do here: strip it and resolve the original spelling,
        // exactly as the pre-salvage extraction did. Pattern lanes keep
        // failing closed on the marker (`arm_pattern_match_condition`), and a
        // marker over a genuinely unknown type still falls through to the
        // Opaque rejection below under the ORIGINAL name.
        let ty = crate::const_pattern_desugar::unmodeled_const_pat_name(ty).unwrap_or(ty);
        match ty {
            "()" => Ok(TrustVcType::Unit),
            "bool" => Ok(TrustVcType::Bool),
            "char" => Ok(TrustVcType::Char),
            "str" => Ok(TrustVcType::StrSlice),
            "String" | "alloc::string::String" | "std::string::String" => Ok(TrustVcType::String),
            "i8" => Ok(TrustVcType::Int { width: 8 }),
            "i16" => Ok(TrustVcType::Int { width: 16 }),
            "i32" => Ok(TrustVcType::Int { width: 32 }),
            "i64" => Ok(TrustVcType::Int { width: 64 }),
            "i128" => Ok(TrustVcType::Int { width: 128 }),
            "isize" => Ok(TrustVcType::Int {
                width: pointer_width(),
            }),
            "u8" => Ok(TrustVcType::Uint { width: 8 }),
            "u16" => Ok(TrustVcType::Uint { width: 16 }),
            "u32" => Ok(TrustVcType::Uint { width: 32 }),
            "u64" => Ok(TrustVcType::Uint { width: 64 }),
            "u128" => Ok(TrustVcType::Uint { width: 128 }),
            "usize" => Ok(TrustVcType::Uint {
                width: pointer_width(),
            }),
            "f32" => Ok(TrustVcType::Float { width: 32 }),
            "f64" => Ok(TrustVcType::Float { width: 64 }),
            "real" => Ok(TrustVcType::Real),
            "int" => Ok(TrustVcType::MathInt),
            "nat" => Ok(TrustVcType::Nat),
            _ => {
                if let Some((element, len)) = split_array_type(ty) {
                    let element = Self::parse_inner(element.trim(), strict)?;
                    let len = len
                        .trim()
                        .parse::<usize>()
                        .map_err(|_| Self::invalid_syntax_error("array length", ty))?;
                    Ok(TrustVcType::Array(Box::new(element), len))
                } else if let Some(element) = split_slice_type(ty) {
                    let element = Self::parse_inner(element.trim(), strict)?;
                    Ok(TrustVcType::Seq(Box::new(element)))
                } else if let Some(inner) =
                    ty.strip_prefix("Seq<").and_then(|s| s.strip_suffix('>'))
                {
                    let element = Self::parse_inner(inner, strict)?;
                    Ok(TrustVcType::Seq(Box::new(element)))
                } else if let Some(inner) = strip_vec_type_args(ty) {
                    let element = Self::parse_inner(inner.trim(), strict)?;
                    Ok(TrustVcType::Seq(Box::new(element)))
                } else if let Some((_kind, inner)) = strip_std_set_type_args(ty) {
                    let element = Self::parse_inner(inner.trim(), strict)?;
                    Ok(TrustVcType::Set(Box::new(element)))
                } else if let Some(inner) =
                    ty.strip_prefix("Set<").and_then(|s| s.strip_suffix('>'))
                {
                    let element = Self::parse_inner(inner, strict)?;
                    Ok(TrustVcType::Set(Box::new(element)))
                } else if let Some(inner) = ty
                    .strip_prefix("Multiset<")
                    .and_then(|s| s.strip_suffix('>'))
                {
                    let element = Self::parse_inner(inner, strict)?;
                    Ok(TrustVcType::Multiset(Box::new(element)))
                } else if let Some(inner) =
                    ty.strip_prefix("Map<").and_then(|s| s.strip_suffix('>'))
                {
                    if let Some((key, value)) = split_generic_args(inner) {
                        let key_type = Self::parse_inner(key.trim(), strict)?;
                        let value_type = Self::parse_inner(value.trim(), strict)?;
                        Ok(TrustVcType::Map(Box::new(key_type), Box::new(value_type)))
                    } else {
                        Err(Self::invalid_syntax_error("Map", ty))
                    }
                } else if let Some((kind, inner)) = strip_std_map_type_args(ty) {
                    if let Some((key, value)) = split_generic_args(inner) {
                        let key_type = Self::parse_inner(key.trim(), strict)?;
                        let value_type = Self::parse_inner(value.trim(), strict)?;
                        Ok(TrustVcType::Map(Box::new(key_type), Box::new(value_type)))
                    } else {
                        Err(Self::invalid_syntax_error(kind, ty))
                    }
                } else if let Some(inner) =
                    ty.strip_prefix("SpecFn<").and_then(|s| s.strip_suffix('>'))
                {
                    if let Some((args, ret)) = split_generic_args(inner) {
                        let arg_types = if let Some(tuple_inner) = args
                            .trim()
                            .strip_prefix('(')
                            .and_then(|s| s.strip_suffix(')'))
                        {
                            let parts = split_top_level_args(tuple_inner);
                            if parts.is_empty() {
                                return Err(Self::invalid_syntax_error("SpecFn tuple arg", ty));
                            }
                            parts
                                .into_iter()
                                .map(|part| Self::parse_inner(part, strict))
                                .collect::<Result<Vec<_>, _>>()?
                        } else {
                            vec![Self::parse_inner(args.trim(), strict)?]
                        };
                        let ret_type = Self::parse_inner(ret.trim(), strict)?;
                        Ok(TrustVcType::SpecFn(arg_types, Box::new(ret_type)))
                    } else {
                        Err(Self::invalid_syntax_error("SpecFn", ty))
                    }
                } else if let Some(inner) =
                    ty.strip_prefix("Option<").and_then(|s| s.strip_suffix('>'))
                {
                    let value_ty = Self::parse_inner(inner.trim(), strict)?;
                    Ok(Self::builtin_option(value_ty))
                } else if let Some(inner) = strip_cow_type_args(ty) {
                    let inner_ty = cow_inner_type_arg(inner)
                        .ok_or_else(|| Self::invalid_syntax_error("Cow", ty))
                        .and_then(|inner| Self::parse_inner(inner.trim(), strict))?;
                    Ok(Self::builtin_cow(inner_ty))
                } else if let Some(inner) =
                    ty.strip_prefix("Result<").and_then(|s| s.strip_suffix('>'))
                {
                    if let Some((ok, err)) = split_generic_args(inner) {
                        let ok_ty = Self::parse_inner(ok.trim(), strict)?;
                        let err_ty = Self::parse_inner(err.trim(), strict)?;
                        Ok(Self::builtin_result(ok_ty, err_ty))
                    } else {
                        Err(Self::invalid_syntax_error("Result", ty))
                    }
                } else if let Some(inner) = strip_tuple_type_args(ty) {
                    let elements = split_top_level_args(inner)
                        .into_iter()
                        .map(|part| Self::parse_inner(part.trim(), strict))
                        .collect::<Result<Vec<_>, _>>()?;
                    let name = tuple_type_name(&elements);
                    let fields = elements
                        .into_iter()
                        .enumerate()
                        .map(|(index, ty)| (index.to_string(), ty))
                        .collect();
                    Ok(TrustVcType::Datatype {
                        name,
                        variants: vec![DatatypeVariant::new("Tuple", fields)],
                    })
                // Recursive datatypes: List<T> and Tree<T>
                // Uses RecursiveRef for the recursive field to avoid infinite IR.
                } else if let Some(inner) =
                    ty.strip_prefix("List<").and_then(|s| s.strip_suffix('>'))
                {
                    let elem_ty = Self::parse_inner(inner.trim(), strict)?;
                    Ok(Self::builtin_list(elem_ty))
                } else if let Some(inner) =
                    ty.strip_prefix("Tree<").and_then(|s| s.strip_suffix('>'))
                {
                    let elem_ty = Self::parse_inner(inner.trim(), strict)?;
                    Ok(Self::builtin_tree(elem_ty))
                // Ghost/Tracked/Proph/Snapshot wrappers erase to their inner type at SMT level.
                // These are verification-only wrappers; ay sees just T.
                } else if let Some(inner) = ty
                    .strip_prefix("Tracked<")
                    .and_then(|s| s.strip_suffix('>'))
                {
                    Self::parse_inner(inner.trim(), strict)
                } else if let Some(inner) =
                    ty.strip_prefix("Ghost<").and_then(|s| s.strip_suffix('>'))
                {
                    Self::parse_inner(inner.trim(), strict)
                } else if let Some(inner) =
                    ty.strip_prefix("Proph<").and_then(|s| s.strip_suffix('>'))
                {
                    Self::parse_inner(inner.trim(), strict)
                } else if let Some(inner) = ty
                    .strip_prefix("Snapshot<")
                    .and_then(|s| s.strip_suffix('>'))
                {
                    Self::parse_inner(inner.trim(), strict)
                // `PhantomData<T>` is a zero-sized marker with exactly one
                // inhabitant, so it is sound to treat it as isomorphic to the
                // unit type `()`. The inner `T` is still parsed (so unknown
                // inner types fail closed under `strict`), but the type erases
                // to `Unit`. This matches Verus's `phantom_data_is_unit`, where
                // any two `PhantomData<T>` values are provably equal. Cluster
                // #2779.
                } else if let Some(inner) = strip_phantom_data_type_args(ty) {
                    Self::parse_inner(inner.trim(), strict)?;
                    Ok(TrustVcType::Unit)
                // Recognize short uppercase identifiers as type parameters
                // (e.g., "T", "A", "AB"). Follows Rust convention where generic
                // type params are 1-2 uppercase letters. Part of #2431.
                } else if !ty.is_empty()
                    && ty.len() <= 2
                    && ty.starts_with(|c: char| c.is_ascii_uppercase())
                    && ty.chars().all(|c| c.is_ascii_uppercase())
                {
                    Ok(TrustVcType::TypeParam(ty.to_string()))
                } else if ty.is_empty() {
                    Err(TrustVcTypeParseError::EmptyTypeString)
                } else if strict {
                    Err(TrustVcTypeParseError::UnknownType {
                        input: ty.to_string(),
                    })
                } else {
                    Ok(TrustVcType::Opaque(ty.to_string()))
                }
            }
        }
    }

    /// Converts back to the canonical type string representation.
    ///
    /// Round-trip property: `TrustVcType::from_str(ty.to_type_string())` should
    /// return an equivalent type (modulo isize/usize normalization to the
    /// pointer-width integer). Float types (f32/f64) are preserved as separate
    /// `Float { width }` variants so the encoder can preserve IEEE 754 sorts.
    #[must_use]
    pub fn to_type_string(&self) -> String {
        match self {
            TrustVcType::Unit => "()".to_string(),
            TrustVcType::Bool => "bool".to_string(),
            TrustVcType::Char => "char".to_string(),
            TrustVcType::StrSlice => "str".to_string(),
            TrustVcType::String => "String".to_string(),
            TrustVcType::Int { width } => match width {
                8 => "i8".to_string(),
                16 => "i16".to_string(),
                32 => "i32".to_string(),
                64 => "i64".to_string(),
                128 => "i128".to_string(),
                _ => format!("i{}", width),
            },
            TrustVcType::Uint { width } => match width {
                8 => "u8".to_string(),
                16 => "u16".to_string(),
                32 => "u32".to_string(),
                64 => "u64".to_string(),
                128 => "u128".to_string(),
                _ => format!("u{}", width),
            },
            TrustVcType::MathInt => "int".to_string(),
            TrustVcType::Nat => "nat".to_string(),
            TrustVcType::Real => "real".to_string(),
            TrustVcType::Float { width } => match width {
                32 => "f32".to_string(),
                64 => "f64".to_string(),
                _ => format!("f{}", width),
            },
            TrustVcType::Seq(element) => format!("Seq<{}>", element.to_type_string()),
            TrustVcType::Array(element, len) => {
                format!("[{}; {}]", element.to_type_string(), len)
            }
            TrustVcType::Set(element) => format!("Set<{}>", element.to_type_string()),
            TrustVcType::Multiset(element) => format!("Multiset<{}>", element.to_type_string()),
            TrustVcType::Map(key, value) => {
                format!("Map<{}, {}>", key.to_type_string(), value.to_type_string())
            }
            TrustVcType::SpecFn(args, ret) => {
                let args = match args.as_slice() {
                    [TrustVcType::Unit] => "((),)".to_string(),
                    [arg] => arg.to_type_string(),
                    _ => format!(
                        "({})",
                        args.iter()
                            .map(TrustVcType::to_type_string)
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                };
                format!("SpecFn<{}, {}>", args, ret.to_type_string())
            }
            TrustVcType::Datatype { name, .. } => name.clone(),
            TrustVcType::RecursiveRef(name) => name.clone(),
            TrustVcType::TypeParam(name) => name.clone(),
            TrustVcType::Poly => "Poly".to_string(),
            TrustVcType::Opaque(name) => name.clone(),
        }
    }

    fn invalid_syntax_error(kind: &'static str, input: impl Into<String>) -> TrustVcTypeParseError {
        TrustVcTypeParseError::InvalidSyntax {
            kind,
            input: input.into(),
        }
    }

    fn builtin_option(value_ty: TrustVcType) -> TrustVcType {
        let value_name = value_ty.to_type_string();
        TrustVcType::Datatype {
            name: format!("Option<{}>", value_name),
            variants: vec![
                DatatypeVariant {
                    name: "None".to_string(),
                    fields: vec![],
                },
                DatatypeVariant {
                    name: "Some".to_string(),
                    fields: vec![("0".to_string(), value_ty)],
                },
            ],
        }
    }

    fn builtin_result(ok_ty: TrustVcType, err_ty: TrustVcType) -> TrustVcType {
        let ok_name = ok_ty.to_type_string();
        let err_name = err_ty.to_type_string();
        TrustVcType::Datatype {
            name: format!("Result<{}, {}>", ok_name, err_name),
            variants: vec![
                DatatypeVariant {
                    name: "Ok".to_string(),
                    fields: vec![("0".to_string(), ok_ty)],
                },
                DatatypeVariant {
                    name: "Err".to_string(),
                    fields: vec![("0".to_string(), err_ty)],
                },
            ],
        }
    }

    fn builtin_cow(inner_ty: TrustVcType) -> TrustVcType {
        let inner_name = inner_ty.to_type_string();
        TrustVcType::Datatype {
            name: format!("Cow<{}>", inner_name),
            variants: vec![
                DatatypeVariant {
                    name: "Borrowed".to_string(),
                    fields: vec![("0".to_string(), inner_ty.clone())],
                },
                DatatypeVariant {
                    name: "Owned".to_string(),
                    fields: vec![("0".to_string(), inner_ty)],
                },
            ],
        }
    }

    /// Recursive linked list: `List<T>` → Nil | Cons(head: T, tail: RecursiveRef)
    fn builtin_list(elem_ty: TrustVcType) -> TrustVcType {
        let elem_name = elem_ty.to_type_string();
        let datatype_name = format!("List<{}>", elem_name);
        TrustVcType::Datatype {
            name: datatype_name.clone(),
            variants: vec![
                DatatypeVariant {
                    name: "Nil".to_string(),
                    fields: vec![],
                },
                DatatypeVariant {
                    name: "Cons".to_string(),
                    fields: vec![
                        ("head".to_string(), elem_ty),
                        ("tail".to_string(), TrustVcType::RecursiveRef(datatype_name)),
                    ],
                },
            ],
        }
    }

    /// Recursive binary tree: `Tree<T>` → Leaf(val: T) | Branch(left, right: RecursiveRef)
    fn builtin_tree(elem_ty: TrustVcType) -> TrustVcType {
        let elem_name = elem_ty.to_type_string();
        let datatype_name = format!("Tree<{}>", elem_name);
        TrustVcType::Datatype {
            name: datatype_name.clone(),
            variants: vec![
                DatatypeVariant {
                    name: "Leaf".to_string(),
                    fields: vec![("val".to_string(), elem_ty)],
                },
                DatatypeVariant {
                    name: "Branch".to_string(),
                    fields: vec![
                        (
                            "left".to_string(),
                            TrustVcType::RecursiveRef(datatype_name.clone()),
                        ),
                        (
                            "right".to_string(),
                            TrustVcType::RecursiveRef(datatype_name),
                        ),
                    ],
                },
            ],
        }
    }
}

fn strip_reference_type(ty: &str) -> Option<&str> {
    let mut rest = ty.strip_prefix('&')?.trim_start();
    if let Some(after_tick) = rest.strip_prefix('\'') {
        let mut lifetime_len = after_tick
            .char_indices()
            .find(|(_, ch)| !(*ch == '_' || ch.is_ascii_alphanumeric()))
            .map(|(index, _)| index)
            .unwrap_or(after_tick.len());
        if lifetime_len == after_tick.len() {
            if let Some(compact_len) = compact_lifetime_len_before_type(after_tick) {
                lifetime_len = compact_len;
            }
        }
        rest = after_tick[lifetime_len..].trim_start();
    }
    if let Some(after_mut) = rest.strip_prefix("mut") {
        rest = after_mut.trim_start();
    }
    Some(rest)
}

fn compact_lifetime_len_before_type(rest: &str) -> Option<usize> {
    (1..rest.len()).find(|&index| {
        let (lifetime, ty) = rest.split_at(index);
        is_lifetime_ident(lifetime) && looks_like_type_start(ty)
    })
}

fn is_lifetime_ident(value: &str) -> bool {
    let mut chars = value.chars();
    matches!(chars.next(), Some(ch) if ch == '_' || ch.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

fn looks_like_type_start(value: &str) -> bool {
    matches!(
        value,
        "bool"
            | "char"
            | "str"
            | "String"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "f32"
            | "f64"
            | "real"
            | "int"
            | "nat"
    ) || value.starts_with(char::is_uppercase)
        || value.starts_with('[')
        || value.starts_with('(')
        || value.starts_with("Seq<")
        || value.starts_with("Vec<")
        || value.starts_with("Set<")
        || value.starts_with("Map<")
        || value.starts_with("Option<")
        || value.starts_with("Result<")
}

fn strip_cow_type_args(ty: &str) -> Option<&str> {
    [
        "Cow",
        "std::borrow::Cow",
        "alloc::borrow::Cow",
        "core::borrow::Cow",
    ]
    .into_iter()
    .find_map(|prefix| {
        ty.strip_prefix(prefix)
            .and_then(|rest| rest.strip_prefix('<'))
            .and_then(|rest| rest.strip_suffix('>'))
    })
}

fn strip_phantom_data_type_args(ty: &str) -> Option<&str> {
    [
        "PhantomData",
        "core::marker::PhantomData",
        "std::marker::PhantomData",
    ]
    .into_iter()
    .find_map(|prefix| {
        ty.strip_prefix(prefix)
            .and_then(|rest| rest.strip_prefix('<'))
            .and_then(|rest| rest.strip_suffix('>'))
    })
}

fn strip_vec_type_args(ty: &str) -> Option<&str> {
    ["Vec", "std::vec::Vec", "alloc::vec::Vec"]
        .into_iter()
        .find_map(|prefix| {
            ty.strip_prefix(prefix)
                .and_then(|rest| rest.strip_prefix('<'))
                .and_then(|rest| rest.strip_suffix('>'))
        })
}

fn strip_std_map_type_args(ty: &str) -> Option<(&'static str, &str)> {
    [
        ("HashMap", "HashMap"),
        ("HashMap", "std::collections::HashMap"),
        ("HashMap", "std::collections::hash_map::HashMap"),
        ("BTreeMap", "BTreeMap"),
        ("BTreeMap", "std::collections::BTreeMap"),
        ("BTreeMap", "std::collections::btree_map::BTreeMap"),
        ("BTreeMap", "alloc::collections::BTreeMap"),
        ("BTreeMap", "alloc::collections::btree_map::BTreeMap"),
    ]
    .into_iter()
    .find_map(|(kind, prefix)| {
        ty.strip_prefix(prefix)
            .and_then(|rest| rest.strip_prefix('<'))
            .and_then(|rest| rest.strip_suffix('>'))
            .map(|inner| (kind, inner))
    })
}

fn strip_std_set_type_args(ty: &str) -> Option<(&'static str, &str)> {
    [
        ("HashSet", "HashSet"),
        ("HashSet", "std::collections::HashSet"),
        ("HashSet", "std::collections::hash_set::HashSet"),
        ("BTreeSet", "BTreeSet"),
        ("BTreeSet", "std::collections::BTreeSet"),
        ("BTreeSet", "std::collections::btree_set::BTreeSet"),
        ("BTreeSet", "alloc::collections::BTreeSet"),
        ("BTreeSet", "alloc::collections::btree_set::BTreeSet"),
    ]
    .into_iter()
    .find_map(|(kind, prefix)| {
        ty.strip_prefix(prefix)
            .and_then(|rest| rest.strip_prefix('<'))
            .and_then(|rest| rest.strip_suffix('>'))
            .map(|inner| (kind, inner))
    })
}

fn cow_inner_type_arg(args: &str) -> Option<&str> {
    let type_args = split_top_level_args(args)
        .into_iter()
        .filter(|arg| {
            let trimmed = arg.trim_start();
            !trimmed.starts_with('\'') && !trimmed.is_empty()
        })
        .collect::<Vec<_>>();
    match type_args.as_slice() {
        [inner] => Some(inner),
        _ => None,
    }
}

fn split_array_type(ty: &str) -> Option<(&str, &str)> {
    let inner = ty.strip_prefix('[')?.strip_suffix(']')?;
    let mut angle_depth = 0usize;
    let mut paren_depth = 0usize;
    let mut bracket_depth = 0usize;
    for (index, ch) in inner.char_indices() {
        match ch {
            '<' => angle_depth += 1,
            '>' => angle_depth = angle_depth.saturating_sub(1),
            '(' => paren_depth += 1,
            ')' => paren_depth = paren_depth.saturating_sub(1),
            '[' => bracket_depth += 1,
            ']' => bracket_depth = bracket_depth.saturating_sub(1),
            ';' if angle_depth == 0 && paren_depth == 0 && bracket_depth == 0 => {
                return Some((&inner[..index], &inner[index + 1..]));
            }
            _ => {}
        }
    }
    None
}

fn split_slice_type(ty: &str) -> Option<&str> {
    let inner = ty.strip_prefix('[')?.strip_suffix(']')?;
    if split_array_type(ty).is_some() {
        None
    } else {
        Some(inner)
    }
}

fn strip_tuple_type_args(ty: &str) -> Option<&str> {
    let inner = ty.strip_prefix('(')?.strip_suffix(')')?;
    let parts = split_top_level_args(inner);
    if parts.is_empty() {
        return None;
    }
    (parts.len() > 1 || inner.trim_end().ends_with(',')).then_some(inner)
}

fn tuple_type_name(element_tys: &[TrustVcType]) -> String {
    match element_tys {
        [] => "()".to_string(),
        [ty] => format!("({},)", ty.to_type_string()),
        _ => format!(
            "({})",
            element_tys
                .iter()
                .map(TrustVcType::to_type_string)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

impl std::str::FromStr for TrustVcType {
    type Err = TrustVcTypeParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        TrustVcType::try_from_str(s)
    }
}

#[cfg(test)]
#[path = "ir_type_parse_tests.rs"]
mod tests;
