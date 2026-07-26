//! Type inference and expression classification helpers for local variable extraction.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from `local_vars.rs` for the 500-line limit (#2621).

use quote::quote;

pub(crate) fn is_mut_ref_shadow_var(var_name: &str) -> bool {
    var_name.starts_with("__trust_vc_mutref_")
}

pub(crate) fn is_verification_wrapper_type(ty: &syn::Type) -> bool {
    match ty {
        syn::Type::Path(type_path) => {
            type_path.qself.is_none()
                && type_path.path.segments.last().is_some_and(|seg| {
                    seg.ident == "Ghost"
                        || seg.ident == "Tracked"
                        || seg.ident == "Proph"
                        || seg.ident == "Snapshot"
                })
        }
        syn::Type::Reference(type_ref) => is_verification_wrapper_type(&type_ref.elem),
        _ => false,
    }
}

/// Result of type inference for an expression.
#[derive(Debug)]
pub(crate) enum TypeInference {
    /// Type was successfully inferred (e.g., integer literal with suffix).
    Inferred(String),
    /// Type should be inferred at runtime from a referenced variable.
    /// Contains the name of the variable to look up (e.g., `let y = x` → InferFromRef("x")).
    InferFromRef(String),
    /// String literals are explicitly unsupported in this slice.
    UnsupportedStringLiteral,
    /// Cannot infer type — require explicit annotation.
    Unknown,
}

/// Try to infer the type of an expression from its literal value or type suffix.
///
/// Returns `Inferred(type)` for literals with deterministic types,
/// `InferFromRef(name)` for variable references and binary expressions (#1603),
/// `Unknown` for complex expressions that need explicit annotation.
pub(crate) fn infer_type_from_expr(expr: &syn::Expr) -> TypeInference {
    match expr {
        syn::Expr::Lit(expr_lit) => match &expr_lit.lit {
            syn::Lit::Int(int_lit) => {
                let suffix = int_lit.suffix();
                if suffix.is_empty() {
                    // No suffix — default to i32 (matches Rust default)
                    TypeInference::Inferred("i32".to_string())
                } else {
                    // Has suffix: i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, usize, isize
                    TypeInference::Inferred(suffix.to_string())
                }
            }
            syn::Lit::Bool(_) => TypeInference::Inferred("bool".to_string()),
            syn::Lit::Float(float_lit) => {
                let suffix = float_lit.suffix();
                if suffix.is_empty() {
                    TypeInference::Inferred("f64".to_string())
                } else {
                    TypeInference::Inferred(suffix.to_string())
                }
            }
            syn::Lit::Char(_) => TypeInference::Inferred("char".to_string()),
            syn::Lit::Str(_) => TypeInference::UnsupportedStringLiteral,
            _ => TypeInference::Unknown,
        },
        syn::Expr::Tuple(tuple) if tuple.elems.is_empty() => {
            TypeInference::Inferred("()".to_string())
        }
        syn::Expr::Unary(unary) => {
            // Handle negation: `-5` should infer same type as `5`
            if matches!(unary.op, syn::UnOp::Neg(_)) {
                infer_type_from_expr(&unary.expr)
            } else {
                TypeInference::Unknown
            }
        }
        syn::Expr::Path(expr_path) => {
            if let Some(ty) = infer_type_from_nullary_constructor_path(&expr_path.path) {
                return TypeInference::Inferred(ty);
            }
            // Variable reference like `let result = x` — infer type from the
            // referenced variable at runtime via collect_variable_from_ref (#1603).
            if let Some(ident) = expr_path.path.get_ident() {
                TypeInference::InferFromRef(ident.to_string())
            } else {
                TypeInference::Unknown
            }
        }
        syn::Expr::Call(call) => infer_type_from_constructor_call(call).unwrap_or({
            // Function call — cannot infer return type at macro level.
            // Require explicit type annotation.
            TypeInference::Unknown
        }),
        syn::Expr::Binary(expr_binary) => {
            // Binary expression like `let y = x + 1` — infer type from the
            // first variable operand at runtime (#1603).
            let ref_name = extract_first_ident(&expr_binary.left)
                .or_else(|| extract_first_ident(&expr_binary.right));
            match ref_name {
                Some(name) => TypeInference::InferFromRef(name),
                None => {
                    // No variable operands (e.g., `let z = 1 + 2`) — fall back to
                    // inferring from the left operand's literal type.
                    infer_type_from_expr(&expr_binary.left)
                }
            }
        }
        syn::Expr::Cast(expr_cast) => {
            // Cast expression like `let y = x as u64` — target type is explicit.
            TypeInference::Inferred(extract_type_string(&expr_cast.ty))
        }
        syn::Expr::Paren(expr_paren) => {
            // Parenthesized expression like `let y = (x)` — recurse through parens.
            infer_type_from_expr(&expr_paren.expr)
        }
        syn::Expr::MethodCall(_) => TypeInference::Unknown,
        _ => TypeInference::Unknown,
    }
}

fn infer_type_from_constructor_call(call: &syn::ExprCall) -> Option<TypeInference> {
    let syn::Expr::Path(func_path) = call.func.as_ref() else {
        return None;
    };
    if let Some(ty) = infer_type_from_result_constructor_path(&func_path.path) {
        return Some(TypeInference::Inferred(ty));
    }
    if let Some(option_inner) = option_inner_from_constructor_path(&func_path.path) {
        return Some(TypeInference::Inferred(format!("Option<{option_inner}>")));
    }

    let last = func_path.path.segments.last()?;
    if last.ident == "Some" && call.args.len() == 1 {
        if let syn::PathArguments::AngleBracketed(args) = &last.arguments {
            let inner = generic_arg_type_string(args, 0)?;
            return Some(TypeInference::Inferred(format!("Option<{inner}>")));
        }
        let arg = call.args.first()?;
        if let TypeInference::Inferred(inner) = infer_type_from_expr(arg) {
            return Some(TypeInference::Inferred(format!("Option<{inner}>")));
        }
    }

    None
}

fn infer_type_from_nullary_constructor_path(path: &syn::Path) -> Option<String> {
    let last = path.segments.last()?;
    if last.ident == "None" {
        if let syn::PathArguments::AngleBracketed(args) = &last.arguments {
            let inner = generic_arg_type_string(args, 0)?;
            return Some(format!("Option<{inner}>"));
        }
        return option_inner_from_constructor_path(path).map(|inner| format!("Option<{inner}>"));
    }
    None
}

fn infer_type_from_result_constructor_path(path: &syn::Path) -> Option<String> {
    let last = path.segments.last()?;
    let variant = last.ident.to_string();
    if variant != "Ok" && variant != "Err" {
        return None;
    }
    if let syn::PathArguments::AngleBracketed(args) = &last.arguments {
        let ok = generic_arg_type_string(args, 0)?;
        let err = generic_arg_type_string(args, 1)?;
        return Some(format!("Result<{ok}, {err}>"));
    }
    let result_segment = path.segments.iter().rev().nth(1)?;
    if result_segment.ident != "Result" {
        return None;
    }
    let syn::PathArguments::AngleBracketed(args) = &result_segment.arguments else {
        return None;
    };
    let ok = generic_arg_type_string(args, 0)?;
    let err = generic_arg_type_string(args, 1)?;
    Some(format!("Result<{ok}, {err}>"))
}

fn option_inner_from_constructor_path(path: &syn::Path) -> Option<String> {
    let option_segment = path.segments.iter().rev().nth(1)?;
    if option_segment.ident != "Option" {
        return None;
    }
    let syn::PathArguments::AngleBracketed(args) = &option_segment.arguments else {
        return None;
    };
    generic_arg_type_string(args, 0)
}

fn generic_arg_type_string(
    args: &syn::AngleBracketedGenericArguments,
    index: usize,
) -> Option<String> {
    args.args
        .iter()
        .filter_map(|arg| match arg {
            syn::GenericArgument::Type(ty) => Some(extract_type_string(ty)),
            _ => None,
        })
        .nth(index)
}

/// Checks whether an expression is a `trust_vc::arbitrary!()` macro invocation.
///
/// Matches both `trust_vc::arbitrary!(T)` and `arbitrary!(T)` via trailing
/// segment. When detected, the enclosing let-binding should NOT generate
/// any constraint — the variable must remain unconstrained. Part of #2518.
pub(crate) fn is_arbitrary_expr(expr: &syn::Expr) -> bool {
    // Direct macro: `trust_vc::arbitrary!(i32)` or `arbitrary!(i32)`
    if let syn::Expr::Macro(m) = expr {
        return m
            .mac
            .path
            .segments
            .last()
            .is_some_and(|seg| seg.ident == "arbitrary");
    }
    // The macro expands to a block `{ <T as Default>::default() }`.
    // Since attribute macros see the pre-expansion form, only the
    // macro case above should fire. The block case is a safety net.
    if let syn::Expr::Block(b) = expr {
        if let [syn::Stmt::Expr(inner, _)] = b.block.stmts.as_slice() {
            return is_arbitrary_expr(inner);
        }
    }
    false
}

pub(crate) fn is_string_literal_expr(expr: &syn::Expr) -> bool {
    matches!(
        expr,
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(_),
            ..
        })
    )
}

/// Extracts the first identifier from an expression (for type inference from binary ops).
///
/// For `x + 1`, returns `Some("x")`. For `1 + 2`, returns `None`.
pub(crate) fn extract_first_ident(expr: &syn::Expr) -> Option<String> {
    match expr {
        syn::Expr::Path(expr_path) => expr_path.path.get_ident().map(|i| i.to_string()),
        syn::Expr::Paren(paren) => extract_first_ident(&paren.expr),
        _ => None,
    }
}

/// Checks whether a Rust expression can be encoded as a ay condition.
///
/// Returns true for expressions the ay encoder can parse and translate:
/// literals, variable references, arithmetic/comparison/logical binary ops,
/// unary negation/not, casts, and parenthesized expressions. Returns false
/// for function calls, method calls, closures, and other opaque expressions
/// that the encoder cannot evaluate.
///
/// Used by `extract_local_variables` to decide whether to emit a let-binding
/// constraint `var == expr`. Fixes #1556.
pub(crate) fn is_encodable_expr(expr: &syn::Expr) -> bool {
    match expr {
        syn::Expr::Lit(_) => true,
        syn::Expr::Path(p) => {
            if is_builtin_nullary_constructor_path(&p.path) {
                return true;
            }
            // Simple variable references (e.g., `x`) are encodable.
            // Qualified paths (e.g., `std::i32::MAX`) are not — the encoder
            // doesn't resolve module paths.
            p.path.get_ident().is_some()
        }
        syn::Expr::Binary(b) => is_encodable_expr(&b.left) && is_encodable_expr(&b.right),
        syn::Expr::Unary(u) => {
            if matches!(u.op, syn::UnOp::Deref(_)) {
                false
            } else {
                is_encodable_expr(&u.expr)
            }
        }
        syn::Expr::Paren(p) => is_encodable_expr(&p.expr),
        syn::Expr::Cast(c) => is_encodable_expr(&c.expr),
        syn::Expr::Macro(m) => {
            // choose! macros are symbolically encodable — the encoder
            // generates Skolem function + axiom. Part of #2143.
            m.mac
                .path
                .segments
                .last()
                .is_some_and(|seg| seg.ident == "choose")
        }
        syn::Expr::Reference(r) => {
            // &str literals etc. — the variable is declared but the
            // expression itself isn't numeric/BV-encodable. Skip.
            let _ = r;
            false
        }
        syn::Expr::Call(call) => is_builtin_constructor_call(call),
        syn::Expr::MethodCall(method) => {
            is_supported_option_method_name(&method.method.to_string())
        }
        _ => false,
    }
}

fn is_builtin_constructor_call(call: &syn::ExprCall) -> bool {
    let syn::Expr::Path(func_path) = call.func.as_ref() else {
        return false;
    };
    let Some(last) = func_path.path.segments.last() else {
        return false;
    };
    matches!(last.ident.to_string().as_str(), "Some" | "Ok" | "Err")
        || option_inner_from_constructor_path(&func_path.path).is_some()
        || infer_type_from_result_constructor_path(&func_path.path).is_some()
}

fn is_builtin_nullary_constructor_path(path: &syn::Path) -> bool {
    path.segments
        .last()
        .is_some_and(|segment| segment.ident == "None")
        && (matches!(
            path.segments.last().map(|segment| &segment.arguments),
            Some(syn::PathArguments::AngleBracketed(_))
        ) || option_inner_from_constructor_path(path).is_some())
}

fn is_supported_option_method_name(method: &str) -> bool {
    matches!(
        method,
        "is_some"
            | "is_none"
            | "unwrap"
            | "expect"
            | "unwrap_or_default"
            | "unwrap_or_else"
            | "ok_or_else"
            | "and_then"
            | "cloned"
    )
}

/// Extract a type string from a syn::Type for ay variable declaration.
///
/// Returns the type as a string that `TrustVcType::from_str` can parse (e.g., "i32", "u64", "bool").
/// For unsupported types, falls back to "i32".
pub(crate) fn extract_type_string(ty: &syn::Type) -> String {
    match ty {
        syn::Type::Path(type_path) => {
            let path = &type_path.path;
            // Ghost<T>, Tracked<T>, Proph<T>, and Snapshot<T> erase to T at SMT level.
            if let Some(seg) = path.segments.last() {
                let name = seg.ident.to_string();
                if name == "Tracked" || name == "Ghost" || name == "Proph" || name == "Snapshot" {
                    if let syn::PathArguments::AngleBracketed(args) = &seg.arguments {
                        if let Some(syn::GenericArgument::Type(inner)) = args.args.first() {
                            return extract_type_string(inner);
                        }
                    }
                }
            }
            // Handle simple paths like `i32`, `u64`, `bool`, `Seq<i32>`, etc.
            quote!(#path).to_string().replace(' ', "")
        }
        syn::Type::Reference(type_ref) => {
            // For `&T` or `&mut T`, extract the inner type
            extract_type_string(&type_ref.elem)
        }
        _ => {
            // Unsupported type syntax — pass through stringified form so
            // TrustVcType::parse_or_opaque returns Opaque, caught by contains_opaque() guards
            quote!(#ty).to_string().replace(' ', "")
        }
    }
}
