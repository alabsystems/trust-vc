//! Place lowering: lowers `syn::Expr` AST into `TrustVcPlace` IR.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Provides `lower_syn_place()` which walks a `syn::Expr` tree that represents
//! a memory place (`x`, `x.field`, `x[i]`, `x.field[i]`) and produces a
//! `TrustVcPlace`. Reuses `TypeEnv::lookup_field` for field type metadata and
//! collection element type extraction for index projections.
//!
//! Originally part of #2515 (place-based reasoning).

use super::{lower_syn_expr_with_depth, LoweringError, TypeEnv};
use crate::ir::TrustVcType;
use crate::ir_place::TrustVcPlace;

/// Lowers a `syn::Expr` that represents a memory place into a `TrustVcPlace`.
///
/// Supported surface:
/// - `x` — root variable
/// - `*x` — deref (transparent, treated as root)
/// - `x.field` — single field projection
/// - `x.inner.field` — nested field projection
/// - `x[i]` — index projection (Seq/Map/array receivers only)
/// - `x.field[i]` — field then index projection
#[cfg_attr(not(test), allow(dead_code))] // HEAD callers are test-only today.
pub(crate) fn lower_syn_place(
    expr: &syn::Expr,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcPlace, LoweringError> {
    match expr {
        // Root: simple variable path `x`
        syn::Expr::Path(path) if path.path.segments.len() == 1 => {
            let name = path
                .path
                .segments
                .first()
                .map(|segment| segment.ident.to_string())
                .ok_or_else(|| {
                    LoweringError::UnsupportedExpr("path expression missing root segment".into())
                })?;
            let ty = env
                .lookup(&name)
                .cloned()
                .ok_or_else(|| LoweringError::UnresolvedVar(name.clone()))?;
            Ok(TrustVcPlace::root(name, ty))
        }

        // Deref: `*x` — transparent for place purposes
        syn::Expr::Unary(un) if matches!(un.op, syn::UnOp::Deref(_)) => {
            lower_syn_place(&un.expr, env, depth)
        }

        // Field access: `base.field`
        syn::Expr::Field(field) => {
            let base_place = lower_syn_place(&field.base, env, depth)?;
            let base_ty_name = base_place.place_ty.to_type_string();
            let field_name = match &field.member {
                syn::Member::Named(ident) => ident.to_string(),
                syn::Member::Unnamed(index) => index.index.to_string(),
            };
            let meta = env
                .lookup_field(&base_ty_name, &field_name)
                .ok_or_else(|| {
                    LoweringError::UnsupportedExpr(format!(
                        "place field '{}' on type '{}'",
                        field_name, base_ty_name
                    ))
                })?;
            let field_ty = meta.field_type.clone();
            Ok(base_place.field(field_name, field_ty))
        }

        // Index: `base[index]`
        syn::Expr::Index(idx) => {
            let base_place = lower_syn_place(&idx.expr, env, depth)?;
            let index_expr = lower_syn_expr_with_depth(&idx.index, env, depth)?;
            let elem_ty = match &base_place.place_ty {
                TrustVcType::Seq(elem) | TrustVcType::Array(elem, _) => *elem.clone(),
                TrustVcType::Map(_, val) => *val.clone(),
                other => {
                    return Err(LoweringError::TypeInference(format!(
                        "place indexing requires Seq/Map/array receiver, got '{}'",
                        other.to_type_string()
                    )));
                }
            };
            Ok(base_place.index(index_expr, elem_ty))
        }

        // Paren: `(expr)` — transparent
        syn::Expr::Paren(p) => lower_syn_place(&p.expr, env, depth),

        // Reference: `&expr` — transparent for place purposes
        syn::Expr::Reference(r) => lower_syn_place(&r.expr, env, depth),

        _ => Err(LoweringError::UnsupportedExpr(format!(
            "unsupported place expression: {}",
            quote::quote!(#expr)
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{DatatypeVariant, TrustVcType};
    use crate::ir_place::PlaceProjection;

    fn i32_ty() -> TrustVcType {
        TrustVcType::Int { width: 32 }
    }

    fn seq_i32() -> TrustVcType {
        TrustVcType::Seq(Box::new(i32_ty()))
    }

    fn struct_ty(name: &str, fields: Vec<(&str, TrustVcType)>) -> TrustVcType {
        TrustVcType::Datatype {
            name: name.to_string(),
            variants: vec![DatatypeVariant {
                name: name.to_string(),
                fields: fields
                    .into_iter()
                    .map(|(n, ty)| (n.to_string(), ty))
                    .collect(),
            }],
        }
    }

    fn env_with_var(name: &str, ty: TrustVcType) -> TypeEnv {
        let mut env = TypeEnv::new();
        env.insert(name.to_string(), ty);
        env
    }

    fn parse_expr(s: &str) -> syn::Expr {
        syn::parse_str(s).unwrap()
    }

    #[test]
    fn test_lower_root_variable() {
        let env = env_with_var("x", i32_ty());
        let place = lower_syn_place(&parse_expr("x"), &env, 0).unwrap();
        assert_eq!(place.root_name, "x");
        assert!(place.is_root());
        assert_eq!(place.place_ty, i32_ty());
    }

    #[test]
    fn test_lower_deref_root() {
        let env = env_with_var("x", i32_ty());
        let place = lower_syn_place(&parse_expr("*x"), &env, 0).unwrap();
        assert_eq!(place.root_name, "x");
        assert!(place.is_root());
    }

    #[test]
    fn test_lower_field_access() {
        let ty = struct_ty("Counter", vec![("count", i32_ty())]);
        let env = env_with_var("c", ty);
        let place = lower_syn_place(&parse_expr("c.count"), &env, 0).unwrap();
        assert_eq!(place.root_name, "c");
        assert_eq!(place.projections.len(), 1);
        assert!(matches!(
            &place.projections[0],
            PlaceProjection::Field { field_name, .. } if field_name == "count"
        ));
        assert_eq!(place.place_ty, i32_ty());
    }

    #[test]
    fn test_lower_nested_field() {
        let inner_ty = struct_ty("Inner", vec![("value", i32_ty())]);
        let outer_ty = struct_ty("Outer", vec![("inner", inner_ty.clone())]);
        let mut env = env_with_var("o", outer_ty);
        // Register Inner's field metadata explicitly (register_type_metadata
        // handles this for Outer, but Inner needs explicit insert for its fields)
        env.insert("__inner_probe".to_string(), inner_ty);

        let place = lower_syn_place(&parse_expr("o.inner.value"), &env, 0).unwrap();
        assert_eq!(place.root_name, "o");
        assert_eq!(place.projections.len(), 2);
        assert_eq!(place.place_ty, i32_ty());
    }

    #[test]
    fn test_lower_index_seq() {
        let env = env_with_var("s", seq_i32());
        // We also need `i` in the env for the index expression
        let mut env = env;
        env.insert("i".to_string(), i32_ty());

        let place = lower_syn_place(&parse_expr("s[i]"), &env, 0).unwrap();
        assert_eq!(place.root_name, "s");
        assert_eq!(place.projections.len(), 1);
        assert!(matches!(
            &place.projections[0],
            PlaceProjection::Index { elem_ty, .. } if *elem_ty == i32_ty()
        ));
        assert_eq!(place.place_ty, i32_ty());
    }

    #[test]
    fn test_lower_field_then_index() {
        let ty = struct_ty("State", vec![("entries", seq_i32())]);
        let mut env = env_with_var("st", ty);
        env.insert("i".to_string(), i32_ty());

        let place = lower_syn_place(&parse_expr("st.entries[i]"), &env, 0).unwrap();
        assert_eq!(place.root_name, "st");
        assert_eq!(place.projections.len(), 2);
        assert!(matches!(
            &place.projections[0],
            PlaceProjection::Field { field_name, .. } if field_name == "entries"
        ));
        assert!(matches!(
            &place.projections[1],
            PlaceProjection::Index { .. }
        ));
        assert_eq!(place.place_ty, i32_ty());
    }

    #[test]
    fn test_lower_unresolved_root() {
        let env = TypeEnv::new();
        let result = lower_syn_place(&parse_expr("unknown"), &env, 0);
        assert!(matches!(result, Err(LoweringError::UnresolvedVar(_))));
    }

    #[test]
    fn test_lower_unsupported_index_type() {
        let mut env = env_with_var("x", i32_ty());
        env.insert("i".to_string(), i32_ty());

        let result = lower_syn_place(&parse_expr("x[i]"), &env, 0);
        assert!(matches!(result, Err(LoweringError::TypeInference(_))));
    }

    #[test]
    fn test_lower_reference_transparent() {
        let env = env_with_var("x", i32_ty());
        let place = lower_syn_place(&parse_expr("& x"), &env, 0).unwrap();
        assert_eq!(place.root_name, "x");
        assert!(place.is_root());
    }

    #[test]
    fn test_lower_tuple_field() {
        let ty = struct_ty("Pair", vec![("0", i32_ty()), ("1", i32_ty())]);
        let env = env_with_var("p", ty);

        let place = lower_syn_place(&parse_expr("p.0"), &env, 0).unwrap();
        assert_eq!(place.root_name, "p");
        assert!(matches!(
            &place.projections[0],
            PlaceProjection::Field { field_name, .. } if field_name == "0"
        ));
    }
}
