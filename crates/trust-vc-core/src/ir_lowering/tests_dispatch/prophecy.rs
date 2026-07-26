// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Prophecy variable lowering tests.

use crate::ir::TrustVcType;
use crate::ir_expr::*;
use crate::ir_lowering::*;

#[test]
fn lower_proph_new_returns_prophecy_ir() {
    let expr: syn::Expr = syn::parse_str("Proph::<u64>::new()").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).expect("Proph::new should lower");
    assert_eq!(
        result,
        TrustVcExpr::ProphecyNew {
            name: "__trust_vc_prophecy_unbound__".to_string(),
            ty: TrustVcType::Uint { width: 64 },
        }
    );
}

#[test]
fn lower_proph_view_uses_registered_prophecy_name() {
    let expr: syn::Expr = syn::parse_str("p.view()").unwrap();
    let mut env = TypeEnv::new();
    env.insert("p".to_string(), TrustVcType::Uint { width: 64 });
    env.insert_prophecy_binding("p".to_string(), TrustVcType::Uint { width: 64 });

    let result = lower_syn_expr(&expr, &env).expect("Proph::view should lower");
    assert_eq!(
        result,
        TrustVcExpr::ProphecyNew {
            name: "p".to_string(),
            ty: TrustVcType::Uint { width: 64 },
        }
    );
}

#[test]
fn lower_proph_resolve_uses_registered_prophecy_name() {
    let expr: syn::Expr = syn::parse_str("p.resolve(7u64)").unwrap();
    let mut env = TypeEnv::new();
    env.insert("p".to_string(), TrustVcType::Uint { width: 64 });
    env.insert_prophecy_binding("p".to_string(), TrustVcType::Uint { width: 64 });

    let result = lower_syn_expr(&expr, &env).expect("Proph::resolve should lower");
    match result {
        TrustVcExpr::ProphecyResolve { name, value } => {
            assert_eq!(name, "p");
            assert_eq!(
                *value,
                TrustVcExpr::IntLit {
                    value: 7,
                    ty: TrustVcType::Uint { width: 64 }
                }
            );
        }
        other => panic!("expected ProphecyResolve, got {other:?}"),
    }
}

#[test]
fn lower_block_registers_prophecy_binding_for_view_and_resolve() {
    let expr: syn::Expr =
        syn::parse_str("{ let p = Proph::<u64>::new(); let v = p.view(); p.resolve(v) }").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).expect("prophecy block should lower");

    match result {
        TrustVcExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "p");
            assert!(matches!(*value, TrustVcExpr::ProphecyNew { .. }));
            match *body {
                TrustVcExpr::Let {
                    name, value, body, ..
                } => {
                    assert_eq!(name, "v");
                    assert!(matches!(
                        *value,
                        TrustVcExpr::ProphecyNew { name, .. } if name == "p"
                    ));
                    assert!(matches!(
                        *body,
                        TrustVcExpr::ProphecyResolve { name, .. } if name == "p"
                    ));
                }
                other => panic!("expected nested let for prophecy view, got {other:?}"),
            }
        }
        other => panic!("expected let-wrapped prophecy lowering, got {other:?}"),
    }
}
