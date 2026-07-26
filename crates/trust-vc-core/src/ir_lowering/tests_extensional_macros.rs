// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::{infer_expr_type, lower_syn_expr, trust_vc_type_from_syn_type, TypeEnv};
use crate::ir::{CollectionOp, CompareOp, QuantifierKind, TrustVcType};
use crate::ir_expr::TrustVcExpr;

fn env_with(vars: &[(&str, &str)]) -> TypeEnv {
    let mut env = TypeEnv::new();
    for (name, ty) in vars {
        let parsed_ty: syn::Type =
            syn::parse_str(ty).unwrap_or_else(|err| panic!("parse type `{ty}`: {err}"));
        let trust_vc_ty = trust_vc_type_from_syn_type(&parsed_ty)
            .unwrap_or_else(|err| panic!("convert type `{ty}`: {err:?}"));
        env.insert((*name).to_string(), trust_vc_ty);
    }
    env
}

#[test]
fn lower_ext_eq_macro_over_seq_builds_collection_formula() {
    let expr: syn::Expr = syn::parse_str("ext_eq!(lhs, rhs)").unwrap();
    let env = env_with(&[("lhs", "Seq<i32>"), ("rhs", "Seq<i32>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("ext_eq! over Seq should lower");

    assert_eq!(
        infer_expr_type(&lowered),
        TrustVcType::Bool,
        "ext_eq! must lower to a boolean formula"
    );
    assert!(
        lowered.references_collection(),
        "Seq ext_eq! should lower through collection operations, got {lowered:?}"
    );
}

#[test]
fn lower_ext_eq_macro_over_seq_add_operand_builds_collection_formula() {
    let expr: syn::Expr = syn::parse_str("ext_eq!(lhs, mid.add(rhs))").unwrap();
    let env = env_with(&[
        ("lhs", "Seq<i32>"),
        ("mid", "Seq<i32>"),
        ("rhs", "Seq<i32>"),
    ]);
    let lowered = lower_syn_expr(&expr, &env).expect("ext_eq! over Seq::add operand should lower");

    assert_eq!(
        infer_expr_type(&lowered),
        TrustVcType::Bool,
        "ext_eq! over concat should lower to a boolean formula"
    );
    assert!(
        lowered.references_collection(),
        "Seq concat ext_eq! should lower through collection operations, got {lowered:?}"
    );
}

#[test]
fn lower_ext_ne_macro_wraps_collection_formula_in_not() {
    let expr: syn::Expr = syn::parse_str("trust_vc::ext_ne!(lhs, rhs)").unwrap();
    let env = env_with(&[("lhs", "Set<u32>"), ("rhs", "Set<u32>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("ext_ne! over Set should lower");

    match lowered {
        TrustVcExpr::Not(inner) => {
            assert!(
                inner.references_collection(),
                "ext_ne! should negate a collection-aware ext_eq formula, got {inner:?}"
            );
        }
        other => panic!("expected Not(collection-formula), got {other:?}"),
    }
}

#[test]
fn lower_strict_eq_macro_over_map_builds_raw_equality_marker() {
    let expr: syn::Expr = syn::parse_str("strict_eq!(lhs, rhs)").unwrap();
    let env = env_with(&[("lhs", "Map<i32, bool>"), ("rhs", "Map<i32, bool>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("strict_eq! over Map should lower");

    match lowered {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, crate::extensional_eq::STRICT_EQ_FN);
            assert_eq!(args.len(), 2);
            assert_eq!(return_ty, TrustVcType::Bool);
            assert_eq!(infer_expr_type(&args[0]), infer_expr_type(&args[1]));
            assert_eq!(
                infer_expr_type(&args[0]),
                TrustVcType::Map(
                    Box::new(TrustVcType::Int { width: 32 }),
                    Box::new(TrustVcType::Bool)
                )
            );
        }
        other => panic!("expected strict equality marker FnCall, got {other:?}"),
    }
}

#[test]
fn lower_strict_eq_macro_over_set_mk_map_constant_folded_body_builds_true() {
    let expr: syn::Expr = syn::parse_str(
        "strict_eq!(
            s.mk_map(SpecFn::new(|x: i32| x + 4i32)),
            s.mk_map(SpecFn::new(|y: i32| y + (2i32 + 2i32)))
        )",
    )
    .unwrap();
    let env = env_with(&[("s", "Set<i32>")]);
    let lowered = lower_syn_expr(&expr, &env)
        .expect("strict_eq! over matching Set::mk_map functions should lower");

    assert_eq!(lowered, TrustVcExpr::BoolLit(true));
}

#[test]
fn lower_strict_eq_macro_over_set_mk_map_commuted_body_builds_false() {
    let expr: syn::Expr = syn::parse_str(
        "strict_eq!(
            s.mk_map(SpecFn::new(|x: i32| x + 4i32)),
            s.mk_map(SpecFn::new(|y: i32| (2i32 + 2i32) + y))
        )",
    )
    .unwrap();
    let env = env_with(&[("s", "Set<i32>")]);
    let lowered = lower_syn_expr(&expr, &env)
        .expect("strict_eq! over non-definitionally-identical Set::mk_map functions should lower");

    assert_eq!(lowered, TrustVcExpr::BoolLit(false));
}

#[test]
fn lower_equal_macro_alias_over_map_builds_raw_equality_marker() {
    let expr: syn::Expr = syn::parse_str("trust_vc::equal!(lhs, rhs)").unwrap();
    let env = env_with(&[("lhs", "Map<i32, bool>"), ("rhs", "Map<i32, bool>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("equal! over Map should lower");

    match lowered {
        TrustVcExpr::FnCall { name, args, .. } => {
            assert_eq!(name, crate::extensional_eq::STRICT_EQ_FN);
            assert_eq!(args.len(), 2);
        }
        other => panic!("expected strict equality marker FnCall, got {other:?}"),
    }
}

#[test]
fn lower_ext_eq_macro_over_multiset_builds_forall_count_formula() {
    let expr: syn::Expr = syn::parse_str("ext_eq!(lhs, rhs)").unwrap();
    let env = env_with(&[("lhs", "Multiset<i32>"), ("rhs", "Multiset<i32>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("ext_eq! over Multiset should lower");

    match lowered {
        TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            bound_vars,
            body,
            ..
        } => {
            assert_eq!(
                bound_vars,
                vec![(
                    "__trust_vc_ext_multiset_elem".to_string(),
                    TrustVcType::Int { width: 32 }
                )]
            );
            match *body {
                TrustVcExpr::Compare {
                    op: CompareOp::Eq,
                    left,
                    right,
                } => {
                    for side in [left, right] {
                        match *side {
                            TrustVcExpr::CollectionOp {
                                op: CollectionOp::Count,
                                ty,
                                ..
                            } => assert_eq!(ty, TrustVcType::Nat),
                            other => panic!("expected multiset count side, got {other:?}"),
                        }
                    }
                }
                other => panic!("expected count equality body, got {other:?}"),
            }
        }
        other => panic!("expected forall count equality, got {other:?}"),
    }
}

#[test]
fn lower_ext_eq_macro_over_spec_fn_closures_builds_forall_body_eq() {
    let expr: syn::Expr =
        syn::parse_str("ext_eq!(SpecFn::new(|i: i32| i + 1i32), SpecFn::new(|j: i32| 1i32 + j))")
            .unwrap();
    let env = env_with(&[]);
    let lowered = lower_syn_expr(&expr, &env).expect("ext_eq! over SpecFn closures should lower");

    match lowered {
        TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            bound_vars,
            body,
            ..
        } => {
            assert_eq!(
                bound_vars,
                vec![(
                    "__trust_vc_ext_spec_arg0".to_string(),
                    TrustVcType::Int { width: 32 }
                )]
            );
            assert!(matches!(*body, TrustVcExpr::Compare { .. }));
        }
        other => panic!("expected forall body equality for SpecFn ext_eq, got {other:?}"),
    }
}

#[test]
fn lower_ext_eq_macro_over_spec_fn_int_closures_builds_forall_math_int_body_eq() {
    let expr: syn::Expr =
        syn::parse_str("ext_eq!(SpecFn::new(|i: int| i + 1), SpecFn::new(|j: int| 1 + j))")
            .unwrap();
    let env = env_with(&[]);
    let lowered =
        lower_syn_expr(&expr, &env).expect("ext_eq! over SpecFn<int, int> closures should lower");

    match lowered {
        TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            bound_vars,
            body,
            ..
        } => {
            assert_eq!(
                bound_vars,
                vec![("__trust_vc_ext_spec_arg0".to_string(), TrustVcType::MathInt)]
            );
            match *body {
                TrustVcExpr::Compare { left, right, .. } => {
                    assert_eq!(infer_expr_type(&left), TrustVcType::MathInt);
                    assert_eq!(infer_expr_type(&right), TrustVcType::MathInt);
                }
                other => panic!("expected equality body for SpecFn<int, int>, got {other:?}"),
            }
        }
        other => panic!("expected forall body equality for SpecFn<int, int>, got {other:?}"),
    }
}

#[test]
fn lower_ext_eq_macro_over_spec_fn_vars_builds_forall_apply_formula() {
    let expr: syn::Expr = syn::parse_str("ext_eq!(f, g)").unwrap();
    let env = env_with(&[("f", "SpecFn<i32, i32>"), ("g", "SpecFn<i32, i32>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("ext_eq! over SpecFn vars should lower");

    match lowered {
        TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            bound_vars,
            body,
            ..
        } => {
            assert_eq!(
                bound_vars,
                vec![(
                    "__trust_vc_ext_spec_arg0".to_string(),
                    TrustVcType::Int { width: 32 }
                )]
            );
            match *body {
                TrustVcExpr::Compare {
                    op: CompareOp::Eq,
                    left,
                    right,
                } => {
                    let (
                        TrustVcExpr::FnCall {
                            name: left_name,
                            args: left_args,
                            ..
                        },
                        TrustVcExpr::FnCall {
                            name: right_name,
                            args: right_args,
                            ..
                        },
                    ) = (*left, *right)
                    else {
                        panic!("expected SpecFn application calls in extensional body");
                    };
                    assert_eq!(left_name, right_name);
                    assert_eq!(left_args.len(), 2);
                    assert_eq!(right_args.len(), 2);
                }
                other => panic!("expected equality over SpecFn application calls, got {other:?}"),
            }
        }
        other => panic!("expected forall application equality for SpecFn ext_eq, got {other:?}"),
    }
}

#[test]
fn lower_ext_eq_macro_over_spec_fn_nat_vars_builds_forall_nat_apply_formula() {
    let expr: syn::Expr = syn::parse_str("ext_eq!(f, g)").unwrap();
    let env = env_with(&[("f", "SpecFn<nat, nat>"), ("g", "SpecFn<nat, nat>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("ext_eq! over SpecFn<nat, nat> should lower");

    match lowered {
        TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            bound_vars,
            body,
            ..
        } => {
            assert_eq!(
                bound_vars,
                vec![("__trust_vc_ext_spec_arg0".to_string(), TrustVcType::Nat)]
            );
            match *body {
                TrustVcExpr::Compare {
                    op: CompareOp::Eq,
                    left,
                    right,
                } => {
                    let (
                        TrustVcExpr::FnCall {
                            name: left_name,
                            args: left_args,
                            ..
                        },
                        TrustVcExpr::FnCall {
                            name: right_name,
                            args: right_args,
                            ..
                        },
                    ) = (*left, *right)
                    else {
                        panic!("expected SpecFn application calls in nat extensional body");
                    };
                    assert_eq!(left_name, right_name);
                    assert_eq!(left_args.len(), 2);
                    assert_eq!(right_args.len(), 2);
                }
                other => {
                    panic!(
                        "expected equality over SpecFn<nat, nat> application calls, got {other:?}"
                    )
                }
            }
        }
        other => panic!("expected forall application equality for SpecFn<nat, nat>, got {other:?}"),
    }
}

#[test]
fn lower_ext_eq_macro_over_spec_fn_closures_with_calls_builds_forall_apply_formula() {
    let expr: syn::Expr = syn::parse_str(
        "ext_eq!(SpecFn::new(|n: i32| f.call((n + k2) + k1)), SpecFn::new(|n: i32| f.call(n + (k1 + k2))))",
    )
    .unwrap();
    let env = env_with(&[("f", "SpecFn<i32, i32>"), ("k1", "i32"), ("k2", "i32")]);
    let lowered = lower_syn_expr(&expr, &env)
        .expect("ext_eq! over SpecFn closures that call a SpecFn should lower");

    match lowered {
        TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            body,
            ..
        } => match *body {
            TrustVcExpr::Compare {
                op: CompareOp::Eq,
                left,
                right,
            } => {
                let (
                    TrustVcExpr::FnCall {
                        args: left_args, ..
                    },
                    TrustVcExpr::FnCall {
                        args: right_args, ..
                    },
                ) = (*left, *right)
                else {
                    panic!("expected SpecFn application calls in extensional body");
                };
                assert_eq!(left_args.len(), 2);
                assert_eq!(right_args.len(), 2);
                assert_eq!(
                    left_args[1], right_args[1],
                    "arithmetic-equivalent SpecFn::call arguments should be canonicalized"
                );
            }
            other => panic!("expected equality over SpecFn application calls, got {other:?}"),
        },
        other => panic!("expected forall application equality for SpecFn ext_eq, got {other:?}"),
    }
}

#[test]
fn lower_ext_eq_macro_over_spec_fn_int_closures_with_nat_offsets_canonicalizes_apply_args() {
    let expr: syn::Expr = syn::parse_str(
        "ext_eq!(SpecFn::new(|n: int| f.call((n + (k2 as int)) + (k1 as int))), SpecFn::new(|n: int| f.call(n + ((k1 as int) + (k2 as int)))))",
    )
    .unwrap();
    let env = env_with(&[("f", "SpecFn<int, int>"), ("k1", "nat"), ("k2", "nat")]);
    let lowered = lower_syn_expr(&expr, &env)
        .expect("ext_eq! over SpecFn<int, int> closures with nat offsets should lower");

    match lowered {
        TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            bound_vars,
            body,
            ..
        } => {
            assert_eq!(
                bound_vars,
                vec![("__trust_vc_ext_spec_arg0".to_string(), TrustVcType::MathInt)]
            );
            match *body {
                TrustVcExpr::Compare {
                    op: CompareOp::Eq,
                    left,
                    right,
                } => {
                    let (
                        TrustVcExpr::FnCall {
                            args: left_args, ..
                        },
                        TrustVcExpr::FnCall {
                            args: right_args, ..
                        },
                    ) = (*left, *right)
                    else {
                        panic!("expected SpecFn<int, int> application calls in extensional body");
                    };
                    assert_eq!(left_args.len(), 2);
                    assert_eq!(right_args.len(), 2);
                    assert_eq!(
                        left_args[1], right_args[1],
                        "nat-offset SpecFn::call arguments should canonicalize in MathInt mode"
                    );
                }
                other => panic!(
                    "expected equality over SpecFn<int, int> application calls, got {other:?}"
                ),
            }
        }
        other => panic!(
            "expected forall application equality for SpecFn<int, int> nat offsets, got {other:?}"
        ),
    }
}

#[test]
fn lower_ext_eq_macro_over_spec_fn_int_closures_with_generic_return() {
    let expr: syn::Expr = syn::parse_str(
        "ext_eq!(SpecFn::new(|n: int| f.call((n + (k2 as int)) + (k1 as int))), SpecFn::new(|n: int| f.call(n + ((k1 as int) + (k2 as int)))))",
    )
    .unwrap();
    let env = env_with(&[("f", "SpecFn<int, A>"), ("k1", "nat"), ("k2", "nat")]);
    let lowered =
        lower_syn_expr(&expr, &env).expect("ext_eq! over SpecFn<int, A> closures should lower");

    match lowered {
        TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            bound_vars,
            body,
            ..
        } => {
            assert_eq!(
                bound_vars,
                vec![("__trust_vc_ext_spec_arg0".to_string(), TrustVcType::MathInt)]
            );
            match *body {
                TrustVcExpr::Compare {
                    op: CompareOp::Eq,
                    left,
                    right,
                } => {
                    let (
                        TrustVcExpr::FnCall {
                            args: left_args,
                            return_ty: left_return_ty,
                            ..
                        },
                        TrustVcExpr::FnCall {
                            args: right_args,
                            return_ty: right_return_ty,
                            ..
                        },
                    ) = (*left, *right)
                    else {
                        panic!("expected SpecFn<int, A> application calls in extensional body");
                    };
                    assert_eq!(left_return_ty, TrustVcType::TypeParam("A".to_string()));
                    assert_eq!(right_return_ty, TrustVcType::TypeParam("A".to_string()));
                    assert_eq!(left_args.len(), 2);
                    assert_eq!(right_args.len(), 2);
                    assert_eq!(
                        left_args[1], right_args[1],
                        "generic-return SpecFn::call arguments should canonicalize in MathInt mode"
                    );
                }
                other => {
                    panic!("expected equality over SpecFn<int, A> application calls, got {other:?}")
                }
            }
        }
        other => {
            panic!("expected forall application equality for SpecFn<int, A>, got {other:?}")
        }
    }
}

#[test]
fn lower_ext_ne_macro_over_multiset_wraps_count_formula_in_not() {
    let expr: syn::Expr = syn::parse_str("ext_ne!(lhs, rhs)").unwrap();
    let env = env_with(&[("lhs", "Multiset<i32>"), ("rhs", "Multiset<i32>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("ext_ne! over Multiset should lower");

    match lowered {
        TrustVcExpr::Not(inner) => match *inner {
            TrustVcExpr::Quantifier {
                kind: QuantifierKind::Forall,
                ..
            } => {}
            other => panic!("expected negated forall count formula, got {other:?}"),
        },
        other => panic!("expected Not(forall count formula), got {other:?}"),
    }
}

#[cfg(feature = "native-strings")]
#[test]
fn lower_ext_eq_macro_over_string_builds_collection_formula() {
    let expr: syn::Expr = syn::parse_str("ext_eq!(lhs, rhs)").unwrap();
    let env = env_with(&[("lhs", "String"), ("rhs", "String")]);
    let lowered = lower_syn_expr(&expr, &env).expect("string ext_eq! should lower");
    assert!(
        lowered.references_collection(),
        "string ext_eq! should lower through the Seq<char> bridge, got {lowered:?}"
    );
}
