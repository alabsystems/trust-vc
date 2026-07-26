//! CollectionOp and Index receiver_name rename tests (soundness-critical).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from rewrite_variant_coverage/mod.rs (#2145).

use super::*;

// ---- CollectionOp receiver_name (SOUNDNESS-CRITICAL) ----

/// SOUNDNESS-CRITICAL: CollectionOp receiver_name must be renamed during
/// pre-state substitution. If missed, inductive step verification would
/// use a post-state collection where it should use the pre-state one,
/// producing a false proof.
#[test]
fn test_typed_rename_collection_op_receiver_name() {
    let expr = TrustVcExpr::CollectionOp {
        op: CollectionOp::Push,
        receiver: Box::new(TrustVcExpr::Var {
            name: "s".to_string(),
            ty: seq_i32_ty(),
        }),
        receiver_name: Some("s".to_string()),
        args: vec![var("x")],
        ty: seq_i32_ty(),
    };
    let vars = make_vars(&["s", "x"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::CollectionOp {
        receiver,
        receiver_name,
        args,
        ..
    } = &result
    {
        assert_eq!(
            **receiver,
            TrustVcExpr::Var {
                name: "s__trust_vc_pre".to_string(),
                ty: seq_i32_ty(),
            },
            "CollectionOp receiver Var must be renamed"
        );
        assert_eq!(
            receiver_name.as_deref(),
            Some("s__trust_vc_pre"),
            "CollectionOp receiver_name must be renamed for pre-state substitution"
        );
        assert_eq!(
            args[0],
            TrustVcExpr::Var {
                name: "x__trust_vc_pre".to_string(),
                ty: i32_ty(),
            }
        );
    } else {
        panic!("expected CollectionOp");
    }
}

/// Negative companion: CollectionOp receiver_name that is NOT a target
/// variable must NOT be renamed.
#[test]
fn test_typed_rename_collection_op_receiver_name_non_target() {
    let expr = TrustVcExpr::CollectionOp {
        op: CollectionOp::Len,
        receiver: Box::new(TrustVcExpr::Var {
            name: "s".to_string(),
            ty: seq_i32_ty(),
        }),
        receiver_name: Some("s".to_string()),
        args: vec![],
        ty: i32_ty(),
    };
    let vars = make_vars(&["x", "y"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::CollectionOp { receiver_name, .. } = &result {
        assert_eq!(
            receiver_name.as_deref(),
            Some("s"),
            "non-target receiver_name must NOT be renamed"
        );
    } else {
        panic!("expected CollectionOp");
    }
}

/// SOUNDNESS-CRITICAL: CollectionOp receiver_name must respect shadowing.
#[test]
fn test_typed_rename_collection_op_receiver_name_shadowed() {
    let inner = TrustVcExpr::CollectionOp {
        op: CollectionOp::Len,
        receiver: Box::new(TrustVcExpr::Var {
            name: "s".to_string(),
            ty: seq_i32_ty(),
        }),
        receiver_name: Some("s".to_string()),
        args: vec![],
        ty: i32_ty(),
    };
    let expr = TrustVcExpr::Let {
        name: "s".to_string(),
        ty: seq_i32_ty(),
        value: Box::new(TrustVcExpr::Var {
            name: "other".to_string(),
            ty: seq_i32_ty(),
        }),
        body: Box::new(inner),
    };
    let vars = make_vars(&["s"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Let { body, .. } = &result {
        if let TrustVcExpr::CollectionOp { receiver_name, .. } = body.as_ref() {
            assert_eq!(
                receiver_name.as_deref(),
                Some("s"),
                "let-shadowed receiver_name must NOT be renamed"
            );
        } else {
            panic!("expected CollectionOp in let body");
        }
    } else {
        panic!("expected Let");
    }
}

/// CollectionOp with None receiver_name: should not panic.
#[test]
fn test_typed_rename_collection_op_no_receiver_name() {
    let expr = TrustVcExpr::CollectionOp {
        op: CollectionOp::Len,
        receiver: Box::new(var("s")),
        receiver_name: None,
        args: vec![],
        ty: i32_ty(),
    };
    let vars = make_vars(&["s"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::CollectionOp {
        receiver,
        receiver_name,
        ..
    } = &result
    {
        assert_eq!(
            **receiver,
            TrustVcExpr::Var {
                name: "s__trust_vc_pre".to_string(),
                ty: i32_ty(),
            }
        );
        assert_eq!(*receiver_name, None, "None receiver_name stays None");
    } else {
        panic!("expected CollectionOp");
    }
}

// ---- Index receiver_name (SOUNDNESS-CRITICAL) ----

/// SOUNDNESS-CRITICAL: Index receiver_name must be renamed during pre-state
/// substitution, same concern as CollectionOp.
#[test]
fn test_typed_rename_index_receiver_name() {
    let expr = TrustVcExpr::Index {
        receiver: Box::new(TrustVcExpr::Var {
            name: "s".to_string(),
            ty: seq_i32_ty(),
        }),
        index: Box::new(var("i")),
        receiver_name: Some("s".to_string()),
        elem_ty: i32_ty(),
    };
    let vars = vec![
        VariableDecl {
            bounded_len: false,
            name: "s".to_string(),
            ty: seq_i32_ty(),
        },
        VariableDecl {
            bounded_len: false,
            name: "i".to_string(),
            ty: i32_ty(),
        },
    ];
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Index {
        receiver,
        index,
        receiver_name,
        ..
    } = &result
    {
        assert_eq!(
            **receiver,
            TrustVcExpr::Var {
                name: "s__trust_vc_pre".to_string(),
                ty: seq_i32_ty(),
            },
            "Index receiver Var must be renamed"
        );
        assert_eq!(
            receiver_name.as_deref(),
            Some("s__trust_vc_pre"),
            "Index receiver_name must be renamed for pre-state substitution"
        );
        assert_eq!(
            **index,
            TrustVcExpr::Var {
                name: "i__trust_vc_pre".to_string(),
                ty: i32_ty(),
            }
        );
    } else {
        panic!("expected Index");
    }
}

/// Index receiver_name respects shadowing.
#[test]
fn test_typed_rename_index_receiver_name_shadowed() {
    let inner = TrustVcExpr::Index {
        receiver: Box::new(TrustVcExpr::Var {
            name: "s".to_string(),
            ty: seq_i32_ty(),
        }),
        index: Box::new(var("i")),
        receiver_name: Some("s".to_string()),
        elem_ty: i32_ty(),
    };
    let expr = TrustVcExpr::Let {
        name: "s".to_string(),
        ty: seq_i32_ty(),
        value: Box::new(TrustVcExpr::Var {
            name: "other".to_string(),
            ty: seq_i32_ty(),
        }),
        body: Box::new(inner),
    };
    let vars = vec![VariableDecl {
        bounded_len: false,
        name: "s".to_string(),
        ty: seq_i32_ty(),
    }];
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Let { body, .. } = &result {
        if let TrustVcExpr::Index { receiver_name, .. } = body.as_ref() {
            assert_eq!(
                receiver_name.as_deref(),
                Some("s"),
                "let-shadowed Index receiver_name must NOT be renamed"
            );
        } else {
            panic!("expected Index in let body");
        }
    } else {
        panic!("expected Let");
    }
}

/// Index with None receiver_name.
#[test]
fn test_typed_rename_index_no_receiver_name() {
    let expr = TrustVcExpr::Index {
        receiver: Box::new(var("s")),
        index: Box::new(var("i")),
        receiver_name: None,
        elem_ty: i32_ty(),
    };
    let vars = make_vars(&["s", "i"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Index {
        receiver,
        index,
        receiver_name,
        ..
    } = &result
    {
        assert_eq!(
            **receiver,
            TrustVcExpr::Var {
                name: "s__trust_vc_pre".to_string(),
                ty: i32_ty(),
            }
        );
        assert_eq!(
            **index,
            TrustVcExpr::Var {
                name: "i__trust_vc_pre".to_string(),
                ty: i32_ty(),
            }
        );
        assert_eq!(*receiver_name, None);
    } else {
        panic!("expected Index");
    }
}
