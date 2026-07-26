// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::substitution::substitute_vars_in_expr;
use crate::ir::{TrustVcExpr, TrustVcType};

#[test]
fn test_substitute_vars_read_place_root_name() {
    use crate::ir_place::TrustVcPlace;

    let place = TrustVcPlace::root("x", TrustVcType::Int { width: 32 })
        .field("count", TrustVcType::Int { width: 32 });
    let expr = TrustVcExpr::ReadPlace {
        place,
        ty: TrustVcType::Int { width: 32 },
    };
    let replacement = TrustVcExpr::Var {
        name: "y".to_string(),
        ty: TrustVcType::Int { width: 32 },
    };
    let subst = std::collections::HashMap::from([("x", &replacement)]);
    let result = substitute_vars_in_expr(&expr, &subst);
    if let TrustVcExpr::ReadPlace { place, .. } = &result {
        assert_eq!(
            place.root_name, "y",
            "ReadPlace root_name 'x' should be substituted to 'y'"
        );
    } else {
        panic!("expected ReadPlace, got {:?}", result);
    }
}

#[test]
fn test_substitute_vars_read_place_root_not_in_subst() {
    use crate::ir_place::TrustVcPlace;

    let place = TrustVcPlace::root("c", TrustVcType::Int { width: 32 })
        .field("count", TrustVcType::Int { width: 32 });
    let expr = TrustVcExpr::ReadPlace {
        place,
        ty: TrustVcType::Int { width: 32 },
    };
    let replacement = TrustVcExpr::Var {
        name: "y".to_string(),
        ty: TrustVcType::Int { width: 32 },
    };
    let subst = std::collections::HashMap::from([("x", &replacement)]);
    let result = substitute_vars_in_expr(&expr, &subst);
    if let TrustVcExpr::ReadPlace { place, .. } = &result {
        assert_eq!(
            place.root_name, "c",
            "root_name not in subst should stay unchanged"
        );
    } else {
        panic!("expected ReadPlace, got {:?}", result);
    }
}

#[test]
fn test_substitute_vars_place_disjoint_root_names() {
    use crate::ir_place::TrustVcPlace;

    let left = TrustVcPlace::root("a", TrustVcType::Int { width: 32 });
    let right = TrustVcPlace::root("b", TrustVcType::Int { width: 32 });
    let expr = TrustVcExpr::PlaceDisjoint { left, right };
    let repl_a = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::Int { width: 32 },
    };
    let repl_b = TrustVcExpr::Var {
        name: "y".to_string(),
        ty: TrustVcType::Int { width: 32 },
    };
    let subst = std::collections::HashMap::from([("a", &repl_a), ("b", &repl_b)]);
    let result = substitute_vars_in_expr(&expr, &subst);
    if let TrustVcExpr::PlaceDisjoint { left, right } = &result {
        assert_eq!(left.root_name, "x");
        assert_eq!(right.root_name, "y");
    } else {
        panic!("expected PlaceDisjoint, got {:?}", result);
    }
}

#[test]
fn test_substitute_vars_read_place_non_var_replacement_preserves_root() {
    use crate::ir_place::TrustVcPlace;

    let place = TrustVcPlace::root("x", TrustVcType::Int { width: 32 });
    let expr = TrustVcExpr::ReadPlace {
        place,
        ty: TrustVcType::Int { width: 32 },
    };
    let replacement = TrustVcExpr::IntLit {
        value: 42,
        ty: TrustVcType::Int { width: 32 },
    };
    let subst = std::collections::HashMap::from([("x", &replacement)]);
    let result = substitute_vars_in_expr(&expr, &subst);
    if let TrustVcExpr::ReadPlace { place, .. } = &result {
        assert_eq!(
            place.root_name, "x",
            "non-Var replacement should not change root_name"
        );
    } else {
        panic!("expected ReadPlace, got {:?}", result);
    }
}
