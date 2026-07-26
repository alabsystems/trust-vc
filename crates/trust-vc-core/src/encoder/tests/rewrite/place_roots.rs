// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ---- Typed rewrite: Place root_name handling (#2533) ----

#[test]
fn test_typed_rename_read_place_root_name() {
    use crate::ir_place::TrustVcPlace;
    let vars = make_vars(&["c"]);
    let place = TrustVcPlace::root("c", i32_ty()).field("count", i32_ty());
    let expr = TrustVcExpr::ReadPlace {
        place,
        ty: i32_ty(),
    };
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::ReadPlace { place, .. } = &result {
        assert_eq!(
            place.root_name, "c__trust_vc_pre",
            "ReadPlace root_name must be renamed"
        );
    } else {
        panic!("expected ReadPlace");
    }
}

#[test]
fn test_typed_rename_read_place_root_not_in_targets() {
    use crate::ir_place::TrustVcPlace;
    let vars = make_vars(&["x"]);
    let place = TrustVcPlace::root("c", i32_ty()).field("count", i32_ty());
    let expr = TrustVcExpr::ReadPlace {
        place,
        ty: i32_ty(),
    };
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::ReadPlace { place, .. } = &result {
        assert_eq!(
            place.root_name, "c",
            "root_name not in targets should stay unchanged"
        );
    } else {
        panic!("expected ReadPlace");
    }
}

#[test]
fn test_typed_rename_place_disjoint_root_names() {
    use crate::ir_place::TrustVcPlace;
    let vars = make_vars(&["a", "b"]);
    let left = TrustVcPlace::root("a", i32_ty());
    let right = TrustVcPlace::root("b", i32_ty());
    let expr = TrustVcExpr::PlaceDisjoint { left, right };
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::PlaceDisjoint { left, right } = &result {
        assert_eq!(left.root_name, "a__trust_vc_pre");
        assert_eq!(right.root_name, "b__trust_vc_pre");
    } else {
        panic!("expected PlaceDisjoint");
    }
}
