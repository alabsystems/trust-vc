// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::{DefHash, Expr, ExprKind, FnId, LocalId, Place, SpanId, Ty};

pub(super) fn owner() -> FnId {
    FnId(DefHash::new(57, 1))
}

pub(super) fn choice(ty: Ty) -> Expr {
    let value = Expr::read(Place::local(LocalId(7)), ty.clone(), SpanId(0));
    let predicate = Expr::new(
        Ty::Bool,
        SpanId(0),
        ExprKind::Call {
            callee: owner(),
            type_args: vec![ty.clone()],
            args: vec![value.clone()],
        },
    );
    Expr::new(
        ty.clone(),
        SpanId(0),
        ExprKind::Choose {
            vars: vec![(LocalId(7), ty)],
            triggers: vec![vec![predicate.clone()]],
            cond: Box::new(predicate),
            result: Box::new(value),
        },
    )
}
