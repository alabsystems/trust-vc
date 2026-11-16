// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::helpers::*;
use super::*;

#[test]
fn known_owned_nominal_layout_keeps_the_original_depth_refusal() {
    let mut source = nonowned_dag(70);
    source.adts[0].variants[0].fields[0].ty = Ty::MutRef(Box::new(scalar()));
    // A single child per level reaches the actual depth limit cheaply;
    // classification must not turn this owned inventory into nonowned.
    for adt in source.adts.iter_mut().skip(1) {
        adt.variants[0].fields.truncate(1);
    }
    let generated = generate(&source);
    let Some(FnVcs::Refused(problem)) = generated.get(source.fns[0].id) else {
        panic!("a deep owned layout must remain refused: {generated:?}");
    };
    assert_eq!(problem.tag, "resolution-type");
    assert_eq!(problem.detail, "owned-place layout exceeds depth bound");
}

#[test]
fn a_nonowned_nominal_value_can_move_twice_and_return() {
    let mut inventory = nonowned_dag(5);
    let ty = Ty::Adt(adt(5), vec![]);
    let mut f = function(1002, ty.clone());
    let input = add(&mut f, ty.clone(), Mode::Exec, LocalKind::Param);
    let first = add(&mut f, ty.clone(), Mode::Exec, LocalKind::Let);
    let second = add(&mut f, ty.clone(), Mode::Exec, LocalKind::Let);
    f.body = Body::Stmts(Block::new(vec![
        stmt(StmtKind::Let {
            local: first,
            init: Some(read(input, ty.clone())),
        }),
        stmt(StmtKind::Let {
            local: second,
            init: Some(read(first, ty.clone())),
        }),
        ret(Some(read(second, ty))),
    ]));
    inventory.fns = vec![f];
    let generated = generate(&inventory);
    assert!(
        matches!(generated.get(inventory.fns[0].id), Some(FnVcs::Checks(checks)) if checks.is_empty()),
        "nonowned value transfers need no affine layout: {generated:?}"
    );
}
