// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Added ownership passes share the original resolution work ceiling.
use super::*;

#[test]
fn owned_loop_state_cannot_refill_the_original_resolution_budget() {
    let mut f = function(Ty::Unit);
    for _ in 0..600 {
        add(&mut f, reference(scalar()), Mode::Exec, LocalKind::Param);
    }
    let mut body = Vec::new();
    for _ in 0..400 {
        body.push(stmt(StmtKind::Block(Block::default())));
    }
    body.push(leave(0, 13));
    f.body = Body::Stmts(Block::new(vec![isolated(0, body, vec![]), ret(None)]));
    require_refusal(krate(f), "resolution-size");
}
