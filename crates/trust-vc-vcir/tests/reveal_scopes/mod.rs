//! Fuel scope regressions using the shared VcIR builders and AY solver.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

fn opaque_one() -> FnDecl {
    let mut one = Fb::new(1, "one", Mode::Spec, Ty::int());
    one.decl.attrs.opaque = true;
    let value = one.lit(1, Ty::int());
    one.spec_body(value)
}

/// The reader lowers an assert-by proof to an arbitrary branch ending
/// unreachable, followed by the proven proposition as an assumption.
/// Learning `one() > 0` this way must not expose the stronger definition.
#[test]
fn assert_by_reveal_does_not_escape_its_proof() {
    let build = |claim_definition: bool| {
        let mut t = Fb::new(2, "t", Mode::Proof, Ty::Unit);
        let choice = t.let_local("proof_choice", Ty::Bool);
        let arbitrary = t.let_stmt(choice, None);
        let reveal = t.stmt(StmtKind::Reveal {
            callee: fn_id(1),
            fuel: None,
        });
        let call = t.call(fn_id(1), vec![], Ty::int());
        let zero = t.lit(0, Ty::int());
        let positive = t.cmp(BinOp::Gt, call, zero);
        let proof_check = t.assert(positive.clone());
        let dead_end = t.stmt(StmtKind::Unreachable);
        let cond = t.rd(choice);
        let proof = t.if_then(cond, vec![reveal, proof_check, dead_end]);
        let proved = t.assume(positive.clone());
        let conclusion = if claim_definition {
            let call = t.call(fn_id(1), vec![], Ty::int());
            let one = t.lit(1, Ty::int());
            t.cmp(BinOp::Eq, call, one)
        } else {
            positive
        };
        let check = t.assert(conclusion);
        let ret = t.ret(None);
        krate(vec![
            opaque_one(),
            t.body(vec![arbitrary, proof, proved, check, ret]),
        ])
    };
    assert_eq!(verdicts(&checks_of(&build(false), 2)), "PP");
    assert_eq!(verdicts(&checks_of(&build(true), 2)), "PR");
}

/// All paths reaching the assertion revealed `one`, including the path
/// through a nested branch whose sibling returns. Check both orientations
/// of that return and the one-line false twin of the final assertion.
#[test]
fn nested_branch_reveal_survives_a_returning_sibling() {
    let build = |return_then: bool, claim: i128| {
        let mut t = Fb::new(2, "t", Mode::Proof, Ty::Unit);
        let a = t.param("a", Ty::Bool);
        let b = t.param("b", Ty::Bool);
        let outer_reveal = t.stmt(StmtKind::Reveal {
            callee: fn_id(1),
            fuel: None,
        });
        let inner_reveal = t.stmt(StmtKind::Reveal {
            callee: fn_id(1),
            fuel: None,
        });
        let inner_return = t.ret(None);
        let (then_stmts, else_stmts) = if return_then {
            (vec![inner_return], vec![inner_reveal])
        } else {
            (vec![inner_reveal], vec![inner_return])
        };
        let inner_cond = t.rd(b);
        let inner = t.stmt(StmtKind::If {
            cond: inner_cond,
            then_block: Block::new(then_stmts),
            else_block: Block::new(else_stmts),
        });
        let outer_cond = t.rd(a);
        let outer = t.stmt(StmtKind::If {
            cond: outer_cond,
            then_block: Block::new(vec![outer_reveal]),
            else_block: Block::new(vec![inner]),
        });
        let call = t.call(fn_id(1), vec![], Ty::int());
        let expected = t.lit(claim, Ty::int());
        let goal = t.cmp(BinOp::Eq, call, expected);
        let check = t.assert(goal);
        let ret = t.ret(None);
        krate(vec![opaque_one(), t.body(vec![outer, check, ret])])
    };
    for return_then in [false, true] {
        assert_eq!(verdicts(&checks_of(&build(return_then, 1), 2)), "P");
        assert_eq!(verdicts(&checks_of(&build(return_then, 2), 2)), "R");
    }
}
