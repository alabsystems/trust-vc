//! Spec-controlled physical branches retain every check and actual guard.
use super::*;

fn guarded_checks(bad_branch: bool, wrong_assertion: bool) -> VcCrate {
    let mut f = Fb::new(1530, "guarded_spec_checks", Mode::Exec, Ty::Unit);
    let c = f.param("c", Ty::Bool);
    f.decl.locals[c.index()].mode = Mode::Spec;
    let condition = f.rd(c);
    let expected = f.tt(bad_branch);
    let required = f.bin(BinOp::Eq, condition, expected, Ty::Bool);
    let clause = f.clause(required);
    f.decl.requires.push(clause);
    let result = f.let_local("result", Ty::uint(8));
    f.decl.locals[result.index()].mode = Mode::Spec;
    f.decl.locals[result.index()].prophecy = trust_vc_vcir::DeclProphecy::DelayedInfer;
    f.decl.locals[result.index()].kind = LocalKind::Temp;
    let declared = f.stmt(StmtKind::Let {
        local: result,
        init: None,
    });
    let a = f.lit(255, Ty::uint(8));
    let b = f.lit(1, Ty::uint(8));
    let value = f.checked(BinOp::Add, a, b);
    let yes = f.stmt(StmtKind::AssignSpec {
        place: Place::local(result),
        value,
    });
    let a = f.lit(0, Ty::uint(8));
    let b = f.lit(1, Ty::uint(8));
    let value = f.checked(BinOp::Add, a, b);
    let no = f.stmt(StmtKind::AssignSpec {
        place: Place::local(result),
        value,
    });
    let cond = f.rd(c);
    let branch = f.stmt(StmtKind::IfSpec {
        cond,
        then_block: Block::new(vec![yes]),
        else_block: Block::new(vec![no]),
    });
    let mut body = vec![declared, branch];
    if !bad_branch {
        let result = f.rd(result);
        let one = f.lit(if wrong_assertion { 2 } else { 1 }, Ty::uint(8));
        let expr = f.bin(BinOp::Eq, result, one, Ty::Bool);
        body.push(f.assert(expr));
    }
    body.push(f.ret(None));
    krate(vec![f.body(body)])
}

#[test]
fn spec_guarded_assignment_checks_are_neither_erased_nor_unconditionally_assumed() {
    assert_eq!(
        verdicts(&checks_of(&guarded_checks(false, false), 1530)),
        "PPP"
    );
    assert_eq!(
        verdicts(&checks_of(&guarded_checks(false, true), 1530)),
        "PPR"
    );
    assert_eq!(
        verdicts(&checks_of(&guarded_checks(true, false), 1530)),
        "RP"
    );
}

#[test]
fn checked_spec_store_preserves_ordinary_rhs_value_and_overflow() {
    for (overflow, expected) in [(false, "PP"), (true, "R")] {
        let mut f = Fb::new(1531, "checked_store", Mode::Exec, Ty::Unit);
        let x = f.param("x", Ty::uint(8));
        f.decl.locals[x.index()].mode = Mode::Spec;
        let read = f.rd(x);
        let limit = f.lit(255, Ty::uint(8));
        let precondition = f.bin(
            if overflow { BinOp::Eq } else { BinOp::Lt },
            read,
            limit,
            Ty::Bool,
        );
        let clause = f.clause(precondition);
        f.decl.requires.push(clause);
        let y = f.let_local("y", Ty::uint(8));
        f.decl.locals[y.index()].mode = Mode::Spec;
        let zero = f.lit(0, Ty::uint(8));
        let declared = f.stmt(StmtKind::Let {
            local: y,
            init: Some(zero),
        });
        let read = f.rd(x);
        let one = f.lit(1, Ty::uint(8));
        let value = f.checked(BinOp::Add, read, one);
        let assigned = f.stmt(StmtKind::AssignSpec {
            place: Place::local(y),
            value,
        });
        let mut body = vec![declared, assigned];
        if !overflow {
            let y = f.rd(y);
            let x = f.rd(x);
            let assertion = f.bin(BinOp::Gt, y, x, Ty::Bool);
            body.push(f.assert(assertion));
        }
        body.push(f.ret(None));
        assert_eq!(
            verdicts(&checks_of(&krate(vec![f.body(body)]), 1531)),
            expected
        );
    }
}
