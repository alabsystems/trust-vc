//! Genuine solver controls: Spec-valued checked evaluation is neither erased nor assumed.
use super::*;

fn arithmetic(false_assertion: bool, overflow: bool) -> VcCrate {
    let mut f = Fb::new(1300, "spec_checked", Mode::Exec, Ty::Unit);
    let x = f.param("x", Ty::uint(8));
    f.decl.locals[x.index()].mode = Mode::Spec;
    let value = f.let_local("value", Ty::uint(8));
    f.decl.locals[value.index()].mode = Mode::Spec;
    let read = f.rd(x);
    let limit = f.lit(255, Ty::uint(8));
    let condition = f.bin(
        if overflow { BinOp::Eq } else { BinOp::Lt },
        read,
        limit,
        Ty::Bool,
    );
    let clause = f.clause(condition);
    f.decl.requires.push(clause);
    let read = f.rd(x);
    let one = f.lit(1, Ty::uint(8));
    let init = f.checked(BinOp::Add, read, one);
    let binding = f.stmt(StmtKind::LetChecked { local: value, init });
    let mut body = vec![binding];
    if !overflow {
        let value = f.rd(value);
        let original = f.rd(x);
        let assertion = f.bin(
            if false_assertion {
                BinOp::Eq
            } else {
                BinOp::Gt
            },
            value,
            original,
            Ty::Bool,
        );
        body.push(f.assert(assertion));
    }
    body.push(f.ret(None));
    krate(vec![f.body(body)])
}

#[test]
fn spec_inputs_keep_both_overflow_and_truth_obligations() {
    assert_eq!(verdicts(&checks_of(&arithmetic(false, false), 1300)), "PP");
    assert_eq!(verdicts(&checks_of(&arithmetic(true, false), 1300)), "PR");
    assert_eq!(verdicts(&checks_of(&arithmetic(false, true), 1300)), "R");
}

fn conditional(take_bad_arm: bool) -> VcCrate {
    let mut f = Fb::new(1301, "conditional_checked", Mode::Exec, Ty::Unit);
    let choose = f.param("choose", Ty::Bool);
    f.decl.locals[choose.index()].mode = Mode::Spec;
    let value = f.let_local("value", Ty::uint(8));
    f.decl.locals[value.index()].mode = Mode::Spec;
    let condition = f.rd(choose);
    let required = f.tt(take_bad_arm);
    let condition = f.bin(BinOp::Eq, condition, required, Ty::Bool);
    let clause = f.clause(condition);
    f.decl.requires.push(clause);
    let a = f.lit(255, Ty::uint(8));
    let b = f.lit(1, Ty::uint(8));
    let bad = f.checked(BinOp::Add, a, b);
    let a = f.lit(0, Ty::uint(8));
    let b = f.lit(1, Ty::uint(8));
    let good = f.checked(BinOp::Add, a, b);
    let condition = f.rd(choose);
    let init = Expr::new(
        Ty::uint(8),
        f.span(),
        ExprKind::If {
            cond: Box::new(condition),
            then_expr: Box::new(bad),
            else_expr: Box::new(good),
        },
    );
    let binding = f.stmt(StmtKind::LetChecked { local: value, init });
    let returned = f.ret(None);
    krate(vec![f.body(vec![binding, returned])])
}

#[test]
fn conditional_checks_retain_their_actual_guards() {
    assert_eq!(verdicts(&checks_of(&conditional(false), 1301)), "PP");
    assert_eq!(verdicts(&checks_of(&conditional(true), 1301)), "RP");
}
