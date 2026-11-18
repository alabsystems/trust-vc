//! New evaluation forms preserve the original value/conditional distinction.
use super::*;

fn source_assignment(checked: bool) -> VcCrate {
    let mut f = function(
        1540,
        if checked { Mode::Exec } else { Mode::Proof },
        Ty::Unit,
    );
    let target = add(
        &mut f,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Let,
        DeclProphecy::DelayedInfer,
    );
    let assignment = stmt(if checked {
        StmtKind::AssignSpec {
            place: Place::local(target),
            value: boolean(false),
        }
    } else {
        StmtKind::Assign {
            place: Place::local(target),
            value: boolean(false),
        }
    });
    let kind = if checked {
        StmtKind::IfSpec {
            cond: call(1, Ty::Bool, vec![]),
            then_block: Block::new(vec![assignment]),
            else_block: Block::default(),
        }
    } else {
        StmtKind::If {
            cond: call(1, Ty::Bool, vec![]),
            then_block: Block::new(vec![assignment]),
            else_block: Block::default(),
        }
    };
    f.body = Body::Stmts(Block::new(vec![let_stmt(target, None), stmt(kind)]));
    source(vec![f])
}

#[test]
fn checked_store_does_not_manufacture_rhs_taint_from_a_prophetic_guard() {
    let ordinary = check_crate(&source_assignment(false));
    let checked = check_crate(&source_assignment(true));
    assert_eq!(checked, ordinary);
    assert_eq!(checked.len(), 1, "{checked:?}");
    assert!(checked[0].message.contains(
        "assignment to non-prophetic location cannot occur in prophecy-conditional context"
    ));
    assert!(!checked[0].message.contains("prophetic value not allowed"));
}

fn unit_result(complete: bool, duplicate: bool) -> VcCrate {
    let mut producer = function(1541, Mode::Proof, Ty::Unit);
    producer.locals[producer.ret.index()].mode = Mode::Proof;
    let mut caller = function(1542, Mode::Exec, Ty::Unit);
    let c = add(
        &mut caller,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Param,
        DeclProphecy::Default,
    );
    let result = add(
        &mut caller,
        Ty::Unit,
        Mode::Spec,
        LocalKind::Temp,
        DeclProphecy::DelayedInfer,
    );
    let mut yes = vec![invoke(1541, vec![], Some(result), 1)];
    if duplicate {
        yes.push(invoke(1541, vec![], Some(result), 2));
    }
    let no = if complete {
        vec![invoke(1541, vec![], Some(result), 3)]
    } else {
        vec![]
    };
    caller.body = Body::Stmts(Block::new(vec![
        let_stmt(result, None),
        stmt(StmtKind::IfSpec {
            cond: read(c, Ty::Bool),
            then_block: Block::new(yes),
            else_block: Block::new(no),
        }),
        stmt(StmtKind::GhostTail {
            block: Block::default(),
            tail: read(result, Ty::Unit),
        }),
    ]));
    source(vec![producer, caller])
}

#[test]
fn spec_storage_does_not_clear_raw_unit_origins_and_missing_or_reused_origins_stay_unknown() {
    use trust_vc_vcir::wf::{ghost_tail_modes, GhostTailModeClass};
    let good = unit_result(true, false);
    accepted(&good);
    let observations = ghost_tail_modes(&good);
    assert_eq!(observations.len(), 1);
    assert_eq!(observations[0].class, Some(GhostTailModeClass::NonSpec));
    for bad in [unit_result(false, false), unit_result(true, true)] {
        let observations = ghost_tail_modes(&bad);
        assert_eq!(observations.len(), 1);
        assert_eq!(observations[0].class, None);
        assert!(check_crate(&bad).iter().any(|e| e
            .message
            .contains("without a valid raw Unit value-mode origin")));
    }
}

#[test]
fn checked_store_keeps_explicit_prophetic_marker_and_tainted_rhs() {
    let mut f = function(1543, Mode::Exec, Ty::Bool);
    f.locals[f.ret.index()].mode = Mode::Spec;
    let target = add(
        &mut f,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Let,
        DeclProphecy::Prophetic,
    );
    f.body = Body::Stmts(Block::new(vec![
        let_stmt(target, Some(boolean(false))),
        stmt(StmtKind::AssignSpec {
            place: Place::local(target),
            value: call(1, Ty::Bool, vec![]),
        }),
        stmt(StmtKind::Return {
            value: Some(read(target, Ty::Bool)),
            site: SiteId(1),
        }),
    ]));
    rejected(
        &source(vec![f]),
        1543,
        "prophetic value not allowed for return value",
    );
}
