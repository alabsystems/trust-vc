//! Prophecy effects are checked before either ordinary or diagnostic generation.
//! Controls follow upstream `rust_verify_test/tests/prophecy.rs` using real
//! prophetic declarations; no future/reference semantics are assumed here.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_vcir::vcgen::{self, FnVcs};
use trust_vc_vcir::*;

fn id(n: u64) -> FnId {
    FnId(DefHash::new(91, n))
}
fn span() -> SpanId {
    SpanId(0)
}
fn boolean(value: bool) -> Expr {
    Expr::bool_lit(value, span())
}
fn integer(value: i128) -> Expr {
    Expr::int_lit(value, Ty::int(), span())
}
fn local(ty: Ty, mode: Mode, kind: LocalKind, prophecy: DeclProphecy) -> LocalDecl {
    LocalDecl {
        name: "value".into(),
        ty,
        mode,
        prophecy,
        mutable: kind == LocalKind::Let,
        kind,
        span: span(),
    }
}
fn function(n: u64, mode: Mode, result: Ty) -> FnDecl {
    FnDecl {
        id: id(n),
        name: format!("f{n}"),
        span: span(),
        mode,
        role: FnRole::Item,
        kind: FnKind::Function,
        type_params: vec![],
        locals: vec![local(
            result,
            if mode == Mode::Exec {
                Mode::Exec
            } else {
                Mode::Spec
            },
            LocalKind::Return,
            DeclProphecy::Default,
        )],
        params: vec![],
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        unwind: None,
        attrs: FnAttrs::default(),
        body: if mode == Mode::Spec {
            Body::None
        } else {
            Body::Stmts(Block::default())
        },
    }
}
fn add(decl: &mut FnDecl, ty: Ty, mode: Mode, kind: LocalKind, prophecy: DeclProphecy) -> LocalId {
    let id = LocalId(decl.locals.len() as u32);
    decl.locals.push(local(ty, mode, kind, prophecy));
    if kind == LocalKind::Param {
        decl.params.push(id);
    }
    id
}
fn read(local: LocalId, ty: Ty) -> Expr {
    Expr::read(Place::local(local), ty, span())
}
fn call(n: u64, ty: Ty, args: Vec<Expr>) -> Expr {
    Expr::new(
        ty,
        span(),
        ExprKind::Call {
            callee: id(n),
            type_args: vec![],
            args,
        },
    )
}
fn stmt(kind: StmtKind) -> Stmt {
    Stmt::new(span(), kind)
}
fn let_stmt(local: LocalId, init: Option<Expr>) -> Stmt {
    stmt(StmtKind::Let { local, init })
}
fn assign(local: LocalId, value: Expr) -> Stmt {
    stmt(StmtKind::Assign {
        place: Place::local(local),
        value,
    })
}
fn invoke(n: u64, args: Vec<Expr>, dest: Option<LocalId>, site: u32) -> Stmt {
    stmt(StmtKind::Call {
        callee: id(n),
        type_args: vec![],
        args,
        dest: dest.map(Place::local),
        site: SiteId(site),
    })
}
fn branch(cond: Expr, yes: Vec<Stmt>) -> Stmt {
    stmt(StmtKind::If {
        cond,
        then_block: Block::new(yes),
        else_block: Block::default(),
    })
}
fn assume(expr: Expr) -> Stmt {
    stmt(StmtKind::Assume {
        expr,
        attrs: ClauseAttrs::default(),
    })
}
fn source(mut functions: Vec<FnDecl>) -> VcCrate {
    let mut seed = function(1, Mode::Spec, Ty::Bool);
    seed.attrs.prophetic = true;
    seed.body = Body::Spec(boolean(true));
    let mut krate = VcCrate::new("prophecy effects");
    krate.fns.push(seed);
    krate.fns.append(&mut functions);
    krate
}
fn accepted(krate: &VcCrate) {
    assert!(check_crate(krate).is_empty(), "{:?}", check_crate(krate));
    assert!(check_crate_for_diagnostics(krate).errors.is_empty());
}
fn rejected(krate: &VcCrate, owner: u64, message: &str) {
    let errors = check_crate(krate);
    assert!(
        errors.iter().all(|e| e.class == WfClass::User),
        "{errors:?}"
    );
    assert!(
        errors
            .iter()
            .any(|e| e.function == Some(id(owner)) && e.message.contains(message)),
        "{errors:?}"
    );
    assert_eq!(check_crate_for_diagnostics(krate).errors, errors);
}

fn loop_stmt(cond: Option<LoopCond>, body: Vec<Stmt>, decreases: Vec<Expr>) -> Stmt {
    stmt(StmtKind::Loop(Box::new(Loop {
        id: LoopId(1),
        isolation: true,
        allow_complex_invariants: false,
        cond,
        invariants: vec![],
        decreases,
        body: Block::new(body),
        sites: LoopSites {
            entry: SiteId(10),
            end: SiteId(11),
            exit: SiteId(12),
        },
    })))
}

#[path = "prophecy_flow/binders.rs"]
mod binders;
#[path = "prophecy_flow/calls_and_branches.rs"]
mod calls_and_branches;
#[path = "prophecy_flow/declarations.rs"]
mod declarations;
#[path = "prophecy_flow/loops.rs"]
mod loops;
#[path = "prophecy_flow/values.rs"]
mod values;

#[test]
fn annotated_constant_calls_taint_bodies_and_both_generation_entries_refuse() {
    values::annotated_constant_calls_taint_bodies_and_both_generation_entries_refuse();
}

#[test]
fn pure_spec_parameters_start_nonprophetic_and_calls_join_actual_arguments() {
    values::pure_spec_parameters_start_nonprophetic_and_calls_join_actual_arguments();
}

#[test]
fn expression_let_discards_unused_initializer_but_propagates_bound_reads() {
    values::expression_let_discards_unused_initializer_but_propagates_bound_reads();
}

#[test]
fn constant_if_arms_still_depend_on_the_prophetic_condition() {
    values::constant_if_arms_still_depend_on_the_prophetic_condition();
}

#[test]
fn inference_is_fixed_at_declaration_and_explicit_prophetic_constants_stay_prophetic() {
    values::inference_is_fixed_at_declaration_and_explicit_prophetic_constants_stay_prophetic();
}

#[test]
fn default_no_initializer_is_fixed_but_delayed_inference_uses_first_assignment() {
    values::default_no_initializer_is_fixed_but_delayed_inference_uses_first_assignment();
}

#[test]
fn delayed_inference_does_not_join_outer_control_on_first_assignment() {
    values::delayed_inference_does_not_join_outer_control_on_first_assignment();
}

#[test]
fn inferred_initializers_and_conditional_declarations_are_prophetic() {
    values::inferred_initializers_and_conditional_declarations_are_prophetic();
}

#[test]
fn non_ghost_declarations_and_exec_arguments_reject_prophetic_data() {
    calls_and_branches::non_ghost_declarations_and_exec_arguments_reject_prophetic_data();
}

#[test]
fn exec_calls_and_returns_cannot_be_prophecy_conditional() {
    calls_and_branches::exec_calls_and_returns_cannot_be_prophecy_conditional();
}

#[test]
fn proof_calls_allow_only_spec_parameters_and_spec_or_unit_results() {
    calls_and_branches::proof_calls_allow_only_spec_parameters_and_spec_or_unit_results();
}

#[test]
fn pure_spec_result_proof_call_preserves_argument_taint_at_its_destination() {
    calls_and_branches::pure_spec_result_proof_call_preserves_argument_taint_at_its_destination();
}

#[test]
fn generated_conditional_results_join_both_branches_independently() {
    calls_and_branches::generated_conditional_results_join_both_branches_independently();
}

#[test]
fn generated_short_circuit_results_include_condition_and_require_both_initializations() {
    calls_and_branches::generated_short_circuit_results_include_condition_and_require_both_initializations();
}

#[test]
fn prophetic_functions_still_cannot_use_prophecy_for_termination_measures() {
    loops::prophetic_functions_still_cannot_use_prophecy_for_termination_measures();
}

#[test]
fn loop_condition_retains_taint_from_its_computation_block() {
    loops::loop_condition_retains_taint_from_its_computation_block();
}

#[test]
fn loop_decreases_reject_prophetic_values() {
    loops::loop_decreases_reject_prophetic_values();
}

#[test]
fn loop_and_loop_control_cannot_depend_on_prophetic_conditions() {
    loops::loop_and_loop_control_cannot_depend_on_prophetic_conditions();
}

#[test]
fn quantifier_triggers_do_not_taint_values_but_quantifier_bodies_do() {
    binders::quantifier_triggers_do_not_taint_values_but_quantifier_bodies_do();
}

#[test]
fn choose_joins_condition_and_result_with_nonprophetic_bound_variables() {
    binders::choose_joins_condition_and_result_with_nonprophetic_bound_variables();
}

#[test]
fn diagnostic_binders_keep_prophecy_errors_and_other_function_diagnostics() {
    binders::diagnostic_binders_keep_prophecy_errors_and_other_function_diagnostics();
}

#[test]
fn short_circuit_control_reaches_embedded_proof_blocks() {
    binders::short_circuit_control_reaches_embedded_proof_blocks();
}

#[test]
fn only_spec_functions_and_ghost_declarations_can_be_marked_prophetic() {
    declarations::only_spec_functions_and_ghost_declarations_can_be_marked_prophetic();
}

#[test]
fn checked_imported_definition_cannot_change_the_signature_prophecy_effect() {
    declarations::checked_imported_definition_cannot_change_the_signature_prophecy_effect();
}
