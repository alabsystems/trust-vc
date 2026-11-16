//! Native encoder and solver controls for template-scoped ground demand.
use super::*;
use crate::encoder::diagnostics::EncodingApproximation;
use crate::encoder::tests::result_oracles::{expect_counterexample, expect_verified};
use crate::ir::{ArithOp, TrustVcType};
use crate::prepared_context::prepare_context;
use crate::vc::{FunctionContext, ProofObligation, VerificationContext};

fn int_ty() -> TrustVcType {
    TrustVcType::Int { width: 32 }
}
fn var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.into(),
        ty: int_ty(),
    }
}
fn lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: int_ty(),
    }
}
fn call(name: &str, args: Vec<TrustVcExpr>) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: name.into(),
        args,
        return_ty: int_ty(),
    }
}
fn context() -> VerificationContext {
    let mut ctx = VerificationContext::new();
    for name in ["n", "m"] {
        ctx.declare_var_typed(name, int_ty());
    }
    for name in ["f", "g", "h"] {
        ctx.declare_helper_function_typed(name, int_ty(), vec![("x".into(), int_ty())]);
    }
    ctx.declare_helper_function_typed("q", int_ty(), vec![]);
    // Existing zero-arity compatibility uses the same native variable namespace.
    ctx.declare_helper_function_typed("n", int_ty(), vec![]);
    ctx
}
fn encoder(ctx: &VerificationContext) -> AYEncoder {
    let prepared = prepare_context(ctx).expect("typed context");
    let mut encoder = AYEncoder::new();
    for variable in &prepared.variables {
        encoder.declare_variable(variable).expect("variable");
    }
    for helper in &prepared.helper_function_contexts {
        encoder.register_function_context(helper).expect("helper");
    }
    encoder
}
fn encode(encoder: &mut AYEncoder, expr: TrustVcExpr) -> Term {
    encoder
        .encode_condition_typed(&expr)
        .expect("actual typed expression")
}

#[test]
fn template_scope_keeps_closed_subcalls_and_real_symbolic_callers() {
    let mut encoder = encoder(&context());
    let n = encoder.variables["n"];
    encoder.with_ground_template_scope(&[n], |encoder| {
        encode(encoder, call("f", vec![call("g", vec![var("n")])]));
        assert_eq!(encoder.state.ground_pool.ground_term_count(), 0);
        encode(encoder, call("f", vec![call("g", vec![lit(5)])]));
        assert_eq!(
            encoder.state.ground_pool.ground_term_count(),
            2,
            "closed g(5) and its closed caller remain genuine dependencies"
        );
        encode(
            encoder,
            TrustVcExpr::Let {
                name: "alias".into(),
                ty: int_ty(),
                value: Box::new(var("n")),
                body: Box::new(call("h", vec![var("alias")])),
            },
        );
        assert_eq!(
            encoder.state.ground_pool.ground_term_count(),
            2,
            "a native alias of the binder remains a template"
        );
        encode(
            encoder,
            TrustVcExpr::Let {
                name: "n".into(),
                ty: int_ty(),
                value: Box::new(lit(5)),
                body: Box::new(call("h", vec![var("n")])),
            },
        );
        assert_eq!(
            encoder.state.ground_pool.ground_term_count(),
            3,
            "a shadowed constant is ground, despite its source spelling"
        );
        encode(
            encoder,
            call(
                "h",
                vec![TrustVcExpr::Arith {
                    op: ArithOp::Sub,
                    left: Box::new(var("n")),
                    right: Box::new(var("n")),
                    ty: int_ty(),
                }],
            ),
        );
        assert_eq!(
            encoder.state.ground_pool.ground_term_count(),
            4,
            "a folded closed native argument is a genuine seed"
        );
        encode(encoder, call("n", vec![]));
        assert_eq!(
            encoder.state.ground_pool.ground_term_count(),
            4,
            "zero-arity variable compatibility must inspect the result Term"
        );
        encode(encoder, call("q", vec![]));
        assert_eq!(
            encoder.state.ground_pool.ground_term_count(),
            5,
            "a genuine independent zero-arity function is preserved"
        );
    });
    encode(&mut encoder, call("f", vec![var("n")]));
    assert_eq!(
        encoder.state.ground_pool.ground_term_count(),
        6,
        "the SAME free native n is genuine demand after the template scope"
    );
}

#[test]
fn template_scope_unions_nested_binders_and_restores_on_error_and_unwind() {
    let mut encoder = encoder(&context());
    let n = encoder.variables["n"];
    let m = encoder.variables["m"];
    encoder.with_ground_template_scope(&[n], |encoder| {
        let failed: Result<(), ()> = encoder.with_ground_template_scope(&[m], |encoder| {
            encode(encoder, call("f", vec![var("n")]));
            encode(encoder, call("g", vec![var("m")]));
            assert_eq!(encoder.state.ground_pool.ground_term_count(), 0);
            Err(())
        });
        assert!(failed.is_err());
        encode(encoder, call("g", vec![var("m")]));
        assert_eq!(encoder.state.ground_pool.ground_term_count(), 1);
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            encoder.with_ground_template_scope(&[m], |encoder| {
                encode(encoder, call("h", vec![var("m")]));
                panic!("template unwind control");
            });
        }));
        assert!(panic.is_err());
        encode(encoder, call("h", vec![var("m")]));
        encode(encoder, call("f", vec![var("n")]));
        assert_eq!(
            encoder.state.ground_pool.ground_term_count(),
            2,
            "inner scope restored; the outer binder remains active"
        );
    });
    encode(&mut encoder, call("f", vec![var("n")]));
    assert_eq!(encoder.state.ground_pool.ground_term_count(), 3);
    let mut other = Solver::try_new(ay_dpll::api::Logic::All).expect("other real solver");
    let foreign = other.declare_const("foreign", ay_dpll::api::Sort::bitvec(32));
    let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        encoder.with_ground_template_scope(&[foreign], |_| ());
    }));
    assert!(
        rejected.is_err(),
        "foreign scope handles must not become clean leaves"
    );
    assert!(encoder.state.ground_pool.template_scopes.is_empty());
    let rejected_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        encoder.with_ground_template_scope(&[n], |encoder| {
            encoder.state.ground_pool.register_expr_scoped(
                &encoder.solver,
                "foreign",
                vec![],
                vec![],
                foreign,
            );
        });
    }));
    assert!(
        rejected_result.is_err(),
        "foreign candidate results must not become clean leaves"
    );
    assert!(encoder.state.ground_pool.template_scopes.is_empty());
    assert_eq!(encoder.state.ground_pool.ground_term_count(), 3);
    encoder.with_ground_template_scope(&[], |encoder| {
        encode(encoder, call("h", vec![var("n")]));
    });
    assert_eq!(
        encoder.state.ground_pool.ground_term_count(),
        4,
        "the zero-binder path retains ordinary caller demand"
    );
}

#[test]
fn inferred_trigger_templates_do_not_mint_ground_demand() {
    let mut ctx = context();
    ctx.obligations.push(
        ProofObligation::broadcast_assume("f_identity", "f(n) == n")
            .with_bound_vars(vec!["n".into()]),
    );
    let prepared = prepare_context(&ctx).expect("prepare inferred trigger");
    let mut encoder = encoder(&ctx);
    let all: Vec<_> = encoder.variables.values().copied().collect();
    encoder
        .add_typed_broadcast(&prepared.obligations[0], &all)
        .expect("broadcast");
    assert_eq!(
        encoder.state.ground_pool.ground_term_count(),
        0,
        "neither body nor inferred trigger is a caller occurrence"
    );
    encode(&mut encoder, call("f", vec![lit(5)]));
    assert_eq!(encoder.state.ground_pool.ground_term_count(), 1);
}

#[test]
fn template_filter_preserves_positive_false_and_symbolic_core_verdicts() {
    for (goal, should_verify) in [
        ("f(5) == 5", true),
        ("f(5) == 6", false),
        ("f(n) == n", true),
        ("f(n) == n + 1", false),
    ] {
        let mut ctx = context();
        ctx.set_function_context(FunctionContext {
            name: "f".into(),
            params: vec![("n".into(), int_ty())],
            return_type: int_ty(),
            is_recursive: true,
            mode: crate::mode::FunctionMode::Spec,
            trait_bounds: vec![],
        });
        ctx.obligations.push(
            ProofObligation::broadcast_assume("__body_axiom_f", "f(n) == n")
                .with_bound_vars(vec!["n".into()])
                .with_trigger_patterns(vec![vec!["f(n)".into()]]),
        );
        ctx.push_obligation(ProofObligation::assert("actual_caller", goal));
        let result = AYEncoder::verify(&ctx);
        if should_verify {
            expect_verified(&result, goal);
        } else {
            expect_counterexample(&result, goal);
        }
    }
}

#[test]
fn closed_nested_callee_survives_when_its_universal_is_declined() {
    fn ctx(goal: Option<&str>) -> VerificationContext {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("n", int_ty());
        ctx.declare_var_typed("x", TrustVcType::Uint { width: 32 });
        ctx.declare_helper_function_typed(
            "g",
            int_ty(),
            vec![("x".into(), TrustVcType::Uint { width: 32 })],
        );
        ctx.declare_helper_function_typed("f", int_ty(), vec![("n".into(), int_ty())]);
        ctx.obligations.push(
            ProofObligation::broadcast_assume("__body_axiom_g", "g(x) == x as i32")
                .with_bound_vars(vec!["x".into()])
                .with_trigger_patterns(vec![vec!["g(x)".into()]]),
        );
        ctx.obligations.push(
            ProofObligation::broadcast_assume("__body_axiom_f", "f(n) == g(5u32)")
                .with_bound_vars(vec!["n".into()])
                .with_trigger_patterns(vec![vec!["f(n)".into()]]),
        );
        if let Some(goal) = goal {
            ctx.push_obligation(ProofObligation::assert("nested_ground_caller", goal));
        }
        ctx
    }
    let context = ctx(None);
    let prepared = prepare_context(&context).expect("prepare callee recovery");
    let mut encoder = encoder(&context);
    let all: Vec<_> = encoder.variables.values().copied().collect();
    encoder
        .add_typed_broadcast(&prepared.obligations[0], &all)
        .expect("callee");
    assert!(
        encoder
            .state
            .diagnostics
            .count(EncodingApproximation::HoistCapturedByPendingBinder)
            > 0,
        "this control MUST exercise the real capture-declined callee boundary"
    );
    encoder
        .add_typed_broadcast(&prepared.obligations[1], &all)
        .expect("caller");
    assert_eq!(
        encoder.state.ground_pool.ground_term_count(),
        1,
        "closed g(5) survives; the two binder placeholders are not caller demand"
    );
    for (goal, should_verify) in [
        ("f(0) == 5", true),
        ("f(n) == 5", true),
        ("f(0) == 6", false),
    ] {
        let result = AYEncoder::verify(&ctx(Some(goal)));
        if should_verify {
            expect_verified(&result, goal);
        } else {
            expect_counterexample(&result, goal);
        }
    }
}
